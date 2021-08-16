// Copyright (c) 2016-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <consensus/validation.h>
#include <logging.h>
#include <policy/rbf.h>
#include <policy/settings.h>
#include <util/moneystr.h>
#include <util/rbf.h>

#include <string>

RBFTransactionState IsRBFOptIn(const CTransaction& tx, const CTxMemPool& pool)
{
    AssertLockHeld(pool.cs);

    // If this transaction is not in our mempool, then we can't be sure
    // we will know about all its inputs.
    if (!pool.exists(tx.GetHash())) {
        return RBFTransactionState::UNKNOWN;
    }

    // Now check the transaction itself.
    CTxMemPoolEntry entry = *pool.mapTx.find(tx.GetHash());
    // If we've already exceeded `MAX_BIP125_REPLACEMENT_CANDIDATES` then there's
    // no need to do extra work checking tx's ancestors.
    if (entry.GetCountWithDescendants() > MAX_BIP125_REPLACEMENT_CANDIDATES) {
      return RBFTransactionState::FINAL;
    }
    if (SignalsOptInRBF(tx)) {
        return RBFTransactionState::REPLACEABLE_BIP125;
    }

    // Now check if RBF signaling is inherited from any unconfirmed ancestors.
    CTxMemPool::setEntries set_ancestors;
    CTxMemPoolEntry::Parents staged_ancestors = entry.GetMemPoolParentsConst();
    // This is a breadth-first traversal of tx's unconfirmed ancestors.
    while (!staged_ancestors.empty()) {
        const CTxMemPoolEntry& stage = staged_ancestors.begin()->get();
        const CTxMemPool::txiter stage_it = pool.mapTx.iterator_to(stage);
        set_ancestors.insert(stage_it);
        staged_ancestors.erase(stage);

        // If we exceeded `MAX_BIP125_REPLACEMENT_CANDIDATES` then there's
        // no need to do extra work checking stage's ancestors.
        if (stage.GetCountWithDescendants() > MAX_BIP125_REPLACEMENT_CANDIDATES) {
            continue;
        }
        // We can return once we find a single ancestor signaling RBF. This is
        // because RBF opt-in is inherited if *any* unconfirmed ancestors are signaling.
        if (SignalsOptInRBF(stage.GetTx())) {
            return RBFTransactionState::REPLACEABLE_BIP125;
        }

        for (const CTxMemPoolEntry& parent : stage.GetMemPoolParentsConst()) {
            const CTxMemPool::txiter parent_it = pool.mapTx.iterator_to(parent);
            // If this is a new ancestor, add it.
            if (set_ancestors.count(parent_it) == 0) {
                staged_ancestors.insert(parent);
            }
        }
    }
    return RBFTransactionState::FINAL;
}

bool GetEntriesForRBF(const CTransaction& tx, CTxMemPool& m_pool,
                      const CTxMemPool::setEntries setIterConflicting,
                      TxValidationState& state, CTxMemPool::setEntries& allConflicting)
{
    AssertLockHeld(m_pool.cs);
    const uint256 hash = tx.GetHash();

    // Calculate the set of transactions that would have to be evicted
    for (CTxMemPool::txiter it : setIterConflicting) {
        m_pool.CalculateDescendants(it, allConflicting);
    }

    if (allConflicting.size() > MAX_BIP125_REPLACEMENT_CANDIDATES) {
      return state.Invalid(TxValidationResult::TX_MEMPOOL_POLICY, "too many replacements",
              strprintf("rejecting replacement %s; too many replacements (%d > %d)\n",
                  hash.ToString(),
                  allConflicting.size(),
                  MAX_BIP125_REPLACEMENT_CANDIDATES));
    }
    return true;
}

bool HasNoNewUnconfirmed(const CTransaction& tx, CTxMemPool& m_pool,
                         const CTxMemPool::setEntries setIterConflicting, TxValidationState& state)
{
    AssertLockHeld(m_pool.cs);
    std::set<uint256> setConflictsParents;
    for (const auto& mi : setIterConflicting) {
        for (const CTxIn &txin : mi->GetTx().vin)
        {
            setConflictsParents.insert(txin.prevout.hash);
        }
    }

    for (unsigned int j = 0; j < tx.vin.size(); j++)
    {
        // We don't want to accept replacements that require low
        // feerate junk to be mined first. Ideally we'd keep track of
        // the ancestor feerates and make the decision based on that,
        // but for now requiring all new inputs to be confirmed works.
        //
        // Note that if you relax this to make RBF a little more useful,
        // this may break the CalculateMempoolAncestors RBF relaxation,
        // above. See the comment above the first CalculateMempoolAncestors
        // call for more info.
        if (!setConflictsParents.count(tx.vin[j].prevout.hash))
        {
            // Rather than check the UTXO set - potentially expensive -
            // it's cheaper to just check if the new input refers to a
            // tx that's in the mempool.
            if (m_pool.exists(tx.vin[j].prevout.hash)) {
                return state.Invalid(TxValidationResult::TX_MEMPOOL_POLICY, "replacement-adds-unconfirmed",
                        strprintf("replacement %s adds unconfirmed input, idx %d",
                            tx.GetHash().ToString(), j));
            }
        }
    }
    return true;
}

bool SpendsAndConflictsDisjoint(CTxMemPool::setEntries& setAncestors, std::set<uint256> setConflicts,
                                TxValidationState& state, const uint256& hash)
{
    for (CTxMemPool::txiter ancestorIt : setAncestors)
    {
        const uint256 &hashAncestor = ancestorIt->GetTx().GetHash();
        if (setConflicts.count(hashAncestor))
        {
            return state.Invalid(TxValidationResult::TX_CONSENSUS, "bad-txns-spends-conflicting-tx",
                    strprintf("%s spends conflicting transaction %s",
                        hash.ToString(),
                        hashAncestor.ToString()));
        }
    }
    return true;
}

bool PaysMoreThanConflicts(const CTxMemPool::setEntries& setIterConflicting, CFeeRate newFeeRate,
                           TxValidationState& state, const uint256& hash)
{
    for (const auto& mi : setIterConflicting) {
        // Don't allow the replacement to reduce the feerate of the
        // mempool.
        //
        // We usually don't want to accept replacements with lower
        // feerates than what they replaced as that would lower the
        // feerate of the next block. Requiring that the feerate always
        // be increased is also an easy-to-reason about way to prevent
        // DoS attacks via replacements.
        //
        // We only consider the feerates of transactions being directly
        // replaced, not their indirect descendants. While that does
        // mean high feerate children are ignored when deciding whether
        // or not to replace, we do require the replacement to pay more
        // overall fees too, mitigating most cases.
        CFeeRate oldFeeRate(mi->GetModifiedFee(), mi->GetTxSize());
        if (newFeeRate <= oldFeeRate)
        {
            return state.Invalid(TxValidationResult::TX_MEMPOOL_POLICY, "insufficient fee",
                    strprintf("rejecting replacement %s; new feerate %s <= old feerate %s",
                        hash.ToString(),
                        newFeeRate.ToString(),
                        oldFeeRate.ToString()));
        }
    }
    return true;
}

bool PaysForRBF(CAmount nConflictingFees, CAmount nModifiedFees, size_t nSize,
                TxValidationState& state, const uint256& hash)
{
    // The replacement must pay greater fees than the transactions it
    // replaces - if we did the bandwidth used by those conflicting
    // transactions would not be paid for.
    if (nModifiedFees < nConflictingFees)
    {
        return state.Invalid(TxValidationResult::TX_MEMPOOL_POLICY, "insufficient fee",
                strprintf("rejecting replacement %s, less fees than conflicting txs; %s < %s",
                    hash.ToString(), FormatMoney(nModifiedFees), FormatMoney(nConflictingFees)));
    }

    // Finally in addition to paying more fees than the conflicts the
    // new transaction must pay for its own bandwidth.
    CAmount nDeltaFees = nModifiedFees - nConflictingFees;
    if (nDeltaFees < ::incrementalRelayFee.GetFee(nSize))
    {
        return state.Invalid(TxValidationResult::TX_MEMPOOL_POLICY, "insufficient fee",
                strprintf("rejecting replacement %s, not enough additional fees to relay; %s < %s",
                    hash.ToString(),
                    FormatMoney(nDeltaFees),
                    FormatMoney(::incrementalRelayFee.GetFee(nSize))));
    }
    return true;
}
