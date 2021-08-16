// Copyright (c) 2016-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_UTIL_RBF_H
#define BITCOIN_UTIL_RBF_H

#include <cstdint>

class CTransaction;

static const uint32_t MAX_BIP125_RBF_SEQUENCE = 0xfffffffd;

// Check whether the sequence numbers on this transaction are signaling
// opt-in to replace-by-fee, according to BIP 125.
// rbf signaling is inherited, and while child transactions may not explicitly
// signal RBF (like this function checks for), they will inherit rbf
// replaceability if any of their unconfirmed parents are signaling opt-in to rbf.
bool SignalsOptInRBF(const CTransaction &tx);

#endif // BITCOIN_UTIL_RBF_H
