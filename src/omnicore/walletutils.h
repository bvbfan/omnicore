#ifndef BITCOIN_OMNICORE_WALLETUTILS_H
#define BITCOIN_OMNICORE_WALLETUTILS_H

class CPubKey;

namespace interfaces {
class Wallet;
class WalletLoader;
} // namespace interfaces

#include <script/standard.h>

#include <string>

#ifdef ENABLE_WALLET
namespace wallet {
class CCoinControl;
}
#endif

namespace mastercore
{
/** Retrieves a public key from the wallet, or converts a hex-string to a public key. */
bool AddressToPubKey(interfaces::Wallet *iWallet, const std::string& key, CPubKey& pubKey);

/** Checks, whether enough spendable outputs are available to pay for transaction fees. */
bool CheckFee(interfaces::Wallet& iWallet, const std::string& fromAddress, size_t nDataSize);

/** Checks, whether the output qualifies as input for a transaction. */
bool CheckInput(const CTxOut& txOut, int nHeight, CTxDestination& dest);

/** IsMine wrapper to determine whether the address is in the wallet. */
int IsMyAddress(const std::string& address, interfaces::Wallet* iWallet);

/** IsMine wrapper to determine whether the address is in the wallet. */
bool IsMyAddressAllWallets(const std::string& address);

/** Estimate the minimum fee considering user set parameters and the required fee. */
CAmount GetEstimatedFeePerKb(interfaces::Wallet& iWallet);

/** Output values below this value are considered uneconomic, because it would
* require more fees to pay than the output is worth. */
int64_t GetEconomicThreshold(interfaces::Wallet& iWallet, const CTxOut& txOut);

/** Init wallets based on node context */
void InitWallets(interfaces::WalletLoader* loader);

#ifdef ENABLE_WALLET
/** Selects spendable outputs to create a transaction. */
int64_t SelectCoins(interfaces::Wallet& iWallet, const std::string& fromAddress, wallet::CCoinControl& coinControl, int64_t amountRequired = 0);

/** Selects all spendable outputs to create a transaction. */
int64_t SelectAllCoins(interfaces::Wallet& iWallet, const std::string& fromAddress, wallet::CCoinControl& coinControl);
#endif
}

#endif // BITCOIN_OMNICORE_WALLETUTILS_H
