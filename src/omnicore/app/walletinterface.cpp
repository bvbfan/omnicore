// Copyright (c) 2018-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <interfaces/handler.h>
#include <interfaces/node.h>
#include <interfaces/wallet.h>

#include <consensus/amount.h>
#include <core_io.h>
#include <event2/http.h>
#include <key_io.h>
#include <omnicore/coinscache.h>
#include <omnicore/omnicore.h>
#include <omnicore/script.h>
#include <omnicore/utilsbitcoin.h>
#include <primitives/transaction.h>
#include <policy/fees.h>
#include <policy/fees_args.h>
#include <policy/policy.h>
#include <script/script.h>
#include <script/standard.h>
#include <sync.h>
#include <uint256.h>
#include <univalue.h>
#include <util/check.h>
#include <util/message.h>
#include <util/moneystr.h>
#include <util/strencodings.h>
#include <util/system.h>
#include <util/translation.h>
#include <util/ui_change_type.h>
#include <wallet/coincontrol.h>
#include <wallet/context.h>
#include <wallet/feebumper.h>
#include <wallet/fees.h>
#include <wallet/ismine.h>
#include <wallet/load.h>
#include <wallet/receive.h>
#include <wallet/rpc/wallet.h>
#include <wallet/spend.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>

#include <algorithm>
#include <memory>
#include <numeric>
#include <string>
#include <vector>

using interfaces::Node;
using interfaces::Handler;
using interfaces::Wallet;
using interfaces::WalletAddress;
using interfaces::WalletBalances;
using interfaces::WalletOrderForm;
using interfaces::WalletTx;
using interfaces::WalletTxOut;
using interfaces::WalletTxStatus;
using interfaces::WalletValueMap;
using mastercore::GetHeight;

namespace wallet {
// All members of the classes in this namespace are intentionally public, as the
// classes themselves are private.
namespace {

struct CWalletAddressInfo
{
    isminetype type = ISMINE_NO;
    bool is_change = false;
    CPubKey pubkey;
    std::string name;
};

class OmniWalletImpl : public Wallet
{
    std::string m_wallet_uri;
    std::unique_ptr<Node> m_node;
    const std::string m_wallet_name;
    mutable RecursiveMutex cs_wallet;
    std::vector<uint256> m_txid_cache;
    std::unordered_set<COutPoint, SaltedOutpointHasher> m_spends;
    mutable std::unordered_map<std::string, CWalletAddressInfo> m_address_cache;
    std::unordered_map<uint256, std::shared_ptr<CWalletTx>, SaltedTxidHasher> m_cwallettx_cache;
    UniValue executeRPC(const std::string& method, const UniValue& params = {}) const
    {
        try {
            return m_node->executeRpc(method, params, m_wallet_uri);
        } catch (const UniValue& err) {
            return err;
        }
        return {};
    }
    void ListTransactions(const std::function<void(CWalletTx&)> callback)
    {
        if (!callback) return;
        UniValue args(UniValue::VARR);
        args.push_back("*");
        auto wsize = m_txid_cache.size();
        args.push_back(size_t{INT_MAX} - wsize);
        args.push_back(wsize);
        auto txs = executeRPC("listtransactions", args);
        for (auto i = 0u; i < txs.size(); i++) {
            auto& tx = txs[i];
            m_txid_cache.push_back(uint256S(tx["txid"].get_str()));
        }
        std::unordered_set<uint256, SaltedTxidHasher> txids;
        for (auto& txid : m_txid_cache) {
            if (!txids.insert(txid).second) {
                continue;
            }
            if (auto wtx = GetWTxCached(txid)) {
                callback(*wtx);
            }
        }
    }
    CWalletAddressInfo AddressInfo(const CTxDestination& dest) const
    {
        if (!IsValidDestination(dest)) {
            return {};
        }
        auto address = EncodeDestination(dest);
        auto it = m_address_cache.find(address);
        if (it == m_address_cache.end()) {
            UniValue args(UniValue::VARR);
            args.push_back(address);
            auto addressInfo = executeRPC("getaddressinfo", args);
            auto ismine = addressInfo["ismine"].getBool() ? ISMINE_SPENDABLE :
                          addressInfo["iswatchonly"].getBool() ? ISMINE_WATCH_ONLY : ISMINE_NO;
            auto name = addressInfo["labels"][0].getValStr();
            auto ischange = addressInfo["ischange"].getBool();
            CPubKey pubkey;
            if (addressInfo["pubkey"].isStr()) {
                auto hex = ParseHex(addressInfo["pubkey"].get_str());
                pubkey.Set(hex.begin(), hex.end());
            }
            if (!pubkey.IsValid() && addressInfo["solvable"].getBool()) {
                auto desc = addressInfo["desc"].get_str();
                auto splits = spanparsing::Split(desc, "])");
                if (splits.size() > 1) {
                    auto hex = ParseHex({splits[1].data(), splits[1].size()});
                    if (hex.size() == 32) {
                        hex.insert(hex.begin(), 0x02);
                    }
                    pubkey.Set(hex.begin(), hex.end());
                }
            }
            it = m_address_cache.emplace(address, CWalletAddressInfo{ismine, ischange, pubkey, name}).first;
        }
        return it->second;
    }
    template<typename T, typename F>
    CAmount Sum(const T& cont, F func)
    {
        auto sum = [&](CAmount sum, auto& next) { return sum + func(next); };
        return std::accumulate(cont.begin(), cont.end(), CAmount{0}, sum);
    }
    bool GetChange(const CTxOut& txout)
    {
        CTxDestination dest;
        auto isChange = ExtractDestination(txout.scriptPubKey, dest)
                        && AddressInfo(dest).is_change;
        return isChange ? txout.nValue : 0;
    }
    CAmount GetChange(const CTransaction& tx)
    {
        return Sum(tx.vout, [&](auto& txout) { return GetChange(txout); });
    }
    CAmount GetDebit(const CTxIn& txin, const isminefilter& filter)
    {
        if (auto wtx = GetWTxCached(txin.prevout.hash)) {
            if (txin.prevout.n < wtx->tx->vout.size())
                if (txoutIsMine(wtx->tx->vout[txin.prevout.n]) & filter)
                    return wtx->tx->vout[txin.prevout.n].nValue;
        }
        return 0;
    }
    CAmount GetDebit(const CTransaction& tx, const isminefilter& filter)
    {
         return Sum(tx.vin, [&](auto& txin) { return GetDebit(txin, filter); });
    }
    CAmount GetCredit(const CTxOut& txout, const isminefilter& filter)
    {
        return (txoutIsMine(txout) & filter) ? txout.nValue : 0;
    }
    CAmount GetCredit(const CTransaction& tx, const isminefilter& filter)
    {
        return Sum(tx.vout, [&](auto& txout) { return GetCredit(txout, filter); });
    }
    CAmount GetCachableAmount(CWalletTx& wtx, CWalletTx::AmountType type, const isminefilter& filter)
    {
        auto& amount = wtx.m_amounts[type];
        if (!amount.m_cached[filter]) {
            amount.Set(filter, type == CWalletTx::DEBIT ? GetDebit(*wtx.tx, filter)
                                                        : GetCredit(*wtx.tx, filter));
        }
        return amount.m_value[filter];
    }
    CAmount GetCreditCached(CWalletTx& wtx, const isminefilter& filter)
    {
        const isminefilter get_amount_filter{filter & ISMINE_ALL};
        return get_amount_filter ?
            GetCachableAmount(wtx, CWalletTx::CREDIT, get_amount_filter) : 0;
    }
    CAmount GetDebitCached(CWalletTx& wtx, const isminefilter& filter)
    {
        const isminefilter get_amount_filter{filter & ISMINE_ALL};
        return get_amount_filter ?
            GetCachableAmount(wtx, CWalletTx::DEBIT, get_amount_filter) : 0;
    }
    CAmount GetChangeCached(CWalletTx& wtx)
    {
        if (wtx.fChangeCached)
            return wtx.nChangeCached;
        wtx.nChangeCached = GetChange(*wtx.tx);
        wtx.fChangeCached = true;
        return wtx.nChangeCached;
    }
    bool IsTrustedCached(CWalletTx& wtx, std::set<uint256>* trusted_parents = nullptr)
    {
        if (wtx.state<TxStateConfirmed>()) return true;
        if (wtx.state<TxStateInactive>()) return false;
        // using wtx's cached debit
        if (GetDebitCached(wtx, ISMINE_ALL) <= 0) return false;

        // Don't trust unconfirmed transactions from us unless they are in the mempool.
        if (!wtx.InMempool()) return false;

        std::set<uint256> parents;
        if (!trusted_parents) trusted_parents = &parents;
        // Trusted if all inputs are from us and are in the mempool:
        for (const CTxIn& txin : wtx.tx->vin) {
            // Transactions not sent by us: not trusted
            auto parent = GetWTxCached(txin.prevout.hash);
            if (!parent) return false;
            const auto& parentOut = parent->tx->vout[txin.prevout.n];
            // Check that this specific input being spent is trusted
            if (txoutIsMine(parentOut) != ISMINE_SPENDABLE) return false;
            // If we've already trusted this parent, continue
            if (trusted_parents->count(parent->GetHash())) continue;
            // Recurse to check that the parent is also trusted
            if (!IsTrustedCached(*parent, trusted_parents)) return false;
            trusted_parents->insert(parent->GetHash());
        }
        return true;
    }
    std::shared_ptr<CWalletTx> GetWTxCached(const uint256& txid)
    {
        auto it = m_cwallettx_cache.find(txid);
        if (it != m_cwallettx_cache.end()) {
            return it->second;
        }
        if (txid.IsNull()) {
            return {};
        }
        UniValue args(UniValue::VARR);
        args.push_back(txid.GetHex());
        auto result = executeRPC("gettransaction", args);
        if (txid != uint256S(result["txid"].getValStr())) {
            return {};
        }
        auto confirmations = result["confirmations"].getInt<int>();
        bool trusted = true;
        bool abandoned = false;
        TxState txstate = TxStateInMempool{};
        auto& details = result["details"];
        for (auto i = 0u; i < details[i].size(); i++) {
            auto& abandoned_value = find_value(details[i], "abandoned");
            if (abandoned_value.isBool()) {
                abandoned = abandoned_value.get_bool();
                break;
            }
        }
        if (confirmations < 0 || abandoned) {
            txstate = TxStateInactive{abandoned};
        }
        auto& trusted_value = find_value(result, "trusted");
        if (trusted_value.isBool()) {
            trusted = trusted_value.get_bool();
        } else if (confirmations > 0) {
            auto blockhash = uint256S(result["blockhash"].get_str());
            auto blockheight = result["blockheight"].getInt<int>();
            auto blockindex = result["blockindex"].getInt<int>();
            txstate = TxStateConfirmed{blockhash, blockheight, blockindex};
        }
        CMutableTransaction tx;
        if (!DecodeHexTx(tx, result["hex"].get_str())) {
            return {};
        }
        auto wtx = std::make_shared<CWalletTx>(MakeTransactionRef(std::move(tx)), txstate);
        if (confirmations != 0) { // mempool tx isn't cached
            m_cwallettx_cache.emplace(txid, wtx);
        }
        if (confirmations >= 0 && !abandoned) {
            for (auto& txin : wtx->tx->vin) {
                m_spends.insert(txin.prevout);
            }
        }
        wtx->nTimeReceived = result["time"].getInt<uint32_t>();
        auto& n = find_value(result, "n");
        n.isNum() && (wtx->nOrderPos = n.getInt<int64_t>());
        auto& timestart = find_value(result, "timesmart");
        timestart.isNum() && (wtx->nTimeSmart = timestart.getInt<uint32_t>());
        return wtx;
    }
    //! Construct wallet tx struct.
    WalletTx MakeWalletTx(CWalletTx& wtx)
    {
        WalletTx result;
        result.tx = wtx.tx;
        for (const auto& txin : wtx.tx->vin) {
            result.txin_is_mine.emplace_back(txinIsMine(txin));
        }
        for (const auto& txout : wtx.tx->vout) {
            result.txout_is_mine.emplace_back(txoutIsMine(txout));
            result.txout_address.emplace_back();
            result.txout_address_is_mine.emplace_back(
                ExtractDestination(txout.scriptPubKey, result.txout_address.back()) ?
                                   isMine(result.txout_address.back()) : ISMINE_NO);
        }
        bool immature_coinbase = false;
        if (auto state = wtx.state<TxStateConfirmed>()) {
            immature_coinbase = wtx.IsCoinBase() &&
                (GetHeight() - state->confirmed_block_height < COINBASE_MATURITY);
            result.block_hash = state->confirmed_block_hash;
        }
        result.credit = immature_coinbase ? 0 : GetCreditCached(wtx, ISMINE_ALL);
        result.debit = wtx.IsCoinBase() ? 0 : GetDebitCached(wtx, ISMINE_ALL);
        result.change = GetChangeCached(wtx);
        result.time = wtx.GetTxTime();
        result.value_map = wtx.mapValue;
        result.is_coinbase = wtx.IsCoinBase();
        result.order_position = wtx.nOrderPos;
        return result;
    }
    //! Construct wallet tx status struct.
    WalletTxStatus MakeWalletTxStatus(CWalletTx& wtx)
    {
        WalletTxStatus result;
        auto state = wtx.state<TxStateConfirmed>();
        result.block_height = state ? state->confirmed_block_height
            : wtx.state<TxStateInactive>() ? -1 : 0;
        int confirmations = result.block_height > 0 ?
            (GetHeight() - result.block_height + 1) : 0;
        result.blocks_to_maturity = wtx.IsCoinBase() ?
            std::max(0, (COINBASE_MATURITY + 1) - confirmations) : 0;
        result.depth_in_main_chain = confirmations;
        result.time_received = wtx.nTimeReceived;
        result.lock_time = wtx.tx->nLockTime;
        result.is_trusted = IsTrustedCached(wtx);
        result.is_abandoned = wtx.isAbandoned();
        result.is_coinbase = wtx.IsCoinBase();
        result.is_in_main_chain = confirmations > 0;
        return result;
    }
    //! Construct wallet TxOut struct.
    WalletTxOut MakeWalletTxOut(const CWalletTx& wtx, uint32_t n, int depth)
    {
        WalletTxOut result;
        result.txout = wtx.tx->vout[n];
        result.time = wtx.GetTxTime();
        result.depth_in_main_chain = depth;
        result.is_spent = isSpent(wtx.GetHash(), n);
        return result;
    }
public:
    explicit OmniWalletImpl(std::unique_ptr<Node> node, const std::string& name) : m_node(std::move(node)), m_wallet_name(name)
    {
        m_wallet_uri = "/wallet/";
        if (!name.empty()) {
            if (auto encodedURI = evhttp_uriencode(name.data(), name.size(), false)) {
                m_wallet_uri += encodedURI;
                free(encodedURI);
            }
        }
        m_wallet_uri += m_node->walletLoader().getWallets().at(0)->getWalletName();
    }
    bool encryptWallet(const SecureString& wallet_passphrase) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(wallet_passphrase);
        executeRPC("encryptwallet", args);
        return true;
    }
    bool isCrypted() override { return false; }
    bool lock() override
    {
        executeRPC("walletlock");
        return true;
    }
    bool unlock(const SecureString& wallet_passphrase) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(wallet_passphrase);
        executeRPC("walletpassphrase", args);
        return true;
    }
    bool isLocked() override { return false; }
    bool changeWalletPassphrase(const SecureString& old_wallet_passphrase, const SecureString& new_wallet_passphrase) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(old_wallet_passphrase);
        args.push_back(new_wallet_passphrase);
        executeRPC("walletpassphrasechange", args);
        return true;
    }
    void abortRescan() override
    {
        executeRPC("abortrescan");
    }
    bool backupWallet(const std::string& filename) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(filename);
        executeRPC("backupwallet", args);
        return true;
    }
    std::string getWalletName() override
    {
        return m_wallet_name;
    }
    util::Result<CTxDestination> getNewDestination(const OutputType type, const std::string& label) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(label);
        args.push_back(FormatOutputType(type));
        auto address = executeRPC("getnewaddress", args);
        std::string err_str;
        auto dest = DecodeDestination(address.get_str(), err_str);
        if (IsValidDestination(dest)) {
            return dest;
        }
        return util::Error{err_str};
    }
    bool getPubKey(const CTxDestination& dest, CPubKey& pub_key) override
    {
        LOCK(cs_wallet);
        pub_key = AddressInfo(dest).pubkey;
        return pub_key.IsValid();
    }
    SigningResult signMessage(const std::string& message, const PKHash& pkhash, std::string& str_sig) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(EncodeDestination(CTxDestination{pkhash}));
        args.push_back(message);
        str_sig = executeRPC("signmessage", args).get_str();
        return SigningResult::OK;
    }
    bool isSpendable(const CTxDestination& dest) override
    {
        return isMine(dest) & ISMINE_SPENDABLE;
    }
    bool haveWatchOnly() override { return false; }
    bool setAddressBook(const CTxDestination& dest, const std::string& name, const std::string& purpose) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(EncodeDestination(dest));
        args.push_back(name);
        executeRPC("setlabel", args);
        return true;
    }
    bool delAddressBook(const CTxDestination&) override { return false; }
    isminetype isMine(const CTxDestination& dest) override
    {
        LOCK(cs_wallet);
        return AddressInfo(dest).type;
    }
    bool getAddress(const CTxDestination& dest,
        std::string* name,
        isminetype* is_mine,
        std::string* purpose) override
    {
        LOCK(cs_wallet);
        auto info = AddressInfo(dest);
        if (name) *name = info.name;
        if (is_mine) *is_mine = info.type;
        if (purpose) *purpose = "";
        return true;
    }
    std::vector<WalletAddress> getAddresses() const override
    {
        LOCK(cs_wallet);
        std::vector<WalletAddress> result;
        auto labels = executeRPC("listlabels");
        for (auto i = 0u; i < labels.size(); ++i) {
            UniValue args(UniValue::VARR);
            args.push_back(labels[i].getValStr());
            auto addresses = executeRPC("getaddressesbylabel", args);
            for (auto j = 0u; j < addresses.size(); ++j) {
                auto& address = addresses[j];
                auto dest = DecodeDestination(address.getKeys()[0]);
                result.emplace_back(dest, AddressInfo(dest).type, labels[i].get_str(), address.getValues()[0].get_str());
            }
        }
        return result;
    }
    std::vector<std::string> getAddressReceiveRequests() override { return {}; }
    bool setAddressReceiveRequest(const CTxDestination& dest, const std::string& id, const std::string& value) override { return false; }
    bool displayAddress(const CTxDestination& dest) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(EncodeDestination(dest));
        executeRPC("walletdisplayaddress", args);
        return true;
    }
    void availableCoins(std::vector<COutput>& vCoins, const CCoinControl* coinControl, const CAmount& nMinimumAmount) override
    {
        UniValue args(UniValue::VARR);
        if (coinControl) {
            args.push_back(coinControl->m_min_depth);
            args.push_back(coinControl->m_max_depth);
            args.push_back(UniValue::VARR);
            args.push_back(coinControl->m_include_unsafe_inputs);
            UniValue options(UniValue::VOBJ);
            options.pushKV("minimumAmount", ValueFromAmount(nMinimumAmount));
            args.push_back(options);
        }
        auto checkSelected = coinControl && coinControl->HasSelected() && !coinControl->m_allow_other_inputs;
        auto coins = executeRPC("listunspent", args);
        for (auto i = 0u; i < coins.size(); i++) {
            auto& coin = coins[i];
            COutPoint outpoint{uint256S(coin["txid"].get_str()), coin["vout"].getInt<uint32_t>()};
            if (checkSelected && !coinControl->IsSelected(outpoint)) continue;
            CAmount amount;
            if (!ParseFixedPoint(coin["amount"].getValStr(), 8, &amount)) continue;
            auto hex = ParseHex(coin["scriptPubKey"].get_str());
            CTxOut txout{amount, CScript{hex.begin(), hex.end()}};
            int depth = coin["confirmations"].getInt<int>();
            int input_bytes = 0;
            bool spendable = coin["spendable"].get_bool();
            bool solvable = coin["solvable"].get_bool();
            bool safe = coin["safe"].get_bool();
            Coin me_coin;
            bool from_me = txinIsMine(CTxIn{outpoint}) & ISMINE_SPENDABLE;
            vCoins.emplace_back(outpoint, txout, depth, input_bytes, spendable, solvable, safe, 0, from_me);
        }
    }
    bool lockCoin(const COutPoint& outpoint, const bool) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(false);
        UniValue trxs(UniValue::VARR);
        UniValue obj(UniValue::VOBJ);
        obj.pushKV("txid", outpoint.hash.GetHex());
        obj.pushKV("vout", outpoint.n);
        trxs.push_back(obj);
        args.push_back(trxs);
        executeRPC("lockunspent", args);
        return true;
    }
    bool unlockCoin(const COutPoint& outpoint) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(true);
        UniValue trxs(UniValue::VARR);
        UniValue obj(UniValue::VOBJ);
        obj.pushKV("txid", outpoint.hash.GetHex());
        obj.pushKV("vout", outpoint.n);
        trxs.push_back(obj);
        args.push_back(trxs);
        executeRPC("lockunspent", args);
        return true;
    }
    bool isLockedCoin(const COutPoint& outpoint) override
    {
        std::vector<COutPoint> coins;
        listLockedCoins(coins);
        return std::find(coins.begin(), coins.end(), outpoint) != coins.end();
    }
    void listLockedCoins(std::vector<COutPoint>& coins) override
    {
        auto unspents = executeRPC("listlockunspent");
        for (auto i = 0u; i < unspents.size(); i++) {
            auto& unspent = unspents[i];
            coins.emplace_back(uint256S(unspent["txid"].get_str()), unspent["vout"].getInt<uint32_t>());
        }
    }
    util::Result<CTransactionRef> createTransaction(const std::vector<CRecipient>& recipients,
        const CCoinControl& coin_control,
        bool sign,
        int& change_pos,
        CAmount& fee,
        bool omni,
        CAmount* required_fee) override
    {
        CMutableTransaction tx;
        std::vector<COutPoint> outpoints;
        coin_control.ListSelected(outpoints);
        for (auto& outpoint : outpoints) {
            tx.vin.emplace_back(outpoint.hash, outpoint.n);
        }
        UniValue subtractFromOutputs(UniValue::VARR);
        for (auto i = 0u; i < recipients.size(); i++) {
            auto& recipient = recipients[i];
            tx.vout.emplace_back(recipient.nAmount, recipient.scriptPubKey);
            if (recipient.fSubtractFeeFromAmount) {
                subtractFromOutputs.push_back(i);
            }
        }
        UniValue options(UniValue::VOBJ);
        bool addPersistentChange = (omni && recipients.size() == 1)
                                || (!omni && subtractFromOutputs.empty()
                                && coin_control.m_subtract_fee_from_change);
        auto changeScript = GetScriptForDestination(coin_control.destChange);
        auto changeDust = GetDustThreshold({0, changeScript}, minRelayTxFee);
        // NOTE: this is not ideal, find better way
        // adds dust to dest change to prevent transaction with no change
        if (addPersistentChange) {
            auto value = coin_control.m_selected_amount - CTransaction{tx}.GetValueOut();
            if (value >= changeDust) {
                tx.vout.emplace_back(value, changeScript);
                if (subtractFromOutputs.empty() && coin_control.m_subtract_fee_from_change) {
                    subtractFromOutputs.push_back(tx.vout.size() - 1);
                }
            } else {
                addPersistentChange = false;
            }
        }
        options.pushKV("subtract_fee_from_outputs", subtractFromOutputs);
        options.pushKV("add_inputs", coin_control.m_allow_other_inputs);
        if (IsValidDestination(coin_control.destChange)) {
            options.pushKV("change_address", EncodeDestination(coin_control.destChange));
        } else if (coin_control.m_change_type) {
            options.pushKV("change_type", FormatOutputType(*coin_control.m_change_type));
        }
        options.pushKV("change_position", change_pos);
        options.pushKV("include_unsafe", coin_control.m_include_unsafe_inputs);
        options.pushKV("include_watching", coin_control.fAllowWatchOnly);
        if (coin_control.fOverrideFeeRate && coin_control.m_feerate) {
            options.pushKV("feeRate", ValueFromAmount(coin_control.m_feerate->GetFeePerK()));
        }
        UniValue args(UniValue::VARR);
        args.push_back(EncodeHexTx(CTransaction{tx}));
        args.push_back(options);
        auto result = executeRPC("fundrawtransaction", args);
        if (!DecodeHexTx(tx, result["hex"].getValStr())) {
            if (required_fee) {
                for (auto& txin : tx.vin) {
                    txin.scriptSig = CScript{} << std::vector<uint8_t>(71, 0);
                }
                auto size = GetVirtualTransactionSize(CTransaction{tx});
                *required_fee = std::max(coin_control.m_mininum_fee, getRequiredFee(size));
            }
            return util::Error{"Cannot decode tx"};
        }
        if (!ParseFixedPoint(result["fee"].getValStr(), 8, &fee)) {
            return util::Error{"Cannot parse fee"};
        }
        change_pos = result["changepos"].getInt<int>();
        if (addPersistentChange) {
            // merge changes
            for (int i = 0; i < tx.vout.size(); ++i) {
                if (i != change_pos && tx.vout[i].scriptPubKey == changeScript) {
                    if (change_pos < 0) {
                        change_pos = i;
                    } else {
                        auto& change = tx.vout.at(change_pos);
                        change.nValue += tx.vout[i].nValue;
                        change.scriptPubKey = tx.vout[i].scriptPubKey;
                        tx.vout.erase(tx.vout.begin() + i);
                    }
                    break;
                }
            }
        }
        auto fee_needed = std::max(coin_control.m_mininum_fee, fee);
        if (fee_needed > fee && (coin_control.m_subtract_fee_from_change || required_fee)) {
            if (change_pos < 0) {
                if (required_fee) {
                    *required_fee = fee_needed;
                }
                return util::Error{"Change pos less than zero"};
            }
            auto& change = tx.vout.at(change_pos);
            auto changeValue = change.nValue - (fee_needed - fee);
            if (required_fee) {
                *required_fee = fee_needed - fee + (changeValue > changeDust ? 0 : changeDust);
            }
            if (coin_control.m_subtract_fee_from_change) {
                change.nValue = changeValue;
                // Error if this output is reduced to be below dust
                if (IsDust(change, minRelayTxFee)) {
                    if (change.nValue < 0) {
                        return util::Error{"The change amount is too small to pay the fee"};
                    } else {
                        return util::Error{"The change amount is too small to send after the fee has been deducted"};
                    }
                }
                fee = fee_needed;
            }
        }
        if (sign && !signTransaction(tx, {}, SIGHASH_ALL)) {
            return util::Error{"Cannot sign tx"};
        }
        return MakeTransactionRef(std::move(tx));
    }
    bool signTransaction(CMutableTransaction& tx, const std::map<COutPoint, Coin>& coins, int sighash) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(EncodeHexTx(CTransaction{tx}));
        UniValue prevtxs(UniValue::VARR);
        for (auto& [prevout, coin] : coins) {
            UniValue prevtx(UniValue::VOBJ);
            prevtx.pushKV("txid", prevout.hash.GetHex());
            prevtx.pushKV("vout", int64_t(prevout.n));
            prevtx.pushKV("scriptPubKey", HexStr(coin.out.scriptPubKey));
            prevtx.pushKV("amount", ValueFromAmount(coin.out.nValue));
            prevtxs.push_back(prevtx);
        }
        args.push_back(prevtxs);
        args.push_back(SighashToStr(sighash));
        auto result = executeRPC("signrawtransactionwithwallet", args);
        return result["complete"].getBool() && DecodeHexTx(tx, result["hex"].get_str());
    }
    void commitTransaction(CTransactionRef tx, WalletValueMap, WalletOrderForm) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(EncodeHexTx(*tx));
        m_node->executeRpc("sendrawtransaction", args, "/");
    }
    bool transactionCanBeAbandoned(const uint256&) override { return true; }
    bool abandonTransaction(const uint256& txid) override
    {
        UniValue args(UniValue::VARR);
        args.push_back(txid.GetHex());
        executeRPC("abandontransaction", args);
        return true;
    }
    // feebumber disabled
    bool transactionCanBeBumped(const uint256&) override { return false; }
    bool createBumpTransaction(const uint256&, const CCoinControl&, std::vector<bilingual_str>&, CAmount&, CAmount&, CMutableTransaction&) override { return false; }
    bool signBumpTransaction(CMutableTransaction&) override { return false; }
    bool commitBumpTransaction(const uint256&, CMutableTransaction&&, std::vector<bilingual_str>&, uint256&) override { return false; }
    CTransactionRef getTx(const uint256& txid) override
    {
        LOCK(cs_wallet);
        auto wtx = GetWTxCached(txid);
        return wtx ? wtx->tx : nullptr;
    }
    WalletTx getWalletTx(const uint256& txid) override
    {
        LOCK(cs_wallet);
        auto wtx = GetWTxCached(txid);
        return wtx ? MakeWalletTx(*wtx) : WalletTx{};
    }
    std::set<WalletTx> getWalletTxs() override
    {
        LOCK(cs_wallet);
        std::set<WalletTx> result;
        ListTransactions([&](CWalletTx& wtx) {
            result.insert(MakeWalletTx(wtx));
        });
        return result;
    }
    std::vector<WalletTx> getWalletTxsDetails(std::map<uint256, WalletTxStatus>& tx_status) override
    {
        LOCK(cs_wallet);
        std::vector<WalletTx> result;
        ListTransactions([&](CWalletTx& wtx) {
            result.push_back(MakeWalletTx(wtx));
            tx_status.emplace(wtx.GetHash(), MakeWalletTxStatus(wtx));
        });
        return result;
    }
    bool tryGetTxStatus(const uint256& txid,
        interfaces::WalletTxStatus& tx_status,
        int& num_blocks,
        int64_t& block_time) override
    {
        LOCK(cs_wallet);
        auto wtx = GetWTxCached(txid);
        if (!wtx) return false;
        tx_status = MakeWalletTxStatus(*wtx);
        num_blocks = tx_status.block_height;
        block_time = wtx->GetTxTime();
        return true;
    }
    WalletTx getWalletTxDetails(const uint256& txid,
        WalletTxStatus& tx_status,
        WalletOrderForm& order_form,
        bool& in_mempool,
        int& num_blocks) override
    {
        LOCK(cs_wallet);
        auto wtx = GetWTxCached(txid);
        if (!wtx) return {};
        tx_status = MakeWalletTxStatus(*wtx);
        num_blocks = tx_status.block_height;
        in_mempool = wtx->InMempool();
        return MakeWalletTx(*wtx);
    }
    TransactionError fillPSBT(int sighash_type, bool sign, bool bip32derivs,
                              size_t* n_signed, PartiallySignedTransaction& psbtx,
                              bool& complete) override { return TransactionError::OK; }
    WalletBalances getBalances() override
    {
        LOCK(cs_wallet);
        WalletBalances result;
        ListTransactions([&](CWalletTx& wtx) {
            auto ws = MakeWalletTxStatus(wtx);
            if (ws.blocks_to_maturity > 0) {
                result.immature_balance += GetCachableAmount(wtx, CWalletTx::IMMATURE_CREDIT, ISMINE_SPENDABLE);
                result.immature_watch_only_balance += GetCachableAmount(wtx, CWalletTx::IMMATURE_CREDIT, ISMINE_WATCH_ONLY);
                return;
            }
            const int tx_depth{ws.depth_in_main_chain};
            if (tx_depth < 0) return;
            const CAmount tx_credit_mine{GetCreditCached(wtx, ISMINE_SPENDABLE)};
            const CAmount tx_credit_watchonly{GetCreditCached(wtx, ISMINE_WATCH_ONLY)};
            if (ws.is_trusted) {
                result.balance += tx_credit_mine;
                result.watch_only_balance += tx_credit_watchonly;
            } else if (wtx.InMempool()) {
                result.unconfirmed_balance += tx_credit_mine;
                result.unconfirmed_watch_only_balance += tx_credit_watchonly;
            }
        });
        return result;
    }
    bool tryGetBalances(WalletBalances& balances, uint256& block_hash) override
    {
        block_hash.SetNull();
        balances = getBalances();
        return true;
    }
    CAmount getBalance() override
    {
        return getBalances().balance;
    }
    CAmount getAvailableBalance(const CCoinControl& coin_control) override
    {
        std::vector<COutput> coins;
        availableCoins(coins, &coin_control, 1);
        return Sum(coins, [](const COutput& output) { return output.txout.nValue; });
    }
    bool isSpent(const uint256& hash, unsigned int n) override
    {
        return m_spends.count(COutPoint{hash, n}) > 0;
    }
    isminetype txinIsMine(const CTxIn& txin) override
    {
        LOCK(cs_wallet);
        auto wtx = GetWTxCached(txin.prevout.hash);
        return wtx ? txoutIsMine(wtx->tx->vout[txin.prevout.n]) : ISMINE_NO;
    }
    isminetype txoutIsMine(const CTxOut& txout) override
    {
        CTxDestination dest;
        return ExtractDestination(txout.scriptPubKey, dest) ? isMine(dest) : ISMINE_NO;
    }
    CAmount getDebit(const CTxIn& txin, isminefilter filter) override
    {
        LOCK(cs_wallet);
        return GetDebit(txin, filter);
    }
    CAmount getCredit(const CTxOut& txout, isminefilter filter) override
    {
        LOCK(cs_wallet);
        return GetCredit(txout, filter);
    }
    CoinsList listCoins() override { return {}; }
    std::vector<WalletTxOut> getCoins(const std::vector<COutPoint>& outputs) override
    {
        LOCK(cs_wallet);
        std::vector<WalletTxOut> result;
        result.reserve(outputs.size());
        for (const auto& output : outputs) {
            result.emplace_back();
            if (auto wtx = GetWTxCached(output.hash)) {
                auto status = MakeWalletTxStatus(*wtx);
                if (status.depth_in_main_chain >= 0) {
                    result.back() = MakeWalletTxOut(*wtx, output.n, status.depth_in_main_chain);
                }
            }
        }
        return result;
    }
    CAmount getRequiredFee(unsigned int tx_bytes) override
    {
        return std::max(minTxFee, minRelayTxFee).GetFee(tx_bytes);
    }
    CAmount getMinimumFee(unsigned int tx_bytes,
        const CCoinControl& coin_control,
        int* returned_target,
        FeeReason* reason) override
    {
        FeeCalculation fee_calc;
        /* User control of how to calculate fee uses the following parameter precedence:
         1 . coin_control.m_f*eerate
         2. coin_control.m_confirm_target
         3. m_pay_tx_fee (user-set member variable of wallet)
         4. m_confirm_target (user-set member variable of wallet)
         The first parameter that is set is used.
         */
        CFeeRate feerate_needed;
        if (returned_target) *returned_target = 0;
        if (coin_control.m_feerate) { // 1.
            feerate_needed = *(coin_control.m_feerate);
            if (reason) *reason = FeeReason::PAYTXFEE;
            // Allow to override automatic min/max check over coin control instance
            if (coin_control.fOverrideFeeRate) return feerate_needed.GetFee(tx_bytes);
        }
        else if (!coin_control.m_confirm_target) { // 3. TODO: remove magic value of 0 for wallet member m_pay_tx_fee
            if (auto pay_tx_fee = ParseMoney(gArgs.GetArg("-paytxfee", ""))) {
                payTxFee = CFeeRate{*pay_tx_fee};
            }
            feerate_needed = payTxFee;
            if (reason) *reason = FeeReason::PAYTXFEE;
        }
        else { // 2. or 4.
            // We will use smart fee estimation
            auto target = coin_control.m_confirm_target ? *coin_control.m_confirm_target : getConfirmTarget();
            // By default estimates are economical iff we are signaling opt-in-RBF
            bool conservative_estimate = !coin_control.m_signal_bip125_rbf.value_or(DEFAULT_WALLET_RBF);
            // Allow to override the default fee estimate mode over the CoinControl instance
            if (coin_control.m_fee_mode == FeeEstimateMode::CONSERVATIVE) conservative_estimate = true;
            else if (coin_control.m_fee_mode == FeeEstimateMode::ECONOMICAL) conservative_estimate = false;

            static const CBlockPolicyEstimator feeEstimator(FeeestPath(gArgs));
            feerate_needed = feeEstimator.estimateSmartFee(target, &fee_calc, conservative_estimate);
            if (feerate_needed == CFeeRate(0)) {
                feerate_needed = fallbackFee;
                if (reason) *reason = FeeReason::FALLBACK;

                // directly return if fallback fee is disabled (feerate 0 == disabled)
                if (feerate_needed == CFeeRate(0)) return feerate_needed.GetFee(tx_bytes);
            }
            // Obey mempool min fee when using smart fee estimation
            CFeeRate min_mempool_feerate = minTxFee;
            if (feerate_needed < min_mempool_feerate) {
                feerate_needed = min_mempool_feerate;
                if (reason) *reason = FeeReason::MEMPOOL_MIN;
            }
        }
        // prevent user from paying a fee below the required fee rate
        CFeeRate required_feerate = std::max(minTxFee, minRelayTxFee);
        if (required_feerate > feerate_needed) {
            feerate_needed = required_feerate;
            if (reason) *reason = FeeReason::REQUIRED;
        }
        return feerate_needed.GetFee(tx_bytes);
    }
    unsigned int getConfirmTarget() override { return DEFAULT_TX_CONFIRM_TARGET; }
    bool hdEnabled() override { return true; }
    bool canGetAddresses() override { return true; }
    bool hasExternalSigner() override{ return executeRPC("getwalletinfo")["external_signer"].getBool(); }
    bool privateKeysDisabled() override { return !executeRPC("getwalletinfo")["private_keys_enabled"].getBool(); }
    bool taprootEnabled() override { return true; }
    OutputType getDefaultAddressType() override { return OutputType::BECH32; }
    CAmount getDefaultMaxTxFee() override { return maxTxFee.GetFeePerK(); }
    void remove() override {}
    bool isLegacy() override { return false; }
    std::unique_ptr<Handler> handleUnload(UnloadFn) override { return {}; }
    std::unique_ptr<Handler> handleShowProgress(ShowProgressFn) override { return {}; }
    std::unique_ptr<Handler> handleStatusChanged(StatusChangedFn) override { return {}; }
    std::unique_ptr<Handler> handleAddressBookChanged(AddressBookChangedFn) override { return {}; }
    std::unique_ptr<Handler> handleTransactionChanged(TransactionChangedFn) override { return {}; }
    std::unique_ptr<Handler> handleWatchOnlyChanged(WatchOnlyChangedFn) override { return {}; }
    std::unique_ptr<Handler> handleCanGetAddressesChanged(CanGetAddressesChangedFn) override { return {}; }
};
} // namespace
} // namespace wallet

std::unique_ptr<Wallet> MakeOmniWalletInterface(std::unique_ptr<Node> node, const std::string& wallet_name)
{
    return std::make_unique<wallet::OmniWalletImpl>(std::move(node), wallet_name);
}
