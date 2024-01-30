#include <omnicore/createtx.h>
#include <omnicore/omnicore.h>
#include <omnicore/rpc.h>
#include <omnicore/rpctxobject.h>
#include <omnicore/rpcvalues.h>
#include <omnicore/utilsbitcoin.h>

#include <coins.h>
#include <core_io.h>
#include <interfaces/wallet.h>
#include <primitives/transaction.h>
#include <pubkey.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <sync.h>
#include <uint256.h>
#include <util/strencodings.h>
#include <wallet/rpc/util.h>
#ifdef ENABLE_WALLET
#include <wallet/wallet.h>
using namespace wallet;
#endif

#include <univalue.h>

#include <stdint.h>
#include <string>

#ifdef ENABLE_WALLET
extern std::pair<std::shared_ptr<CWallet>, std::unique_ptr<interfaces::Wallet>> GetWalletFromContextForJSONRPCRequest(const JSONRPCRequest& request);
#endif

static UniValue omni_decodetransaction(const JSONRPCRequest& request)
{
#ifdef ENABLE_WALLET
    auto [wallet, pWallet] = GetWalletFromContextForJSONRPCRequest(request);
#else
    std::unique_ptr<interfaces::Wallet> pWallet;
#endif

    RPCHelpMan{"omni_decodetransaction",
       "\nDecodes an Omni transaction.\n"
       "\nIf the inputs of the transaction are not in the chain, then they must be provided, because "
       "the transaction inputs are used to identify the sender of a transaction.\n"
       "\nA block height can be provided, which is used to determine the parsing rules.\n",
       {
           {"rawtx", RPCArg::Type::STR, RPCArg::Optional::NO, "the raw transaction to decode\n"},
           {"prevtxs", RPCArg::Type::ARR, RPCArg::DefaultHint{"none"}, "a JSON array of transaction inputs\n",
                {
                    {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                        {
                            {"txid:hash", RPCArg::Type::STR, RPCArg::Optional::NO, "the transaction hash\n"},
                            {"vout:n", RPCArg::Type::NUM, RPCArg::Optional::NO, "the output number\n"},
                            {"scriptPubKey:hex", RPCArg::Type::STR, RPCArg::Optional::NO, "the output script\n"},
                            {"value:n.nnnnnnnn", RPCArg::Type::NUM, RPCArg::Optional::NO, "the output value\n"},
                        }
                    }
                },
           },
           {"height", RPCArg::Type::NUM, RPCArg::DefaultHint{"0 for chain height"}, "the parsing block height\n"},
       },
       RPCResult{
           RPCResult::Type::ARR, "", "",
           {
               {RPCResult::Type::STR_HEX, "txid", "the hex-encoded hash of the transaction"},
               {RPCResult::Type::STR_AMOUNT, "fee", "the transaction fee in bitcoins"},
               {RPCResult::Type::STR, "sendingaddress", "the Bitcoin address of the sender"},
               {RPCResult::Type::STR, "referenceaddress", "a Bitcoin address used as reference (if any)"},
               {RPCResult::Type::BOOL, "ismine", "whether the transaction involes an address in the wallet"},
               {RPCResult::Type::NUM, "version", "the transaction version"},
               {RPCResult::Type::NUM, "type_int", "the transaction type as number"},
               {RPCResult::Type::STR, "type", "the transaction type as string"},
               {RPCResult::Type::ELISION, "", "other transaction type specific properties"},
           }
       },
       RPCExamples{
           HelpExampleCli("omni_decodetransaction", "\"010000000163af14ce6d477e1c793507e32a5b7696288fa89705c0d02a3f66beb3c5b8afee0100000000ffffffff02ac020000000000004751210261ea979f6a06f9dafe00fb1263ea0aca959875a7073556a088cdfadcd494b3752102a3fd0a8a067e06941e066f78d930bfc47746f097fcd3f7ab27db8ddf37168b6b52ae22020000000000001976a914946cb2e08075bcbaf157e47bcb67eb2b2339d24288ac00000000\" \"[{\\\"txid\\\":\\\"eeafb8c5b3be663f2ad0c00597a88f2896765b2ae30735791c7e476dce14af63\\\",\\\"vout\\\":1,\\\"scriptPubKey\\\":\\\"76a9149084c0bd89289bc025d0264f7f23148fb683d56c88ac\\\",\\\"value\\\":0.0001123}]\"")
           + HelpExampleRpc("omni_decodetransaction", "\"010000000163af14ce6d477e1c793507e32a5b7696288fa89705c0d02a3f66beb3c5b8afee0100000000ffffffff02ac020000000000004751210261ea979f6a06f9dafe00fb1263ea0aca959875a7073556a088cdfadcd494b3752102a3fd0a8a067e06941e066f78d930bfc47746f097fcd3f7ab27db8ddf37168b6b52ae22020000000000001976a914946cb2e08075bcbaf157e47bcb67eb2b2339d24288ac00000000\", [{\"txid\":\"eeafb8c5b3be663f2ad0c00597a88f2896765b2ae30735791c7e476dce14af63\",\"vout\":1,\"scriptPubKey\":\"76a9149084c0bd89289bc025d0264f7f23148fb683d56c88ac\",\"value\":0.0001123}]")
       }
    }.Check(request);

    std::vector<PrevTxsEntry> prevTxsParsed;
    CTransaction tx = ParseTransaction(request.params[0]);

    if (request.params.size() > 1) {
        prevTxsParsed = ParsePrevTxs(request.params[1]);
    }

    int blockHeight = 0;
    if (request.params.size() > 2) {
        blockHeight = request.params[2].getInt<int>();
    } else {
        blockHeight = mastercore::GetHeight();
    }

    UniValue txObj(UniValue::VOBJ);
    int populateResult = populateRPCTransactionObject(tx, std::move(prevTxsParsed), txObj, "", false, "", blockHeight, pWallet.get());

    if (populateResult != 0) PopulateFailure(populateResult);

    return txObj;
}

static UniValue omni_createrawtx_opreturn(const JSONRPCRequest& request)
{
    RPCHelpMan{"omni_createrawtx_opreturn",
       "\nAdds a payload with class C (op-return) encoding to the transaction.\n"
       "\nIf no raw transaction is provided, a new transaction is created.\n"
       "\nIf the data encoding fails, then the transaction is not modified.\n",
       {
           {"rawtx", RPCArg::Type::STR, RPCArg::Optional::NO, "the raw transaction to extend (can be null)\n"},
           {"payload", RPCArg::Type::STR, RPCArg::Optional::NO, "the hex-encoded payload to add\n"},
       },
       RPCResult{
           RPCResult::Type::STR_HEX, "rawtx", "the hex-encoded modified raw transaction"
       },
       RPCExamples{
           HelpExampleCli("omni_createrawtx_opreturn", "\"01000000000000000000\" \"00000000000000020000000006dac2c0\"")
           + HelpExampleRpc("omni_createrawtx_opreturn", "\"01000000000000000000\", \"00000000000000020000000006dac2c0\"")
       }
    }.Check(request);

    CMutableTransaction tx = ParseMutableTransaction(request.params[0]);
    std::vector<unsigned char> payload = ParseHexV(request.params[1], "payload");

    // extend the transaction
    tx = OmniTxBuilder(tx)
            .addOpReturn(payload)
            .build();

    return EncodeHexTx(CTransaction(tx));
}

static UniValue omni_createrawtx_multisig(const JSONRPCRequest& request)
{
#ifdef ENABLE_WALLET
    auto [wallet, pWallet] = GetWalletFromContextForJSONRPCRequest(request);
#else
    std::unique_ptr<interfaces::Wallet> pWallet;
#endif

    RPCHelpMan{"omni_createrawtx_multisig",
       "\nAdds a payload with class B (bare-multisig) encoding to the transaction.\n"
       "\nIf no raw transaction is provided, a new transaction is created.\n"
       "\nIf the data encoding fails, then the transaction is not modified.\n",
       {
           {"rawtx", RPCArg::Type::STR, RPCArg::Optional::NO, "the raw transaction to extend (can be null)\n"},
           {"payload", RPCArg::Type::STR, RPCArg::Optional::NO, "the hex-encoded payload to add\n"},
           {"seed", RPCArg::Type::STR, RPCArg::Optional::NO, "the seed for obfuscation\n"},
           {"redeemkey", RPCArg::Type::STR, RPCArg::Optional::NO, "a public key or address for dust redemption\n"},
       },
       RPCResult{
           RPCResult::Type::STR_HEX, "rawtx", "the hex-encoded modified raw transaction"
       },
       RPCExamples{
           HelpExampleCli("omni_createrawtx_multisig", "\"0100000001a7a9402ecd77f3c9f745793c9ec805bfa2e14b89877581c734c774864247e6f50400000000ffffffff01aa0a0000000000001976a9146d18edfe073d53f84dd491dae1379f8fb0dfe5d488ac00000000\" \"00000000000000020000000000989680\" \"1LifmeXYHeUe2qdKWBGVwfbUCMMrwYtoMm\" \"0252ce4bdd3ce38b4ebbc5a6e1343608230da508ff12d23d85b58c964204c4cef3\"")
           + HelpExampleRpc("omni_createrawtx_multisig", "\"0100000001a7a9402ecd77f3c9f745793c9ec805bfa2e14b89877581c734c774864247e6f50400000000ffffffff01aa0a0000000000001976a9146d18edfe073d53f84dd491dae1379f8fb0dfe5d488ac00000000\", \"00000000000000020000000000989680\", \"1LifmeXYHeUe2qdKWBGVwfbUCMMrwYtoMm\", \"0252ce4bdd3ce38b4ebbc5a6e1343608230da508ff12d23d85b58c964204c4cef3\"")
       }
    }.Check(request);

    CMutableTransaction tx = ParseMutableTransaction(request.params[0]);
    std::vector<unsigned char> payload = ParseHexV(request.params[1], "payload");
    std::string obfuscationSeed = ParseAddressOrEmpty(request.params[2]);
    CPubKey redeemKey = ParsePubKeyOrAddress(pWallet.get(), request.params[3]);

    // extend the transaction
    tx = OmniTxBuilder(tx)
            .addMultisig(payload, obfuscationSeed, redeemKey)
            .build();

    return EncodeHexTx(CTransaction(tx));
}

static UniValue omni_createrawtx_input(const JSONRPCRequest& request)
{
    RPCHelpMan{"omni_createrawtx_input",
       "\nAdds a transaction input to the transaction.\n"
       "\nIf no raw transaction is provided, a new transaction is created.\n",
       {
           {"rawtx", RPCArg::Type::STR, RPCArg::Optional::NO, "the raw transaction to extend (can be null)\n"},
           {"txid", RPCArg::Type::STR, RPCArg::Optional::NO, "the hash of the input transaction\n"},
           {"n", RPCArg::Type::NUM, RPCArg::Optional::NO, "the index of the transaction output used as input\n"},
       },
       RPCResult{
           RPCResult::Type::STR_HEX, "rawtx", "the hex-encoded modified raw transaction"
       },
       RPCExamples{
           HelpExampleCli("omni_createrawtx_input", "\"01000000000000000000\" \"b006729017df05eda586df9ad3f8ccfee5be340aadf88155b784d1fc0e8342ee\" 0")
           + HelpExampleRpc("omni_createrawtx_input", "\"01000000000000000000\", \"b006729017df05eda586df9ad3f8ccfee5be340aadf88155b784d1fc0e8342ee\", 0")
       }
    }.Check(request);

    CMutableTransaction tx = ParseMutableTransaction(request.params[0]);
    uint256 txid = ParseHashV(request.params[1], "txid");
    uint32_t nOut = ParseOutputIndex(request.params[2]);

    // extend the transaction
    tx = OmniTxBuilder(tx)
            .addInput(txid, nOut)
            .build();

    return EncodeHexTx(CTransaction(tx));
}

static UniValue omni_createrawtx_reference(const JSONRPCRequest& request)
{
    RPCHelpMan{"omni_createrawtx_reference",
       "\nAdds a reference output to the transaction.\n"
       "\nIf no raw transaction is provided, a new transaction is created.\n"
       "\nThe output value is set to at least the dust threshold.\n",
       {
           {"rawtx", RPCArg::Type::STR, RPCArg::Optional::NO, "the raw transaction to extend (can be null)\n"},
           {"destination", RPCArg::Type::STR, RPCArg::Optional::NO, "the reference address or destination\n"},
           {"referenceamount", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "the optional reference amount (minimal by default)\n"},
       },
       RPCResult{
           RPCResult::Type::STR_HEX, "rawtx", "the hex-encoded modified raw transaction"
       },
       RPCExamples{
           HelpExampleCli("omni_createrawtx_reference", "\"0100000001a7a9402ecd77f3c9f745793c9ec805bfa2e14b89877581c734c774864247e6f50400000000ffffffff03aa0a0000000000001976a9146d18edfe073d53f84dd491dae1379f8fb0dfe5d488ac5c0d0000000000004751210252ce4bdd3ce38b4ebbc5a6e1343608230da508ff12d23d85b58c964204c4cef3210294cc195fc096f87d0f813a337ae7e5f961b1c8a18f1f8604a909b3a5121f065b52aeaa0a0000000000001976a914946cb2e08075bcbaf157e47bcb67eb2b2339d24288ac00000000\" \"1CE8bBr1dYZRMnpmyYsFEoexa1YoPz2mfB\" 0.005")
           + HelpExampleRpc("omni_createrawtx_reference", "\"0100000001a7a9402ecd77f3c9f745793c9ec805bfa2e14b89877581c734c774864247e6f50400000000ffffffff03aa0a0000000000001976a9146d18edfe073d53f84dd491dae1379f8fb0dfe5d488ac5c0d0000000000004751210252ce4bdd3ce38b4ebbc5a6e1343608230da508ff12d23d85b58c964204c4cef3210294cc195fc096f87d0f813a337ae7e5f961b1c8a18f1f8604a909b3a5121f065b52aeaa0a0000000000001976a914946cb2e08075bcbaf157e47bcb67eb2b2339d24288ac00000000\", \"1CE8bBr1dYZRMnpmyYsFEoexa1YoPz2mfB\", 0.005")
       }
    }.Check(request);

    CMutableTransaction tx = ParseMutableTransaction(request.params[0]);
    std::string destination = ParseAddress(request.params[1]);
    int64_t amount = (request.params.size() > 2) ? ParseAmount(request.params[2], true): 0;

    // extend the transaction
    tx = OmniTxBuilder(tx)
            .addReference(destination, amount)
            .build();

    return EncodeHexTx(CTransaction(tx));
}

static UniValue omni_createrawtx_change(const JSONRPCRequest& request)
{
    RPCHelpMan{"omni_createrawtx_change",
       "\nAdds a change output to the transaction.\n"
       "\nThe provided inputs are not added to the transaction, but only used to "
       "determine the change. It is assumed that the inputs were previously added, "
       "for example via \"createrawtransaction\".\n"
       "\nOptionally a position can be provided, where the change output should be "
       "inserted, starting with 0. If the number of outputs is smaller than the position, "
       "then the change output is added to the end. Change outputs should be inserted "
       "before reference outputs, and as per default, the change output is added to the "
       "first position.\n"
       "\nIf the change amount would be considered as dust, then no change output is added.\n",
       {
           {"rawtx", RPCArg::Type::STR, RPCArg::Optional::NO, "the raw transaction to decode\n"},
           {"prevtxs", RPCArg::Type::ARR, RPCArg::Optional::NO, "a JSON array of transaction inputs\n",
                {
                    {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                        {
                            {"txid:hash", RPCArg::Type::STR, RPCArg::Optional::NO, "the transaction hash\n"},
                            {"vout:n", RPCArg::Type::NUM, RPCArg::Optional::NO, "the output number\n"},
                            {"scriptPubKey:hex", RPCArg::Type::STR, RPCArg::Optional::NO, "the output script\n"},
                            {"value:n.nnnnnnnn", RPCArg::Type::NUM, RPCArg::Optional::NO, "the output value\n"},
                        }
                    }
                }
           },
           {"destination", RPCArg::Type::STR, RPCArg::Optional::NO, "the destination for the change\n"},
           {"fee", RPCArg::Type::NUM, RPCArg::Optional::NO, "the desired transaction fees\n"},
           {"position", RPCArg::Type::NUM, RPCArg::DefaultHint{"first position"}, "the position of the change output\n"},
       },
       RPCResult{
           RPCResult::Type::STR_HEX, "rawtx", "the hex-encoded modified raw transaction"
       },
       RPCExamples{
           HelpExampleCli("omni_createrawtx_change", "\"0100000001b15ee60431ef57ec682790dec5a3c0d83a0c360633ea8308fbf6d5fc10a779670400000000ffffffff025c0d00000000000047512102f3e471222bb57a7d416c82bf81c627bfcd2bdc47f36e763ae69935bba4601ece21021580b888ff56feb27f17f08802ebed26258c23697d6a462d43fc13b565fda2dd52aeaa0a0000000000001976a914946cb2e08075bcbaf157e47bcb67eb2b2339d24288ac00000000\" \"[{\\\"txid\\\":\\\"6779a710fcd5f6fb0883ea3306360c3ad8c0a3c5de902768ec57ef3104e65eb1\\\",\\\"vout\\\":4,\\\"scriptPubKey\\\":\\\"76a9147b25205fd98d462880a3e5b0541235831ae959e588ac\\\",\\\"value\\\":0.00068257}]\" \"1CE8bBr1dYZRMnpmyYsFEoexa1YoPz2mfB\" 0.00003500 1")
           + HelpExampleRpc("omni_createrawtx_change", "\"0100000001b15ee60431ef57ec682790dec5a3c0d83a0c360633ea8308fbf6d5fc10a779670400000000ffffffff025c0d00000000000047512102f3e471222bb57a7d416c82bf81c627bfcd2bdc47f36e763ae69935bba4601ece21021580b888ff56feb27f17f08802ebed26258c23697d6a462d43fc13b565fda2dd52aeaa0a0000000000001976a914946cb2e08075bcbaf157e47bcb67eb2b2339d24288ac00000000\", [{\"txid\":\"6779a710fcd5f6fb0883ea3306360c3ad8c0a3c5de902768ec57ef3104e65eb1\",\"vout\":4,\"scriptPubKey\":\"76a9147b25205fd98d462880a3e5b0541235831ae959e588ac\",\"value\":0.00068257}], \"1CE8bBr1dYZRMnpmyYsFEoexa1YoPz2mfB\", 0.00003500, 1")
       }
    }.Check(request);

    CMutableTransaction tx = ParseMutableTransaction(request.params[0]);
    std::vector<PrevTxsEntry> prevTxsParsed = ParsePrevTxs(request.params[1]);
    std::string destination = ParseAddress(request.params[2]);
    int64_t txFee = AmountFromValue(request.params[3]);
    uint32_t nOut = request.params.size() > 4 ? request.params[4].getInt<int64_t>() : 0;

    // use a dummy coins view to store the user provided transaction inputs
    CCoinsViewCacheOnly viewTemp;
    InputsToView(prevTxsParsed, viewTemp);

    // extend the transaction
    tx = OmniTxBuilder(tx)
            .addChange(destination, viewTemp, txFee, nOut)
            .build();

    return EncodeHexTx(CTransaction(tx));
}

static const CRPCCommand commands[] =
{ //  category                         name                          actor (function)             okSafeMode
  //  -------------------------------- ----------------------------- ---------------------------- ----------
    { "omni layer (raw transactions)", "omni_decodetransaction",     &omni_decodetransaction,     {"rawtx", "prevtxs", "height"} },
    { "omni layer (raw transactions)", "omni_createrawtx_opreturn",  &omni_createrawtx_opreturn,  {"rawtx", "payload"} },
    { "omni layer (raw transactions)", "omni_createrawtx_multisig",  &omni_createrawtx_multisig,  {"rawtx", "payload", "seed", "redeemkey"} },
    { "omni layer (raw transactions)", "omni_createrawtx_input",     &omni_createrawtx_input,     {"rawtx", "txid", "n"} },
    { "omni layer (raw transactions)", "omni_createrawtx_reference", &omni_createrawtx_reference, {"rawtx", "destination", "referenceamount"} },
    { "omni layer (raw transactions)", "omni_createrawtx_change",    &omni_createrawtx_change,    {"rawtx", "prevtxs", "destination", "fee", "position"} },

};

void RegisterOmniRawTransactionRPCCommands(CRPCTable &tableRPC)
{
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        tableRPC.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
