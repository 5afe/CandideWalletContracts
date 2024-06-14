using SafeHarness as safeContract;

methods {
    // Social Recovery Module Functions
    function getRecoveryHash(address, address[] calldata, uint256, uint256) internal returns (bytes32) => CONSTANT;
    function nonce(address) external returns (uint256) envfree;
    function SignatureChecker.isValidSignatureNow(address signer, bytes32 dataHash, bytes memory signatures) internal returns (bool) => isValidSignatureNowSummary(signer, dataHash, signatures);

    // Wildcard Functions
    function _.execTransactionFromModule(address to, uint256 value, bytes data, Enum.Operation operation) external with (env e) => summarizeSafeExecTransactionFromModule(calledContract, e, to, value, data, operation) expect bool ALL;
    function _.isModuleEnabled(address module) external => DISPATCHER(false);
    function _.isOwner(address owner) external => DISPATCHER(false);
    function _.getOwners() external => DISPATCHER(false);
    function _._ external => DISPATCH[] default NONDET;
}

// A summary function that helps the prover resolve calls to `safeContract`.
function summarizeSafeExecTransactionFromModule(address callee, env e, address to, uint256 value, bytes data, Enum.Operation operation) returns bool {
    if (callee == safeContract) {
        return safeContract.execTransactionFromModule(e, to, value, data, operation);
    }
    return _;
}

ghost isValidSignatureNowSummary(address, bytes32, bytes) returns bool;

rule multiConfirmRecoveryOnlyWithLegitimateSignatures(env e) {
    address _wallet;
    address[] _newOwners;
    uint256 _newThreshold;
    uint256 walletNonce = currentContract.nonce(_wallet);
    SocialRecoveryModule.SignatureData[] signatures;
    bool _execute;
    bytes32 recoveryHash = getRecoveryHash(
        e,
        _wallet,
        _newOwners,
        _newThreshold,
        walletNonce
    );

    checkSignatures@withrevert(e, _wallet, recoveryHash, signatures);
    bool signatureCheckSuccess = !lastReverted;

    multiConfirmRecovery(e, _wallet, _newOwners, _newThreshold, signatures, _execute);

    assert signatureCheckSuccess, "Recovery confirmed with invalid signatures";
}