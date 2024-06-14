using SafeHarness as safeContract;

methods {
    // Social Recovery Module Functions
    function nonce(address) external returns (uint256) envfree;
    function isGuardian(address, address) external returns (bool) envfree;

    // Social Recovery Module Summaries
    function getRecoveryHash(address, address[] calldata, uint256, uint256) internal returns (bytes32) => CONSTANT;
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

persistent ghost mathint recoveryConfirmationCount {
    init_state axiom recoveryConfirmationCount == 0;
}

hook Sstore confirmedHashes[KEY bytes32 recoveryHash][KEY address guardian] bool value {
    recoveryConfirmationCount = recoveryConfirmationCount + 1;
}

// This rule the `multiConfirmRecovery` function can only be called with legitimate signatures.
// It assumes that the harnessed `checkSignatures` function is implemented correctly and reverts if the signatures are invalid.
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

// This rule checks that the number of approvals counted by the contract is equal to the number of valid signatures.
rule approvalsCountShouldEqualTheAmountOfSignatures(env e) {
    require recoveryConfirmationCount == 0;
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

    uint256 validSignatures = countValidSignatures(e, _wallet, recoveryHash, signatures);

    multiConfirmRecovery(e, _wallet, _newOwners, _newThreshold, signatures, _execute);

    assert validSignatures == assert_uint256(recoveryConfirmationCount), "more approvals counted than valid signatures";
}

// This rule checks that only supplied signatures and signers are counted as approvals.
rule noShadowApprovals(env e) {
    address _wallet;
    address[] _newOwners;
    uint256 _newThreshold;
    uint256 walletNonce = currentContract.nonce(_wallet);
    uint256 signatureIndex;
    SocialRecoveryModule.SignatureData[] signatures;
    bool _execute;
    bytes32 recoveryHash = getRecoveryHash(
        e,
        _wallet,
        _newOwners,
        _newThreshold,
        walletNonce
    );
    address otherAddress;
    require signatures[signatureIndex].signer != otherAddress;
    require !currentContract.confirmedHashes[recoveryHash][otherAddress];

    multiConfirmRecovery(e, _wallet, _newOwners, _newThreshold, signatures, _execute);

    assert forall uint256 i. 0 <= i && i < signatures.length => currentContract.confirmedHashes[recoveryHash][signatures[i].signer];
    assert !currentContract.confirmedHashes[recoveryHash][otherAddress];
}