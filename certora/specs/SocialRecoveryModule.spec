using SafeHarness as safeContract;

definition SENTINEL() returns address = 1;

methods {
    // Social Recovery Module Functions
    function isGuardian(address, address) external returns (bool) envfree;
    function guardiansCount(address) external returns (uint256) envfree;
    function threshold(address) external returns (uint256) envfree;
    function nonce(address) external returns (uint256) envfree;
    function getRecoveryHash(address, address[], uint256, uint256) external returns (bytes32) envfree;
    function getRecoveryApprovals(address, address[], uint256) external returns (uint256) envfree;
    function countGuardians(address) external returns (uint256) envfree;
    function getGuardians(address) external returns (address[]) envfree;

    // Safe Functions
    function safeContract.isModuleEnabled(address module) external returns (bool) envfree;
    function safeContract.isOwner(address owner) external returns (bool) envfree;
    function safeContract.getOwners() external returns (address[] memory) envfree;
    function safeContract.getThreshold() external returns (uint256) envfree;

    // Wildcard Functions (Because of use of ISafe interface in Social Recovery Module)
    function _.isModuleEnabled(address module) external => summarizeSafeIsModuleEnabled(calledContract, module) expect bool ALL; // `calledContract` is a special variable.
    function _.isOwner(address owner) external => summarizeSafeIsOwner(calledContract, owner) expect bool ALL;
    function _.getOwners() external => summarizeSafeGetOwners(calledContract) expect address[] ALL;
    function _.execTransactionFromModule(address to, uint256 value, bytes data, Enum.Operation operation) external with (env e) => summarizeSafeExecTransactionFromModule(calledContract, e, to, value, data, operation) expect bool ALL;
}

// A summary function that helps the prover resolve calls to `safeContract`.
function summarizeSafeIsModuleEnabled(address callee, address module) returns bool {
    if (callee == safeContract) {
        return safeContract.isModuleEnabled(module);
    }
    return _;
}

// A summary function that helps the prover resolve calls to `safeContract`.
function summarizeSafeIsOwner(address callee, address owner) returns bool {
    if (callee == safeContract) {
        return safeContract.isOwner(owner);
    }
    return _;
}

// A summary function that helps the prover resolve calls to `safeContract`.
function summarizeSafeGetOwners(address callee) returns address[] {
    if (callee == safeContract) {
        return safeContract.getOwners();
    }
    return _;
}

// A summary function that helps the prover resolve calls to `safeContract`.
function summarizeSafeExecTransactionFromModule(address callee, env e, address to, uint256 value, bytes data, Enum.Operation operation) returns bool {
    if (callee == safeContract) {
        return safeContract.execTransactionFromModule(e, to, value, data, operation);
    }
    return _;
}

// A setup function that requires Safe contract to enable the Social Recovery Module.
function requireSocialRecoveryModuleEnabled() {
    require(safeContract.isModuleEnabled(currentContract));
}

// Setup function that `require`s the integrity of the guardians linked list in the
// `GuardianStorage` contract. For proof of this integrity, see `GuardianStorage.spec`.
function requireGuardiansLinkedListIntegrity(address guardian) {
    uint256 index;
    require index < currentContract.entries[safeContract].count;
    require currentContract.isGuardian(safeContract, guardian) =>
        currentContract.getGuardians(safeContract)[index] == guardian;
    require !currentContract.isGuardian(safeContract, guardian) =>
        (forall address prevGuardian. currentContract.entries[safeContract].guardians[prevGuardian] != guardian);
    require currentContract.entries[safeContract].count == currentContract.countGuardians(safeContract);
}

// This integrity rule verifies that if the addGuardianWithThreshold(...) executes, then ensure that:
// - the Social Recovery Module is enabled
// - the caller to the Module has to be the Safe Contract
// - the new guardian is added to the guardian list,
// - and no other account (guardian or not) is affected.
rule addGuardianWorksAsExpected(env e, address guardian, uint256 threshold, address otherAccount) {
    requireGuardiansLinkedListIntegrity(guardian);

    // If threshold is same as before, then no change is made to the threshold during guardian addition.
    // Thus, it is required to add this check to ensure no initial state have threshold > count.
    require threshold == currentContract.entries[safeContract].threshold =>
        currentContract.entries[safeContract].threshold <= currentContract.entries[safeContract].count;

    uint256 currentGuardiansCount = currentContract.entries[safeContract].count;
    bool otherAccountIsGuardian = currentContract.isGuardian(safeContract, otherAccount);

    currentContract.addGuardianWithThreshold(e, guardian, threshold);

    assert e.msg.sender == safeContract =>
        safeContract.isModuleEnabled(currentContract) &&
        currentContract.isGuardian(safeContract, guardian) &&
        guardian != otherAccount => otherAccountIsGuardian == currentContract.isGuardian(safeContract, otherAccount) &&
        currentGuardiansCount + 1 == to_mathint(currentContract.entries[safeContract].count) &&
        threshold > 0 && threshold <= currentContract.entries[safeContract].count;
}

// This integrity rule verifies that the guardian can always be added considering ideal conditions.
rule guardianCanAlwaysBeAdded(env e, address guardian, uint256 threshold) {
    requireSocialRecoveryModuleEnabled();
    requireGuardiansLinkedListIntegrity(guardian);

    // No value should be sent with the transaction.
    require e.msg.value == 0;

    uint256 currentGuardiansCount = currentContract.entries[safeContract].count;    
    // The guardian count should be less than the maximum value to prevent overflow.
    require currentGuardiansCount < max_uint256; // To prevent overflow (Realistically can't reach).

    // The guardian should not be values such as zero, sentinel, or the Safe contract itself.
    require guardian != 0;
    require guardian != SENTINEL();
    require guardian != safeContract;

    // The guardian should not be an owner of the Safe contract at the time of addition.
    require !safeContract.isOwner(guardian);
    // The guardian should not be already added as a guardian.
    require !currentContract.isGuardian(safeContract, guardian);

    // The threshold must be greater than 0 and less than or equal to the total number of guardians after adding the new guardian.
    require threshold > 0 && to_mathint(threshold) <= currentContract.entries[safeContract].count + 1;

    // Safe contract should be the sender of the transaction.
    require e.msg.sender == safeContract;
    currentContract.addGuardianWithThreshold@withrevert(e, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted &&
        currentContract.isGuardian(safeContract, guardian) &&
        currentGuardiansCount + 1 == to_mathint(currentContract.entries[safeContract].count);
}

// This integrity rule verifies the possibilites in which the addition of a new guardian can revert.
rule addGuardianRevertPossibilities(env e, address guardian, uint256 threshold) {
    bool isGuardian = currentContract.isGuardian(safeContract, guardian);

    currentContract.addGuardianWithThreshold@withrevert(e, guardian, threshold);
    bool isReverted = lastReverted;

    assert isReverted =>
        isGuardian ||
        e.msg.sender != safeContract ||
        e.msg.value != 0 ||
        guardian == 0 ||
        guardian == SENTINEL() ||
        guardian == safeContract ||
        safeContract.isOwner(guardian) ||
        threshold == 0 ||
        to_mathint(threshold) > currentContract.entries[safeContract].count + 1 ||
        currentContract.entries[safeContract].count == max_uint256 ||
        !safeContract.isModuleEnabled(currentContract);
}

// This integrity rule verifies that if the revokeGuardianWithThreshold(...) executes, then ensure that:
// - the Social Recovery Module is enabled
// - the caller to the Module has to be the Safe Contract
// - the guardian is revoked from the guardian list
// - the linked list integrity remains,
// - and no other account (guardian or not) is affected.
rule revokeGuardiansWorksAsExpected(env e, address guardian, address prevGuardian, uint256 threshold, address otherAccount) {
    requireGuardiansLinkedListIntegrity(guardian);

    address nextGuardian = currentContract.entries[safeContract].guardians[guardian];
    bool otherAccountIsGuardian = currentContract.isGuardian(safeContract, otherAccount);

    uint256 currentGuardiansCount = currentContract.entries[safeContract].count;

    currentContract.revokeGuardianWithThreshold(e, prevGuardian, guardian, threshold);

    assert e.msg.sender == safeContract =>
        safeContract.isModuleEnabled(currentContract) &&
        !currentContract.isGuardian(safeContract, guardian) &&
        currentContract.entries[safeContract].guardians[prevGuardian] == nextGuardian &&
        guardian != otherAccount => otherAccountIsGuardian == currentContract.isGuardian(safeContract, otherAccount) &&
        currentGuardiansCount - 1 == to_mathint(currentContract.entries[safeContract].count) &&
        threshold <= currentContract.entries[safeContract].count;
}

// This integrity rule verifies that the guardian can always be revoked considering ideal conditions.
rule guardianCanAlwaysBeRevoked(env e, address guardian, address prevGuardian, uint256 threshold) {
    requireSocialRecoveryModuleEnabled();
    requireGuardiansLinkedListIntegrity(guardian);

    // No value should be sent with the transaction.
    require e.msg.value == 0;
    // If new threshold is 0, then you must be removing the last guardian meaning the guardian count should be 1.
    require threshold == 0 => currentContract.entries[safeContract].count == 1;
    // The new threshold should be less than or equal to the guardian count after removing.
    require to_mathint(threshold) <= currentContract.entries[safeContract].count - 1;
    // The address should be a guardian.
    require currentContract.isGuardian(safeContract, guardian);

    address nextGuardian = currentContract.entries[safeContract].guardians[guardian];
    require currentContract.entries[safeContract].guardians[prevGuardian] == guardian;

    uint256 currentGuardiansCount = currentContract.entries[safeContract].count;    

    // Safe Contract should be the sender of the transaction.
    require e.msg.sender == safeContract;
    currentContract.revokeGuardianWithThreshold@withrevert(e, prevGuardian, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted &&
        currentContract.entries[safeContract].guardians[prevGuardian] == nextGuardian &&
        !currentContract.isGuardian(safeContract, guardian) &&
        currentGuardiansCount - 1 == to_mathint(currentContract.entries[safeContract].count);
}

// This integrity rule verifies the possibilites in which the revocation of a new guardian can revert.
rule revokeGuardianRevertPossibilities(env e, address prevGuardian, address guardian, uint256 threshold) {
    requireGuardiansLinkedListIntegrity(guardian);

    bool isGuardian = currentContract.isGuardian(safeContract, guardian);

    currentContract.revokeGuardianWithThreshold@withrevert(e, prevGuardian, guardian, threshold);
    bool isReverted = lastReverted;

    assert isReverted =>
        !isGuardian ||
        e.msg.sender != safeContract ||
        e.msg.value != 0 ||
        !safeContract.isModuleEnabled(currentContract) ||
        currentContract.entries[safeContract].guardians[prevGuardian] != guardian ||
        to_mathint(threshold) > currentContract.entries[safeContract].count - 1 ||
        (threshold == 0 && currentContract.entries[safeContract].count != 1);
}

// This rule verifies that the guardian can always initiate recovery considering some ideal conditions.
rule confirmRecoveryCanAlwaysBeInitiatedByGuardian(env e, address guardian, address[] newOwners, uint256 newThreshold, bool execute) {
    uint256 index;
    // Index must be valid.
    require index < newOwners.length;

    // The threshold should always be greater than 0 and less than the number of new owners.
    require newThreshold > 0;
    require newThreshold <= newOwners.length;

    // No ether should be sent as part of this function call, and the caller should be a guardian.
    require e.msg.value == 0;
    require e.msg.sender == guardian;
    require currentContract.isGuardian(safeContract, guardian);

    requireGuardiansLinkedListIntegrity(guardian);

    // Nonce and timestamp + recovery period should not overflow (Realistically can't reach).
    require e.block.timestamp + currentContract.recoveryPeriod <= max_uint64;
    uint256 nonce = currentContract.nonce(safeContract);
    require nonce < max_uint256;

    bytes32 recoveryHash = currentContract.getRecoveryHash(safeContract, newOwners, newThreshold, nonce);
    // This ensures that the recovery is not already initiated.
    require currentContract.recoveryRequests[safeContract].executeAfter == 0;

    // This ensures that the required threshold is reached.
    require currentContract.getRecoveryApprovals(safeContract, newOwners, newThreshold) == currentContract.threshold(safeContract);

    currentContract.confirmRecovery@withrevert(e, safeContract, newOwners, newThreshold, execute);
    bool isReverted = lastReverted;

    assert !isReverted &&
        currentContract.confirmedHashes[recoveryHash][e.msg.sender];
    assert execute =>
        to_mathint(currentContract.recoveryRequests[safeContract].executeAfter) == e.block.timestamp + currentContract.recoveryPeriod &&
        currentContract.recoveryRequests[safeContract].newThreshold == newThreshold &&
        currentContract.recoveryRequests[safeContract].newOwners.length == newOwners.length &&
        currentContract.recoveryRequests[safeContract].newOwners[index] == newOwners[index];
}

// This rule verifies that the finalization cannot happen if the recovery module is not enabled.
// Exceptions are made for the case where the Safe has only one owner and the recovery is initiated
// - with zero new owners and zero as the new threshold
// - with same last owner & threshold as Safe.
rule disabledRecoveryModuleResultsInFinalizationRevert(env e) {
    address[] currentOwners = safeContract.getOwners();
    uint256 currentThreshold = safeContract.getThreshold();

    require !safeContract.isModuleEnabled(currentContract);

    currentContract.finalizeRecovery@withrevert(e, safeContract);
    bool isReverted = lastReverted;

    // If the recovery finalization is initiated with the safe having only one owner,
    // and the finalize recovery initiated with no new owners and zero as new threshold,
    // OR with the same last owner of safe and threshold == newThreshold == 1,
    // then the finalize recovery call goes through, as no owner is removed and no new
    // owner is added. Though it is not possible to have a recovery initiation with zero
    // owners.
    assert isReverted ||
        (currentOwners[0] == safeContract.getOwners()[0] &&
            safeContract.getOwners().length == 1 &&
            currentThreshold == safeContract.getThreshold());
}

// Recovery can be cancelled
rule cancelRecovery(env e) {
    require e.msg.sender == safeContract;
    require e.msg.value == 0;

    // A recovery request must be initiated.
    require currentContract.recoveryRequests[safeContract].executeAfter > 0;
    require currentContract.walletsNonces[safeContract] > 0;

    currentContract.cancelRecovery@withrevert(e, safeContract);
    assert !lastReverted;
}

// Cancelling recovery for a wallet does not affect other wallets
rule cancelRecoveryDoesNotAffectOtherWallet(env e, address otherWallet) {
    require e.msg.sender == safeContract;
    require e.msg.value == 0;

    SocialRecoveryModule.RecoveryRequest otherRequestBefore = currentContract.getRecoveryRequest(e, otherWallet);
    uint256 otherWalletNonceBefore = currentContract.walletsNonces[otherWallet];
    uint256 i;
    require i < otherRequestBefore.newOwners.length;

    // A recovery request must be initiated.
    require currentContract.recoveryRequests[safeContract].executeAfter > 0;
    require currentContract.walletsNonces[safeContract] > 0;

    currentContract.cancelRecovery(e, safeContract);

    SocialRecoveryModule.RecoveryRequest otherRequestAfter = currentContract.getRecoveryRequest(e, otherWallet);

    assert safeContract != otherWallet =>
        otherRequestBefore.guardiansApprovalCount == otherRequestAfter.guardiansApprovalCount &&
        otherRequestBefore.newThreshold == otherRequestAfter.newThreshold &&
        otherRequestBefore.executeAfter == otherRequestAfter.executeAfter &&
        otherRequestBefore.newOwners.length == otherRequestAfter.newOwners.length &&
        otherRequestBefore.newOwners[i] == otherRequestAfter.newOwners[i] &&
        otherWalletNonceBefore == currentContract.walletsNonces[otherWallet];
}
