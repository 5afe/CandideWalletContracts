using SafeHarness as safeContract;
using GuardianStorageHarness as guardianStorageContract;

definition SENTINEL() returns address = 1;

methods {
    // Social Recovery Module Functions
    function isGuardian(address, address) external returns (bool) envfree;
    function guardiansCount(address) external returns (uint256) envfree;
    function threshold(address) external returns (uint256) envfree;
    function nonce(address) external returns (uint256) envfree;
    function encodeRecoveryDataHash(address, address[], uint256, uint256) external returns (bytes32) envfree;

    // Guardian Storage Functions
    function guardianStorageContract.countGuardians(address) external returns (uint256) envfree;

    // Safe Functions
    function safeContract.isModuleEnabled(address module) external returns (bool) envfree;
    function safeContract.isOwner(address owner) external returns (bool) envfree;
    function safeContract.getOwners() external returns (address[] memory) envfree;

    // Wildcard Functions (Because of use of ISafe interface in Social Recovery Module)
    function _.isModuleEnabled(address module) external => safeIsModuleEnabled(calledContract, module) expect bool ALL; // `calledContract` is a special variable.
    function _.isOwner(address owner) external => sumarizeSafeIsOwner(calledContract, owner) expect bool ALL;
}

// A summary function to check if a module is enabled in the Safe contract.
function safeIsModuleEnabled(address callee, address module) returns bool {
    assert callee == safeContract;
    return safeContract.isModuleEnabled(module);
}

// A summary function to check if an address is an owner in the Safe contract.
function sumarizeSafeIsOwner(address callee, address owner) returns bool {
    assert callee == safeContract;
    return safeContract.isOwner(owner);
}

// A setup function that requires Safe contract to enabled the Social Recovery Module.
function requireSocialRecoveryModuleEnabled() {
    require(safeContract.isModuleEnabled(currentContract));
}

// This integrity rule verifies that the addGuardianWithThreshold(...) if executes ensures that
// the Social Recovery Module is enabled, the caller to the Module has to be the Safe Contract,
// the new guardian is added to the guardian list, and no other account (guardian or not) is affected.
rule addGuardianWorksAsExpected(env e, address guardian, uint256 threshold, address otherAccount) {

    uint256 currentGuardiansCount = guardianStorageContract.entries[safeContract].count;

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    require guardian != otherAccount;
    bool otherAccountIsGuardian = currentContract.isGuardian(safeContract, otherAccount);

    currentContract.addGuardianWithThreshold(e, safeContract, guardian, threshold);

    assert safeContract.isModuleEnabled(currentContract);
    assert e.msg.sender == safeContract;
    assert currentContract.isGuardian(safeContract, guardian);
    assert otherAccountIsGuardian == currentContract.isGuardian(safeContract, otherAccount);
    assert currentGuardiansCount + 1 == to_mathint(guardianStorageContract.entries[safeContract].count);
}

// This integrity rule verifies that the guardian can always be added considering ideal conditions.
rule guardianCanAlwaysBeAdded(env e, address guardian, uint256 threshold) {

    requireSocialRecoveryModuleEnabled();

    require e.msg.value == 0;
    require threshold > 0;
    require guardianStorageContract.entries[safeContract].count < max_uint256; // To prevent overflow (Realistically can't reach).

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    require guardian != 0;
    require guardian != SENTINEL();
    require guardian != safeContract;

    require !safeContract.isOwner(guardian);
    require !currentContract.isGuardian(safeContract, guardian);

    require threshold < guardianStorageContract.countGuardians(safeContract);

    require e.msg.sender == safeContract;
    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted && currentContract.isGuardian(safeContract, guardian);
}

// This integrity rule verifies that the addition of a new guardian always reverts if the guardian is already added.
rule addGuardiansRevertIfDuplicateGuardian(env e, address guardian, uint256 threshold) {

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    require currentContract.isGuardian(safeContract, guardian);

    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);
    bool isReverted = lastReverted;

    assert lastReverted;
}

// This integrity rule verifies that the revokeGuardianWithThreshold(...) if executes ensures that
// the Social Recovery Module is enabled, the caller to the Module has to be the Safe Contract, the
// guardian is removed from the guardian list, the linked list integrity remains and no other account
// (guardian or not) is affected.
rule removeGuardiansWorksAsExpected(env e, address guardian, address prevGuardian, uint256 threshold, address otherAccount) {

    address nextGuardian = guardianStorageContract.entries[safeContract].guardians[guardian];

    require guardian != otherAccount;
    bool otherAccountIsGuardian = currentContract.isGuardian(safeContract, otherAccount);

    uint256 currentGuardiansCount = guardianStorageContract.entries[safeContract].count;
    require currentGuardiansCount > 0;

    // This could be removed once linked list invariant is implemented.
    // <------------------------------------------------------------>
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.
    require guardian != prevGuardian;
    require guardian != nextGuardian;
    require prevGuardian != nextGuardian;
    // <------------------------------------------------------------>

    currentContract.revokeGuardianWithThreshold(e, safeContract, prevGuardian, guardian, threshold);

    assert safeContract.isModuleEnabled(currentContract);
    assert e.msg.sender == safeContract;
    assert !currentContract.isGuardian(safeContract, guardian);
    assert guardianStorageContract.entries[safeContract].guardians[prevGuardian] == nextGuardian;
    assert otherAccountIsGuardian == currentContract.isGuardian(safeContract, otherAccount);
    assert currentGuardiansCount - 1 == to_mathint(guardianStorageContract.entries[safeContract].count);
}

// This integrity rule verifies that the guardian can always be removed considering ideal conditions.
rule guardianCanAlwaysBeRemoved(env e, address guardian, address prevGuardian, uint256 threshold) {

    requireSocialRecoveryModuleEnabled();

    require e.msg.value == 0;
    require guardian != 0;
    require threshold > 0;
    require currentContract.isGuardian(safeContract, guardian);
    require guardianStorageContract.entries[safeContract].count > threshold;

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 && guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    address nextGuardian = guardianStorageContract.entries[safeContract].guardians[guardian];
    require prevGuardian != nextGuardian;
    require guardianStorageContract.entries[safeContract].guardians[prevGuardian] == guardian;

    require e.msg.sender == safeContract;
    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted &&
        guardianStorageContract.entries[safeContract].guardians[prevGuardian] == nextGuardian &&
        !currentContract.isGuardian(safeContract, guardian);
}

// This rule verifies that only the guardian can initiate recovery.
rule confirmRecoveryIsInitiatedByGuardian(env e, address[] newOwners, uint256 newThreshold, bool execute, uint256 index) {
    require index < newOwners.length; // Index should be less than the number of owners.
    require newThreshold <= newOwners.length; // Threshold should be less than or equal to the number of owners.
    require e.block.timestamp + currentContract.recoveryPeriod < max_uint64; // The year will be 2500+ (Roughly 500 years from now).

    uint256 nonce = currentContract.nonce(safeContract);
    bytes32 recoveryHash = currentContract.encodeRecoveryDataHash(safeContract, newOwners, newThreshold, nonce);

    currentContract.confirmRecovery@withrevert(e, safeContract, newOwners, newThreshold, execute);
    bool isReverted = lastReverted; // Check if the transaction is reverted.

    // Check if the recovery initiation started.
    assert !isReverted =>
        currentContract.isGuardian(safeContract, e.msg.sender) && // Only guardian can call this function.
        currentContract.confirmedHashes[recoveryHash][e.msg.sender]; // Check if the guardian confirmed the recovery.
    // Check if the recovery is executed as well.
    assert !isReverted && execute =>
        to_mathint(currentContract.recoveryRequests[safeContract].executeAfter) == e.block.timestamp + currentContract.recoveryPeriod && // Check if the recovery finalization time is set.
        currentContract.recoveryRequests[safeContract].newThreshold == newThreshold; // Check if the new threshold is set.
}
