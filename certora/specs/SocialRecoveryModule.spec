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
    function getRecoveryApprovals(address, address[], uint256) external returns (uint256) envfree;

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

// This rule verifies that the guardian can always initiate recovery considering some ideal conditions.
rule confirmRecoveryCanAlwaysBeInitiatedByGuardian(env e, address guardian, address[] newOwners, uint256 newThreshold, bool execute) {

    require newThreshold > 0;
    require newThreshold <= newOwners.length;

    require e.msg.value == 0;
    require e.msg.sender == guardian;
    require currentContract.isGuardian(safeContract, guardian);
    require guardianStorageContract.entries[safeContract].count == guardianStorageContract.countGuardians(safeContract);
    require e.block.timestamp + currentContract.recoveryPeriod < max_uint64;

    uint256 nonce = currentContract.nonce(safeContract);
    require nonce < max_uint256;

    bytes32 recoveryHash = currentContract.encodeRecoveryDataHash(safeContract, newOwners, newThreshold, nonce);
    require currentContract.recoveryRequests[safeContract].executeAfter == 0; // This ensures that the recovery is not already initiated.

    // This ensures that the required threshold is reached.
    require currentContract.getRecoveryApprovals(safeContract, newOwners, newThreshold) == currentContract.threshold(safeContract);

    currentContract.confirmRecovery@withrevert(e, safeContract, newOwners, newThreshold, execute);
    bool isReverted = lastReverted;

    assert !isReverted &&
        currentContract.confirmedHashes[recoveryHash][e.msg.sender];
    assert execute =>
        to_mathint(currentContract.recoveryRequests[safeContract].executeAfter) == e.block.timestamp + currentContract.recoveryPeriod &&
        currentContract.recoveryRequests[safeContract].newThreshold == newThreshold;
}
