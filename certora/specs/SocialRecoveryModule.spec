using SafeHarness as safeContract;
using GuardianStorageHarness as guardianStorageContract;

definition SENTINEL() returns address = 1;

methods {
    // Social Recovery Module Functions
    function isGuardian(address, address) external returns (bool) envfree;
    function guardiansCount(address) external returns (uint256) envfree;
    function threshold(address) external returns (uint256) envfree;

    // Guardian Storage Functions
    function guardianStorageContract.countGuardians(address) external returns (uint256) envfree;

    // Safe Functions
    function safeContract.isModuleEnabled(address module) external returns (bool) envfree;
    function safeContract.isOwner(address owner) external returns (bool) envfree;

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

    require currentContract.isGuardian(safeContract, guardian);

    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);
    bool isReverted = lastReverted;

    assert lastReverted;
}

// This integrity rule verifies that the revokeGuardianWithThreshold(...) if executes ensures that
// the Social Recovery Module is enabled, the caller to the Module has to be the Safe Contract, the
// guardian is revoked from the guardian list, the linked list integrity remains and no other account
// (guardian or not) is affected.
rule revokeGuardiansWorksAsExpected(env e, address guardian, address prevGuardian, uint256 threshold, address otherAccount) {

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

// This integrity rule verifies that the guardian can always be revoked considering ideal conditions.
rule guardianCanAlwaysBeRevoked(env e, address guardian, address prevGuardian, uint256 threshold) {

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

// This integrity rule verifies that the addition of a new guardian always reverts if the guardian is already added.
rule revokeGuardianRevertIfAddressNotGuardian(env e, address otherAccount, address prevGuardian, uint256 threshold) {

    require !currentContract.isGuardian(safeContract, otherAccount);

    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, otherAccount, threshold);
    bool isReverted = lastReverted;

    assert lastReverted;
}
