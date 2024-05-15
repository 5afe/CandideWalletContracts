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
    function _.isModuleEnabled(address module) external => safeIsModuleEnabled(module) expect bool ALL;
    function _.isOwner(address owner) external => safeCallerCheckIsOwner(calledContract, owner) expect bool ALL; // `calledContract` is a special variable.
}

// A summary function to check if a module is enabled in the Safe contract.
function safeIsModuleEnabled(address module) returns bool {
    return safeContract.isModuleEnabled(module);
}

// A summary function to check if an address is an owner in the Safe contract.
function safeCallerCheckIsOwner(address calledContractAddress, address owner) returns bool {
    assert calledContractAddress == safeContract; // This checks that the caller is Safe Smart Account.
    return safeContract.isOwner(owner);
}

// A setup function that requires Safe contract to enabled the Social Recovery Module.
function requireSocialRecoveryModuleEnabled() {
    require(safeContract.isModuleEnabled(currentContract));
}

// This integrity rule verifies that the addGuardianWithThreshold(...) works as expected.
rule addGuardianWorksAsExpected(env e, address guardian, uint256 threshold, address otherGuardian) {

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    require guardian != otherGuardian;

    bool otherWasGuardian = currentContract.isGuardian(safeContract, otherGuardian);

    currentContract.addGuardianWithThreshold(e, safeContract, guardian, threshold);

    assert safeContract.isModuleEnabled(currentContract);
    assert e.msg.sender == safeContract;
    assert currentContract.isGuardian(safeContract, guardian);
    assert otherWasGuardian == currentContract.isGuardian(safeContract, otherGuardian);
}

// This integrity rule verifies that the guardian can always be added considering ideal conditions.
rule guardianCanAlwaysBeAdded(env e, address guardian, uint256 threshold, address otherGuardian) {

    requireSocialRecoveryModuleEnabled();

    require e.msg.value == 0;
    require threshold > 0;
    require guardianStorageContract.entries[safeContract].count < max_uint256; // To prevent overflow (Realistically can't reach).

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    require guardian != 0;
    require guardian != SENTINEL();
    require guardian != safeContract;
    require guardian != otherGuardian;

    require !safeContract.isOwner(guardian);
    require !currentContract.isGuardian(safeContract, guardian);

    require threshold < guardianStorageContract.countGuardians(safeContract);

    bool otherWasGuardian = currentContract.isGuardian(safeContract, otherGuardian);

    require e.msg.sender == safeContract;
    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted => currentContract.isGuardian(safeContract, guardian);
    assert otherWasGuardian == currentContract.isGuardian(safeContract, otherGuardian);
}

// This integrity rule verifies that the revokeGuardianWithThreshold(...) works as expected.
rule removeGuardiansWorksAsExpected(env e, address guardian, address prevGuardian, uint256 threshold) {

    address nextGuardian = guardianStorageContract.entries[safeContract].guardians[guardian];

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
}

// This integrity rule verifies that the guardian can always be removed considering ideal conditions.
rule guardianCanAlwaysBeRemoved(env e, address guardian, address prevGuardian, uint256 threshold) {

    requireSocialRecoveryModuleEnabled();

    require e.msg.value == 0;

    // This can be removed once linked list invariant is implemented.
    require guardianStorageContract.entries[safeContract].count > 0 => guardianStorageContract.entries[safeContract].guardians[SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    address nextGuardian = guardianStorageContract.entries[safeContract].guardians[guardian];
    require prevGuardian != nextGuardian;

    require e.msg.sender == safeContract;
    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted =>
        guardianStorageContract.entries[safeContract].guardians[prevGuardian] == nextGuardian &&
        !currentContract.isGuardian(safeContract, guardian);
}
