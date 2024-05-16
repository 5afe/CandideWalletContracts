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

// A summary function that asserts that all `ISafe.isModuleEnabled` calls are done
// to the `safeContract`, returning the same result as `safeContract.isModuleEnabled(...)`.
function safeIsModuleEnabled(address callee, address module) returns bool {
    assert callee == safeContract;
    return safeContract.isModuleEnabled(module);
}

// A summary function that asserts that all `ISafe.isOwner` calls are done
// to the `safeContract`, returning the same result as `safeContract.isOwner(...)`.
function sumarizeSafeIsOwner(address callee, address owner) returns bool {
    assert callee == safeContract;
    return safeContract.isOwner(owner);
}

// A setup function that requires Safe contract to enable the Social Recovery Module.
function requireSocialRecoveryModuleEnabled() {
    require(safeContract.isModuleEnabled(currentContract));
}

function requireGuardiansLinkedListIntegrity() {
    require guardianStorageContract.entries[safeContract].count == guardianStorageContract.countGuardians(safeContract);
}

// This integrity rule verifies that if the addGuardianWithThreshold(...) executes, then ensure that:
// - the Social Recovery Module is enabled
// - the caller to the Module has to be the Safe Contract
// - the new guardian is added to the guardian list,
// - and no other account (guardian or not) is affected.
rule addGuardianWorksAsExpected(env e, address guardian, uint256 threshold, address otherAccount) {
    uint256 currentGuardiansCount = guardianStorageContract.entries[safeContract].count;

    requireGuardiansLinkedListIntegrity();

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
    requireGuardiansLinkedListIntegrity();

    require guardian != 0;
    require guardian != SENTINEL();
    require guardian != safeContract;

    require !safeContract.isOwner(guardian);
    require !currentContract.isGuardian(safeContract, guardian);

    require threshold <= guardianStorageContract.countGuardians(safeContract);

    require e.msg.sender == safeContract;
    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted && currentContract.isGuardian(safeContract, guardian);
}

// This integrity rule verifies that the addition of a new guardian always reverts if the guardian is already added.
rule addGuardianRevertIfDuplicateGuardian(env e, address guardian, uint256 threshold) {
    bool isGuardian = currentContract.isGuardian(safeContract, guardian);

    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);

    assert isGuardian => lastReverted;
}

// This integrity rule verifies that the addition of a new guardian can revert due to different reasons even if the address is not a guardian.
rule addGuardianCanRevertEvenIfAddressIsNotGuardian(env e, address otherAccount, uint256 threshold) {
    bool isNotGuardian = !currentContract.isGuardian(safeContract, otherAccount);

    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, otherAccount, threshold);

    assert isNotGuardian && lastReverted =>
        e.msg.sender != safeContract ||
        e.msg.value != 0 ||
        otherAccount == 0 ||
        otherAccount == SENTINEL() ||
        otherAccount == safeContract ||
        safeContract.isOwner(otherAccount) ||
        threshold == 0 ||
        threshold >= guardianStorageContract.entries[safeContract].count ||
        guardianStorageContract.entries[safeContract].count == max_uint256 ||
        !safeContract.isModuleEnabled(currentContract);
}

// This integrity rule verifies that if the revokeGuardianWithThreshold(...) executes, then ensure that:
// - the Social Recovery Module is enabled
// - the caller to the Module has to be the Safe Contract
// - the guardian is revoked from the guardian list
// - the linked list integrity remains,
// - and no other account (guardian or not) is affected.
rule revokeGuardiansWorksAsExpected(env e, address guardian, address prevGuardian, uint256 threshold, address otherAccount) {
    address nextGuardian = guardianStorageContract.entries[safeContract].guardians[guardian];

    require guardian != otherAccount;
    bool otherAccountIsGuardian = currentContract.isGuardian(safeContract, otherAccount);

    uint256 currentGuardiansCount = guardianStorageContract.entries[safeContract].count;
    require currentGuardiansCount > 0;

    requireGuardiansLinkedListIntegrity();
    require guardianStorageContract.entries[safeContract].guardians[guardian] != guardian;

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
    require guardianStorageContract.countGuardians(safeContract) > threshold;
    require currentContract.isGuardian(safeContract, guardian);
    require guardianStorageContract.entries[safeContract].guardians[guardian] != guardian;
    requireGuardiansLinkedListIntegrity();

    address nextGuardian = guardianStorageContract.entries[safeContract].guardians[guardian];
    require guardianStorageContract.entries[safeContract].guardians[prevGuardian] == guardian;

    require e.msg.sender == safeContract;
    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, guardian, threshold);
    bool isReverted = lastReverted;

    assert !isReverted &&
        guardianStorageContract.entries[safeContract].guardians[prevGuardian] == nextGuardian &&
        !currentContract.isGuardian(safeContract, guardian);
}

// This integrity rule verifies that the revocation of an address always reverts if the address is not a guardian.
rule revokeGuardianRevertIfAddressNotGuardian(env e, address otherAccount, address prevGuardian, uint256 threshold) {
    bool isNotGuardian = !currentContract.isGuardian(safeContract, otherAccount);

    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, otherAccount, threshold);

    assert isNotGuardian => lastReverted;
}

// This integrity rule verifies that the revocation of an address can revert due to different reasons even if the address is a guardian.
rule revokeGuardianCanRevertEvenIfAddressIsGuardian(env e, address otherAccount, address prevGuardian, uint256 threshold) {
    bool isGuardian = currentContract.isGuardian(safeContract, otherAccount);

    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, otherAccount, threshold);

    assert isGuardian && lastReverted =>
        e.msg.sender != safeContract ||
        e.msg.value != 0 ||
        otherAccount == 0 ||
        otherAccount == SENTINEL() ||
        threshold == 0 ||
        guardianStorageContract.entries[safeContract].count == 0 ||
        threshold >= guardianStorageContract.entries[safeContract].count ||
        !safeContract.isModuleEnabled(currentContract) ||
        guardianStorageContract.entries[safeContract].guardians[prevGuardian] != otherAccount;
}
