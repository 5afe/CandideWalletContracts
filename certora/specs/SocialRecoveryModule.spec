using SafeHarness as safeContract;
using GuardianStorageHarness as guardianStorageContract;

definition SENTINEL() returns address = 1;

methods {
    // Social Recovery Module Functions
    function isGuardian(address, address) external returns (bool) envfree;
    function guardiansCount(address) external returns (uint256) envfree;
    function threshold(address) external returns (uint256) envfree;

    // Guardian Storage Functions
    function guardianStorageContract.getGuardiansCount(address) external returns (uint256) envfree;

    // Safe Functions
    function safeContract.isModuleEnabled(address module) external returns (bool) envfree;
    function safeContract.isOwner(address owner) external returns (bool) envfree;

    // Wildcard Functions (Because of use of ISafe interface in Social Recovery Module)
    function _.isModuleEnabled(address module) external => safeIsModuleEnabled(module) expect bool ALL;
    function _.isOwner(address owner) external => safeIsOwner(calledContract, owner) expect bool ALL;
}

// Ghost variable to store the guardian mapping of a Safe.
ghost mapping(address => mapping(address => address)) ghostGuardians {
    init_state axiom
        forall address safeAccount.
        forall address guardian.
            ghostGuardians[safeAccount][guardian] == 0;
}
hook Sload address value guardianStorageContract.entries[KEY address safeAccount].guardians[KEY address guardian] {
    require ghostGuardians[safeAccount][guardian] == value;
}
hook Sstore guardianStorageContract.entries[KEY address safeAccount].guardians[KEY address guardian] address value {
    ghostGuardians[safeAccount][guardian] = value;
}

// Ghost variable to store the guardian count of a Safe.
ghost mapping(address => mathint) ghostGuardianCount {
    init_state axiom forall address safeAccount. ghostGuardianCount[safeAccount] == 0;
}
hook Sload uint256 value guardianStorageContract.entries[KEY address safeAccount].count {
    require ghostGuardianCount[safeAccount] == to_mathint(value);
}
hook Sstore guardianStorageContract.entries[KEY address safeAccount].count uint256 value {
    ghostGuardianCount[safeAccount] = value;
}

// Ghost variable to store the threshold of a Safe.
ghost mapping(address => mathint) ghostThreshold {
    init_state axiom forall address safeAccount. ghostThreshold[safeAccount] == 0;
}
hook Sload uint256 value guardianStorageContract.entries[KEY address safeAccount].threshold {
    require ghostThreshold[safeAccount] == to_mathint(value);
}
hook Sstore guardianStorageContract.entries[KEY address safeAccount].threshold uint256 value {
    ghostThreshold[safeAccount] = value;
}

// A summary function to check if a module is enabled in the Safe contract.
function safeIsModuleEnabled(address module) returns bool {
    return safeContract.isModuleEnabled(module);
}

// A summary function to check if an address is an owner in the Safe contract.
function safeIsOwner(address calledContractAddress, address owner) returns bool {
    assert calledContractAddress == safeContract; // This checks that the contract is Safe Smart Account.
    return safeContract.isOwner(owner);
}

// A setup function that requires Safe contract to enabled the Social Recovery Module.
function requireSocialRecoveryModuleEnabled() {
    require(safeContract.isModuleEnabled(currentContract));
}

// A helper function to verify that two addresses are not the same.
function notSameAddress(address a, address b) {
    require(a != b);
}

// This rule verifies that the addGuardianWithThreshold(...) works as expected.
rule addGuardianWorksAsExpected(env e, address guardian, uint256 threshold, address otherGuardian) {

    // This can be removed once linked list invariant is implemented.
    require ghostGuardianCount[safeContract] > 0 => ghostGuardians[safeContract][SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    notSameAddress(guardian, otherGuardian); // Should not be the same as the other guardian.

    bool otherWasGuardian = currentContract.isGuardian(safeContract, otherGuardian);

    currentContract.addGuardianWithThreshold(e, safeContract, guardian, threshold);

    assert safeContract.isModuleEnabled(currentContract); // Social Recovery Module should be enabled.
    assert e.msg.sender == safeContract; // Only Safe contract can call this function.
    assert currentContract.isGuardian(safeContract, guardian); // Check if the guardian is added.
    assert otherWasGuardian == currentContract.isGuardian(safeContract, otherGuardian); // Check if the other guardian is not affected.    
}

// This rule verifies that the guardian can always be added considering ideal conditions.
rule guardianCanAlwaysBeAdded(env e, address guardian, uint256 threshold, address otherGuardian) {

    requireSocialRecoveryModuleEnabled(); // Social Recovery Module should be enabled.

    require e.msg.value == 0; // No value should be sent.
    require threshold > 0; // Threshold should be greater than zero.
    require ghostGuardianCount[safeContract] < max_uint256; // To prevent overflow (Realistically can't reach).

    // This can be removed once linked list invariant is implemented.
    require ghostGuardianCount[safeContract] > 0 => ghostGuardians[safeContract][SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    // Probably can be made as a setup function based on if the below is repeated mostly.
    notSameAddress(guardian, 0); // Should not be a zero address.
    notSameAddress(guardian, SENTINEL()); // Should not be the SENTINEL address.
    notSameAddress(guardian, safeContract); // Should not be the Safe contract address.
    notSameAddress(guardian, otherGuardian); // Guardians should be unique.

    require !safeContract.isOwner(guardian); // The guardian should not be an owner of the Safe contract.
    require !currentContract.isGuardian(safeContract, guardian); // The guardian should not be already a guardian.

    // Threshold should be less than or equal to the number of guardians.
    require threshold < guardianStorageContract.getGuardiansCount(safeContract);

    bool otherWasGuardian = currentContract.isGuardian(safeContract, otherGuardian);

    require e.msg.sender == safeContract; // Only Safe contract can call this function.
    currentContract.addGuardianWithThreshold@withrevert(e, safeContract, guardian, threshold);
    bool isReverted = lastReverted; // Check if the transaction is reverted.

    assert !isReverted => currentContract.isGuardian(safeContract, guardian); // Check if the guardian is added.
    assert otherWasGuardian == currentContract.isGuardian(safeContract, otherGuardian); // Check if the other guardian is not affected.
}

// This rule verifies that the revokeGuardianWithThreshold(...) works as expected.
rule removeGuardiansWorksAsExpected(env e, address guardian, address prevGuardian, uint256 threshold) {

    address nextGuardian = ghostGuardians[safeContract][guardian];

    // This could be removed once linked list invariant is implemented.
    // <------------------------------------------------------------>
    require ghostGuardianCount[safeContract] > 0 => ghostGuardians[safeContract][SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.
    notSameAddress(guardian, prevGuardian); // Guardians should be unique.
    notSameAddress(guardian, nextGuardian);
    notSameAddress(prevGuardian, nextGuardian);
    // <------------------------------------------------------------>

    currentContract.revokeGuardianWithThreshold(e, safeContract, prevGuardian, guardian, threshold);

    // Check if the guardian is removed.
    assert safeContract.isModuleEnabled(currentContract); // Social Recovery Module should be enabled.
    assert e.msg.sender == safeContract; // Only Safe contract can call this function.
    assert !currentContract.isGuardian(safeContract, guardian); // Check if the guardian is removed.
    assert ghostGuardians[safeContract][prevGuardian] == nextGuardian; // Check if the linked list is updated.
}

// This rule verifies that the guardian can always be removed considering ideal conditions.
rule guardianCanAlwaysBeRemoved(env e, address guardian, address prevGuardian, uint256 threshold) {

    requireSocialRecoveryModuleEnabled(); // Social Recovery Module should be enabled.

    require e.msg.value == 0; // No value should be sent.

    // This can be removed once linked list invariant is implemented.
    require ghostGuardianCount[safeContract] > 0 => ghostGuardians[safeContract][SENTINEL()] != 0; // Sentinel should not be zero if there are guardians.

    address nextGuardian = ghostGuardians[safeContract][guardian];
    notSameAddress(prevGuardian, nextGuardian); // Guardians should be unique.

    require e.msg.sender == safeContract; // Only Safe contract can call this function.
    currentContract.revokeGuardianWithThreshold@withrevert(e, safeContract, prevGuardian, guardian, threshold);
    bool isReverted = lastReverted; // Check if the transaction is reverted.

    // Check if the guardian is removed.
    assert !isReverted =>
        ghostGuardians[safeContract][prevGuardian] == nextGuardian &&
        !currentContract.isGuardian(safeContract, guardian);
}
