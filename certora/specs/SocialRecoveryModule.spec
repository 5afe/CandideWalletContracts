using SafeHarness as safeContract;

methods {
    // Safe Functions
    function safeContract.isModuleEnabled(address) external returns (bool) envfree;
    function safeContract.disableModule(address, address) external;
}

// A setup function that requires Safe contract to enabled the Social Recovery
// Module.
function setupRequireRecoveryModule() {
    require(safeContract.isModuleEnabled(currentContract));
}

// This is a dummy rule to verify the Safe Contract Setup with the Social Recovery
// Module is working as intended.
rule recoveryModuleCanBeDisabled {
    env e;
    address prevModule;

    setupRequireSafeTokenInvariants();

    safeContract.disableModule@withrevert(e, prevModule, currentContract);
    bool isReverted = lastReverted;

    assert isReverted || (!isReverted && !safeContract.isModuleEnabled(currentContract));
}
