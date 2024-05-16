// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.12 <0.9.0;
import {GuardianStorage} from "../../contracts/modules/social_recovery/storage/GuardianStorage.sol";

contract GuardianStorageHarness is GuardianStorage {

    /**
     * @notice Gets the count of guaridans for FV based on the linked list starting from SENTINEL (if any).
     * @dev This is needed for FV to avoid cases where we have values which does not start with SENTINEL.
     * @param _wallet The target wallet.
     * @return count of guardians.
     */
    function countGuardians(address _wallet) public view returns (uint256 count) {
        GuardianStorageEntry storage entry = entries[_wallet];
        address currentGuardian = entry.guardians[SENTINEL_GUARDIANS];

        // The sentinel guardian pointing to address 0 is the initial state for the
        // guardian storage entry for an account and is equivalent to an empty list
        // where the sentinel points to itself. We handle this special case here.
        if (currentGuardian == address(0)) {
            return 0;
        }

        while (currentGuardian != SENTINEL_GUARDIANS && currentGuardian != address(0)) {
            count++;
            currentGuardian = entry.guardians[currentGuardian];
        }
    }
}
