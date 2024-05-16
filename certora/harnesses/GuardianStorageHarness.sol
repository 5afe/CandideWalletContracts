// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.12 <0.9.0;
import {GuardianStorage} from "../../contracts/modules/social_recovery/storage/GuardianStorage.sol";

contract GuardianStorageHarness is GuardianStorage {

    /**
     * @notice Gets the count of guaridans for a wallet based on the actual linked list.
     * @dev This is needed for FV to avoid cases where we have values which does not start with SENTINEL.
     * @param _wallet The target wallet.
     * @return count of guardians.
     */
    function countGuardians(address _wallet) public view returns (uint256 count) {
        GuardianStorageEntry storage entry = entries[_wallet];
        if (entry.count == 0 || entry.guardians[SENTINEL_GUARDIANS] == SENTINEL_GUARDIANS || entry.guardians[SENTINEL_GUARDIANS] == address(0)) {
            return 0;
        }

        address currentGuardian = entry.guardians[SENTINEL_GUARDIANS];
        while (currentGuardian != SENTINEL_GUARDIANS && currentGuardian != address(0)) {
            currentGuardian = entry.guardians[currentGuardian];
            count++;
        }
    }
}
