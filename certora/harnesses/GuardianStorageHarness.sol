// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.12 <0.9.0;
import {GuardianStorage} from "../../contracts/modules/social_recovery/storage/GuardianStorage.sol";

contract GuardianStorageHarness is GuardianStorage {

    /**
     * @dev Gets the count of guaridans for a wallet.
     * @param _wallet The target wallet.
     * @return count of guardians.
     */
    function getGuardiansCount(address _wallet) public view returns (uint256 count) {
        GuardianStorageEntry storage entry = entries[_wallet];
        if (entry.count == 0 || entry.guardians[SENTINEL_GUARDIANS] == SENTINEL_GUARDIANS || entry.guardians[SENTINEL_GUARDIANS] == address(0)) {
            return 0;
        }

        address currentGuardian = entry.guardians[SENTINEL_GUARDIANS];
        while (currentGuardian != SENTINEL_GUARDIANS) {
            currentGuardian = entry.guardians[currentGuardian];
            count++;
        }
    }
}
