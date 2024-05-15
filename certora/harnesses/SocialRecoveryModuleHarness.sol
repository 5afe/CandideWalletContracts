// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.8.12 <0.9.0;
import {SocialRecoveryModule} from "../../contracts/modules/social_recovery/SocialRecoveryModule.sol";
import {IGuardianStorage} from "../../contracts/modules/social_recovery/storage/IGuardianStorage.sol";

contract SocialRecoveryModuleHarness is SocialRecoveryModule {
    constructor(IGuardianStorage _guardianStorage, uint256 _recoveryPeriod) SocialRecoveryModule(_guardianStorage, _recoveryPeriod) {}

    function encodeRecoveryDataHash(address _wallet, address[] calldata _newOwners, uint256 _newThreshold, uint256 _nonce) public view returns (bytes32) {
        return keccak256(encodeRecoveryData(_wallet, _newOwners, _newThreshold, _nonce));
    }
}
