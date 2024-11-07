// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Script.sol";
import "../src/Halo2Verifier.sol";
import "../src/CryptoIdolArtExtra.sol";
import "../src/CryptoIdolArt.sol";
import "../src/CryptoIdol.sol";

contract DeployScript is Script {
    Halo2Verifier public civ;
    CryptoIdolArtExtra public ciae;
    CryptoIdolArt public cia;
    CryptoIdol public ci;

    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        vm.startBroadcast(deployerPrivateKey);

        // Deploy the dependent contracts
        civ = new Halo2Verifier();
        ciae = new CryptoIdolArtExtra();
        cia = new CryptoIdolArt(address(ciae));

        // Deploy the main contract with the necessary constructor parameters
        ci = new CryptoIdol(msg.sender, address(civ), address(cia));

        vm.stopBroadcast();
    }
}