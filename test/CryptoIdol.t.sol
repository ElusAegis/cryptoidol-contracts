// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console2} from "forge-std/Test.sol";
import {CryptoIdol} from "../src/CryptoIdol.sol";
import {CryptoIdolVerifier} from "../src/CryptoIdolVerifier.sol";
import {LibString} from "solady/src/utils/LibString.sol";

abstract contract ERC721TokenReceiver {
    function onERC721Received(address, address, uint256, bytes calldata)
        external
        virtual
        returns (bytes4)
    {
        return ERC721TokenReceiver.onERC721Received.selector;
    }
}

contract CryptoIdolTest is Test, ERC721TokenReceiver {
    using LibString for uint256;

    CryptoIdol public ci;
    CryptoIdolVerifier public civ;

    function setUp() public {
        civ = new CryptoIdolVerifier();
        ci = new CryptoIdol(address(this), address(civ));
    }

    function testIfOwnerCanUpdateVerifier() public {
        CryptoIdolVerifier newCiv = new CryptoIdolVerifier();

        ci.updateVerifier(address(newCiv));

        assertEq(address(ci.verifier()), address(newCiv));

        ci.updateVerifier(address(civ));

        assertEq(address(ci.verifier()), address(civ));
    }

    function testFailIfNonOwnerCanUpdateVerifier() public {
        CryptoIdolVerifier newCiv = new CryptoIdolVerifier();
        vm.prank(address(1));
        ci.updateVerifier(address(newCiv));
    }

    function testFail_Mint() public {
        for (uint i=0; i < 10001; ++i) {
            string[] memory input_proof = new string[](3);
            input_proof[0] = "echo";
            input_proof[1] = "-n";
            input_proof[2] = "0x127dfd437c3bb2d7d35ce8eb6bdf58d8550cab28810fa73dd54a5732ec7f122028dd6d0e677375415a2372130a0ed642255d6c578c70613482da0bb72fbfe6f90754f8fc4b495f69a66e076b6dec4ce3cde78937cdce9807969281a294464c831b7fc0d92248fb651a9d00fcf74442aa79fbf143cc5d70a60007c9511ca0f4bc2dae61c30a70130f9a2fbd2a936b9aeca7b58c8f73a13fd349557d713c072e61198e07ee161d96b9cddf2442b9827549b6f71cc74fcd5bfbf9c5181a8816d4f506b7657bc4dd2f32911915d63ebfa27d2c5bcf85fceb33b1062d063980822d8811fec21411d75066ec8f408adfb0b251f4b63dc41507991f5f150581c125e7d41e9070dd0cddab9b22c2ab55d6faac3ca9b567a0858c30f22445341c442c89c213f028453b6c5c3ba35a858c05839fcbc7bfb28e3f1e53cb877358f99b541d360c0d425807e98223f1344eb0e532e65e691cb2141638295efd5c0b39bd53957a219dacde62c3cb3a5070a3c30f086bbb1428a8d1cd8c6ec1058b91bdec0958d40056bcff41f1086758e26e2f7759b321581088135d0f86b8284a2add79d4771818990631cea0c935b7df6ec1a3ea83f9eadc3472bfdd4333f5557884d1deb8031f700ee94ab45c69b53d27fbdf65e9672689f9a1b6b83a95fc34eb7d3bdcb3ad2667d1204a38a760d30eb0df2091eb5c0ba50e8e74272dff1cefa8465f983be30ecc0bc425e62729bd6946a9ae8ce8f79dd07ad78fcf8228678020239e2c73440a3d08000d2dbf55355be14fb8bb6cab7aff61d94a32bc7fbca5ca861c83b66514beb14674c1437a16e0f5ed1d10d1e9f42a0bff64b6142996629c9dc2d812411fa05f87b2d5608091841c6f73e2ec17748c821bbaadf13bb89199d38a01bc53091ad6627324f2471fc0caed422fd79f0412d21fef9ad9630a9adbd499b9d4680a4e12549f017415ebfba6491481221a9fa810576cb1247eebb8f9748bfd0b87062a40852126acd8f81da3610150c01519e0c9a045f695cd6ddcbe683342a8df0df45d855befa336e9d5df3dd7281f6568128fd426ac6c0eea033d1383478cbe0f96ba0ae59901cc6fa576d2978ec2587e0ccfac12a1962dd3863d8113a3f0bc2a969f292ec53f31a5aaebffc18c609ce6465cdc571bb45fcbacc1258c76b76f2becc2e8f9657338e9c719e23941ab2aff1f30df11c2d9aafff78b0271a977c01941cdcfa6018722be05bab66ccc60142290a8f5cb1bc345bf2d5beb49da296d0107a00bb05d9de265ecfd78a9a05e00d50e1f50ed29b4c19ac9387366b1dae016b74f5767b2726d2ffebbad313ceca912f1e8311dd58199e2092eba8b71e54f14e4552823be36e66f2fc89bbe6230980b5f1eaa09cbae3ee703daf2fb79853f2b930f15010c77656459d1099e0bcd6127ea97b52703c5ac6fbe40e8d1d6fe010892f8f64818ac1eda346ec074a92da946662cf54d233be24cd72f5fe5d9259b1f611aecca800cd02eaadf4154b7b959f3f674f2bd61defe4bb0b169db8f43172fe2e63be27503462d55b63a4c07c5a74110c9bc32228c0b7758cd875ec5506812de06231ee93cb389d215b9974306ba87d9afe4e0178eafd45826ba750ff4bb18eede46082a650f208765812bf109412c51b8bf405c22d259a81ccb01d22aec1c2137bd486cf26b08f0df56250c8f341d2b32045f24d89f687b4ae03f13c2220bec0fcb25e6493ab198bec3324c5cfaff65a97b58062cb23ed4157de2fa06a41430d178fb08e02ec967cd3276a0b9feead0484609f36f864489cb734c4763c2188535389cf1d7973e743c3bfa3c15003a377fbfe2338df7c0c91213a3b7e1f000b13aef81a47e0a5fcbb9226ba1fb9479d868ec807df4b157a7f9a55a50b4161e0983ace2552618828ad667ae2cac87b89cb7799611b9c8a4a3d1db83548554249914068bc8f8e27bb0f04efcdbf42e8d114e8ad2ec8b19dd6286c7d797bf1410b9ac7325ed3c2ddf275d261e0613df6f94d7bc9d52c442ec624687dd4751ea23117fe266123240fa0c1dbbe0f10363a23aa022db7e243e5ad07355037b05dd0cbf683cb0843d83602671a5596b18c586037e51cf71c5c591f18d1d70477c842ebdac4a2900d748f4c2caa934469b290f73c12630bcce8560608bcfcabe77662fc4930b39fa012ec4ea7bf5d664ca10926276406cb6c07da5964700b47ee8da109138d44716e2e95955398f7631250fd2f98a1ae8d00c0e8393e98e4ec79b27147a89df2cf2cdf465894bb5a3523193c05f253652fdaf3dabfbcad5f5454de814ee3f5cd7fdb704ad9155fb42faf91a8948beb4a3c5eeca55fc3618ab7fe14f0f51ddabb45271f29e851dd8dc72cc0c94156424c6d76ad513ed6e5dd34777511211139fef9b1ea614ce39d021d750bef7dac22d1d6b0754f1f75ca52b8a6337187d140566b7c148cc7fb2069f0a8d3f242dc2fa67c768c3472e952e8ef3b57806cb3df6e231d1d3a08179d98fe66c499fc57c2dadd4a793013cabed113936931be0d013d9e849ca312eff52b0fef9eb7af5baae2c9485e6d7ca10a66ee6c4bc20c8b437c8010f6e36c5578538014818e7f3d5e7bbb97285caa0e984fc11ca86039cb9601c35150c5089504c257ab2484c8a8acfe38413dc8d54e39556acf4861f8835c9a0b9ec3cd2a4ce528e6b6deeb12f83f2228d6389c51ec339d50f4b491a795366e41f85a96c1ad235dddf696ef76d2931c62ea328635e82710eccd6e030009094afb655930f5ab66dfdd3508bc420a87680053b4c89259ceda054166513bb4606024834918b2cfe95766cc1011cb0b3996f48fb10c52681ddf48608e9191ce73a95829fa043ebbe9fdf15f65569f7f089cb8f9b79544f4a70937018fc1b316e3fbf2d552cb3c86f82f986f47a5f82428172d62bc9060271341587c80b0f3715d5daa1557c6a191867f81ad777687dbc04203867525159b57779e5bb4411c9182a5fd229380d1be39284f2d2b52dc810b11e48b15b779ff2c95526478211c9182a5fd229380d1be39284f2d2b52dc810b11e48b15b779ff2c9552647820606274872e904514fae54c392fe05eebacb317cf21864c2145ef527e8fd9732000000000000000000000000000000000000000000000000000000000000000012a96346dc56bb373fa7a47481f2a555af7e698d7d5ee85e15b52a71eca6b52600000000000000000000000000000000000000000000000000000000000000000bfa5869e48bffb049af571b016c1d02f704867d529dc476b4a8bbbc9ba20cc700000000000000000000000000000000000000000000000000000000000000000c24b61b51e788fd16e52b7b36fa8900069d3ba1a8e0e33e0596f58c00adf8ea0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000025d1658b140c13094d36e2043cffa1ecb01445407f41e08940c939e939f1df221ceb995dc741d45436421b83f487762998685ae973395e1def8695bc3a7c48ac2f58ab52bbf23d07c1cf1d3b909349863231b8c18f4f1a792b641a2201c4e3cf1bb2e7cfaa9fa5283abf35c359d354d2029d4602f854b6fe66e709f3388d7c5504f9306478f85bf10ff9e6a871fa4f51b8323f545f1f928958487d5604da95d210695f710363a2a59725a9722f1f103797d7246a80c678a331f631a47f1a72982a47c24ea8c234baa3b8c92e0f90a9dc5108b6eae3ba4a7d9adbb6a407ea4813258218cc390dd445f73f6f7a9b96736e822c17795ccb861d832411e3f82a25dc2c35757e458af546c0e40729b98c3944281c93e57aa62c956a52b0a6a16ac21716e3399f5a595d209b93e5c1162124ceac81a5a942ec6dec634f1e405e45163e294978424c55f3e4d5ee1ba358c696c9bb9b3f41c1946c9c5ff4c0abcc9737f2304a39194bed1832f1cc0dd16dcd22a4a2836210ea919c791ae94e54491aa71b1f5915894a0532f5b967dd6803305046132c1464d9e470bfa762d3936d1afa1f0a53212fa32a08f3a16eddafb21f28d3fa5c68de79f77a5ea9f799def83052e20ebc04c55bf570740e73c7c9ad206969805dc775cf7f3b96c99751584b42ae3c2d031c2cf234e97c7edf4f3f5157a667230ca90efb584ce2a8064e6a3332833e291778011ed24a0aa5f9e39385551ed11e2fbd0eabcd9e586fbdab257d3ed08314c2135bba6a4ec65f4fe10f1fc53491d6915f24d2055c50ea81443bc3fed5f305eb69043695a255579709151c3c3b30a4e54512fa86584ea67b1150eb78fda92c3bb6c632d1da59421a4c7b311a4a26772453f1ec28a665a42ce7e337388665211dac05d94326b6dc0584a56406d982b227239e658d46ace8e76d2cb0fd1f062c1e2c120013147ebac78abea1da376cd631770b64f408756ef2405b9085c97612b21293158d932736155f6571406a67ec40d37f1df1d6453a47a8ddc95cda142a5dab6e640d4f51a1c4cb6e611219e39c4634cf9f2f9fe4f489bc343bdcfc930d78692d9b0cf97a807ef94d215c9d567c777da38447659632fcf77fbbcb4c0e259d0627925082f0c358fc9ed4d87ea06ba4cfae2b0bfdc1b7826cabc10bb52e20f62739e2aaaecec94c2e6fe064f9ff0b83bfb3e5961250dd776409d516edae0059d67bafe367e3070fe0002b5a481071e6b7461fe00b8b7d0964221c484df90ed20e230a92a5f8ea3d133c6407b2ffa849454190273285ff38710c2523bb3e2ec7bbdd8c9e54275e5a7c9430c331e5d57a29d0a1fa02f3793217aa8ddb83170ab47acace7677455e8f72bd15248a16e26502d8c0da6ad7180bb8de7f66c5b02eeeb1097a82e1d589a98c740ddfac10b6423b9acf895ab81694d52f62915e462f135791804a8f1f4a305a044d62bd8429c74fa722e18b60353fdb06934a611e254c61d9caab50a63ba42107f19b2dbd903037b9deacd4945977e20ac1eef403149f7e597115482c1d37dd83af3f9feb33a2d86823363939a0aca5692d1609060b27b448e1ef414237cd8aba666d788b5cdb8ad8fb3ecc6f578aaa56838a83290de347ba95ab6dc2109e5897a330d135a458a79a73dd1474a17cb8931b4a72b608c22aaf9feb20877a2c9274eb13d96912be4d9b5743ea1cdb7ded77480a116c2f1dd0809bb923f32fab5b669653ca536dbd7a6053ba6fbb362d28a149adc424";

            bytes memory proof = vm.ffi(input_proof);
            // bytes memory proof = abi.decode(res_proof, (bytes));

            string[] memory input_instance_0 = new string[](3);
            input_instance_0[0] = "echo";
            input_instance_0[1] = "-n";
            input_instance_0[2] = "0x1d4fe12616b87b7b24900ea142a0147c94d7d19dd4617e37c84316b40faf2b44";

            bytes memory res_instance_0 = vm.ffi(input_instance_0);
            uint256 instance_0 = abi.decode(res_instance_0, (uint256));

            string[] memory input_instance_1 = new string[](3);
            input_instance_1[0] = "echo";
            input_instance_1[1] = "-n";
            input_instance_1[2] = "0x0000000000000000000000000000000000000000000000000000000000000023";

            bytes memory res_instance_1 = vm.ffi(input_instance_1);
            uint256 instance_1 = abi.decode(res_instance_1, (uint256));

            uint256[] memory instances = new uint256[](2);
            instances[0] = instance_0;
            instances[1] = instance_1;
            ci.mint(
                proof,
                instances
            );
            assertEq(ci.balanceOf(address(this)), i+1);

            // output metadata into file
            string memory metadata_output = ci.tokenURI(i+1);
            vm.writeJson(metadata_output, string(abi.encodePacked("./test/metadata", (i+1).toString())));
        }
    }
}
