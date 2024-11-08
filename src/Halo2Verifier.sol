// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    DELTA = 4131629893567559867359510883348571134090853742863529169391034518566172092834;
    uint256 internal constant        R = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant    PROOF_LEN_CPTR = 0x6014f51944;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x10c4;
    uint256 internal constant     INSTANCE_CPTR = 0x10e4;

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x06e4;
    uint256 internal constant  LAST_QUOTIENT_X_CPTR = 0x07a4;

    uint256 internal constant                VK_MPTR = 0x05a0;
    uint256 internal constant         VK_DIGEST_MPTR = 0x05a0;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x05c0;
    uint256 internal constant                 K_MPTR = 0x05e0;
    uint256 internal constant             N_INV_MPTR = 0x0600;
    uint256 internal constant             OMEGA_MPTR = 0x0620;
    uint256 internal constant         OMEGA_INV_MPTR = 0x0640;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x0660;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x0680;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x06a0;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x06c0;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x06e0;
    uint256 internal constant              G1_X_MPTR = 0x0700;
    uint256 internal constant              G1_Y_MPTR = 0x0720;
    uint256 internal constant            G2_X_1_MPTR = 0x0740;
    uint256 internal constant            G2_X_2_MPTR = 0x0760;
    uint256 internal constant            G2_Y_1_MPTR = 0x0780;
    uint256 internal constant            G2_Y_2_MPTR = 0x07a0;
    uint256 internal constant      NEG_S_G2_X_1_MPTR = 0x07c0;
    uint256 internal constant      NEG_S_G2_X_2_MPTR = 0x07e0;
    uint256 internal constant      NEG_S_G2_Y_1_MPTR = 0x0800;
    uint256 internal constant      NEG_S_G2_Y_2_MPTR = 0x0820;

    uint256 internal constant CHALLENGE_MPTR = 0x0f00;

    uint256 internal constant THETA_MPTR = 0x0f00;
    uint256 internal constant  BETA_MPTR = 0x0f20;
    uint256 internal constant GAMMA_MPTR = 0x0f40;
    uint256 internal constant     Y_MPTR = 0x0f60;
    uint256 internal constant     X_MPTR = 0x0f80;
    uint256 internal constant  ZETA_MPTR = 0x0fa0;
    uint256 internal constant    NU_MPTR = 0x0fc0;
    uint256 internal constant    MU_MPTR = 0x0fe0;

    uint256 internal constant       ACC_LHS_X_MPTR = 0x1000;
    uint256 internal constant       ACC_LHS_Y_MPTR = 0x1020;
    uint256 internal constant       ACC_RHS_X_MPTR = 0x1040;
    uint256 internal constant       ACC_RHS_Y_MPTR = 0x1060;
    uint256 internal constant             X_N_MPTR = 0x1080;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x10a0;
    uint256 internal constant          L_LAST_MPTR = 0x10c0;
    uint256 internal constant         L_BLIND_MPTR = 0x10e0;
    uint256 internal constant             L_0_MPTR = 0x1100;
    uint256 internal constant   INSTANCE_EVAL_MPTR = 0x1120;
    uint256 internal constant   QUOTIENT_EVAL_MPTR = 0x1140;
    uint256 internal constant      QUOTIENT_X_MPTR = 0x1160;
    uint256 internal constant      QUOTIENT_Y_MPTR = 0x1180;
    uint256 internal constant          R_EVAL_MPTR = 0x11a0;
    uint256 internal constant   PAIRING_LHS_X_MPTR = 0x11c0;
    uint256 internal constant   PAIRING_LHS_Y_MPTR = 0x11e0;
    uint256 internal constant   PAIRING_RHS_X_MPTR = 0x1200;
    uint256 internal constant   PAIRING_RHS_Y_MPTR = 0x1220;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(ret0, eq(mulmod(y, y, q), addmod(mulmod(x, mulmod(x, x, q), q), 3, q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), R)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), R)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(R, 2))
                mstore(add(gp_mptr, 0xa0), R)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), R)
                    all_inv := mulmod(all_inv, mload(mptr), R)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), R)
                let inv_second := mulmod(all_inv, mload(first_mptr), R)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let q := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true

            {
                // Load vk_digest and num_instances of vk into memory
                mstore(0x05a0, 0x29a5a4a2b4a90e246e5fedbdc909d47c3cfccdbe18e0e25852268854dfd0facf) // vk_digest
                mstore(0x05c0, 0x0000000000000000000000000000000000000000000000000000000000000002) // num_instances

                // Check valid length of proof
                success := and(success, eq(0x1060, calldataload(sub(PROOF_LEN_CPTR, 0x6014F51900))))

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(success, eq(num_instances, calldataload(NUM_INSTANCE_CPTR)))

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := INSTANCE_CPTR
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0180) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 2
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0200) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 3
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0300) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 4
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0100) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0860) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W'

                // Load full vk into memory
                mstore(0x05a0, 0x29a5a4a2b4a90e246e5fedbdc909d47c3cfccdbe18e0e25852268854dfd0facf) // vk_digest
                mstore(0x05c0, 0x0000000000000000000000000000000000000000000000000000000000000002) // num_instances
                mstore(0x05e0, 0x0000000000000000000000000000000000000000000000000000000000000010) // k
                mstore(0x0600, 0x30641e0e92bebef818268d663bcad6dbcfd6c0149170f6d7d350b1b1fa6c1001) // n_inv
                mstore(0x0620, 0x09d2cc4b5782fbe923e49ace3f647643a5f5d8fb89091c3ababd582133584b29) // omega
                mstore(0x0640, 0x0cf312e84f2456134e812826473d3dfb577b2bfdba762aba88b47b740472c1f0) // omega_inv
                mstore(0x0660, 0x17cbd779ed6ea1b8e9dbcde0345b2cfdb96e80bea0dd1318bdd0e183a00e0492) // omega_inv_to_l
                mstore(0x0680, 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
                mstore(0x06a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
                mstore(0x06c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
                mstore(0x06e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
                mstore(0x0700, 0x0000000000000000000000000000000000000000000000000000000000000001) // g1_x
                mstore(0x0720, 0x0000000000000000000000000000000000000000000000000000000000000002) // g1_y
                mstore(0x0740, 0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2) // g2_x_1
                mstore(0x0760, 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed) // g2_x_2
                mstore(0x0780, 0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b) // g2_y_1
                mstore(0x07a0, 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa) // g2_y_2
                mstore(0x07c0, 0x186282957db913abd99f91db59fe69922e95040603ef44c0bd7aa3adeef8f5ac) // neg_s_g2_x_1
                mstore(0x07e0, 0x17944351223333f260ddc3b4af45191b856689eda9eab5cbcddbbe570ce860d2) // neg_s_g2_x_2
                mstore(0x0800, 0x06d971ff4a7467c3ec596ed6efc674572e32fd6f52b721f97e35b0b3d3546753) // neg_s_g2_y_1
                mstore(0x0820, 0x06ecdb9f9567f59ed2eee36e1e1d58797fd13cc97fafc2910f5e8a12f202fa9a) // neg_s_g2_y_2
                mstore(0x0840, 0x106303446da9f807d3cc3339385698d123bde847fd70a4d9c3c0d39fe2d5e315) // fixed_comms[0].x
                mstore(0x0860, 0x25eebdf9508bf52a38e4c3684c24c71711b51b874862a99076d3beaade956519) // fixed_comms[0].y
                mstore(0x0880, 0x1794feaff99b6d4a566333348233c04e516b2c24c92b8b2a39c274e71cc81abf) // fixed_comms[1].x
                mstore(0x08a0, 0x01543b5f89244bec18a7505701f9ad300465a7d991190364bb375f0fd3a944db) // fixed_comms[1].y
                mstore(0x08c0, 0x0fb3e0d1e40d37c43a32fceb9b31f10e27288643f9b17d2d8cc253f9a6b29223) // fixed_comms[2].x
                mstore(0x08e0, 0x03290e169a6c14d21cfd99a6e43fb9d0b8f3c1499f64ec3b23372634e86d8065) // fixed_comms[2].y
                mstore(0x0900, 0x2f267281e14a4ae7a64b3ec823db833b830e658dc7a1980dcb573096866415a1) // fixed_comms[3].x
                mstore(0x0920, 0x041955dd85a674b06fbcfcb6df6722bee5f2dd160934002eb21680f3bbedac08) // fixed_comms[3].y
                mstore(0x0940, 0x14d22c42945531bb6095376236bd181afc764da73efc5ba6eb6ac2e12903424d) // fixed_comms[4].x
                mstore(0x0960, 0x1ce90b4ab53ce94a0fdcefd2ba3792c4b709b8f3eba529fc653718ebbb41356a) // fixed_comms[4].y
                mstore(0x0980, 0x0dbae6d5df1891a57d646ab2c79653c7b1c0274127be23afbf7f0b653b8495d8) // fixed_comms[5].x
                mstore(0x09a0, 0x0647bb7689eac2e471002797bcd99b454f0699a77c51d60796e283af7e431310) // fixed_comms[5].y
                mstore(0x09c0, 0x18d7951a134d7003f7ae07094ffc69abe15d171c14e0c984ffc2d19bed1407e9) // fixed_comms[6].x
                mstore(0x09e0, 0x0834c45f90f90a9aff9cdbc41965636cf992186c2e9a853136222bfbe78d7b26) // fixed_comms[6].y
                mstore(0x0a00, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[7].x
                mstore(0x0a20, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[7].y
                mstore(0x0a40, 0x14accff334dc63ff9a47c81066d8fc2a614e22e1e1a965b1a0fb1d5dc4e52474) // fixed_comms[8].x
                mstore(0x0a60, 0x29baf2b82aa354615be8081bc1bfcc72b3b4d99fdbcac13873387d94c08e35e2) // fixed_comms[8].y
                mstore(0x0a80, 0x01e2da9388abbc41798ecf31e626d4ac8f298c44131bf5d85814b64a7c183bca) // fixed_comms[9].x
                mstore(0x0aa0, 0x00d37b34d60d6ce8aa3db875f8f6d4802da40a680e65abbfc28ca2245c16e729) // fixed_comms[9].y
                mstore(0x0ac0, 0x15187e5f8eae2603ce6882771d0bc6fab61f6857906a4456922801a47a46ead4) // fixed_comms[10].x
                mstore(0x0ae0, 0x1d03f794d794f4970434981f11161f00002662f0fbf0b44d01dfd4ae363e14ac) // fixed_comms[10].y
                mstore(0x0b00, 0x22ff86755b063f3d619d82277802a4b09dfc38b7519902d821c6265b26430ed5) // fixed_comms[11].x
                mstore(0x0b20, 0x1a91f2d9c1e59f7eff09539547dfcf22652b4665b926230386c55555e6220ffd) // fixed_comms[11].y
                mstore(0x0b40, 0x03f52266619556074eb4a5845e8394d45f0f340ed7f6a0522e7fdd60f8552798) // fixed_comms[12].x
                mstore(0x0b60, 0x29effdfd1a47ab6e993a107866c8fe25cc9d57b9166d757bcfde72cb7f58cb32) // fixed_comms[12].y
                mstore(0x0b80, 0x203f9f9a24c961e9570e5c61426f56daa8082c5983aecae2c0c956f6b9fdacf2) // fixed_comms[13].x
                mstore(0x0ba0, 0x24bdf89385ccdfbea5b7719b7450abd599d69eddeed629753ffc1bb5ffe7dfab) // fixed_comms[13].y
                mstore(0x0bc0, 0x20be61d9288cb88de2fbb929beb5aec54595183f8d0c484e1b6338b150b3ff1d) // fixed_comms[14].x
                mstore(0x0be0, 0x272457b25421078415bd0c4f1e7ef87f2ab8a34ee59aabd9f557ac235d725b95) // fixed_comms[14].y
                mstore(0x0c00, 0x0084d33f1e65bfc58809c72f0983c412738f44aef2b4b8579c99b1f294ba0610) // fixed_comms[15].x
                mstore(0x0c20, 0x0522c986ee971223e2b4b2b5f311b5f849190a603477d1dd37b1ecf8dc3e1ff6) // fixed_comms[15].y
                mstore(0x0c40, 0x081c40d86decd6f1a9d6b086d58580365a739eee18ef6e6d866b7370ee5124da) // fixed_comms[16].x
                mstore(0x0c60, 0x1cd469715be0a8683f1a7f78a63a31c9dfea5b15100ceca536c3c6d6604f9f32) // fixed_comms[16].y
                mstore(0x0c80, 0x25eba9f24778dcaac5046bf4a173bce97b890be288a7e578002e9c47baf3b016) // fixed_comms[17].x
                mstore(0x0ca0, 0x1d63928545fc91679043257ac222772541379a9c66e2b00b0dd8fe2236d29ae4) // fixed_comms[17].y
                mstore(0x0cc0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].x
                mstore(0x0ce0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].y
                mstore(0x0d00, 0x10f2edff6ab5ed283ed0aa91d79dac8af06419dc93d21a8a3891597f0fa6d8fb) // permutation_comms[0].x
                mstore(0x0d20, 0x1f842f90f5e8bb59b3fa142d1cc1c2f1fb62a441fb33642dfaeeaaaa4e80431f) // permutation_comms[0].y
                mstore(0x0d40, 0x2bc79e8071ebb44d102652ed4fe7040bbe5a4e303c33c97882d6945e6cc01fc7) // permutation_comms[1].x
                mstore(0x0d60, 0x11fd88d1759859d21474cc6e04aebf8d54fc1ccaac3daafa8f90b41cab948dba) // permutation_comms[1].y
                mstore(0x0d80, 0x28eeb393c776888bdacd0e395963df1fbbca616966ff7fb585aae8964f392c4d) // permutation_comms[2].x
                mstore(0x0da0, 0x0b2e6b4cc214e1fc14d963d19c2aae6f1ca4636454f328db7d797f41150d3cd5) // permutation_comms[2].y
                mstore(0x0dc0, 0x08ff208ce75f20a2baf5beb4d9d5e10ab2c2cf3c0771253f133e14ca88e926d3) // permutation_comms[3].x
                mstore(0x0de0, 0x1b8f6a10307c635176140edc54d762d231012a9adc47aa2fa10773bf5cdc4418) // permutation_comms[3].y
                mstore(0x0e00, 0x053df50e334245fe129e72c33759f544c9a76181d3175e3a4c6d5db37a850c0f) // permutation_comms[4].x
                mstore(0x0e20, 0x14334ad9a8aecec64dfeaf1d7153a3520df420811557b12864390b71f8b1073b) // permutation_comms[4].y
                mstore(0x0e40, 0x024946f54b95d6021027462e6684c15a49d9d864d115d4c1def433fa16d90f81) // permutation_comms[5].x
                mstore(0x0e60, 0x12757c2ebae1f4aa58567bda07230a31832c6bf3426adc8aa8c5ca25a9776153) // permutation_comms[5].y
                mstore(0x0e80, 0x12ae23ff5be8e67f64ea5389b14fd051794b7627cde52236e1183f7f5fc09cef) // permutation_comms[6].x
                mstore(0x0ea0, 0x15e461c01bed1973ab24f856a7d10de95505111ee0d3f32eda65ecdac4bf8662) // permutation_comms[6].y
                mstore(0x0ec0, 0x03a424e43332aea704bd29c2a27e084b8402e4ad7ecd8a92a129786abd26d524) // permutation_comms[7].x
                mstore(0x0ee0, 0x02f0f2a16db80b3b559e0700aba13d8c8a134995574c8a23ccf1cedebd4495d2) // permutation_comms[7].y

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(INSTANCE_CPTR, mul(mload(ACC_OFFSET_MPTR), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, eq(mulmod(lhs_y, lhs_y, q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q), 3, q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q), 3, q)))

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6)))
                if iszero(mload(NUM_INSTANCES_MPTR)) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20))

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for
                    { let l_i_cptr_end := add(X_N_MPTR, 0xc0) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := 0
                for
                    {
                        let instance_cptr := INSTANCE_CPTR
                        let instance_cptr_end := add(instance_cptr, mul(0x20, mload(NUM_INSTANCES_MPTR)))
                    }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let y := mload(Y_MPTR)
                {
                    let f_14 := calldataload(0x0a84)
                    let var0 := 0x2
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let a_0 := calldataload(0x07e4)
                    let a_2 := calldataload(0x0824)
                    let var7 := addmod(a_0, a_2, R)
                    let var8 := sub(R, var7)
                    let var9 := addmod(a_4, var8, R)
                    let var10 := mulmod(var6, var9, R)
                    quotient_eval_numer := var10
                }
                {
                    let f_15 := calldataload(0x0aa4)
                    let var0 := 0x1
                    let var1 := sub(R, f_15)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_15, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_5 := calldataload(0x0884)
                    let a_1 := calldataload(0x0804)
                    let a_3 := calldataload(0x0844)
                    let var7 := addmod(a_1, a_3, R)
                    let var8 := sub(R, var7)
                    let var9 := addmod(a_5, var8, R)
                    let var10 := mulmod(var6, var9, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_14 := calldataload(0x0a84)
                    let var0 := 0x1
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let a_0 := calldataload(0x07e4)
                    let a_2 := calldataload(0x0824)
                    let var7 := mulmod(a_0, a_2, R)
                    let var8 := sub(R, var7)
                    let var9 := addmod(a_4, var8, R)
                    let var10 := mulmod(var6, var9, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_16 := calldataload(0x0ac4)
                    let var0 := 0x2
                    let var1 := sub(R, f_16)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_16, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_5 := calldataload(0x0884)
                    let a_1 := calldataload(0x0804)
                    let a_3 := calldataload(0x0844)
                    let var7 := mulmod(a_1, a_3, R)
                    let var8 := sub(R, var7)
                    let var9 := addmod(a_5, var8, R)
                    let var10 := mulmod(var6, var9, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_14 := calldataload(0x0a84)
                    let var0 := 0x1
                    let var1 := sub(R, f_14)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_14, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let a_0 := calldataload(0x07e4)
                    let a_2 := calldataload(0x0824)
                    let var7 := sub(R, a_2)
                    let var8 := addmod(a_0, var7, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_4, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_15 := calldataload(0x0aa4)
                    let var0 := 0x1
                    let var1 := sub(R, f_15)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_15, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_5 := calldataload(0x0884)
                    let a_1 := calldataload(0x0804)
                    let a_3 := calldataload(0x0844)
                    let var7 := sub(R, a_3)
                    let var8 := addmod(a_1, var7, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_5, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_15 := calldataload(0x0aa4)
                    let var0 := 0x2
                    let var1 := sub(R, f_15)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_15, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let var7 := 0x1
                    let var8 := sub(R, var7)
                    let var9 := addmod(a_4, var8, R)
                    let var10 := mulmod(a_4, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_16 := calldataload(0x0ac4)
                    let var0 := 0x1
                    let var1 := sub(R, f_16)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_16, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_5 := calldataload(0x0884)
                    let var7 := sub(R, var0)
                    let var8 := addmod(a_5, var7, R)
                    let var9 := mulmod(a_5, var8, R)
                    let var10 := mulmod(var6, var9, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var10, r)
                }
                {
                    let f_17 := calldataload(0x0ae4)
                    let var0 := 0x2
                    let var1 := sub(R, f_17)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_17, var2, R)
                    let a_4 := calldataload(0x0864)
                    let a_4_prev_1 := calldataload(0x08a4)
                    let var4 := 0x0
                    let a_0 := calldataload(0x07e4)
                    let a_2 := calldataload(0x0824)
                    let var5 := mulmod(a_0, a_2, R)
                    let var6 := addmod(var4, var5, R)
                    let a_1 := calldataload(0x0804)
                    let a_3 := calldataload(0x0844)
                    let var7 := mulmod(a_1, a_3, R)
                    let var8 := addmod(var6, var7, R)
                    let var9 := addmod(a_4_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(var3, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_16 := calldataload(0x0ac4)
                    let var0 := 0x1
                    let var1 := sub(R, f_16)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_16, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let var7 := 0x0
                    let a_0 := calldataload(0x07e4)
                    let a_2 := calldataload(0x0824)
                    let var8 := mulmod(a_0, a_2, R)
                    let var9 := addmod(var7, var8, R)
                    let a_1 := calldataload(0x0804)
                    let a_3 := calldataload(0x0844)
                    let var10 := mulmod(a_1, a_3, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_4, var12, R)
                    let var14 := mulmod(var6, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_18 := calldataload(0x0b04)
                    let var0 := 0x2
                    let var1 := sub(R, f_18)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_18, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let var7 := 0x1
                    let a_2 := calldataload(0x0824)
                    let var8 := mulmod(var7, a_2, R)
                    let a_3 := calldataload(0x0844)
                    let var9 := mulmod(var8, a_3, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_17 := calldataload(0x0ae4)
                    let var0 := 0x1
                    let var1 := sub(R, f_17)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_17, var2, R)
                    let a_4 := calldataload(0x0864)
                    let a_4_prev_1 := calldataload(0x08a4)
                    let a_2 := calldataload(0x0824)
                    let var4 := mulmod(var0, a_2, R)
                    let a_3 := calldataload(0x0844)
                    let var5 := mulmod(var4, a_3, R)
                    let var6 := mulmod(a_4_prev_1, var5, R)
                    let var7 := sub(R, var6)
                    let var8 := addmod(a_4, var7, R)
                    let var9 := mulmod(var3, var8, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var9, r)
                }
                {
                    let f_18 := calldataload(0x0b04)
                    let var0 := 0x1
                    let var1 := sub(R, f_18)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_18, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let var7 := 0x0
                    let a_2 := calldataload(0x0824)
                    let var8 := addmod(var7, a_2, R)
                    let a_3 := calldataload(0x0844)
                    let var9 := addmod(var8, a_3, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_18 := calldataload(0x0b04)
                    let var0 := 0x1
                    let var1 := sub(R, f_18)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_18, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_4 := calldataload(0x0864)
                    let a_4_prev_1 := calldataload(0x08a4)
                    let var7 := 0x0
                    let a_2 := calldataload(0x0824)
                    let var8 := addmod(var7, a_2, R)
                    let a_3 := calldataload(0x0844)
                    let var9 := addmod(var8, a_3, R)
                    let var10 := addmod(a_4_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_4, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(l_0, sub(R, mulmod(l_0, calldataload(0x0c44), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let perm_z_last := calldataload(0x0d04)
                    let eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(perm_z_last, perm_z_last, R), sub(R, perm_z_last), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x0ca4), sub(R, calldataload(0x0c84)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x0d04), sub(R, calldataload(0x0ce4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0c64)
                    let rhs := calldataload(0x0c44)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x07e4), mulmod(beta, calldataload(0x0b44), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0804), mulmod(beta, calldataload(0x0b64), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0824), mulmod(beta, calldataload(0x0b84), R), R), gamma, R), R)
                    mstore(0x00, mulmod(beta, mload(X_MPTR), R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x07e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0804), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0824), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0cc4)
                    let rhs := calldataload(0x0ca4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0844), mulmod(beta, calldataload(0x0ba4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0864), mulmod(beta, calldataload(0x0bc4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0884), mulmod(beta, calldataload(0x0be4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0844), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0864), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0884), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x0d24)
                    let rhs := calldataload(0x0d04)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x08c4), mulmod(beta, calldataload(0x0c04), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mulmod(beta, calldataload(0x0c24), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x08c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), R), gamma, R), R)
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0d44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0d44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x08e4)
                        let f_2 := calldataload(0x0904)
                        table := f_1
                        table := addmod(mulmod(table, theta, R), f_2, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_6 := calldataload(0x0984)
                        let var0 := 0x1
                        let var1 := mulmod(f_6, var0, R)
                        let a_0 := calldataload(0x07e4)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593efffe95d
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        let a_4 := calldataload(0x0864)
                        let var8 := mulmod(var1, a_4, R)
                        let var9 := 0xa91
                        let var10 := mulmod(var4, var9, R)
                        let var11 := addmod(var8, var10, R)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, R), var11, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0d84), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0d64), sub(R, calldataload(0x0d44)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0da4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0da4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x08e4)
                        let f_2 := calldataload(0x0904)
                        table := f_1
                        table := addmod(mulmod(table, theta, R), f_2, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_7 := calldataload(0x09a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_7, var0, R)
                        let a_1 := calldataload(0x0804)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593efffe95d
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        let a_5 := calldataload(0x0884)
                        let var8 := mulmod(var1, a_5, R)
                        let var9 := 0xa91
                        let var10 := mulmod(var4, var9, R)
                        let var11 := addmod(var8, var10, R)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, R), var11, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0de4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0dc4), sub(R, calldataload(0x0da4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0e04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0e04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_3 := calldataload(0x0924)
                        table := f_3
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_8 := calldataload(0x09c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_8, var0, R)
                        let a_0 := calldataload(0x07e4)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0e44), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0e24), sub(R, calldataload(0x0e04)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0e64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0e64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_3 := calldataload(0x0924)
                        table := f_3
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_9 := calldataload(0x09e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_9, var0, R)
                        let a_1 := calldataload(0x0804)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0ea4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0e84), sub(R, calldataload(0x0e64)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0ec4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0ec4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_4 := calldataload(0x0944)
                        table := f_4
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_10 := calldataload(0x0a04)
                        let var0 := 0x1
                        let var1 := mulmod(f_10, var0, R)
                        let a_0 := calldataload(0x07e4)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff001
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0f04), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0ee4), sub(R, calldataload(0x0ec4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0f24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0f24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_4 := calldataload(0x0944)
                        table := f_4
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_11 := calldataload(0x0a24)
                        let var0 := 0x1
                        let var1 := mulmod(f_11, var0, R)
                        let a_1 := calldataload(0x0804)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff001
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0f64), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0f44), sub(R, calldataload(0x0f24)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0f84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0f84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_5 := calldataload(0x0964)
                        table := f_5
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_12 := calldataload(0x0a44)
                        let var0 := 0x1
                        let var1 := mulmod(f_12, var0, R)
                        let a_0 := calldataload(0x07e4)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x0fc4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x0fa4), sub(R, calldataload(0x0f84)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x0fe4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x0fe4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_5 := calldataload(0x0964)
                        table := f_5
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_13 := calldataload(0x0a64)
                        let var0 := 0x1
                        let var1 := mulmod(f_13, var0, R)
                        let a_1 := calldataload(0x0804)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x1024), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x1004), sub(R, calldataload(0x0fe4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }

                pop(y)

                let quotient_eval := mulmod(quotient_eval_numer, mload(X_N_MINUS_1_INV_MPTR), r)
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for
                    {
                        let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                        let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, R)
                    mstore(0x0360, x_pow_of_omega)
                    mstore(0x0340, x)
                    x_pow_of_omega := mulmod(x, omega_inv, R)
                    mstore(0x0320, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    mstore(0x0300, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for
                        {
                            let mptr := 0x0380
                            let mptr_end := 0x0400
                            let point_mptr := 0x0300
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(R, mload(point_mptr)), R))
                    }
                    let s
                    s := mload(0x03c0)
                    mstore(0x0400, s)
                    let diff
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), R)
                    diff := mulmod(diff, mload(0x03e0), R)
                    mstore(0x0420, diff)
                    mstore(0x00, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03e0), R)
                    mstore(0x0440, diff)
                    diff := mload(0x03a0)
                    mstore(0x0460, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), R)
                    mstore(0x0480, diff)
                }
                {
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0x20, coeff)
                }
                {
                    let point_1 := mload(0x0320)
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := addmod(point_1, sub(R, point_2), R)
                    coeff := mulmod(coeff, mload(0x03a0), R)
                    mstore(0x40, coeff)
                    coeff := addmod(point_2, sub(R, point_1), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0x60, coeff)
                }
                {
                    let point_0 := mload(0x0300)
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_0, sub(R, point_2), R)
                    coeff := mulmod(coeff, addmod(point_0, sub(R, point_3), R), R)
                    coeff := mulmod(coeff, mload(0x0380), R)
                    mstore(0x80, coeff)
                    coeff := addmod(point_2, sub(R, point_0), R)
                    coeff := mulmod(coeff, addmod(point_2, sub(R, point_3), R), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_3, sub(R, point_0), R)
                    coeff := mulmod(coeff, addmod(point_3, sub(R, point_2), R), R)
                    coeff := mulmod(coeff, mload(0x03e0), R)
                    mstore(0xc0, coeff)
                }
                {
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_2, sub(R, point_3), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0xe0, coeff)
                    coeff := addmod(point_3, sub(R, point_2), R)
                    coeff := mulmod(coeff, mload(0x03e0), R)
                    mstore(0x0100, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0120)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0420, diff_0_inv)
                    for
                        {
                            let mptr := 0x0440
                            let mptr_end := 0x04a0
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, R))
                    }
                }
                {
                    let coeff := mload(0x20)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0b24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), R), R)
                    for
                        {
                            let mptr := 0x0c24
                            let mptr_end := 0x0b24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    for
                        {
                            let mptr := 0x0b04
                            let mptr_end := 0x08a4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1024), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0fc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0f64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0f04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0ea4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0e44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0de4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0d84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0884), R), R)
                    for
                        {
                            let mptr := 0x0844
                            let mptr_end := 0x07c4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    mstore(0x04a0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x08a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x0864), R), R)
                    r_eval := mulmod(r_eval, mload(0x0440), R)
                    mstore(0x04c0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x0ce4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x0ca4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x0cc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x0c84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x0c44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x0c64), R), R)
                    r_eval := mulmod(r_eval, mload(0x0460), R)
                    mstore(0x04e0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0fe4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1004), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0f84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0fa4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0f24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0f44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0ec4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0ee4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0e64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0e84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0e04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0e24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0da4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0dc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0d44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0d64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x0d04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x0d24), R), R)
                    r_eval := mulmod(r_eval, mload(0x0480), R)
                    mstore(0x0500, r_eval)
                }
                {
                    let sum := mload(0x20)
                    mstore(0x0520, sum)
                }
                {
                    let sum := mload(0x40)
                    sum := addmod(sum, mload(0x60), R)
                    mstore(0x0540, sum)
                }
                {
                    let sum := mload(0x80)
                    sum := addmod(sum, mload(0xa0), R)
                    sum := addmod(sum, mload(0xc0), R)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0xe0)
                    sum := addmod(sum, mload(0x0100), R)
                    mstore(0x0580, sum)
                }
                {
                    for
                        {
                            let mptr := 0x00
                            let mptr_end := 0x80
                            let sum_mptr := 0x0520
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80)
                    let r_eval := mulmod(mload(0x60), mload(0x0500), R)
                    for
                        {
                            let sum_inv_mptr := 0x40
                            let sum_inv_mptr_end := 0x80
                            let r_eval_mptr := 0x04e0
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), R)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), R), R)
                    }
                    mstore(R_EVAL_MPTR, r_eval)
                }
                {
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0x06a4))
                    mstore(0x20, calldataload(0x06c4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, mload(QUOTIENT_X_MPTR), mload(QUOTIENT_Y_MPTR))
                    for
                        {
                            let mptr := 0x0ec0
                            let mptr_end := 0x0800
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, mload(mptr), mload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x03a4
                            let mptr_end := 0x0164
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x0124
                            let mptr_end := 0x24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    mstore(0x80, calldataload(0x0164))
                    mstore(0xa0, calldataload(0x0184))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0440), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), R)
                    mstore(0x80, calldataload(0x0424))
                    mstore(0xa0, calldataload(0x0444))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x03e4), calldataload(0x0404))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0460), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), R)
                    mstore(0x80, calldataload(0x0664))
                    mstore(0xa0, calldataload(0x0684))
                    for
                        {
                            let mptr := 0x0624
                            let mptr_end := 0x0424
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, sub(R, mload(R_EVAL_MPTR)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x1044))
                    mstore(0xa0, calldataload(0x1064))
                    success := ec_mul_tmp(success, sub(R, mload(0x0400)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x1084))
                    mstore(0xa0, calldataload(0x10a4))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x1084))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x10a4))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_LHS_X_MPTR), mload(PAIRING_LHS_Y_MPTR))
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_RHS_X_MPTR), mload(PAIRING_RHS_Y_MPTR))
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}