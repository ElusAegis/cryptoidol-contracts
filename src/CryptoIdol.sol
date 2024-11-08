// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.20;

import {ERC721} from "lib/solady/src/tokens/ERC721.sol";
import {Ownable} from "solady/auth/Ownable.sol";
import {IVerifier} from "./IVerifier.sol";
import {ICryptoIdolArt} from "./ICryptoIdolArt.sol";

/**
 * @notice CryptoIdol NFT Contract, Sing to Mint a CryptoIdol!
 * @author jseam
 *
 *                    __ ~~~~~~~~~~~~~~~~~~~~~~~~~~~____
 *                  ~~                                  ~~~
 *               ~~~                                      ~~~
 *             ~~~                                           ~~
 *           ~~                                                 ~
 *          ~                                                    ~
 *        ~                                                        ~
 *       ~            ~          ~               ~ ~               ~
 *       ~          ~~         ~~              ~~   ~    ~~         ~
 *      ~~          ~~      ~~~~              ~~     ~   ~~         ~~
 *      ~~         ~~  ~~   ~~    ~~~~~   ~~~          ~ ~~         ~~
 *      ~~         ~~~    ~~~~~~~~ ~~~~~~~~             ~~~         ~~
 *      ~~         ~     ~~~~~~   ~~~~~~            ~~    ~          ~
 *      ~~         ~   ~~ ~~~~~~~              ~~~~~~  ~  ~~        ~~
 *      ~~        ~~  ~~~~~~~~~~~              ~~~~~~~~ ~~~~        ~~
 *       ~         ~ ~~ ~~~~~   ~             ~~~~~   ~~ ~~~        ~~
 *       ~~        ~    ~~~~~~~~~             ~~~~~~~~~~  ~~        ~~
 *       ~~        ~    ~~~~~~~~~     ___     ~~~~~~~~~   ~~        ~
 *         ~~      ~~                |   |               ~~       ~~
 *          ~~     ~~                 ~~~                 ~       ~~
 *          ~~~     ~~              ~~~~~~~              ~~     ~~
 *         ~~ ~~    ~~~~~~        ~~~     ~~~         ~~~~~    ~~
 *         ~   ~~~  ~~   ~~~~~~~ ~~         ~~~~~~~~~~~  ~~   ~~ ~~
 *        ~~     ~~~ ~~        ~~~           ~~~~        ~     ~~   ~
 *       ~~        ~~~~        ~~~~          ~~~~       ~~  ~~~     ~~
 *       ~~          ~~~      ~~~~~~       ~~~~~~~     ~~~~~~        ~~
 *      ~~                 ~~~ ~~~~~~~~~~~~~~~~~~ ~~                   ~
 *     ~~                 ~~~  ~~~~~~     ~~~~~~~  ~~~                 ~~
 *     ~~                ~~~~~~~~ ~~      ~~~~~~~   ~~~                 ~~
 *     ~                 ~~~~~     ~~     ~~~~~~~    ~~~                 ~
 *    ~~                ~~         ~~~~~~~~~~~~~~~     ~~                ~~
 *    ~~  ~~            ~~      ~~~~~~    ~~~~~~~~~     ~~~         ~    ~~
 *    ~~ ~~~             ~~  ~~~~~~~~~~~~~~~~~~~~~~~     ~~~        ~~   ~~
 *    ~~~ ~~    ~~      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ~~   ~~~   ~~ ~~~
 *         ~~   ~~~     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~     ~~~  ~~
 *                     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *                         ~~~~~~~~~~~~~~~~~~~~~~~~~~
 *                           ~       ~~~~~      ~~
 *                           ~       ~~  ~      ~
 *                           ~~      ~   ~      ~
 *                            ~     ~~    ~     ~
 *                             ~   ~~     ~~   ~
 *                              ~~~~        ~~~
 */
contract CryptoIdol is ERC721, Ownable {
    // ERRORS
    error COMMIT_ALREADY_EXISTS();
    error NOT_COMMITTER();
    error ALREADY_REVEALED();
    error MINTED_OUT();
    error VERIFICATION_FAILED();

    IVerifier public verifier;
    ICryptoIdolArt public cryptoIdolArt;
    uint256 public tokenCount;
    uint256 public maxTokenCount = 10_000;

    struct Commit {
        address committer;
        uint64 commitTime;
        uint64 revealTime;
    }

    mapping (bytes32 => Commit) public commits;
    mapping (uint256 => uint256) public score;
    mapping (uint256 => address) public minter;
    mapping (uint256 => uint256) public mintTime;
    mapping (uint8 => string) public bgPalette;
    mapping (uint8 => string) public skinPalette;

    /// @notice constructor to initialize contract
    /// @param owner_ owner address that has control over the contract
    /// @param verifier_ ezkl verifier used in the contract
    constructor(
        address owner_,
        address verifier_,
        address cryptoIdolArt_
    ) {
        _initializeOwner(owner_);
        verifier = IVerifier(verifier_);
        cryptoIdolArt = ICryptoIdolArt(cryptoIdolArt_);
    }

    function name() public pure override returns (string memory) {
        return "CryptoIdolV2";
    }

    function symbol() public pure override returns (string memory) {
        return "IDOLNFTV2";
    }

    function tokenURI(uint256 id) public view override returns (string memory) {
        if (!_exists(id)) {
            revert TokenDoesNotExist();
        }

        return cryptoIdolArt.tokenURI(id, score[id]);
    }

    function updateVerifier(address verifier_) external onlyOwner {
        verifier = IVerifier(verifier_);
    }

    function commitResult(bytes32 resultHash) external {
        if (commits[resultHash].commitTime > 0) {
            revert COMMIT_ALREADY_EXISTS();
        } else {
            commits[resultHash] = Commit(
                msg.sender,
                uint64(block.timestamp % 2**64),
                0
            );
        }
    }

    function mint(bytes calldata proof, uint256[] calldata instances) external payable {

        Commit storage c = commits[keccak256(abi.encode(proof, instances))];

        if (c.committer != msg.sender) {
            revert NOT_COMMITTER();
        }

        if (c.revealTime > 0) {
            revert ALREADY_REVEALED();
        } else {
            c.revealTime = uint64(block.timestamp % 2**64);
        }

        ++tokenCount;

        if (tokenCount > maxTokenCount) {
            revert MINTED_OUT();
        }

        if(!verifier.verifyProof(proof, instances)) {
            revert VERIFICATION_FAILED();
        }

        score[tokenCount] = convertScore(instances[1], 2**13, 10);
        minter[tokenCount] = msg.sender;
        mintTime[tokenCount] = block.timestamp;

        _safeMint(msg.sender, tokenCount);
    }

    function withdraw() external onlyOwner {
        (bool sent, ) = owner().call{value: address(this).balance}("");
        require(sent, "Failed to send Ether");
    }


    /**
     * @notice Rescales a score from the original scale to the new scale.
     * @param originalScore The score to be rescaled.
     * @param originalScaleFactor The scale factor of the original score.
     * @param newScaleFactor The scale factor of the new score.
     * @return rescaledScore The real score in the range of 0 to 10, rounded down to the nearest bucket.
     */
    function convertScore(uint256 originalScore, uint256 originalScaleFactor, uint256 newScaleFactor) internal pure returns (uint256) {

        uint256 rescaledScore = originalScore / (originalScaleFactor / newScaleFactor);

        return rescaledScore;
    }
}
