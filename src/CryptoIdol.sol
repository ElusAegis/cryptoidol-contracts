// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.20;

import {ERC721} from "lib/solady/src/tokens/ERC721.sol";
import {Ownable} from "solady/auth/Ownable.sol";
import {Base64} from "solady/utils/Base64.sol";
import {IVerifier} from "./IVerifier.sol";

error COMMIT_ALREADY_EXISTS();
error NOT_COMMITTER();
error ALREADY_REVEALED();
error CHEAPSKATE();
error MINTED_OUT();
error VERIFICATION_FAILED();

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
    IVerifier public verifier;
    uint256 public tokenCount;
    uint256 public maxTokenCount = 10_000;
    uint256 public mintPrice;

    struct Commit {
        address committer;
        uint64 commitTime;
        uint64 revealTime;
    }

    mapping (bytes32 => Commit) commits;
    mapping (uint256 => uint256) score;
    mapping (uint256 => address) minter;
    mapping (uint256 => uint256) mintTime;
    mapping (uint8 => string) bgPalette;
    mapping (uint8 => string) skinPalette;

    /// @notice constructor to initialize contract
    /// @param owner_ owner address that has control over the contract
    /// @param verifier_ ezkl verifier used in the contract
    /// @param mintPrice_ cost in wei (10^18 wei == 1 ether)
    constructor(
        address owner_,
        address verifier_,
        uint256 mintPrice_
    ) {
        _initializeOwner(owner_);
        verifier = IVerifier(verifier_);
        mintPrice = mintPrice_;


        // initialize bgPalette
        // yellow
        bgPalette[0] = '#FFD53E';
        // white
        bgPalette[1] = '#FFFFFF';
        // dark grey
        bgPalette[2] = '#444444';
        // pink
        bgPalette[3] = '#FF8B8B';
        // blue
        bgPalette[4] = '#5283FF';
        // brown
        bgPalette[5] = '#6C4141';
        // lime-green
        bgPalette[6] = '#AAFFA3';
        // red
        bgPalette[7] = '#FF4848';
        // purple
        bgPalette[8] = '#7920C0';

        // initialize skinPalette
        // fair
        skinPalette[0] = '#FFF7E1';
        // tan
        skinPalette[1] = '#BD9285';
        // dark
        skinPalette[2] = '#8B5D4F';

    }

    function name() public pure override returns (string memory) {
        return "CryptoIdol";
    }

    function symbol() public pure override returns (string memory) {
        return "IDOLNFT";
    }

    function tokenURI(uint256 id) public view override returns (string memory) {
        if (!_exists(id)) {
            revert TokenDoesNotExist();
        }

        uint256 number = id;

        string memory image = string(abi.encodePacked(
            '<svg width="1000" height="1000" viewBox="0 0 1000 1000" fill="none" xmlns="http://www.w3.org/2000/svg">',
            _renderSvgPart1(number),
            _renderSvgPart2(number),
            '</svg>'
        ));

        return string(abi.encodePacked(
            'data:application/json;base64,',
            Base64.encode(
                bytes(
                abi.encodePacked('{"image": "data:image/svg+xml;base64,', Base64.encode(bytes(image)), '"}')
                )
            )
        ));
    }

    // extract some elements to prevent stack too deep errors
    function _renderSvgPart1(uint256 number) internal view returns (string memory) {
        return string(abi.encodePacked(
            // bg
            _renderBg(number),
            // hair back
            _renderHair(number)[0],
            // head
            _renderSkin(number)[0],
            // hair front
            _renderHair(number)[1],
            // eye
            _renderEye(number)
        ));
    }

    // extract lower elements to prevent stack too deep errors
    function _renderSvgPart2(uint256 number) internal view returns (string memory) {
        return string(abi.encodePacked(
            // legs
            _renderSkin(number)[1],
            // dress
            _renderDress(number),
            // mouth
            '<path d="M522.5 484C522.5 494.436 512.562 503.5 499.5 503.5C486.438 503.5 476.5 494.436 476.5 484C476.5 473.564 486.438 464.5 499.5 464.5C512.562 464.5 522.5 473.564 522.5 484Z" fill="#FF8181" stroke="black" stroke-width="5"/>',
            // hand wear
            _renderHandWear(number),
            // head wear
            _renderHeadWear(number),
            // hands
            _renderSkin(number)[2]
        ));
    }


    function _renderBg(uint256 number) internal view returns (string memory) {
        return string(abi.encodePacked(
            '<rect width="1000" height="1000" fill="', bgPalette[uint8(number % 9)] ,'"/>'
        ));
    }

    function _renderHair(uint256 number) internal view returns (string[2] memory) {
        string[6] memory hairBackOptions = [
            // Hair Messy
            string(
                abi.encodePacked(
                    '<path d="M244.5 725C226.5 695 265.333 564.833 287 503.5L712 514C711.2 534.8 759.5 614.5 767.5 675C767.5 700.6 753.5 719 746.5 725L722.5 682C734.5 739.6 698.5 763 679 767.5C696.2 747.9 686.167 727 679 719C681.8 739 665.833 759.667 657.5 767.5C582.7 793.1 428.333 778.167 360.5 767.5C342.5 759.9 324.667 732 318 719C314.4 743 324.167 761.333 329.5 767.5C273.5 774.3 269.833 713.333 275 682C265.4 693.2 250.667 715.333 244.5 725Z" stroke="black" stroke-width="10" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '"/>'
                )
            ),
            // Hair Tidy
            string(
                abi.encodePacked(
                    '<path d="M301.31 759.793L326.569 480H668.586L703.55 759.715L603.587 797.5H496.5H391.998L301.31 759.793Z" stroke="black" stroke-width="10" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '"/>"'
                )
            ),
            // Pony Tail Left
            string(
                abi.encodePacked(
                    '<path d="M205 188.5C221.8 136.9 291.667 167 318.5 188.5L283 467.5C290.2 498.7 294 552.833 295 576C300 673 235 740 251 707.5C263.8 681.5 256.333 607.333 251 573.5C251 613.9 220.333 701.333 205 740C191.833 731.5 160.4 689.1 140 587.5C121.5 440 184 253 205 188.5Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            ),
            // Pony Tail Right
            string(
                abi.encodePacked(
                    '<path d="M788.5 188.491C771.7 136.891 701.833 166.991 675 188.491L710.5 467.491C703.3 498.691 699.5 552.824 698.5 575.991C693.5 672.991 758.5 739.991 742.5 707.491C729.7 681.491 737.167 607.324 742.5 573.491C742.5 613.891 773.167 701.324 788.5 739.991C801.667 731.491 833.1 689.091 853.5 587.491C872 439.991 809.5 252.991 788.5 188.491Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            ),
            // Double Pony Tails
            string(
                abi.encodePacked(
                    '<path d="M205 188.5C221.8 136.9 291.667 167 318.5 188.5L283 467.5C290.2 498.7 294 552.833 295 576C300 673 235 740 251 707.5C263.8 681.5 256.333 607.333 251 573.5C251 613.9 220.333 701.333 205 740C191.833 731.5 160.4 689.1 140 587.5C121.5 440 184 253 205 188.5Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                    '<path d="M788.5 188.491C771.7 136.891 701.833 166.991 675 188.491L710.5 467.491C703.3 498.691 699.5 552.824 698.5 575.991C693.5 672.991 758.5 739.991 742.5 707.491C729.7 681.491 737.167 607.324 742.5 573.491C742.5 613.891 773.167 701.324 788.5 739.991C801.667 731.491 833.1 689.091 853.5 587.491C872 439.991 809.5 252.991 788.5 188.491Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            ),
            ''
        ];
        string[6] memory hairFrontOptions = [
            // hime
            string(
                abi.encodePacked(
                    '<path d="M261 302C278 142 429 103.5 495.5 102C657.5 102 720 235.333 731 302C767 527.2 658.833 583.833 624.5 584C655 516.5 650.5 403.5 650.5 371H343.075L351 314.388L366.5 260.5C313.3 392.1 348.833 530.667 371 590C275 502 245.009 452.5 261 302Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '"/> <path d="M630.5 260.5C633.667 271.333 642.548 296 645 314.388C648.282 339 650.5 345 650.5 371M650.5 371C650.5 403.5 655 516.5 624.5 584C658.833 583.833 767 527.2 731 302C720 235.333 657.5 102 495.5 102C429 103.5 278 142 261 302C245.009 452.5 275 502 371 590C348.833 530.667 313.3 392.1 366.5 260.5L351 314.388L343.075 371H650.5Z" stroke="black" stroke-width="10"/>'
                )
            ),
            // bang
            string(
                abi.encodePacked(
                    '<path d="M261 302C278 142 429 103.5 495.5 102C657.5 102 720 235.333 731 302C767 527.2 658.833 583.833 624.5 584C657.837 528.308 649.835 377.057 638.199 306.137C639.466 322.674 629.392 360.534 630 376.5C594 360.5 587.833 287 582 255C567.2 354.6 489.833 380.167 453 380.5C460.6 377.7 484.5 347.667 495.5 333C473.9 357.8 418.5 368.667 393.5 371C434.961 333.4 456.442 293 462 277.5C442 314.7 371.741 355.333 343.075 371L351 314.388L366.5 260.5C313.3 392.1 348.833 530.667 371 590C275 502 245.009 452.5 261 302Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '"/> <path d="M495.5 102C429 103.5 278 142 261 302C245.009 452.5 275 502 371 590C348.833 530.667 313.3 392.1 366.5 260.5L351 314.388L343.075 371C371.741 355.333 442 314.7 462 277.5C456.442 293 434.961 333.4 393.5 371C418.5 368.667 473.9 357.8 495.5 333C484.5 347.667 460.6 377.7 453 380.5C489.833 380.167 567.2 354.6 582 255C587.833 287 594 360.5 630 376.5C629.333 359 641.5 315.2 637.5 302C649.5 371 658.5 527.2 624.5 584C658.833 583.833 767 527.2 731 302C720 235.333 657.5 102 495.5 102Z" stroke="black" stroke-width="10"/>'
                )
            ),
            // middle part
            string(
                abi.encodePacked(
                    '<path d="M261 302C278 142 429 103.5 495.5 102C657.5 102 720 235.333 731 302C767 527.2 658.833 583.833 624.5 584C680.1 474 651.667 322.5 630.5 260.5C642.9 346.1 630.5 353.045 624.5 352.5C580.5 348.5 517.5 286.667 495.5 260.5C469.333 290.167 410.7 359.7 353.5 366.5C352.379 345.038 353.228 295.75 365.01 264.247C313.973 394.722 349.044 531.23 371 590C275 502 245.009 452.5 261 302Z" stroke="black" stroke-width="10" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '"/>'
                )
            ),
            // side part
            string(
                abi.encodePacked(
                    '<path d="M261 302C278 142 429 103.5 495.5 102C657.5 102 720 235.333 731 302C767 527.2 658.833 583.833 624.5 584C680.1 474 651.667 322.5 630.5 260.5C633.667 271.333 635.548 308.612 638 327C561.716 351.037 401.534 383.4 343.075 371L351 314.388L366.5 260.5C313.3 392.1 348.833 530.667 371 590C275 502 245.009 452.5 261 302Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            ),
            // curly
            string(
                abi.encodePacked(
                    '<path d="M287.5 620C278 447.5 245 429.5 253 291C253 199 326 95 490.5 95C671 95 714 181.5 735.5 291C750.5 433.5 689 540.5 704 620C663.6 580.8 631.333 306.667 628.5 265L613.5 350C585.1 334.8 574 339 557.5 265V339C533.5 315.8 519.167 283.667 515 265C501.8 333 466 333.5 434 339C472.4 311.8 453.167 287.5 454.5 265C434 339 394.333 324.333 372.5 339C372.5 284 364 257 364 265C349 453 287.5 620 287.5 620Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            ),
            // bang cover eye
            string(
                abi.encodePacked(
                    '<path d="M615 477.5C528.2 420.7 457.167 296.5 432.5 241.5C432.5 300.7 462.833 381.5 478 414.5C427.433 389.051 386.127 318.156 364.182 269C306.182 347.8 353 498 368.5 587C248 484 253 399.5 254.5 328C256 256.5 313.5 100.5 508 102C663.6 103.2 725.5 253.167 737 328C755.8 503.6 671.833 573.833 627.5 587C662.7 499 649.5 343 638.5 276C648.5 379.2 627 453.333 615 477.5Z" fill="',
                    bgPalette[uint8((number + 1) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            )
        ];

        return [
            hairBackOptions[uint8((number + 1) % 6)],
            hairFrontOptions[uint8(number + 2) % 6]
        ];
    }

    function _renderSkin(uint256 number) internal view returns (string[3] memory) {
        string memory skinColor = skinPalette[uint8(number % 3)];
        return [
            // head
            string(
                abi.encodePacked(
                    '<path d="M730 381C730 426.209 704.612 467.59 662.659 497.861C620.712 528.126 562.513 547 498 547C433.487 547 375.288 528.126 333.341 497.861C291.388 467.59 266 426.209 266 381C266 335.791 291.388 294.41 333.341 264.139C375.288 233.874 433.487 215 498 215C562.513 215 620.712 233.874 662.659 264.139C704.612 294.41 730 335.791 730 381Z" stroke="black" stroke-width="10" fill="',
                    skinColor
                    ,'"/>'
                )
            ),
            // legs
            string(
                abi.encodePacked(
                    '<path d="M493 836.5C493 862.099 488.653 885.039 481.818 901.393C478.395 909.581 474.447 915.882 470.319 920.059C466.208 924.219 462.218 926 458.5 926C454.782 926 450.792 924.219 446.681 920.059C442.553 915.882 438.605 909.581 435.182 901.393C428.347 885.039 424 862.099 424 836.5C424 810.901 428.347 787.961 435.182 771.607C438.605 763.419 442.553 757.118 446.681 752.941C450.792 748.781 454.782 747 458.5 747C462.218 747 466.208 748.781 470.319 752.941C474.447 757.118 478.395 763.419 481.818 771.607C488.653 787.961 493 810.901 493 836.5Z" stroke="black" stroke-width="10" fill="',
                    skinColor,
                    '"/> <path d="M586 836.5C586 862.099 581.653 885.039 574.818 901.393C571.395 909.581 567.447 915.882 563.319 920.059C559.208 924.219 555.218 926 551.5 926C547.782 926 543.792 924.219 539.681 920.059C535.553 915.882 531.605 909.581 528.182 901.393C521.347 885.039 517 862.099 517 836.5C517 810.901 521.347 787.961 528.182 771.607C531.605 763.419 535.553 757.118 539.681 752.941C543.792 748.781 547.782 747 551.5 747C555.218 747 559.208 748.781 563.319 752.941C567.447 757.118 571.395 763.419 574.818 771.607C581.653 787.961 586 810.901 586 836.5Z" stroke="black" stroke-width="10" fill="',
                    skinColor,
                    '"/>'
                )
            ),
            // hands
            string(
                abi.encodePacked(
                    '<path d="M520 623.5C520 642.907 507.086 657 493 657C478.914 657 466 642.907 466 623.5C466 604.093 478.914 590 493 590C507.086 590 520 604.093 520 623.5Z" stroke="black" stroke-width="10" fill="',
                    skinColor,
                    '"/> <path d="M678 729C678 745.623 666.237 758 653 758C639.763 758 628 745.623 628 729C628 712.377 639.763 700 653 700C666.237 700 678 712.377 678 729Z" stroke="black" stroke-width="10" fill="',
                    skinColor,
                    '"/>'
                )
            )
        ];
    }

    function _renderEye(uint256 number) internal pure returns (string memory) {
        string[8] memory eyeOptions = [
            // normal
            '<ellipse cx="406" cy="429" rx="38" ry="44" fill="black"/> <ellipse cx="581" cy="429" rx="38" ry="44" fill="black"/> <ellipse cx="418.5" cy="416" rx="12.5" ry="13" fill="white"/> <ellipse cx="593.5" cy="416" rx="12.5" ry="13" fill="white"/> <path d="M543.5 396.5C562.833 373.667 609.1 348.1 639.5 428.5" stroke="black" stroke-width="10"/> <path d="M446 396.854C426.667 373.917 380.4 348.234 350 429" stroke="black" stroke-width="10"/>',
            // star
            '<path d="M411 392.326L418.897 416.631L419.683 419.049H422.226H447.781L427.106 434.07L425.049 435.565L425.835 437.983L433.732 462.288L413.057 447.267L411 445.772L408.943 447.267L388.268 462.288L396.165 437.983L396.951 435.565L394.894 434.07L374.219 419.049H399.774H402.317L403.103 416.631L411 392.326Z" fill="#FFDC27" stroke="black" stroke-width="7"/> <path d="M584 394.326L591.897 418.631L592.683 421.049H595.226H620.781L600.106 436.07L598.049 437.565L598.835 439.983L606.732 464.288L586.057 449.267L584 447.772L581.943 449.267L561.268 464.288L569.165 439.983L569.951 437.565L567.894 436.07L547.219 421.049H572.774H575.317L576.103 418.631L584 394.326Z" fill="#FFDC27" stroke="black" stroke-width="7"/>',
            // closed
            '<path d="M370 422.5C378.761 425.829 393.895 429.858 410 430.724C424.533 431.505 439.857 429.71 452 422.5" stroke="black" stroke-width="10"/> <path d="M535 422C543.761 425.329 558.895 429.358 575 430.224C589.533 431.005 604.857 429.21 617 422" stroke="black" stroke-width="10"/>',
            // sunglass
            '<rect x="514" y="379" width="122" height="62" fill="black"/> <rect x="353" y="379" width="122" height="62" fill="black"/> <rect x="607" y="392" width="19" height="12" fill="white"/> <rect x="447" y="392" width="19" height="12" fill="white"/> <rect x="469" y="405" width="51" height="11" fill="black"/>',
            // heart
            '<path d="M357.244 401.392C368.844 376.192 392.744 390.892 403.244 401.392C418.744 383.392 437.725 381.049 447.744 401.392C461.782 429.892 403.244 458.892 403.244 458.892C403.244 458.892 342.744 432.892 357.244 401.392Z" fill="#FF2525" stroke="black" stroke-width="10"/> <path d="M543.244 401.392C554.844 376.192 578.744 390.892 589.244 401.392C604.744 383.392 623.725 381.049 633.744 401.392C647.782 429.892 589.244 458.892 589.244 458.892C589.244 458.892 528.744 432.892 543.244 401.392Z" fill="#FF2525" stroke="black" stroke-width="10"/>',
            // shock
            '<circle cx="402.5" cy="415.5" r="29.5" fill="white" stroke="black" stroke-width="10"/> <circle cx="586.5" cy="415.5" r="29.5" fill="white" stroke="black" stroke-width="10"/>',
            // dead
            '<line x1="374.803" y1="396.336" x2="449.803" y2="425.336" stroke="black" stroke-width="10"/> <line y1="-5" x2="80.4423" y2="-5" transform="matrix(-0.932703 0.360645 0.360645 0.932703 614.029 401.003)" stroke="black" stroke-width="10"/> <line y1="-5" x2="80.4423" y2="-5" transform="matrix(-0.811559 -0.58427 -0.58427 0.811559 609.027 440)" stroke="black" stroke-width="10"/> <line x1="445.042" y1="387.864" x2="383.174" y2="438.68" stroke="black" stroke-width="10"/>',
            // struggle
            '<line x1="384.418" y1="386.205" x2="455.418" y2="407.205" stroke="black" stroke-width="10"/> <line x1="380.999" y1="438.418" x2="451.999" y2="407.418" stroke="black" stroke-width="10"/> <line y1="-5" x2="74.0405" y2="-5" transform="matrix(-0.958934 0.283628 0.283628 0.958934 610 391)" stroke="black" stroke-width="10"/> <line y1="-5" x2="77.4726" y2="-5" transform="matrix(-0.916453 -0.400142 -0.400142 0.916453 610 443)" stroke="black" stroke-width="10"/>'
        ];

        return eyeOptions[uint8(number % 8)];
    }

    function _renderDress(uint256 number) internal view returns (string memory) {
        return string(abi.encodePacked(
            '<path d="M353.5 784.5C368.7 758.1 423.5 614.167 449 545.5H554.5L647 784.5C527.8 849.7 401.667 811.667 353.5 784.5Z" fill="',
            bgPalette[uint8((number + 5) % 9)],
            '" stroke="black" stroke-width="10"/>',
            '<path d="M385.5 671.5C373.5 637.1 418.167 580.5 442.5 553L436.75 615L468 598.5C460.4 615.7 471.167 646.667 477.5 660L412.5 692C399.5 694.5 389 676.5 385.5 671.5Z" fill="',
            bgPalette[uint8((number + 7) % 9)],
            '"/>',
            '<path d="M656.5 692L554.5 546L567.5 660L622 731L656.5 692Z" fill="',
            bgPalette[uint8((number + 7) % 9)], '"/>',
            '<path d="M405.5 631.5L436.75 615M436.75 615L468 598.5C460.4 615.7 471.167 646.667 477.5 660L412.5 692C399.5 694.5 389 676.5 385.5 671.5C373.5 637.1 418.167 580.5 442.5 553L436.75 615ZM554.5 546L656.5 692L622 731L567.5 660L554.5 546Z" stroke="black" stroke-width="10"/>'
        ));
    }

    function _renderHandWear(uint256 number) internal pure returns (string memory) {
        string[8] memory handWearOptions = [
            // mic
            '<path d="M547 552C547 577.739 525.062 599 497.5 599C469.938 599 448 577.739 448 552C448 526.261 469.938 505 497.5 505C525.062 505 547 526.261 547 552Z" fill="#868686" stroke="black" stroke-width="10"/> <rect x="477" y="595" width="41" height="95" fill="#D9D9D9" stroke="black" stroke-width="10"/>',
            // ice cream choco
            '<path d="M534 528C534 549.704 517.049 567 496.5 567C475.951 567 459 549.704 459 528C459 506.296 475.951 489 496.5 489C517.049 489 534 506.296 534 528Z" fill="#C56E2F" stroke="black" stroke-width="10"/> <path d="M461.771 547.5L496.5 638.039L531.229 547.5H461.771Z" fill="#E59C46" stroke="black" stroke-width="10"/>',
            // ice cream vanilla
            '<path d="M534 528C534 549.704 517.049 567 496.5 567C475.951 567 459 549.704 459 528C459 506.296 475.951 489 496.5 489C517.049 489 534 506.296 534 528Z" fill="#FFF" stroke="black" stroke-width="10"/> <path d="M461.771 547.5L496.5 638.039L531.229 547.5H461.771Z" fill="#E59C46" stroke="black" stroke-width="10"/>',
            // dango
            '<line x1="481.593" y1="688.029" x2="509.212" y2="474.19" stroke="black" stroke-width="10"/> <circle cx="506.697" cy="509.775" r="24.5" transform="rotate(30 506.697 509.775)" fill="#FF9FDE" stroke="black" stroke-width="7"/> <circle cx="502.456" cy="543.122" r="24.5" transform="rotate(30 502.456 543.122)" fill="white" stroke="black" stroke-width="7"/> <circle cx="498.08" cy="578.701" r="24.5" transform="rotate(30 498.08 578.701)" fill="#AAFFA3" stroke="black" stroke-width="7"/>',
            // yakitori
            '<line x1="481.593" y1="688.029" x2="509.212" y2="474.19" stroke="black" stroke-width="10"/> <path d="M526.936 539.097C525.213 551.538 520.688 562.218 514.946 569.441C509.149 576.735 502.589 579.996 496.652 579.174C490.714 578.352 485.288 573.43 481.691 564.836C478.129 556.324 476.676 544.816 478.399 532.375C480.122 519.934 484.648 509.254 490.389 502.031C496.187 494.738 502.746 491.476 508.683 492.298C514.621 493.12 520.047 498.042 523.644 506.637C527.206 515.148 528.659 526.656 526.936 539.097Z" fill="#BB4F00" stroke="black" stroke-width="7"/>',
            // magic wand
            '<rect x="452" y="513.07" width="20.9389" height="201" transform="rotate(-19.7339 452 513.07)" fill="black"/> <rect x="455.197" y="514.579" width="15.9389" height="34" transform="rotate(-19.7339 455.197 514.579)" fill="white" stroke="black" stroke-width="5"/> <rect x="509.897" y="667.065" width="15.9389" height="34" transform="rotate(-19.7339 509.897 667.065)" fill="white" stroke="black" stroke-width="5"/>',
            // knife,
            '<path d="M466 695.067L472.581 668.881L491.716 592.749L513.053 598.112L487.336 700.43L466 695.067Z" fill="black" stroke="black" stroke-width="10"/> <path d="M561.685 498.976L530.108 440L515.361 498.675L491.716 592.749L535.359 603.718L561.685 498.976Z" fill="#D6CBCB" stroke="black" stroke-width="10"/> <path d="M537 532.5C527.4 521.7 533 488.667 537 473.5C544.6 466.7 556.833 487.333 562 498.5L551.5 541.5L541.756 586.812C541.833 587.366 541.767 587.76 541.5 588L541.756 586.812C541.35 583.906 537 576.598 537 564C537 554.038 549 546 537 532.5Z" fill="#FF1414" stroke="black" stroke-width="5"/>',
            // empty
            ''
        ];

        return handWearOptions[uint8(number % 8)];
    }

    function _renderHeadWear(uint256 number) internal view returns (string memory) {
        string[9] memory headWearOptions = [
            // none
            '',
            // cap
            string(
                abi.encodePacked(
                    '<path d="M329.5 188C292.7 92.8 381.167 43 430 30C549.6 1.99999 592.5 84.6667 599 129.5L329.5 188Z" fill="',
                    bgPalette[uint8((number + 2) % 9)],
                    '" stroke="black" stroke-width="10"/> <path d="M217.5 233L329.5 189L323.5 172.5L217.5 233Z" fill="',
                    bgPalette[uint8((number + 2) % 9)],
                    '" stroke="black" stroke-width="10"/>'
                )
            ),
            // cat ear
            '<path d="M292.5 207.5C269.3 169.5 275.167 108.833 281.5 87.5C305.9 87.5 359.5 114.333 373.5 133C331.5 158 317.5 175 292.5 207.5Z" fill="white" stroke="black" stroke-width="10"/> <path d="M306 182C294.4 169.6 292.833 132.5 293.5 115.5C299.5 100.3 334 126.833 350.5 142C334.9 152 314.333 172.833 306 182Z" fill="#FFBCBC"/> <path d="M692.331 208.534C716.779 171.325 712.928 110.497 707.305 88.965C682.919 88.1556 628.459 113.196 613.848 131.388C654.995 157.768 668.423 175.223 692.331 208.534Z" fill="white" stroke="black" stroke-width="10"/> <path d="M679.685 182.6C691.689 170.592 694.486 133.564 694.383 116.552C688.891 101.161 653.53 126.535 636.536 141.146C651.796 151.658 671.66 173.162 679.685 182.6Z" fill="#FFBCBC"/>',
            // bunny ear
            '<path d="M323.5 29C264.3 73.4 309.833 172.5 340 216.5L388 194.5C402.8 34.1 351.167 17.3333 323.5 29Z" fill="white" stroke="black" stroke-width="10"/> <path d="M334.5 64C309.3 87.6 329.833 170 346.5 208L379 193.5C374.167 139.5 359.7 40.4 334.5 64Z" fill="#FFBCBC"/> <path d="M587 198C584 159.333 585.7 78.7 616.5 65.5C655 49 703 106 703 122.5C698.924 156.656 682.732 202.336 648.486 157.5C648.486 176.7 623.495 205.5 616.5 211L587 198Z" fill="white"/> <path d="M648.486 157.5C682.732 202.336 698.924 156.656 703 122.5C703 106 655 49 616.5 65.5C585.7 78.7 584 159.333 587 198L616.5 211C623.495 205.5 648.486 176.7 648.486 157.5ZM648.486 157.5C642.126 149.173 632.144 127.224 624.5 112L648.486 157.5Z" stroke="black" stroke-width="10"/> <path d="M593.5 195.5C591.5 194.7 610.167 134 620.5 115L641.5 156.5L614 204.5C605.5 200.5 606 200.5 593.5 195.5Z" fill="#FFBCBC"/>',
            // ribbon
            string(abi.encodePacked('<path d="M258.5 162C258.5 137.2 299.833 143 320.5 149L335.5 162V180C327.5 204.8 310.167 220 302.5 224.5C287.833 214 258.5 186.8 258.5 162Z" fill="', bgPalette[uint8((number + 2) % 8)], '" stroke="black" stroke-width="10"/> <path d="M418 129.301C418 152.038 379.887 146.72 360.831 141.219L347 129.301V112.798C354.377 90.0612 370.359 76.1257 377.429 72C390.952 81.6265 418 106.564 418 129.301Z" fill="', bgPalette[uint8((number + 2) % 9)],'" stroke="black" stroke-width="10"/> <path d="M363 146.5C363 156.819 354.84 165 345 165C335.16 165 327 156.819 327 146.5C327 136.181 335.16 128 345 128C354.84 128 363 136.181 363 146.5Z" fill="', bgPalette[uint8((number + 2) % 8)],'" stroke="black" stroke-width="10"/>')),
            // devil horn
            '<path d="M323.157 169.21L316.146 119.382L361.456 141.268L323.157 169.21Z" fill="#FF0000" stroke="black" stroke-width="10"/> <path d="M621.098 136.698L666.859 115.772L658.8 165.441L621.098 136.698Z" fill="#FF0000" stroke="black" stroke-width="10"/>',
            // halo
            '<mask id="path-3-inside-1_2_26" fill="white"> <path fill-rule="evenodd" clip-rule="evenodd" d="M500 82C558.542 82 606 69.464 606 54C606 38.536 558.542 26 500 26C441.458 26 394 38.536 394 54C394 69.464 441.458 82 500 82ZM499.5 62C535.122 62 564 58.4183 564 54C564 49.5817 535.122 46 499.5 46C463.878 46 435 49.5817 435 54C435 58.4183 463.878 62 499.5 62Z"/> </mask> <path fill-rule="evenodd" clip-rule="evenodd" d="M500 82C558.542 82 606 69.464 606 54C606 38.536 558.542 26 500 26C441.458 26 394 38.536 394 54C394 69.464 441.458 82 500 82ZM499.5 62C535.122 62 564 58.4183 564 54C564 49.5817 535.122 46 499.5 46C463.878 46 435 49.5817 435 54C435 58.4183 463.878 62 499.5 62Z" fill="white"/> <path d="M598 54C598 53.5063 598.248 55.1058 593.432 58.1134C589.035 60.8596 582.14 63.6261 572.91 66.0643C554.568 70.9095 528.787 74 500 74V90C529.755 90 556.975 86.8225 576.996 81.5337C586.948 78.9049 595.577 75.6379 601.908 71.6843C607.82 67.9922 614 62.2257 614 54H598ZM500 34C528.787 34 554.568 37.0905 572.91 41.9357C582.14 44.3739 589.035 47.1404 593.432 49.8866C598.248 52.8942 598 54.4937 598 54H614C614 45.7743 607.82 40.0078 601.908 36.3157C595.577 32.3621 586.948 29.0951 576.996 26.4663C556.975 21.1775 529.755 18 500 18V34ZM402 54C402 54.4937 401.752 52.8942 406.568 49.8866C410.965 47.1404 417.86 44.3739 427.09 41.9357C445.432 37.0905 471.213 34 500 34V18C470.245 18 443.026 21.1775 423.004 26.4663C413.052 29.0951 404.423 32.3621 398.092 36.3157C392.18 40.0078 386 45.7743 386 54H402ZM500 74C471.213 74 445.432 70.9095 427.09 66.0643C417.86 63.6261 410.965 60.8596 406.568 58.1134C401.752 55.1058 402 53.5063 402 54H386C386 62.2257 392.18 67.9922 398.092 71.6843C404.423 75.6379 413.052 78.9049 423.004 81.5337C443.026 86.8225 470.245 90 500 90V74ZM556 54C556 51.9517 556.869 50.4921 557.477 49.7498C558.037 49.0666 558.53 48.7788 558.543 48.7709C558.56 48.7607 558.065 49.0312 556.68 49.4372C554.031 50.2139 549.807 51.0128 544.124 51.7177C532.869 53.1136 517.089 54 499.5 54V70C517.534 70 534.003 69.0956 546.093 67.596C552.082 66.8532 557.303 65.9282 561.182 64.7907C563.062 64.2396 565.101 63.5054 566.836 62.4537C568.006 61.7447 572 59.1337 572 54H556ZM499.5 54C517.089 54 532.869 54.8864 544.124 56.2823C549.807 56.9872 554.031 57.7861 556.68 58.5628C558.065 58.9688 558.56 59.2393 558.543 59.2291C558.53 59.2212 558.037 58.9334 557.477 58.2502C556.869 57.5079 556 56.0483 556 54H572C572 48.8663 568.006 46.2553 566.836 45.5463C565.101 44.4946 563.062 43.7604 561.182 43.2093C557.303 42.0718 552.082 41.1468 546.093 40.404C534.003 38.9044 517.534 38 499.5 38V54ZM443 54C443 56.0483 442.131 57.5079 441.523 58.2502C440.963 58.9334 440.47 59.2212 440.457 59.2291C440.44 59.2393 440.935 58.9688 442.32 58.5628C444.969 57.7861 449.193 56.9872 454.876 56.2823C466.131 54.8864 481.911 54 499.5 54V38C481.466 38 464.997 38.9044 452.907 40.404C446.918 41.1468 441.697 42.0718 437.818 43.2093C435.938 43.7604 433.899 44.4946 432.164 45.5463C430.994 46.2553 427 48.8663 427 54H443ZM499.5 54C481.911 54 466.131 53.1136 454.876 51.7177C449.193 51.0128 444.969 50.2139 442.32 49.4372C440.935 49.0312 440.44 48.7607 440.457 48.7709C440.47 48.7788 440.963 49.0666 441.523 49.7498C442.131 50.4921 443 51.9517 443 54H427C427 59.1337 430.994 61.7447 432.164 62.4537C433.899 63.5054 435.938 64.2396 437.818 64.7907C441.697 65.9282 446.918 66.8532 452.907 67.596C464.997 69.0956 481.466 70 499.5 70V54Z" fill="black" mask="url(#path-3-inside-1_2_26)"/>',
            // cowbow hat
            '<path d="M246.298 219C240.298 96.6 326.464 85.6666 370.298 95.5C370.298 82 371.998 50.9 378.798 34.5C385.598 18.1 437.964 12 463.298 11C549.698 11.8 593.964 32 605.298 42L611.298 136C651.298 133.2 713.631 156.167 739.798 168C690.998 168 542.464 224.333 474.298 252.5C446.453 267.59 407.845 284.006 370.298 291.922C308.734 304.901 250.025 295.03 246.298 219Z" fill="#6C4141"/> <path d="M370.298 95.5C326.464 85.6667 240.298 96.6 246.298 219C252.298 341.4 400.798 292.333 474.298 252.5C542.464 224.333 690.998 168 739.798 168M370.298 95.5C370.298 82 371.998 50.9 378.798 34.5C385.598 18.1 437.964 12 463.298 11C549.698 11.8 593.964 32 605.298 42L611.298 136M370.298 95.5V168C403.631 182.667 483.798 207.6 537.798 190C550.131 186.333 580.898 176.8 605.298 168L611.298 136M739.798 168C713.631 156.167 651.298 133.2 611.298 136M739.798 168C636.998 127.2 447.798 236.589 370.298 291.922" stroke="black" stroke-width="10"/>',
            // party hat
            string(abi.encodePacked('<path d="M309.5 213L285 43L407.5 154.5C396.7 190.9 337.667 208.667 309.5 213Z" fill="', bgPalette[uint8((number + 2) % 9)],'" stroke="black" stroke-width="10"/>'))
        ];

        return headWearOptions[uint8(number % 9)];
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
        if (msg.value < mintPrice) {
            revert CHEAPSKATE();
        }

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

        score[tokenCount] = instances[1];
        minter[tokenCount] = msg.sender;
        mintTime[tokenCount] = block.timestamp;

        _safeMint(msg.sender, tokenCount);
    }

    function withdraw() external onlyOwner {
        (bool sent, _) = owner().call{value: address(this).balance}("");
        require(sent, "Failed to send Ether");
    }
}
