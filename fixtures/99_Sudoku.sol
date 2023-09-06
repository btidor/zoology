// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Sudoku {
    function check(uint[9][9] calldata solution) external pure {
        require(solution[0][0] == 4);
        require(solution[0][2] == 6);
        require(solution[0][5] == 8);
        require(solution[0][7] == 7);
        require(solution[0][8] == 3);
        require(solution[1][0] == 8);
        require(solution[1][1] == 9);
        require(solution[1][2] == 2);
        require(solution[1][5] == 7);
        require(solution[2][3] == 4);
        require(solution[3][2] == 9);
        require(solution[3][7] == 3);
        require(solution[4][2] == 8);
        require(solution[4][6] == 6);
        require(solution[4][8] == 5);
        require(solution[5][4] == 3);
        require(solution[5][5] == 4);
        require(solution[6][1] == 8);
        require(solution[6][8] == 4);
        require(solution[7][4] == 5);
        require(solution[7][7] == 2);
        require(solution[7][8] == 9);
        require(solution[8][5] == 2);
        require(solution[8][6] == 8);
        require(solution[8][8] == 6);

        for (uint i = 0; i < 9; i++) {
            for (uint j = 0; j < 9; j++) {
                require(solution[i][j] > 0);
                require(solution[i][j] < 10);

                for (uint k = j+1; k < 9; k++) {
                    require(solution[i][j] != solution[i][k]);
                    require(solution[j][i] != solution[k][i]);
                }
            }
        }

        for (uint m = 0; m < 9; m++) {
            uint a;
            uint b;
            (a, b) = linearToBox(m);
            for (uint n = 0; n < 9; n++) {
                uint c;
                uint d;
                (c, d) = linearToBox(n);
                for (uint p = n+1; p < 9; p++) {
                    uint e;
                    uint f;
                    (e, f) = linearToBox(p);
                    require(solution[3*a+c][3*b+d] != solution[3*a+e][3*b+f]);
                }
            }
        }
    }

    function linearToBox(uint i) internal pure returns (uint, uint) {
        return (i / 3, i % 3);
    }
}
