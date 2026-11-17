pragma circom 2.2.3;

include "source_duplicate_main_child.circom";

template Root() {
    signal output out;
    out <== 1;
}

component main = Root();
