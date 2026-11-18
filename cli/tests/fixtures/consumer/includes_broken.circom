pragma circom 2.1.4;

include "broken_library.circom";

template IntactDefinition() {
    signal output out;
    out <== 1;
}
