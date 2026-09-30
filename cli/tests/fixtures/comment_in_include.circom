pragma circom 2.1.4;
include "comment_path//included.circom";

template UsesIncluded() {
    component child = Included();
    signal output out;
    out <== child.out;
}
