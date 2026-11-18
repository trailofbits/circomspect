pragma circom 2.2.3;
include "source_dependency_lib.circom";

template Main() {
    signal output out;
    component child = Imported();
    out <== child.out;
}

component main = Main();
