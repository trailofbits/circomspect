pragma circom 2.2.3;
include "source_cycle_child.circom";

template Main() {
    signal output out;
    out <== Child();
}

component main = Main();
