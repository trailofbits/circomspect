pragma circom 2.2.3;

template Main() {
    signal output out;
    /*// Given the overlapping opening sequence, this whole line is a comment. */
    out <== 1;
}

component main = Main();
