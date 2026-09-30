pragma circom 2.1.4;

template Unclosed() {
    var value = 1;

template AfterUnclosed() {
    signal input in;
    signal output out;
    out <== in;
}
