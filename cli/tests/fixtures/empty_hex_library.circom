pragma circom 2.1.4;

template InvalidHex() {
    var value = 0x;
}

template AfterInvalidHex() {
    signal input in;
    signal output out;
    out <== in;
}
