pragma circom 2.1.4;

template BrokenToken() {
    var value = @;
}

template AfterInvalidToken() {
    signal input in;
    signal output out;
    out <== in;
}
