pragma circom 2.1.4;

template BeforeError() {
    signal input in;
    signal output out;
    out <== in;
}

template BrokenFirst() {
    var value = ;
}

template BetweenErrors() {
    signal input in;
    signal output out;
    out <== in;
}

template BrokenSecond() {
    var value = ;
}

template AfterError() {
    signal input in;
    signal output out;
    out <== in;
}
