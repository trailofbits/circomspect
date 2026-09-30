pragma circom 2.1.4;
include ;

template AfterMalformedIncludePath() {
    signal input in;
    signal output out;
    out <== in;
}
