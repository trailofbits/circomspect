pragma circom 2.1.4;
include "resolved_library.circom"

template AfterMalformedInclude() {
    signal input in;
    signal output out;
    out <== in;
}
