pragma circom 2.1.4;
template Many(a, b, ) {
    signal output out;
    out <== a;
}
component main = Many(1, 2);
