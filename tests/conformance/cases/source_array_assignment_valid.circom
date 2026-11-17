pragma circom 2.2.3;

template Main() {
    signal input in[2];
    signal output out[2];
    out <== in;
}

component main = Main();
