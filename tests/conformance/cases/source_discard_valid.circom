pragma circom 2.2.3;

template Main() {
    signal input in;
    signal output out;
    _ <== in;
    out <== in;
}

component main = Main();
