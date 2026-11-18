pragma circom 2.1.4;

template Main() {
    signal input in;
    signal output out;
    out <-- in * in * in;
    out === in;
}

component main = Main();
