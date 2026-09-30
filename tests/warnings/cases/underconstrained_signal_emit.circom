pragma circom 2.1.4;
template Main() {
    signal input in;
    signal a;
    signal output out;
    a <-- in;
    out <== in;
}
component main = Main();
