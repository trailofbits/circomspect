pragma circom 2.1.4;
template Main() {
    signal input in;
    signal output out;
    out <-- in == 0 ? 1 : 0;
}
component main = Main();
