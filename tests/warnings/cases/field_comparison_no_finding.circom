pragma circom 2.1.4;
template Main() {
    signal output out;
    out <-- (1 < 2);
}
component main = Main();
