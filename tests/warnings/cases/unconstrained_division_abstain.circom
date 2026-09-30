pragma circom 2.1.4;
template Main() {
    signal input in;
    signal output out;
    out <-- 1 / Missing(in);
}
component main = Main();
