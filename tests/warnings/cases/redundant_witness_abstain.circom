pragma circom 2.1.4;
template Main() {
    signal input in;
    signal output out;
    out <-- in * in;
    out === Missing(in);
}
component main = Main();
