pragma circom 2.1.4;
template Main() {
    var used = 1;
    signal output out;
    out <== used;
}
component main = Main();
