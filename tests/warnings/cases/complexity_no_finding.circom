pragma circom 2.1.4;
template Main() {
    signal input in;
    signal output out;
    var value = 0;
    if (in == 0) {
        value = 1;
    }
    out <-- value;
}
component main = Main();
