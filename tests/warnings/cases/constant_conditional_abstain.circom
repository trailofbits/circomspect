pragma circom 2.1.4;
template Main() {
    signal output out;
    if (Missing()) {
        out <-- 1;
    }
    else {
        out <-- 1;
    }
}
component main = Main();
