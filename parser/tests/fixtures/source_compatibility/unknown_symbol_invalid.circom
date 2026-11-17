pragma circom 2.2.3;

template Main() {
    signal output out;
    absent = 1;
    out <== 1;
}

component main = Main();
