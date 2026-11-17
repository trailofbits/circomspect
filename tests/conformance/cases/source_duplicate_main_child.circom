pragma circom 2.2.3;

template Child() {
    signal output out;
    out <== 1;
}

component main = Child();
