pragma circom 2.2.3;

template Child() {
    signal input left;
    signal input right;
    signal output out;
    out <== left + right;
}

template Main() {
    signal input a;
    signal input b;
    signal output out;
    out <== Child()(right <== b, left <== a);
}

component main = Main();
