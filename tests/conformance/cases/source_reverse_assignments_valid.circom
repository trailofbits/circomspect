pragma circom 2.2.3;

template Main() {
    signal input value;
    signal output witness;
    signal output constrained;
    value --> witness;
    value ==> constrained;
}

component main = Main();
