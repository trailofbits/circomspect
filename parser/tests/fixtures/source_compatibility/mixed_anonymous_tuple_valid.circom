pragma circom 2.2.3;

template Pair() {
    signal input value;
    signal output left;
    signal output right;
    left <== value;
    right <== value + 1;
}

template Main() {
    signal input value;
    signal output first;
    signal output second;
    signal output third;
    (first, second, third) <== (Pair()(value), value);
}

component main = Main();
