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
    signal (first, second) <== Pair()(value);
    var (a, b) = Pair()(value);
    signal output out;
    out <== first + second + a + b;
}

component main = Main();
