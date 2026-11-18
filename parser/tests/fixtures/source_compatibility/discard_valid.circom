pragma circom 2.2.3;

template Main() {
    signal input value;
    signal output out;
    _ = value + 1;
    _ <-- value + 2;
    _ <== value * value;
    value + 3 --> _;
    value * value ==> _;
    out <== value;
}

component main = Main();
