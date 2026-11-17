pragma circom 2.2.3;

template Main() {
    signal input value;
    signal output out;
    (_, out) <== (value, value, value);
}

component main = Main();
