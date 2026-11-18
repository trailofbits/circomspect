pragma circom 2.2.3;

function F(value) {
    _ <== value;
    return value;
}

template Main() {
    signal output out;
    out <== F(1);
}

component main = Main();
