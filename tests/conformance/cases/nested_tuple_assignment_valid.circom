pragma circom 2.2.3;

template Main() {
    signal output a;
    signal output b;
    signal output c;
    (a, (b, c)) <== (1, (2, 3));
}

component main = Main();
