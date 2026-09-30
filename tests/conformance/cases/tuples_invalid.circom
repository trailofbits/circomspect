pragma circom 2.2.3;
template Pair(){
    signal input x;
    signal output a;
    signal output b;
    a <== x;
    b <== x + 1;
}
template Main(){
    signal input x;
    signal output a;
    signal output b;
    (a b) <== Pair()(x);
}
component main = Main();
