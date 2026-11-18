pragma circom 2.2.3;
template Inc(){
    signal input in;
    signal output out;
    out <== in + 1;
}
template Main(){
    signal input x[2];
    signal output y[2];
    y <== [Inc()(x[0]), Inc()(x[1])];
}
component main = Main();
