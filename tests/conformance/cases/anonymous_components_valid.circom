pragma circom 2.2.3;
template Inc(){
    signal input in;
    signal output out;
    out <== in + 1;
}
template Main(){
    signal input in;
    signal output out <== Inc()(in);
}
component main = Main();
