pragma circom 2.2.3;
template Main(){
    signal input in[2;
    signal output out;
    out <== in[0] + in[1];
}
component main = Main();
