pragma circom 2.2.3;
template Main(){
    signal output out;
    out <== (3 & ) + (2 << 1) + (3 == 0 ? 1 : 0);
}
component main = Main();
