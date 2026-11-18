pragma circom 2.2.3;
template Main(){
    signal input ;
    signal output out;
    var x = 1;
    out <== in + x;
}
component main = Main();
