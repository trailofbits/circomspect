pragma circom 2.2.3;
template Main(){
    var a[2] = [1,2];
    signal output out;
    out <== a[0] + a[1];
}
component main = Main();
