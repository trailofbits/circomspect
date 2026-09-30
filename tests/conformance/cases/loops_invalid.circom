pragma circom 2.2.3;
template Main(){
    signal output out[2];
    for(var i = 0; i < 2; i++{
        out[i] <== i;
    }
}
component main = Main();
