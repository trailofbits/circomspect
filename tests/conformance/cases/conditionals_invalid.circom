pragma circom 2.2.3;
template Main(){
    signal output out;
    if(1 {
        out <== 1;
    }
    else {
        out <== 2;
    }
}
component main = Main();
