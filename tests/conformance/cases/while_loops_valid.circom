pragma circom 2.2.3;
template Main(){
    var i = 0;
    while(i < 2){
        i++;
    }
    signal output out;
    out <== i;
}
component main = Main();
