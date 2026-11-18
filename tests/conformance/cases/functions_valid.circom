pragma circom 2.2.3;
function Inc(x){
    return x + 1;
}
template Main(){
    signal output out;
    out <== Inc(2);
}
component main = Main();
