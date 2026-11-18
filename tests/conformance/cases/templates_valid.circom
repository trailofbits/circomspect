pragma circom 2.2.3;
template Child(){
    signal output out;
    out <== 1;
}
template Main(){
    signal output out;
    component c = Child();
    out <== c.out;
}
component main = Main();
