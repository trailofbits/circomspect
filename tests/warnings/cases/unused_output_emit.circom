pragma circom 2.1.4;
template Child(){
    signal output a;
    signal output b;
    a <== 1;
    b <== 2;
}
template Main() {
    signal output out;
    component c = Child();
    out <== c.a;
}
component main = Main();
