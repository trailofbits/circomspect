pragma circom 2.2.3;
bus A(){
    signal x;
}
template Main(){
    input A a[3];
    output A b[3];
    b <== [a[2], a[0], a[1];
}
component main = Main();
