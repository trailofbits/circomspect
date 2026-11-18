pragma circom 2.2.3;
bus B{signal x;}
template Main(){B b; signal output out; out <== 1;}
component main = Main();