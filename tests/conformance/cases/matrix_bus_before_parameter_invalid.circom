pragma circom 2.2.3;
bus B(n){signal x[n];}
template Main(){input B(2)) v; signal output out; out <== 1;}
component main = Main();