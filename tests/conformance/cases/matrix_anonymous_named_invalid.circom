pragma circom 2.2.3;
function F(x){return x;}
template Child(){signal input in; signal output out; out <== in;}
bus B(){signal x;}
template Main(){signal input a[2]; B b; signal output out; out <== Child()(in <==) 1);}
component main = Main();
