pragma circom 2.2.3;
function F)(x){return x;}
template Main(){signal output out; out <== F(1);}
component main = Main();