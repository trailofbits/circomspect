pragma circom 2.2.3;
function F(x,y)){return x+y;}
template Main(){signal output out; out <== F(1,2);}
component main = Main();