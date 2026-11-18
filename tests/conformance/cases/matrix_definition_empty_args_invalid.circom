pragma circom 2.2.3;
function F()){return 1;}
template Main(){signal output out; out <== F();}
component main = Main();