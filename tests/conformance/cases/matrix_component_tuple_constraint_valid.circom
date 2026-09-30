pragma circom 2.2.3;
template Child(){signal output out; out <== 1;}
bus B(){signal x;}
template Main(){
component (v,w) <== (Child(),Child());
signal output out; out <== 1;
}
component main = Main();
