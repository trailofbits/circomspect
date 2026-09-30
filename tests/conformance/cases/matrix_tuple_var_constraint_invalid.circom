pragma circom 2.2.3;
template Child(){signal output out; out <== 1;}
bus B(){signal x;}
template Main(){
var (v,w) <==) (1,2);
signal output out; out <== 1;
}
component main = Main();
