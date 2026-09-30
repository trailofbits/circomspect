pragma circom 2.2.3;
template Child(){signal input in; signal output out; out <== in;}
template Main(){signal input a; signal output out; var x=1;
if (1) x = 2; else x = 3;
out <== 1;
}
component main = Main();
