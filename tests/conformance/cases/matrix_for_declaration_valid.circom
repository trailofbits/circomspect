pragma circom 2.2.3;
template Child(){signal input in; signal output out; out <== in;}
template Main(){signal input a; signal output out; var x=1;
for (var i = 0; i < 2; i++) {x += i;}
out <== 1;
}
component main = Main();
