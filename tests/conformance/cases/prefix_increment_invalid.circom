pragma circom 2.2.3;
template Main(){var x=1; ++x; signal output out; out <== x;}
component main = Main();
