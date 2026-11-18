pragma circom 2.2.3;
bus Pair({
    signal x; signal y;
}
template Main(){
    input Pair p; signal output out; out <== p.x + p.y;
}
component main = Main();
