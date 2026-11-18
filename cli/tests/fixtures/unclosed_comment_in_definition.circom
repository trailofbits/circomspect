pragma circom 2.1.4;

template BeforeBrokenComment() {
    signal input in;
    signal output out;
    out <== in;
}

template BrokenByComment() {
    /* unfinished comment
