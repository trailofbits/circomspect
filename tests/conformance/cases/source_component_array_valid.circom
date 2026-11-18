pragma circom 2.2.3;

template Child() {
    signal input in;
    signal output out;
    out <== in;
}

template Main() {
    signal input in;
    signal output out;
    component children[2];
    children[0] = Child();
    children[1] = Child();
    children[0].in <== in;
    children[1].in <== in;
    out <== children[0].out + children[1].out;
}

component main = Main();
