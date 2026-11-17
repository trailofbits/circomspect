pragma circom 2.2.3;

template Child() {
    signal input value;
    signal output out;
    out <== value + 1;
}

template Main() {
    signal input value;
    signal output first;
    signal output second;
    component child = parallel Child();
    child.value <== value;
    first <== child.out;
    second <== parallel Child()(value);
}

component main = Main();
