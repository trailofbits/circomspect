pragma circom 2.1.4;
template Many(a, b, c, d, e, f, g) {
    signal output out;
    out <== a;
}
template Main() {
    signal output out;
    component c = Many(1, 2, 3, 4, 5, 6, 7);
    out <== c.out;
}
component main = Main();
