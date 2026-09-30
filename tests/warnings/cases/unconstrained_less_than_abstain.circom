pragma circom 2.1.4;
template Main() {
    signal output out;
    component cmp = LessThan(8);
    cmp.in[0] <== 1;
    cmp.in[1] <== 2;
    out <== cmp.out;
}
component main = Main();
