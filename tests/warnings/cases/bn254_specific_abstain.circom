pragma circom 2.1.4;
template Main() {
    signal output out;
    component c = MaybeBN254();
    out <== c.out;
}
component main = Main();
