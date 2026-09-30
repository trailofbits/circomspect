pragma circom 2.1.4;
template Main() {
    signal input in;
    signal output out;
    component bits = Num2Bits(254);
    bits.in <== in;
    out <== bits.out[0];
}
component main = Main();
