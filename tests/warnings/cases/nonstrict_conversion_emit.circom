pragma circom 2.1.4;
template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc = 0;
    var power = 1;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in \ power) % 2;
        out[i] * (out[i] - 1) === 0;
        lc += out[i] * power;
        power += power;
    }
    lc === in;
}
template Main() {
    signal input in;
    signal output out;
    component bits = Num2Bits(254);
    bits.in <== in;
    out <== bits.out[0];
}
component main = Main();
