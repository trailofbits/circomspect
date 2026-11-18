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
template LessThan(n) {
    signal input in[2];
    signal output out;
    component bits = Num2Bits(n + 1);
    bits.in <== in[0] + (1 << n) - in[1];
    out <== 1 - bits.out[n];
}
template Main() {
    signal output out;
    component cmp = LessThan(8);
    cmp.in[0] <== 21888242871839275222246405745257275088548364400416034343698204186575808495363;
    cmp.in[1] <== 1;
    out <== cmp.out;
}
component main = Main();
