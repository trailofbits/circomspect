pragma circom 2.1.4;
template Main() {
    signal input in;
    signal inv;
    signal output out;
    inv <-- 1 / in;
    in * inv === 1;
    out <-- 1 / in;
}
component main = Main();
