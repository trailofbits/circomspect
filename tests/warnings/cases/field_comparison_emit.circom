pragma circom 2.1.4;
template Main() {
    signal output out;
    out <-- (21888242871839275222246405745257275088696311157297823662689037894645226208582 < 1);
}
component main = Main();
