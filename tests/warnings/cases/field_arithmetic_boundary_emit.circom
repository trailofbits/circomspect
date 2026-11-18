pragma circom 2.1.4;
template Main() {
    signal output out;
    out <== 21888242871839275222246405745257275088548364400416034343698204186575808495616 + 2;
}
component main = Main();
