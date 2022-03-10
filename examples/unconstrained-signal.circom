pragma circom 2.0.0;

template ToBits(n) {
    signal input in;
    signal output out[n];
    var value = 0;
    var power = 1;
    var result = 0;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in >> i) & 1;
        // out[i] * (out[i] - 1) === 0;
        result += out[i] * power;
        power = power + power;
    }
    // The output is unconstrained.
    // result === in;
}

component main {public [in]} = ToBits(256);
