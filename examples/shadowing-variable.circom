pragma circom 2.0.0;

template ToBits(n) {
    signal input in;
    signal output out[n];
    var power = 1;
    var result = 0;
    for (var i = 0; i < n; i++) {
        // This declaration shadows the outer declaration of power.
        var power = 2;
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] - 1) === 0;
        result += out[i] * power;
        power = power + power;
    }
    // This declaration shadows the previous declaration of power.
    var power = 3;
    result === in;
}

component main {public [in]} = ToBits(256);
