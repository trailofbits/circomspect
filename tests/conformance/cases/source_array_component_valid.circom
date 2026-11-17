pragma circom 2.2.3;

template BitwiseOr(m) {
    signal input a[m];
    signal input b[m];
    signal output out[m];
    for (var i = 0; i < m; i++) {
        out[i] <== a[i] + b[i] - a[i] * b[i];
    }
}

template OrMultiple(n, m) {
    signal input inputs[n][m];
    signal output out[m];
    signal mids[n][m];
    mids[0] <== inputs[0];
    component ors[n - 1];
    for (var i = 0; i < n - 1; i++) {
        ors[i] = BitwiseOr(m);
        ors[i].a <== mids[i];
        ors[i].b <== inputs[i + 1];
        mids[i + 1] <== ors[i].out;
    }
    out <== mids[n - 1];
}

component main = OrMultiple(2, 2);
