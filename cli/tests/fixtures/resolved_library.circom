pragma circom 2.1.4;

function KnownFunction(x) {
    return x;
}

template KnownTemplate() {
    signal output out;
    out <== 1;
}

template UsesKnownDefinitions() {
    var value = KnownFunction(1);
    component child = KnownTemplate();
    signal output out;
    out <== child.out + value;
}
