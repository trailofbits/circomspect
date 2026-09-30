pragma circom 2.1.4;

function OnlyFunction() {
    return 1;
}

function Parameter(x) {
    return x;
}

template Child(n) {
    signal output out;
    out <== n;
}

template UsesWrongTarget() {
    component child = OnlyFunction();
    signal output out;
    out <== 1;
}

template UsesValidTargets() {
    component child = Child(Parameter(1));
    signal output out;
    out <== child.out;
}

template UsesParallelWrongTarget() {
    component child = parallel OnlyFunction();
}
