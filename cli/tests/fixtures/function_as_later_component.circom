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
    component child;
    child = OnlyFunction();
}

template UsesWrongArrayTarget() {
    component child[1];
    child[0] = parallel OnlyFunction();
}

template UsesValidTarget() {
    component child;
    child = Child(Parameter(1));
    var value = OnlyFunction();
}

template ScopedVarCall() {
    component child;
    {
        var child = OnlyFunction();
    }
    child = Child(Parameter(1));
}
