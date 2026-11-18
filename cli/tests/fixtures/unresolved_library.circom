pragma circom 2.1.4;

function UsesMissingFunction(x) {
    return MissingFunction(MissingInner(x));
}

template UsesMissingTemplate() {
    component child = MissingTemplate();
}
