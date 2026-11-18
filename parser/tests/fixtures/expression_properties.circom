pragma circom 2.2.3;
function Identity(n) { return n; }
template Child(n) { signal input in; signal output out; out <== in; }
template Other() { signal input in; signal output out; out <== in; }
template Properties(n) {
    signal input witness;
    var values[2] = [1,2];
    var index = Identity(n);
    var deferred = values[index] + (n ? -1 : 2);
    assert(deferred);
    if(witness) { var local = values[index]; log(local); }
    if(witness) { var called = Identity(1); }
    var missing = Missing(n);
    var anonymous = Child(n)(in <== witness);
    component child[2]; child[0] = Child(n);
    var prior = child[0].out;
    child[1] = Other();
    assert(prior);
}
