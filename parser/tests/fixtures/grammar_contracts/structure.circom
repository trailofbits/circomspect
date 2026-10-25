pragma circom 2.2.3;
include "café.circom";
bus Bare { signal value; }
bus Empty() { signal value; }
template custom extern_c parallel T(n) {
    signal input {alpha,beta} a[2];
    input signal {gamma} b;
    signal output c <== 1;
    Bare input {tag} d;
    output Empty() {other} e;
    var (p,q) = (1,2);
    component (r,s);
    signal (u,v) <== (3,4);
    var x[2] = [1,2], y;
    component child = T(1);
    for (var i=0; i<2; i++) { x[i] = i; }
    for (y=0; y<2; y+=1) { assert(y); }
    while (y) { y--; }
    if (p) if (q) { log("é",p); } else { log(); }
    else { c === (p+q); }
    T(1)(a<==x[0],b<--d.value);
    T(1)(x[0],d.value);
}
template Omitted {}
template Explicit() {}
component main {public [a,b]} = parallel T(1);
