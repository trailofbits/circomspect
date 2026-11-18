pragma circom 2.1.4;

include "resolved_library.circom";

template UsesLoadedLibrary() {
    var value = KnownFunction(1);
    component child = KnownTemplate();
    signal output out;
    out <== child.out + value;
}
