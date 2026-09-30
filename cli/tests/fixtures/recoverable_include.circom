pragma circom 2.1.4;
include "resolved_library.circom";

template BrokenIncludedConsumer() {
    var value = ;
}

template UsesIncludedTemplate() {
    component child = KnownTemplate();
    signal output out;
    out <== child.out;
}
