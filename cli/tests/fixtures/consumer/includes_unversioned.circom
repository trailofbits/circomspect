pragma circom 2.1.4;

include "unversioned_library.circom";

template UsesUnversionedLibrary() {
    component child = IncludedWithoutVersion();
    signal output out;
    out <== child.out;
}
