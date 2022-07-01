pragma circom 2.0.0;

template ConstantConditional(n) {
    signal input in;
    signal output out;
    var value = 1023;
    var bound = value + 1;
    if (((value + 2) / 2) < bound) {
      value = 0;
    } else {
      value += 1;
    }
    out === in * in + value;
}

component main {public [in]} = ConstantConditional(16);
