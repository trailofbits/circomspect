pragma circom 2.0.0;

template Multiplier(){
   signal input x;
   signal input y;
   signal output z;
   z <== x * y;
}

component main {public [x]} = Multiplier();
