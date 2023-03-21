# Analysis Passes

### Side-effect free assignment

An assigned value which does not contribute either directly or indirectly to a constraint, or a function return value, typically indicates a mistake in the implementation of the circuit. For example, consider the following `BinSum` template from circomlib where we've changed the final constraint to introduce a bug.

```cpp
  template BinSum(n, ops) {
      var nout = nbits((2 ** n - 1) * ops);
      var lin = 0;
      var lout = 0;

      signal input in[ops][n];
      signal output out[nout];

      var e2 = 1;
      for (var k = 0; k < n; k++) {
          for (var j = 0; j < ops; j++) {
              lin += in[j][k] * e2;
          }
          e2 = e2 + e2;
      }

      e2 = 1;
      for (var k = 0; k < nout; k++) {
          out[k] <-- (lin >> k) & 1;
          out[k] * (out[k] - 1) === 0;

          lout += out[k] * e2;  // The value assigned here is not used.
          e2 = e2 + e2;
      }

      lin === nout;  // Should use `lout`, but uses `nout` by mistake.
  }
```

Here, `lout` no longer influences the generated circuit, which is detected by Circomspect.

### Shadowing variable

A shadowing variable declaration is a declaration of a variable with the same name as a previously declared variable. This does not have to be a problem, but if a variable declared in an outer scope is shadowed by mistake, this could change the semantics of the program which would be an issue.

For example, consider this function which is supposed to compute the number of bits needed to represent `a`.

```cpp
  function numberOfBits(a) {
      var n = 1;
      var r = 0;  // Shadowed variable is declared here.
      while (n - 1 < a) {
          var r = r + 1;  // Shadowing declaration here.
          n *= 2;
      }
      return r;
  }
```

Since a new variable `r` is declared in the while-statement body, the outer variable is never updated and the return value is always 0.

### Signal assignment

Signals should typically be assigned using the constraint assignment operator `<==`. This ensures that the circuit and witness generation stay in sync. If `<--` is used it is up to the developer to ensure that the signal is properly constrained. Circomspect will try to detect if the right-hand side of the assignment is a quadratic expression. If it is, the signal assignment can be rewritten using the constraint assignment operator `<==`.

However, sometimes it is not possible to express the assignment using a quadratic expression. In this case Circomspect will try to list all constraints containing the assigned signal to make it easier for the developer (or reviewer) to ensure that the variable is properly constrained.

The Tornado Cash codebase was originally affected by an issue of this type. For details see [the Tornado Cash disclosure](https://tornado-cash.medium.com/tornado-cash-got-hacked-by-us-b1e012a3c9a8).

### Under-constrained signal

Under-constrained signals are one of the most common issues in zero-knowledge circuits. Circomspect will flag intermediate signals that only occur in a single constraint. Since intermediate signals are not available outside the template, this typically indicates an issue with the implementation.

### Unused output signal

When a template is instantiated, the corresponding input signals must be constrained. This is typically also true for the output signals defined by the template, but if we fail to constrain an output signal defined by a template this will not be flagged as an error by the compiler. There are examples (like `Num2Bits` from Circomlib) where the template constrains the input and no further constraints on the output are required. However, in the general case, failing to constrain the output from a template indicates a potential mistake that should be investigated.

Circomspect will generate a warning whenever it identifies an instantiated template where one or more output signals defined by the template are not constrained. Each location can then be manually reviewed for correctness.

This type of issue [was identified by Veridise](https://medium.com/veridise/circom-pairing-a-million-dollar-zk-bug-caught-early-c5624b278f25) during a review of the circom-pairing library.

### Constant branching condition

If a branching statement condition always evaluates to either `true` or `false`, this means that the branch is either always taken, or never taken. This typically indicates a mistake in the code which should be fixed.

### Non-strict binary conversion

Using `Num2Bits` and `Bits2Num` from
[Circomlib](https://github.com/iden3/circomlib) to convert a field element to
and from binary form is only safe if the input size is smaller than the size of
the prime. If not, there may be multiple correct representations of the input
which could cause issues, since we typically expect the circuit output to be
uniquely determined by the input.

For example, suppose that we create a component `n2b` given by `Num2Bits(254)` and set the input to `1`. Now, both the binary representation of `1` _and_ the representation of `p + 1` (where `p` is the order of the underlying finite field) will satisfy the circuit over BN254, since both are 254-bit numbers. If you cannot restrict the input size below the prime size you should use the strict versions `Num2Bits_strict` and `Bits2Num_strict` to convert to and from binary representation. Circomspect will generate a warning if it cannot prove (using constant propagation) that the input size passed to `Num2Bits` or `Bits2Num` is less than the size of the prime in bits.

### Unconstrained less-than

The Circomlib `LessThan` template takes an input size as argument. If the individual input signals are not constrained to be non-negative (for example using the Circomlib `Num2Bits` circuit), it is possible to find inputs `a` and `b` such that `a > b`, but `LessThan` still evaluates to true when given `a` and `b` as inputs.

For example, consider the following template which takes a single input signal
and attempts to constrain it to be less than two.

```cpp
  template LessThanTwo() {
    signal input in;

    component lt = LessThan(8);
    lt.in[0] <== in;
    lt.in[1] <== 2;

    lt.out === 1;
  }
```

Suppose that we define the private input `in` as `p - 254`, where `p` is the prime order of the field. Clearly, `p - 254` is not less than two (at least not when viewed as an unsigned integer), so we would perhaps expect `LessThanTwo` to fail. However, looking at [the implementation](https://github.com/iden3/circomlib/blob/cff5ab6288b55ef23602221694a6a38a0239dcc0/circuits/comparators.circom#L89-L99) of `LessThan`, we see that `lt.out` is given by

```cpp
    1 - n2b.out[8] = 1 - bit 8 of (p - 254 + (1 << 8) - 2) = 1 - 0 = 1.
```

It follows that `p - 254` satisfies `LessThanTwo()`, which is probably not what we expected. Note that, `p - 254` is equal to -254 which _is_ less than two, so there is nothing wrong with the Circomlib `LessThan` circuit. This may just be unexpected behavior if we're thinking of field elements as unsigned integers.

Circomspect will check if the inputs to `LessThan` are constrained to be strictly less than `log(p) - 1` bits using `Num2Bits`. This guarantees that both inputs are non-negative, which avoids this issue. If it cannot prove that both inputs are constrained in this way, a warning is generated.

### Unconstrained division

Since division cannot be expressed directly using a quadratic constraint, it is common to use the following pattern to ensure that the signal `c` is equal to `a / b`.

```cpp
    c <-- a / b;
    c * b === a;
```

This forces `c` to be equal to `a / b` during witness generation, and checks that `c * b = a` during proof verification. However, the statement `c = a / b` only makes sense when `b` is non-zero, whereas `c * b = a` may be true even when `b` is zero. For this reason it is important to also constrain the divisor `b` to ensure that it is non-zero when the proof is verified.

Circomspect will identify signal assignments on the form `c <-- a / b` and ensure that the expression `b` is constrained to be non-zero using the Circomlib `IsZero` template. If no such constraint is found, a warning is emitted.

### BN254 specific circuit

Circom defaults to using the BN254 scalar field (a 254-bit prime field),
but it also supports BSL12-381 (which has a 255-bit scalar field) and
Goldilocks (with a 64-bit scalar field). However, since there are no constants denoting either the prime or the prime size in bits available in the Circom language, some Circomlib templates like `Sign` (which returns the sign of the input signal), and `AliasCheck` (used by the strict versions of `Num2Bits` and `Bits2Num`), hardcode either the BN254 prime size or some other constant related to BN254. Using these circuits with a custom prime may thus lead to unexpected results and should be avoided.

Circomlib templates that may be problematic when used together with curves other than BN254 include the following circuit definitions. (An `x` means that the template should not be used together with the corresponding curve.)

| Template                  | Goldilocks (64 bits) | BLS12-381 (255 bits) |
| :------------------------ | :------------------: | :------------------: |
| `AliasCheck`              |           x          |           x          |
| `BabyPbk`                 |           x          |                      |
| `Bits2Num_strict`         |           x          |           x          |
| `Num2Bits_strict`         |           x          |           x          |
| `CompConstant`            |           x          |           x          |
| `EdDSAVerifier`           |           x          |           x          |
| `EdDSAMiMCVerifier`       |           x          |           x          |
| `EdDSAMiMCSpongeVerifier` |           x          |           x          |
| `EdDSAPoseidonVerifier`   |           x          |           x          |
| `EscalarMulAny`           |           x          |                      |
| `MiMC7`                   |           x          |                      |
| `MultiMiMC7`              |           x          |                      |
| `MiMCFeistel`             |           x          |                      |
| `MiMCSponge`              |           x          |                      |
| `Pedersen`                |           x          |                      |
| `Bits2Point_strict`       |           x          |           x          |
| `Point2Bits_strict`       |           x          |           x          |
| `PoseidonEx`              |           x          |                      |
| `Poseidon`                |           x          |                      |
| `Sign`                    |           x          |           x          |
| `SMTHash1`                |           x          |                      |
| `SMTHash2`                |           x          |                      |
| `SMTProcessor`            |           x          |           x          |
| `SMTProcessorLevel`       |           x          |                      |
| `SMTVerifier`             |           x          |           x          |
| `SMTVerifierLevel`        |           x          |                      |

### Overly complex function or template

As functions and templates grow in complexity they become more difficult to review and maintain. This typically indicates that the code should be refactored into smaller, more easily understandable, components. Circomspect uses cyclomatic complexity to estimate the complexity of each function and template, and will generate a warning if the code is considered too complex. Circomspect will also generate a warning if a function or template takes too many arguments, as this also impacts the readability of the code.

### Bitwise complement

Circom supports taking the 256-bit complement `~x` of a field element `x`. Since the result is reduced modulo `p`, it will typically not satisfy the expected relations `(~x)ᵢ == ~(xᵢ)` for each bit `i`, which could lead to surprising results.

### Field element arithmetic

Circom supports a large number of arithmetic expressions. Since arithmetic expressions can overflow or underflow in Circom it is worth paying extra attention to field arithmetic to ensure that elements are constrained to the correct range.

### Field element comparison

Field elements are normalized to the interval `(-p/2, p/2]` before they are compared, by first reducing them modulo `p` and then mapping them to the correct interval by subtracting `p` from the value `x`, if `x` is greater than `p/2`. In particular, this means that `p/2 + 1 < 0 < p/2 - 1`. This can be surprising if you are used to thinking of elements in `GF(p)` as unsigned integers.
