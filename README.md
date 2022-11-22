# Circomspect 🔎

![Crates.io badge](https://img.shields.io/crates/v/circomspect.svg) ![GitHub badge](https://github.com/trailofbits/circomspect/actions/workflows/ci.yml/badge.svg)

Circomspect is a static analyzer and linter for the [Circom](https://iden3.io/circom) programming language. The codebase borrows heavily from the Rust Circom compiler built by [iden3](https://github.com/iden3).

Circomspect currently implements a number of analysis passes which can identify potential issues in Circom circuits. It is our goal to continue to add new analysis passes to be able to detect more issues in the future.

![Circomspect example image](https://github.com/trailofbits/circomspect/raw/main/doc/circomspect.png)

## Installing Circomspect

Circomspect is available on [crates.io](https://crates.io/crates/circomspect) and can be installed by invoking

```sh
  cargo install circomspect
```

To build Circomspect from source, simply clone the repository and build the
project by running `cargo build` in the project root. To install from source, use

```sh
  cargo install --path cli
```


## Running Circomspect

To run Circomspect on a file or directory, simply run

```sh
  circomspect path/to/circuit
```

By default, Circomspect outputs warnings and errors to stdout. To see informational results as well you can set the output level using the `--level` option. To ignore certain types of results, you can use the `--allow` option together with the corresponding result ID. (The result ID can be obtained by passing the `--verbose` flag to Circomspect.)

To output the results to a Sarif file (which can be read by the [VSCode Sarif Viewer](https://marketplace.visualstudio.com/items?itemName=MS-SarifVSCode.sarif-viewer)), use the option `--sarif-file`.

![VSCode example image](https://github.com/trailofbits/circomspect/raw/main/doc/vscode.png)

Circomspect supports the same curves that Circom does: BN128, BLS12-381, and Ed448-Goldilocks. If you are using a different curve than the default (BN128) you can set the curve using the command line option `--curve`.

## Analysis Passes

The project currently implements analysis passes for the following types of issues.

#### Side-effect free assignments (Warning)

An assigned value which does not contribute either directly or indirectly to a constraint, or a function return value, typically indicates a mistake in the implementation of the circuit. For example, consider the following `BinSum` template from circomlib where we've changed the final constraint to introduce a bug.

```js
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


#### Shadowing variable declarations (Warning)

A shadowing variable declaration is a declaration of a variable with the same name as a previously declared variable. This does not have to be a problem, but if a variable declared in an outer scope is shadowed by mistake, this could change the semantics of the program which would be an issue.

For example, consider this function which is supposed to compute the number of bits needed to represent `a`.

```js
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


#### Signal assignments using the signal assignment operator (Warning)

Signals should typically be assigned using the constraint assignment operator `<==`. This ensures that the circuit and witness generation stay in sync. If `<--` is used it is up to the developer to ensure that the signal is properly constrained. Circomspect will try to detect if the right-hand side of the assignment is a quadratic expression. If it is, the signal assignment can be rewritten using the constraint assignment operator `<==`.

However, sometimes it is not possible to express the assignment using a quadratic expression. In this case Circomspect will try to list all constraints containing the assigned signal to make it easier for the developer (or reviewer) to ensure that the variable is properly constrained.

The Tornado Cash codebase was originally affected by an issue of this type. For details see the Tornado Cash disclosure [here](https://tornado-cash.medium.com/tornado-cash-got-hacked-by-us-b1e012a3c9a8).


#### Branching statement conditions that evaluate to a constant value (Warning)

If a branching statement condition always evaluates to either `true` or `false`, this means that the branch is either always taken, or never taken. This typically indicates a mistake in the code which should be fixed.


#### Use of the non-strict versions of `Num2Bits` and `Bits2Num` from Circomlib (Warning)

Using `Num2Bits` and `Bits2Num` from
[Circomlib](https://github.com/iden3/circomlib) to convert a field element to
and from binary form is only safe if the input size is smaller than the size of
the prime. If not, there may be multiple correct representations of the input
which could cause issues, since we typically expect the circuit output to be
uniquely determined by the input.

For example, suppose that we create a component `n2b` given by `Num2Bits(254)` and set the input to `1`. Now, both the binary representation of `1` _and_ the representation of `p + 1` will satisfy the circuit over BN128, since both are 254-bit numbers. If you cannot restrict the input size below the prime size you should use the strict versions `Num2Bits_strict` and `Bits2Num_strict` to convert to and from binary representation. Circomspect will generate a warning if it cannot prove (using constant propagation) that the input size passed to `Num2Bits` or `Bits2Num` is less than the size of the prime in bits.


#### Unconstrained input signals passed to `LessThan` from Circomlib (Warning)

The Circomlib `LessThan` template takes an input size as argument. If the individual input signals are not constrained to the input size (for example using the Circomlib `Num2Bits` circuit), it is possible to find inputs `a` and `b` such that `a > b`, but `LessThan` still evaluates to true when given `a` and `b` as inputs.

For example, consider the following template which takes a single input signal
and attempts to constrain it to be less than 256.

```js
  template IsByte() {
    signal input in;
    signal output out;

    component lt = LessThan(8);
    lt.in[0] <== in;
    lt.in[1] <== 256;

    out <== lt.out;
  }

  component main = IsByte()
```

Suppose that we define the private input `in` as 512. This would result in the constraints

```js
    component lt = LessThan(8);
    lt.in[0] <== 512;
    lt.in[1] <== 256;
```

Clearly 512 is not less than 256, so we would expect `IsByte` to return 0. However, looking at [the implementation of `LessThan`](https://github.com/iden3/circomlib/blob/cff5ab6288b55ef23602221694a6a38a0239dcc0/circuits/comparators.circom#L89-L99), we see that `lt.out` is given by `1 - n2b.out[8] = 1 - (`bit `8` of `512 + 256 - 256) = 1 - 0 = 1`. It follows that 512 actually satisfies `IsByte()`, which is not what we wanted.

Circomspect will check if the inputs to `LessThan` are constrained to the input size using `Num2Bits`. If it cannot prove that both inputs are constrained in this way, a warning is generated.


#### Divisor in signal assignment not constrained to be non-zero (Warning)

To ensure that a signal `c` is equal to `a / b` (where `b` is not constant), it is common to use a signal assignment to set `c <-- a / b` during witness generation, and then constrain `a`, `b`, and `c` to ensure that `c * b === a` during proof verification. However, the statement `c = a / b` only makes sense when `b` is not zero, whereas `c * b = a` may be true even when `b` is zero. For this reason it is important to also ensure that the divisor is non-zero when the proof is verified.

Circomspect will identify signal assignments on the form `c <-- a / b` and ensure that the expression `b` is constrained to be non-zero using the Circomlib `IsZero` template. If no such constraint is found, a warning is emitted.


#### Using BN128 specific templates together with custom primes (Warning)

Circom defaults to using the BN128 curve (defined over a 254-bit prime field),
but it also supports BSL12-381 (which is defined over a 381-bit field) and
Goldilocks (defined over a 448-bit prime field). However, since there are no constants denoting either the prime or the prime size in bits available in the Circom language, some Circomlib templates like `Sign` (which returns the sign of the input signal), and `AliasCheck` (used by the strict versions of `Num2Bits` and `Bits2Num`), hardcode either the BN128 prime size or some other constant related to BN128. Using these circuits with a custom prime may thus lead to unexpected results and should be avoided.

Circomlib templates that may be problematic when used together with curves other than BN128 include the following circuit definitions.

  1.  `Sign` (defined in `circuits/sign.circom`)
  2.  `AliasCheck` (defined in `circuits/aliascheck.circom`)
  3.  `CompConstant` (defined in `circuits/compconstant.circom`)
  4.  `Num2Bits_strict` (defined in `circuits/bitify.circom`)
  5.  `Bits2Num_strict` (defined in `circuits/bitify.circom`)
  6.  `Bits2Point_Strict` (defined in `circuits/bitify.circom`)
  7.  `Point2Bits_Strict` (defined in `circuits/bitify.circom`)
  8.  `SMTVerifier` (defined in `circuits/smt/smtverifier.circom`)
  9.  `SMTProcessor` (defined in `circuits/smt/smtprocessor.circom`)
  10. `EdDSAVerifier` (defined in `circuits/eddsa.circom`)
  11. `EdDSAPoseidonVerifier` (defined in `circuits/eddsaposeidon.circom`)
  12. `EdDSAMiMCSpongeVerifier` (defined in `circuits/eddsamimcsponge.circom`)


#### Overly complex functions or templates (Warning)

As functions and templates grow in complexity they become more difficult to review and maintain. This typically indicates that the code should be refactored into smaller, more easily understandable, components. Circomspect uses cyclomatic complexity to estimate the complexity of each function and template, and will generate a warning if the code is considered too complex. Circomspect will also generate a warning if a function or template takes too many arguments, as this also impacts the readability of the code.


#### Bitwise complement of field elements (Informational)

Circom supports taking the 256-bit complement `~x` of a field element `x`. Since the result is reduced modulo `p`, it will typically not satisfy the expected relations `(~x)ᵢ == ~(xᵢ)` for each bit `i`, which could lead to surprising results.


#### Field element arithmetic (Informational)

Circom supports a large number of arithmetic expressions. Since arithmetic expressions can overflow or underflow in Circom it is worth paying extra attention to field arithmetic to ensure that elements are constrained to the correct range.


#### Field element comparisons (Informational)

Field elements are normalized to the interval `(-p/2, p/2]` before they are compared, by first reducing them modulo `p` and then mapping them to the correct interval by subtracting `p` from the value `x`, if `x` is greater than `p/2`. In particular, this means that `p/2 + 1 < 0 < p/2 - 1`. This can be surprising if you are used to thinking of elements in `GF(p)` as unsigned integers.
