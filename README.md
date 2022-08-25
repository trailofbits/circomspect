# Circomspect 🔎
Circomspect is a static analyzer and linter for the [Circom](https://github.com/iden3/circom) programming language. The codebase borrows heavily from the Rust Circom compiler built by [iden3](https://github.com/iden3).

Circomspect currently implements a number of analysis passes which can identify potential issues in Circom circuits. It is our goal to continue to add new analysis passes to be able to detect more issues in the future.

<img src="doc/circomspect.png" alt="Output example image" width="1200"/>


## Building Circomspect

To build circomspect, simply clone the repository and build the project by invoking `cargo build` in the project root.

```sh
  git clone https://github.com/trailofbits/circomspect
  cd circomspect
  cargo install --path cli
```


## Running Circomspect

To run circomspect on a file or directory, simple run

```sh
  circomspect path/to/circuit
```

To get more (or less) verbose output you can set the output level using the `--output-level` flag. To output the results to a Sarif file (which can be read by the [VSCode Sarif Viewer](https://marketplace.visualstudio.com/items?itemName=MS-SarifVSCode.sarif-viewer)), use the flag `--sarif-file`.


<img src="doc/vscode.png" alt="VSCode example image" width="1200" />

## Analysis Passes

The project currently implements analysis passes for the following types of issues.

#### 1. Shadowing variable declarations (Warning)

A shadowing variable declaration is a declaration of a variable with the same name as a previously declared variable. This does not have to be a problem, but if a variable declared in an outer scope is shadowed by mistake, this could change the semantics of the program which would be an issue.

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
_Figure 1.1: Since a new variable is declared in the while-statement body, the outer variable is never updated._


#### 2. Unused variable assignments (Warning)

An unused assignment typically indicates a logical mistake in the code and merits further attention.

```js
  template BinSum(n, ops) {
      signal input in[ops][n];
      signal output out[nout];

      var lin = 0;
      var lout = 0;
      var nout = nbits((2 ** n - 1) * ops);

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

          lout += out[k] * e2;  // The value assigned here is never read.
          e2 = e2 + e2;
      }

      lin === nout;  // Should use `lout`, but uses `nout` by mistake.
  }
```
_Figure 2.1: Here, `out` is not properly constrained because of a typo on the last line of the function._


#### 3. Signal assignments using the signal assignment operator (Warning)

Signals should typically be assigned using the constraint assignment operator `<==`. This ensures that the circuit and witness generation stay in sync. If `<--` is used it is up to the developer to ensure that the signal is properly constrained.


#### 4. Branching statement conditions that evaluate to a constant value (Warning)

If a branching statement condition always evaluates to either `true` or `false`, this means that the branch is either always taken, or never taken. This typically indicates a mistake in the code which should be fixed.

#### 5. Use of the non-strict versions of `Num2Bits` and `Bits2Num` (Warning)

Using `Num2Bits` to convert a field element to binary form is only safe if the
input size is smaller than the size of the prime. If not, there may be multiple
correct representations of the input which could cause issues, since we
typically want the output to be uniquely determined by the input.

For example, Suppose that we create a component `n2b` given by `Num2Bits(254)` and set the input to `1`. Now, both the binary representation of `1` _and_ the representation of `p + 1` will satisfy the circuit, since both are 254-bit numbers. If you cannot restrict the input size below 254 bits you should use the strict versions `Num2Bits_strict` and `Bits2Num_strict` to convert to and from binary.

#### 6. Bitwise complement of field elements (Informational)

Circom supports taking the 256-bit complement `~x` of a field element `x`. Since the result is reduced modulo `p`, it will typically not satisfy the expected relations `(~x)ᵢ == ~(xᵢ)` for each bit `i`, which could lead to surprising results.


#### 7. Field element arithmetic (Informational)

Circom supports a large number of arithmetic expressions. Since arithmetic expressions can overflow or underflow in Circom it is worth paying extra attention to field arithmetic to ensure that elements are constrained to the correct range.


#### 8. Field element comparisons (Informational)

Field elements are normalized to the interval `(-p/2, p/2]` before they are compared, by first reducing them modulo `p` and then mapping them to the correct interval by subtracting `p` from the value `x`, if `x` is greater than `p/2`. In particular, this means that `p/2 + 1 < 0 < p/2 - 1`. This can be surprising if you are used to thinking of elements in `GF(p)` as unsigned integers.
