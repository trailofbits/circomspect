# Release Notes

## v0.8.1 (2023-03-21)

-   Updated dependencies flagged by cargo-audit.

## v0.8.0 (2023-03-21)

### Features

-   Circomspect will now only report findings for potential issues in the files
    specified on the command line. (It will still attempt to parse included
    files, but these will only be used to inform the analysis of the files
    specified by the user.)
-   Added support for tags, tuples, and anonymous components. Circomspect now
    supports Circom versions 2.0.0 - 2.1.4.
-   Added templates to the `bn254-specific-circuits` analysis pass.
-   Added `unused-output-signal` analysis pass.
-   All uses of the name BN128 have been replaced with BN254.

### Bug fixes

-   Rewrote the `unconstrained-less-than` analysis pass to better capture the
    underlying issue.
-   Fixed an issue where the cyclomatic complexity calculation could underflow
    in some cases in the `overly-complex-function-or-template` analysis pass.
-   Fixed an issue in the Sarif export implementation where reporting
    descriptors were added multiple times.

## v0.7.2 (2022-12-01)

### Features

-   Added a URL to the issue description for each output.

### Bug Fixes

-   Rewrote description of the unconstrained less-than analysis pass, as the
    previous description was too broad.
-   Fixed grammar in the under-constrained signal warning message.

## v0.7.0 (2022-11-29)

### Features

-   New analysis pass (`unconstrained-less-than`) that detects uses of the
    Circomlib `LessThan` template where the input signals are not constrained
    to be less than the bit size passed to `LessThan`.
-   New analysis pass (`unconstrained-division`) that detects signal
    assignments containing division, where the divisor is not constrained to be
    non-zero.
-   New analysis pass (`bn254-specific-circuits`) that detects uses of
    Circomlib templates with hard-coded BN254-specific constants together with
    a custom curve like BLS12-381 or Goldilocks.
-   New analysis pass (`under-constrained-signal`) that detects intermediate
    signals which do not occur in at least two separate constraints.
-   Rule name is now included in Sarif output. (The rule name is now also
    displayed by the VSCode Sarif extension.)
-   Improved parsing error messages.

### Bug Fixes

-   Fixed an issue during value propagation where values would be propagated to
    arrays by mistake.
-   Fixed an issue in the `nonstrict-binary-conversion` analysis pass where
    some instantiations of `Num2Bits` and `Bits2Num` would not be detected.
-   Fixed an issue where the maximum degree of switch expressions were
    evaluated incorrectly.
-   Previous versions could take a very long time to complete value and degree
    propagation. These analyses are now time boxed and will exit if the
    analysis takes more than 10 seconds to complete.
