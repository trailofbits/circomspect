# Analysis passes

Circomspect analyzes Circom 2.2.3 source, including libraries without a `main`
component. Findings use validated source, control flow, and call-context
facts. A warning describes the property established by that analysis; it does
not establish that a circuit is exploitable. Incomplete analysis is reported
separately as `CS0020`.

## Side-effect-free assignment

`CS0008` reports an assigned local value whose evaluation can be removed and
which reaches no return, output, constraint, or required witness effect.
Function calls need complete effect summaries. Unknown calls, potentially
failing evaluations, symbolic aliases, and observable effects prevent this
finding.

## Unused variable or parameter

`CS0006` reports an assigned local value that is never read before overwrite
or exit, or an internal signal with no read or generated-constraint use.
`CS0007` reports an unused parameter. These are use findings: an unread return
value can be reported even when evaluating its function has side effects.

## Shadowing variable

`CS0001` identifies a declaration that hides an outer symbol. `CS0002`
identifies a parameter-name collision. Resolution uses lexical scopes and
keeps distinct symbols separate.

## Signal assignment

`CS0005` identifies a reachable witness-only assignment to an exact observable
signal with zero incidence in the complete generated constraint closure.
`<--` computes a witness value but creates no constraint. Propagating a
constant through `<--` does not prove that constraints fix that value.

## Redundant witness assignment

`CS0021` reports that the normalized equation of a witness assignment is
already generated on every reachable path. It requires source-valid,
quadratic equations with matching access paths and retained source evidence.
The finding does not recommend changing the assignment operator.

The former `CS0013` diagnostic has been removed.

## Unconstrained signal

`CA01` reports an exact internal signal access with zero generated-constraint
incidence across a complete dependency closure. It does not claim that one
constraint is enough to determine a signal, or that a satisfying witness
exists. Symbolic aliases and incomplete component effects cause abstention.

The former `CS0017` occurrence-count heuristic has been removed.

## Unused output signal

`CS0018` reports an exact component output that has no read or constraint use
in a complete, finite project rooted at `main`. Exported main outputs count
as environment reads. Component readiness, input bindings, nested instances,
array indices, and all consumers are checked. A library's uninstantiated
output cannot be called unused.

## Constant branch condition

`CS0009` reports a condition with the same definite Boolean value on every
reachable execution in the analyzed context. Concrete main and call arguments
can establish a value; a symbolic library parameter alone cannot.

## Non-strict binary conversion

`CS0010` requires a validated bit-decomposition relation and two distinct bit
representations of the same field value that satisfy the analyzed generated
constraints. Template names do not establish conversion behavior. Unknown
widths, unresolved caller restrictions, and incomplete models cause
abstention.

Called conversions currently support a main template with one completed leaf
component, a scalar input, and a one-dimensional bit output. Both candidate
models must satisfy every checked caller and child equation. Generated caller
constraints can therefore prevent a finding. Deeper or additional component
dependencies require further analysis and produce scoped incompleteness.

## Unconstrained less-than

`CS0014` requires a validated comparator relation and an input fixed by a
generated equality outside the proven safe range. It reports the input and
bound. A familiar comparator name or witness-only constant does not establish
this property.

The supported closure has one main template, one comparator, and one bit
conversion child. The comparator has two input elements and uses a validated
`a + 2^n - b` relation with an ordered `n + 1` bit decomposition; `2^(n+1)`
must be smaller than the field prime. A complete satisfying assignment checks
every generated equation in all three scopes. Additional component dependencies
or unsupported guards prevent this finding.

## Unconstrained division

`CS0015` reports a reachable witness division whose exact input divisor has
zero incidence in a complete generated-constraint closure. The message states
that no generated constraint excludes zero; it does not claim that a
satisfying zero-divisor witness exists. Any possible generated dependency or
incomplete call closure prevents the finding.

The supported called case has one main template and one completed leaf
component with scalar inputs initialized by witness-only assignments from
constants or external main inputs. Related parent constraints, incomplete
initialization, internal witness aliases, and deeper calls prevent this claim.

## BN254-specific circuit

`CS0016` reports a reachable hard-coded BN254 assumption incompatible with
the selected curve. Evidence includes the literal and relevant call path.
Names of templates and libraries are not trusted summaries.

## Overly complex function or template

`CS0011` reports certified cyclomatic complexity above 20, computed as
`E - N + 2P` over reachable control flow. `CS0012` reports more than seven
parameters in a validated function or template header.

## Bitwise complement

`CS0004` reports the selected curve's bitwise-complement and field-reduction
semantics as informational output. The bit width depends on the selected
field; it is not always 256 bits.

## Field element arithmetic

`CS0004` also reports certified modular wraparound at an arithmetic expression.
Unknown values do not justify a wraparound finding. Use `--level info` to see
informational results.

## Field element comparison

`CS0003` reports a comparison for which certified operands give different
signed Circom and unsigned orderings. Circom maps canonical residues greater
than half the prime to negative integers for comparisons.

## Incomplete analysis

`CS0020` explains a check the analyzer could not complete. Each displayed notice
identifies the affected source location, names the affected checks when known,
and gives a reason and a next action. It does not identify a circuit defect.

Missing-context notices are informational. For example, when a check depends on
an unknown library parameter, the notice names that parameter and suggests
analyzing a caller that supplies it. This may improve analysis of that instance;
it does not prove the library correct for every parameter value. Libraries do
not need a `main` component. Use `-l INFO` to see these notices; the default
`WARNING` threshold hides them.

Concrete unsupported constructs and analysis limits remain warnings when the
analyzer can provide a useful explanation and action. An explanation that would
only say that information is unavailable is omitted, even at `INFO`. Syntax and
semantic errors remain errors; they do not generate redundant generic coverage
notices. Internal analyzer failures are reported separately as analyzer errors.

Repeated reports of the same source issue are grouped. Distinct messages,
locations and supporting evidence remain separate. Related locations retain
the affected call paths; numbered contexts and call steps distinguish multiple
paths without repeating the warning. A finding in one instance does not imply
that every instance has the same issue.

Source errors and certified findings appear during analysis, before later scopes
are analyzed. If later callers add evidence to an existing finding, a final
`Additional call paths` note links the complete paths to that finding's code and
source location. This note is not counted as another finding and follows the
original finding's filters. Coverage notices are emitted after their causes and
affected checks have been aggregated. SARIF retains complete grouped reports in
source order, independently of terminal arrival order.

The final summary separates source errors, findings, analysis notes and analysis
limitations. It counts only visible reports. `--allow CS0020` hides coverage
notices, and `--level error` hides warnings and informational results. Hidden
notices do not affect exit status; as with other report types, a visible notice
causes a failure exit status. No findings reported does not mean that the code
has been proved safe or that every check completed.
