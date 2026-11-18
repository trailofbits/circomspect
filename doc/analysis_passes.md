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
For a loop, the source comment identifies an unused final update when earlier
assigned values of that variable are read.
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

## Signal-dependent assert

`CS0023` identifies a reachable `assert` whose condition depends on a
witness value. Circom evaluates such assertions while generating a witness;
the assertion itself adds no R1CS constraint. A compile-time assertion on a
parameter is not reported. The rule suppresses a direct equality assertion
when a structurally equivalent generated equality must execute in the same
context. It does not prove that all other assertions lack an equivalent
constraint elsewhere, or that bypassing one yields an accepted proof.

## Unassigned output

`CS0024` checks declared template outputs, including library templates
without `main`. Missing witness assignments and missing generated constraints
produce separate warnings. A `<--` write satisfies the assignment check but
does not create a constraint. For arrays with concrete dimensions, the rule
checks individual elements. Loop indices certified at each write site are
resolved separately. Multiple elements missing assignments or constraints in
one output array produce one warning per issue type with the affected count.
Unresolved write indices, unknown dimensions, incomplete source, and arrays
above 10,000 elements cause scoped abstention. This rule checks
assignment and incidence, not unique determination by the full constraint
system. Custom and external templates are excluded.

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

## Unused public input

`CS0026` reports an explicit public input of `main` whose exact signal element has zero
generated-constraint incidence in the validated main context. Witness-only reads do not bind the
public value to the proof. Private inputs and libraries without a `main` are outside this rule.
Unknown dimensions, incomplete source, and uncertain constraint incidence cause abstention.
This rule establishes independence from generated constraints, not an application-level exploit.

## Alternate witness value

`CS0027` reports a witness-only assignment in a concrete, closed `main` scope when two checked
assignments use the same input values but give the witness target different values. The analyzer
derives the second root of a generated quadratic equation, completes generated assignments, and
checks every generated equation for both candidates. It samples simple input values and may miss
other counterexamples. Unsupported control flow, component closure, or source expressions cause
abstention; absence of this warning does not establish uniqueness.

## Non-injective bit packing

`CS0028` reports a checked collision when a main template constrains an input bit array to
Boolean values and reconstructs a scalar output as their ordered powers-of-two sum. The analyzer
constructs two different bit vectors whose integer values differ by the field modulus, completes
generated assignments, and verifies all generated equations for both vectors. It reports a
constraint-level collision, not a claim that the application accepts both encodings. Unknown
bit widths, additional constraints rejecting a candidate, and incomplete component closure
withhold the warning.

## Feasible zero divisor

`CS0029` reports a witness-only division in a closed `main` template when an exact scalar input
can be zero in a model of every generated constraint and the division site lies on the checked
generation path. The analyzer completes generated assignments and checks other witness-only
assignments before reporting. The division itself would fail at zero, so its witness assignment
is excluded from the candidate model. This rule currently handles direct division expressions
with an input signal denominator; unknown control, source, or component closure withholds the
warning. The existing unconstrained-division warning remains a separate zero-incidence check.

## Unproved binary tag

`CS0030` reports a scalar intermediate or output signal declared with `{binary}` when a checked
model gives it a value other than 0 or 1. The analyzer validates the model against every generated
constraint and witness-only assignment in a closed `main` template. It recognizes a direct Boolean
equation as a sufficient proof and checks inherited constraints through model validation. Input
tags are caller preconditions. Bus fields, arrays, custom templates, and unresolved component
closure are outside this check. The finite candidate search can miss counterexamples, so absence
of a warning does not prove that a tag is valid.

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

## Comparator precondition

`CS0025` examines direct anonymous `LessThan(n)([a,b])` calls with a
constrained two-element input and a known width. It reports a concrete
operand outside `[0, 2^n)` and distinguishes that from a witness-dependent
operand whose range this pass cannot establish. The latter is a review lead,
not proof of a counterexample: a caller may enforce a sufficient range.
This check recognizes the common `LessThan` interface by its template name;
it does not certify the callee's generated equations. `CS0014` remains the
name-independent, model-checked comparator violation rule. Other comparator
interfaces, explicit component bindings, and symbolic widths are not yet
covered by `CS0025`.

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

Generic notices about unsupported constructs or analysis limits are omitted,
even at `INFO`: they do not offer a specific way to improve the analysis. Syntax
and semantic errors remain errors; they do not generate redundant generic
coverage notices. Internal analyzer failures are reported separately as analyzer
errors. An omitted notice does not mean that the affected check succeeded.

Repeated reports of the same source issue are grouped. Distinct messages,
locations and supporting evidence remain separate. Related locations explain
the issue: for example, its input bindings, constraints or component instance.
Generic call histories are omitted. When parameter values help explain a finding,
a compact label such as `Observed for T(n = 0)` identifies an affected call.
Ordinary unused assignments and coverage notices do not carry call histories.
A finding in one instance does not imply that every instance has the same issue.

Source errors and certified findings appear during analysis, before later scopes
are analyzed. At `-l INFO`, an `Additional call paths` note supplies useful argument
contexts discovered after a finding was printed. Calling the same definition with
the same arguments through another path does not produce another note. These
notes do not count as findings and follow the original finding's filters.
Coverage notices are emitted after their causes and affected checks have been
aggregated. SARIF retains complete grouped reports, including useful argument
contexts and proof locations, in source order independently of terminal arrival
order.

The final summary separates source errors, findings, analysis notes and analysis
limitations. It counts only visible reports. `--allow CS0020` hides coverage
notices, and `--level error` hides warnings and informational results. Hidden
notices do not affect exit status; as with other report types, a visible notice
causes a failure exit status. No findings reported does not mean that the code
has been proved safe or that every check completed.
