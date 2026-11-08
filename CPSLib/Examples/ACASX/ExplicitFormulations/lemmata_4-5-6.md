# STTT17 Lemmas 4, 5, and 6

[Proof.lean](Proof.lean) proves corrected versions of the region lemmas from
Sections 5.2-5.3 and Figures 10/12, using definitions in [Model.lean](Model.lean)
and the base ACASX proofs. [Challenge.lean](Challenge.lean) states the targets,
including Lemmas 1–3. The bounded and safeable lemmas use initial clock `0`.
[Counterexample.lean](Counterexample.lean) contains the source variants and checked
counterexamples.
The benchmark config declares the base ACASX Model and Proof as trusted dependencies;
the harness copies them at their original module paths into the benchmark snapshot.

| Lemma | Theorem | Result |
|---|---|---|
| 4 | `bounded_regions_equivalent` | Hatted explicit and implicit bounded regions agree. |
| 5 | `endpoint_cases_redundant` | Safe follow-ups imply endpoint bounds 15/16. |
| 6 | `safeable_regions_equivalent` | Explicit and implicit safeable regions agree. |

All three have proofs without `sorry`. These results concern the corrected Lean
statements; they do not establish a successful replay of the KeYmaera supplement.
Some changes already occur in the supplement, while the Lean endpoint checks go
further. In particular, the Lean Lemma 4 is not an exact transcription of the
formula loaded by the supplied Scala proof script.

## Lemmas 5 and 6 in the supplement

The supplement corrects several expressions used by the Lean statements: the
[lower `.kyx`][bounded-lower] uses the terminal velocity in bound 15, and
`condImplSafeableLo` / `condImplSafeableUp` in [safeable Scala][safeable-scala]
use the initial velocity in both accelerating endpoint heights. The upper
follow-up also uses the upper escape target and reversed sense. The Lean model
comments identify these sources; upper terminal velocity is normalized under
`(w = -1 ∨ w = 1)`, and the explicit-region lemmas specialize the initial clock to zero.

This is a match for those components, not a transcription of completed
supplementary Lemmas 5 and 6: [safeable Scala][safeable-scala] marks both lemmas
as TODO (lines 20-24) and defines the *implicit* safeable condition for Theorem 5.
It does not define or prove the explicit safeable-region equivalence. Lean's
explicit region also uses the bounded cases and endpoint corrections described
below. In particular, the supplement's lower case 5 cutoff is strict, whereas
the unhatted Lean case uses a non-strict cutoff; the equivalence discussed below
uses the additional hatted endpoint check and does not establish equivalence of
the unhatted parts in isolation.

## Corrections to the printed formulas

These are differences from Figs. 10/12 of the
[journal paper](../../../../keymaera/ACASX/STTT17-journal.pdf), not changes made to the
archived Scala or `.kyx` files. Write `T = tl - to` for the supplement's remaining
horizon. Since the Lean region lemmas start at clock zero, their `tl` is `T`.
Scala's `dhd`, `dhf`, `dhfM`, `a`, and `aM` correspond to Lean's `v`, `vlo`,
`vup`, `alo`, and `aup`.

| Location | Change in Lean | Already present in the supplement? | Reason |
|---|---|---|---|
| Fig. 10, `LimplBounded` | `< hp` becomes `< -hp`. | Yes. [Bounded-time Scala][bounded-scala], lines 42-50, uses `w*h < w*ho - hp`. | Correct lower separation. |
| Fig. 10, `bound15` | The linear term is `w * vlo * T`, replacing printed `w * v * T`. | Yes. [Lower `.kyx`][bounded-lower], line 93, uses `w*dhf*(tl-to)`. | After acceleration, the lower nominal trajectory has slope `vlo`. |
| Fig. 12, accelerating endpoints | Use `v * T` for both heights, replacing `vlo * T` / `vup * T`. | Yes. `condImplSafeableLo` and `condImplSafeableUp` in [safeable Scala][safeable-scala], lines 363-394, use `dhd*(tl-to)`. | Integrates the initial velocity during acceleration. |
| Fig. 10, cases 6/13 | Use strict horizon cutoffs, `r < -rp + rv*T`. | Yes. [Lower `.kyx`][bounded-lower], line 82, and [upper `.kyx`][bounded-upper], line 52. | Avoids spurious rejection at `rv = 0, r = -rp`; endpoint checks cover equality. |
| Fig. 10, lower hatted region | Require the horizon endpoint condition for every terminal-velocity sign. | No. [Lower `.kyx`][bounded-lower], lines 74-94, still places that condition inside `w*dhf < 0`. | The lower endpoint can be the worst point even when `w*vlo >= 0`; see the counterexample below. |
| Fig. 10, upper hatted region | Require the horizon endpoint condition for every terminal-velocity sign. | Partly. [Upper `.kyx`][bounded-upper], lines 42-65, already includes the endpoint in the positive-terminal-velocity branch, unlike the paper's nonpositive guard. Lean additionally checks it in the other branch. | Covers a horizon-truncated maximum; checks already implied by other cases are redundant. |

The lower supplement also uses a strict cutoff for case 5, whereas Lean retains
the printed non-strict cutoff there. At equality, the same height condition is
covered by the endpoint check in the negative-terminal-velocity branch.

The lower `.kyx` begins with an `UNFINISHED FILE` warning. This warning is relevant
provenance, but does not mean that no Lemma 4 proof script was supplied: the Scala
file explicitly contains such scripts, as described below.

## Equivalent normalizations and scope

Two changes are equivalent normalizations under the theorem assumptions:

- Bounds 15/16 use the model's switching-time partition; both height formulas
  agree at the switch.
- `v + w * maxI v w vup` equals `w * max (w * vup) (w * v)` for `(w = -1 ∨ w = 1)`, proved
  by `upper_speed` in the [base proof](../Proof.lean).

Lemma 5's upper follow-up uses the upper endpoint, reversed sense, and `vupEx`,
resolving the printed statement's ambiguous lower-target subscript. The same
choice appears in `condImplSafeableUp`, which calls the lower-region builder with
`-w` and `dhfUpExtr`. Initial clock zero is a specialization, not a correction.

## Counterexample to the supplied lower `.kyx` formula

The following state satisfies all assumptions of [bounded lower equivalence][bounded-lower]:

```text
hp = rp = rv = a = tl = w = 1
to = 0
r = 1/2
h = -2
dhd = -10
dhf = 0
```

Here `min(0,w*dhd) = -10`, `max(0,w*(dhf-dhd)) = 10`, and the remaining horizon
is `T = 1`. The explicit side accepts the state:

| Part of the explicit lower formula | Evaluation |
|---|---|
| Expired-horizon disjunct | False: `tl-to = 1`. |
| Nonnegative-target branch | Active: `w*dhf = 0`. |
| Case 1 | Its spatial test holds, but its horizon test is `1/2 <= 0`, which is false. |
| Case 2 | Its spatial test starts at `r >= 9`, which is false. |
| Case 3 | Its spatial test requires `r > 11`, which is false. |
| Case 4 | Its spatial test requires `r > 11`, which is false. |
| Negative-target branch, including the endpoint check | Inactive: `w*dhf < 0` is false. |

Every applicable implication therefore holds, without imposing a height bound.
The implicit side is false at this exact witness:

```text
t = 1, ro = 1, ho = -19/2

t <= tl-to                          holds: 1 <= 1
0 <= t < max(0,w*(dhf-dhd))/a       holds: 0 <= 1 < 10
ho = w*a/2*t^2 + dhd*t             holds: -19/2 = 1/2 - 10

abs(r-ro) > rp                     fails: 1/2 > 1
w*h < w*ho-hp                      fails: -2 < -21/2
```

Thus the explicit and implicit lower regions in the supplied formula are not
equivalent under ordinary real arithmetic. The corrected Lean endpoint condition
rejects this state by requiring the missing inequality `-2 < -21/2`.

The combined lower-or-upper equivalence does not escape this counterexample:
choose `aM = 1` and `dhfM = 0`. The explicit disjunction remains true because its
lower side is true. Its implicit upper side is also false, already at
`t = ro = ho = 0`, where both `abs(r) > rp` and `w*h > hp` fail. The combined
preconditions `aM >= a` and `to <= tl` hold.

These evaluations were checked with exact rational arithmetic. The Lean theorem
`printed_lower_hat_counterexample` proves a counterexample to the corresponding
`Printed` predicate at the same values. That theorem concerns the Lean predicate;
there is no parser-to-Lean equivalence certificate for the archived `.kyx` file.

## Why the Scala source can say "proved Lemma 4"

[AcasXSafeBoundedTime.scala][bounded-scala] contains executable proof tests:

- Lines 273-277 load the lower `.kyx` for Lemma 4a. Lines 510-512 call
  `proveBy`, assert `equivalence shouldBe 'proved`, and store the result.
- Lines 515-517 load the upper `.kyx` for Lemma 4b. Lines 831-834 similarly
  attempt the proof, assert that it is proved, and store it.
- Lines 837-921 combine the two equivalences into Lemma 4. Lines 925-1025
  provide an alternative composition used by the command-line `lemma4` mode.

The assertions express what must succeed when these tests run. Their presence in
the source is not a record that the tests passed for the supplied resources.
In particular, a sound proof checker cannot establish the exact lower formula
above under the same real-arithmetic semantics: it has a concrete counterexample.
The combined Scala test depends on the lower equivalence and does not independently
repair its missing endpoint condition.

The source also has reporting and caching details that matter when reading a log:

- [AcasXBase.scala][base-scala], lines 95-101, skips a prerequisite test when a
  lemma with its name is already in the database. When it does run the test, it
  uses `nilReporter` and prints `...done` without itself checking success or
  whether a lemma was stored. That message is not proof success. The combining
  test separately requires the prerequisite lemmas to be present.
- `lookupRememberedLemmas` is enabled in the same base class. A run can therefore
  reuse stored intermediate results rather than reconstruct every proof step.
- [AcasXRunner.scala][runner-scala], lines 168-193, prints separate succeeded,
  failed, and ignored test summaries. The shown code does not explicitly turn a
  nonempty failure list into a failing process exit code. A completed command,
  or its exit status alone, is insufficient evidence of proof success.

These are reasons to inspect actual test results, not evidence that a false
formula passed the prover. No successful replay of this exact Lemma 4 artifact
has been established here. The inspected extracted JAR-resource copies of the
lower and upper `.kyx` files are byte-identical to their adjacent supplement
copies; this does not identify the resource loaded during any historical run.

To resolve an apparent successful run, capture the actual parsed formula and its
resource, use a fresh lemma database, and inspect the prerequisite and final test
results with the intended KeYmaera X and Mathematica versions. A different runtime
resource or a failing test could explain the discrepancy. If the exact refuted
formula really receives an accepted closed proof, the parser, arithmetic tool,
and proof-checking path would need investigation. No such acceptance or soundness
defect has been demonstrated here.

## Checked counterexamples

[Counterexample.lean](Counterexample.lean) retains source variants in `Printed` and proves:

- `printed_lower_hat_counterexample` and `printed_upper_hat_counterexample`:
  missing endpoint checks can admit states outside the implicit bounded region.
- `printed_bound15_counterexample`: a safe follow-up need not satisfy the printed linear bound.
- `printed_safeable_endpoint_counterexample`: the printed explicit safeable region
  can disagree with the nominal implicit region.
- `printed_stationary_boundary_counterexample`: the non-strict cutoff can reject
  a safe stationary encounter; `corrected_stationary_boundary_example` accepts it.

The endpoint comparison does **not** refute Theorem 5's `NoNMAC` conclusion.
Collision safety, safeable-region preservation, and nonblocking are distinct claims.

[bounded-scala]: ../../../../keymaera/ACASX/STTT17-supplement/AcasXSafeBoundedTime.scala
[bounded-lower]: ../../../../keymaera/ACASX/STTT17-supplement/bounded_lower_equivalence.kyx
[bounded-upper]: ../../../../keymaera/ACASX/STTT17-supplement/bounded_upper_equivalence.kyx
[safeable-scala]: ../../../../keymaera/ACASX/STTT17-supplement/AcasXSafeable.scala
[base-scala]: ../../../../keymaera/ACASX/STTT17-supplement/AcasXBase.scala
[runner-scala]: ../../../../keymaera/ACASX/STTT17-supplement/AcasXRunner.scala
