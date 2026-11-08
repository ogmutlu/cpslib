import CPSLib.Examples.ACASX.Model

/-!
# Safety specifications for aircraft advisories

The five controller specifications follow `ACASX.Model`: immediate response,
delayed response, two-sided advisories, bounded-time safety, and safeability.
A final specification relates planar horizontal motion to the reduced coordinate.

Each controller claim quantifies over every successful result in `SetM.run`,
including every permitted advisory, acceleration, finite cycle count, and continuous
stopping time. Zero cycles are included. Safety does not assert that an advisory
choice passes its test or that a positive-duration evolution is available.

The theorem bodies are challenges for the separate `CPSLib.Examples.ACASX.Proof`.
The existing declaration notes record which statements follow artifact corrections
or strengthen the paper's postconditions.
-/

open CPSLib

namespace ACASX

/-!
## Model 1: immediate response preserves the lower safe region

The initial advisory has a valid sense and lies in `Limpl`. `Bounds` supplies
nonnegative horizontal protection and closing speed, positive vertical protection,
and positive minimum response acceleration. Every result must both avoid a near
mid-air collision and retain `Limpl` for its returned state and advisory.
-/

/-- STTT17 Theorem 1, with the stronger postcondition (+ Limpl) from `acasx.kyx`. -/
theorem immediate_safe :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → (w = -1 ∨ w = 1) → Limpl rp hp rv alo r h v w vlo →
        ∀ res ∈ SetM.run (immediate rp hp rv alo r h v w vlo),
          NoNMAC rp hp res.r res.h ∧
            Limpl rp hp rv alo res.r res.h res.v res.w res.vlo := sorry

/-!
## Model 2: delayed response preserves its remaining-delay region

The delayed claim additionally assumes nonnegative adverse acceleration bound `ad`,
response delay `δ`, and segment bound `ε`. Starting in `Dimpl`, every result avoids
a near mid-air collision and satisfies the delayed region with its returned
remaining delay `res.d`. Thus the postcondition tracks the delay after flight,
rather than reusing its initial value.
-/

/-- STTT17 Theorem 2, with the stronger postcondition (+ Dimpl) from
`safe_delay_implicit.kyx` -/
theorem delayed_safe :
    ∀ rp hp rv alo ad δ ε r h v w vlo d,
      Bounds rp hp rv alo → (0 ≤ ad ∧ 0 ≤ δ ∧ 0 ≤ ε) → (w = -1 ∨ w = 1) →
      Dimpl rp hp rv alo ad r h v w vlo d →
        ∀ res ∈ SetM.run (delayed rp hp rv alo ad δ ε r h v w vlo d),
          NoNMAC rp hp res.r res.h ∧
            Dimpl rp hp rv alo ad res.r res.h res.v res.w res.vlo res.d := sorry

/-!
## Model 3: two-sided compliance prevents a collision

The two-sided claim assumes `alo ≤ aup` and starts in the union `Cimpl` of the
lower and upper safe regions. Every result must satisfy `NoNMAC`. This statement
asks only for collision avoidance; it does not include a safe-region conjunct
for the returned advisory.
-/

/-- STTT17 Theorem 3, also in `acasxtwosided.kyx`. -/
theorem two_sided_safe :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → (w = -1 ∨ w = 1) →
      Cimpl rp hp rv alo aup r h v w vlo vup →
        ∀ res ∈ SetM.run (twoSided rp hp rv alo aup r h v w vlo vup),
          NoNMAC rp hp res.r res.h := sorry

/-!
## Model 4: preserve safety for the remaining time horizon

The initial clock must be within its limit, unless a negative `tl` disables the
limit. Starting in `CimplBounded`, each result avoids a near mid-air collision,
retains a valid advisory sense and clock bound, and satisfies the bounded region
for the remaining horizon at `res.t`.

This claim assumes positive `aup` without requiring `alo ≤ aup`.
-/

/-- STTT17 Theorem 4, with weaker precondition (`0 < aup` instead of `alo ≤ aup`) and
stronger postcondition (+ valid sense, + CimplBounded), following `bounded_implicit.kyx`.
The paper version is equivalent to the case `t=0`. -/
theorem bounded_safe :
    ∀ rp hp rv alo aup tl r h v w vlo vup t,
      Bounds rp hp rv alo ∧ 0 < aup → (w = -1 ∨ w = 1) → (t ≤ tl ∨ tl < 0) →
      CimplBounded rp hp rv alo aup tl t r h v w vlo vup →
        ∀ res ∈ SetM.run (bounded rp hp rv alo aup tl r h v w vlo vup t),
          NoNMAC rp hp res.r res.h ∧ (res.w = -1 ∨ res.w = 1) ∧ (res.t ≤ tl ∨ tl < 0) ∧
          CimplBounded rp hp rv alo aup tl res.t res.r res.h res.v res.w res.vlo res.vup
            := sorry

/-!
## Model 5: preserve the possibility of a safe follow-up

Safeability assumes `alo ≤ aup` and a nonnegative time limit. Its initial region
combines bounded safety with the nominal endpoint checks for follow-up targets
`vloEx` and `vupEx`. The result preserves that full region, as well as collision
avoidance, valid sense, and the clock bound. The follow-up targets remain fixed
parameters while the current advisory may change during the run.
-/

/-- STTT17 Theorem 5, with stronger postcondition (+ valid sense, + CimplSafeable), following
`AcasXSafeable.scala`. The paper version is equivalent to the case `t=0`. -/
theorem safeable_safe :
    ∀ rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → (w = -1 ∨ w = 1) → (t ≤ tl ∨ tl < 0) →
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx →
        ∀ res ∈ SetM.run (safeable rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t),
          NoNMAC rp hp res.r res.h ∧ (res.w = -1 ∨ res.w = 1) ∧ (res.t ≤ tl ∨ tl < 0) ∧
            CimplSafeable rp hp rv alo aup tl res.t res.r res.h res.v
              res.w res.vlo vloEx res.vup vupEx := sorry

/-!
## Horizontal reduction preserves the separation test

Starting from `HorizontalCoordinates`, evolve the planar and reduced coordinates
together for any permitted duration. At every returned state, planar separation
`rp ^ 2 < x_res ^ 2 + y_res ^ 2` is equivalent to the reduced test
`rp ^ 2 - n_res ^ 2 < s_res ^ 2`. This is a coordinate-reduction statement;
the advisory controller assumptions are not needed here.
-/

/-- STTT17 Proposition 1 -/
theorem horizontal_reduction :
    ∀ rp rx ry rv x y s n,
      HorizontalCoordinates rx ry rv x y s n →
        ∀ x_res y_res s_res n_res,
          (x_res, y_res, s_res, n_res) ∈
            SetM.run (evolve (horizontalMotion rx ry rv) (fun _ => True) (x, y, s, n)) →
            (rp ^ 2 < x_res ^ 2 + y_res ^ 2 ↔ rp ^ 2 - n_res ^ 2 < s_res ^ 2) := sorry

end ACASX
