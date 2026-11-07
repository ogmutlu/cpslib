import dLean.Examples.ACASX.Model

open dLean

namespace ACASX

/-- Fig. 3 : L⁻¹_expl -/
@[reducible]
def Lexpl (rp hp rv alo r h v w vlo : ℝ) : Prop :=
  let m := min 0 (w * v)
  let M := maxI v w vlo
  (0 ≤ w * vlo →
    -- case1 -> bound1
    ((-rp ≤ r ∧ r < -rp - rv * m / alo) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    -- case2 -> bound2
    ((-rp - rv * m / alo ≤ r ∧ r ≤ rp - rv * m / alo) →
      w * h < -(m ^ 2) / (2 * alo) - hp) ∧
    -- case3 -> bound3
    ((rp - rv * m / alo < r ∧ r ≤ rp + rv * M / alo) →
      w * rv ^ 2 * h < alo / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
    -- case4 -> bound4
    (rp + rv * M / alo < r →
      rv = 0 ∨ w * rv * h < w * vlo * (r - rp) - rv * M ^ 2 / (2 * alo) - rv * hp)
  ) ∧
  (w * vlo < 0 →
    -- case5 -> bound5
    ((-rp ≤ r ∧ r < -rp + rv * M / alo) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    -- case6 -> bound6
    (-rp + rv * M / alo ≤ r →
      (rv = 0 ∧ rp < r) ∨
        w * rv * h < w * vlo * (r + rp) - rv * M ^ 2 / (2 * alo) - rv * hp)
  )

/-- Fig. 8 : U⁻¹_expl -/
@[reducible]
def Uexpl (rp hp rv aup r h v w vup : ℝ) : Prop :=
  let M := maxI v w vup
  let V := max (w * vup) (w * v)
  (0 < V →
    -- case10 -> bound10
    ((-rp ≤ r ∧ r ≤ rp) → hp < w * h) ∧
    -- case11 -> bound11
    ((rp < r ∧ r ≤ rp + rv * M / aup) →
      aup / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case12 -> bound12
    ((-rp ≤ r ∧ r < -rp + rv * M / aup) →
      aup / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case13 -> bound13
    (-rp + rv * M / aup ≤ r →
      (rv = 0 ∧ rp < r) ∨ V * (r + rp) - rv * M ^ 2 / (2 * aup) + rv * hp < w * rv * h)
  ) ∧
  (V ≤ 0 →
    -- case10 -> bound10
    ((-rp ≤ r ∧ r ≤ rp) → hp < w * h) ∧
    -- case11 -> bound11
    ((rp < r ∧ r ≤ rp + rv * M / aup) →
      aup / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case14 -> bound14
    (rp + rv * M / aup < r →
      rv = 0 ∨ V * (r - rp) - rv * M ^ 2 / (2 * aup) + rv * hp < w * rv * h)
  )

/-- Fig. 8 : C⁻¹_expl -/
@[reducible]
def Cexpl (rp hp rv alo aup r h v w vlo vup : ℝ) : Prop :=
  Lexpl rp hp rv alo r h v w vlo ∨ Uexpl rp hp rv aup r h v w vup

/-- Fig. 5 : Dᵈ_expl -/
@[reducible]
def Dexpl (rp hp rv alo ad r h v w vlo d : ℝ) : Prop :=
  let rd := rv * max 0 d
  let vd := v - w * ad * max 0 d
  let hd := -(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d
  -- case7 -> bound7
  ((-rp ≤ r ∧ r ≤ rp) → w * h < -hp) ∧
  -- case8 -> bound8
  ((rp < r ∧ r ≤ rd + rp) →
    w * rv ^ 2 * h < -ad / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
  -- case9 -> bound9
  ((-rp ≤ r ∧ r < rd - rp) →
    w * rv ^ 2 * h < -ad / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
  Lexpl rp hp rv alo (r - rd) (h - hd) vd w vlo

/-- Fig. 10: cases 1--6, truncated at the advisory horizon. -/
@[reducible]
def LexplBounded (rp hp rv alo tl r h v w vlo : ℝ) : Prop :=
  let m := min 0 (w * v)
  let M := maxI v w vlo
  (0 ≤ w * vlo →
    -- case1 -> bound1
    ((-rp ≤ r ∧ r < -rp - rv * m / alo) ∧ (tl < 0 ∨ r ≤ -rp + rv * tl) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    -- case2 -> bound2
    ((-rp - rv * m / alo ≤ r ∧ r ≤ rp - rv * m / alo) ∧ (tl < 0 ∨ -m / alo ≤ tl) →
      w * h < -(m ^ 2) / (2 * alo) - hp) ∧
    -- case3 -> bound3
    ((rp - rv * m / alo < r ∧ r ≤ rp + rv * M / alo) ∧ (tl < 0 ∨ r ≤ rp + rv * tl) →
      w * rv ^ 2 * h < alo / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) - rv ^ 2 * hp) ∧
    -- case4 -> bound4
    (rp + rv * M / alo < r ∧ (tl < 0 ∨ r ≤ rp + rv * tl) →
      rv = 0 ∨ w * rv * h < w * vlo * (r - rp) - rv * M ^ 2 / (2 * alo) - rv * hp)
  ) ∧
  (w * vlo < 0 →
    -- case5 -> bound5
    ((-rp ≤ r ∧ r < -rp + rv * M / alo) ∧ (tl < 0 ∨ r ≤ -rp + rv * tl) →
      w * rv ^ 2 * h < alo / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) - rv ^ 2 * hp) ∧
    -- case6 -> bound6
    (-rp + rv * M / alo ≤ r ∧ (tl < 0 ∨ r < -rp + rv * tl) →
      (rv = 0 ∧ rp < r) ∨
        w * rv * h < w * vlo * (r + rp) - rv * M ^ 2 / (2 * alo) - rv * hp)
  )

/-- Fig. 10: cases 10--14, truncated at the advisory horizon. -/
@[reducible]
def UexplBounded (rp hp rv aup tl r h v w vup : ℝ) : Prop :=
  let M := maxI v w vup
  let V := max (w * vup) (w * v)
  (0 < V →
    -- case10 -> bound10
    ((-rp ≤ r ∧ r ≤ rp) → hp < w * h) ∧
    -- case11 -> bound11
    ((rp < r ∧ r ≤ rp + rv * M / aup) ∧ (tl < 0 ∨ r ≤ rp + rv * tl) →
      aup / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case12 -> bound12
    ((-rp ≤ r ∧ r < -rp + rv * M / aup) ∧ (tl < 0 ∨ r ≤ -rp + rv * tl) →
      aup / 2 * (r + rp) ^ 2 + w * rv * v * (r + rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case13 -> bound13
    (-rp + rv * M / aup ≤ r ∧ (tl < 0 ∨ r < -rp + rv * tl) →
      (rv = 0 ∧ rp < r) ∨ V * (r + rp) - rv * M ^ 2 / (2 * aup) + rv * hp < w * rv * h)
  ) ∧
  (V ≤ 0 →
    -- case10 -> bound10
    ((-rp ≤ r ∧ r ≤ rp) → hp < w * h) ∧
    -- case11 -> bound11
    ((rp < r ∧ r ≤ rp + rv * M / aup) ∧ (tl < 0 ∨ r ≤ rp + rv * tl) →
      aup / 2 * (r - rp) ^ 2 + w * rv * v * (r - rp) + rv ^ 2 * hp < w * rv ^ 2 * h) ∧
    -- case14 -> bound14
    (rp + rv * M / aup < r ∧ (tl < 0 ∨ r ≤ rp + rv * tl) →
      rv = 0 ∨ V * (r - rp) - rv * M ^ 2 / (2 * aup) + rv * hp < w * rv * h)
  )

/-- Fig. 10: both cases 15 and 16 test horizontal overlap at the horizon. -/
@[reducible]
def horizonCase (rp rv tl r : ℝ) : Prop :=
  0 ≤ tl ∧ -rp + rv * tl ≤ r ∧ r ≤ rp + rv * tl

/-- Fig. 10 bound15: the linear term follows `bounded_lower_equivalence.kyx`
(line 93), with the model's switching-time partition. -/
@[reducible]
def bound15 (hp alo tl h v w vlo : ℝ) : Prop :=
  (tl < maxI v w vlo / alo → w * h < alo / 2 * tl ^ 2 + w * v * tl - hp) ∧
  (maxI v w vlo / alo ≤ tl → w * h < w * vlo * tl - maxI v w vlo ^ 2 / (2 * alo) - hp)

/-- Fig. 10 bound16: follows the endpoint expression in
`bounded_upper_equivalence.kyx` (lines 56--63), normalized using the model's
switching-time partition and terminal speed for `Sense w`. -/
@[reducible]
def bound16 (hp aup tl h v w vup : ℝ) : Prop :=
  (tl < maxI v w vup / aup → aup / 2 * tl ^ 2 + w * v * tl + hp < w * h) ∧
  (maxI v w vup / aup ≤ tl →
    max (w * vup) (w * v) * tl - maxI v w vup ^ 2 / (2 * aup) + hp < w * h)

/-- Corrected Fig. 10 hatted lower region: include the endpoint for both signs. -/
@[reducible]
def LexplBoundedHat (rp hp rv alo tl r h v w vlo : ℝ) : Prop :=
  LexplBounded rp hp rv alo tl r h v w vlo ∧
    (horizonCase rp rv tl r → bound15 hp alo tl h v w vlo)

/-- Corrected Fig. 10 hatted upper region: include the endpoint for both signs. -/
@[reducible]
def UexplBoundedHat (rp hp rv aup tl r h v w vup : ℝ) : Prop :=
  UexplBounded rp hp rv aup tl r h v w vup ∧
    (horizonCase rp rv tl r → bound16 hp aup tl h v w vup)

/-- Corrected Fig. 10 hatted two-sided region. -/
@[reducible]
def CexplBoundedHat (rp hp rv alo aup tl r h v w vlo vup : ℝ) : Prop :=
  LexplBoundedHat rp hp rv alo tl r h v w vlo ∨
    UexplBoundedHat rp hp rv aup tl r h v w vup

/-- Fig. 12 lower endpoint height and velocity, following `condImplSafeableLo`
in `AcasXSafeable.scala` (lines 363--374), for `0 ≤ tl` and initial clock zero.
The accelerating height uses the initial velocity `v`, as in the supplement. -/
noncomputable def lowerExit (alo tl v w vlo : ℝ) : ℝ × ℝ :=
  if tl < maxI v w vlo / alo then
    (w * alo / 2 * tl ^ 2 + v * tl, w * alo * tl + v)
  else
    (vlo * tl - w * maxI v w vlo ^ 2 / (2 * alo), vlo)

/-- Fig. 12 nominal upper endpoint height and velocity, following `condImplSafeableUp`
in `AcasXSafeable.scala` (lines 382--393), for `0 ≤ tl` and initial clock zero.
The accelerating height uses `v`; the final speed is equivalent for `Sense w`. -/
noncomputable def upperExit (aup tl v w vup : ℝ) : ℝ × ℝ :=
  if tl < maxI v w vup / aup then
    (w * aup / 2 * tl ^ 2 + v * tl, w * aup * tl + v)
  else
    (w * max (w * vup) (w * v) * tl - w * maxI v w vup ^ 2 / (2 * aup),
      w * max (w * vup) (w * v))

/-- Fig. 12 explicit lower safeable region; intentionally uses the unhatted part.
The follow-up endpoint follows `condImplSafeableLo` in `AcasXSafeable.scala`.
The supplement does not formalize this explicit safeable region. -/
@[reducible]
def LexplSafeable (rp hp rv alo tl r h v w vlo vloEx : ℝ) : Prop :=
  let ex := lowerExit alo tl v w vlo
  LexplBounded rp hp rv alo tl r h v w vlo ∧
    Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 w vloEx

/-- Fig. 12 explicit upper safeable region, followed by a reversal.
The endpoint and reversed-sense follow-up follow `condImplSafeableUp` in
`AcasXSafeable.scala`; the supplement does not formalize the explicit region. -/
@[reducible]
def UexplSafeable (rp hp rv alo aup tl r h v w vup vupEx : ℝ) : Prop :=
  let ex := upperExit aup tl v w vup
  UexplBounded rp hp rv aup tl r h v w vup ∧
    Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 (-w) vupEx

/-- Corrected Fig. 12 explicit two-sided safeable region. -/
@[reducible]
def CexplSafeable (rp hp rv alo aup tl r h v w vlo vloEx vup vupEx : ℝ) : Prop :=
  LexplSafeable rp hp rv alo tl r h v w vlo vloEx ∨
    UexplSafeable rp hp rv alo aup tl r h v w vup vupEx

end ACASX
