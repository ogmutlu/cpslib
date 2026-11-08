import CPSLib.Examples.ACASX.ExplicitFormulations.Proof

/-! Source variants and checked counterexamples to the printed formulas.
See `lemmata_4-5-6.md` for the source comparison. -/

namespace ACASX

/-- The corrected formula accepts the stationary boundary example without invoking Lemma 4. -/
theorem corrected_stationary_boundary_example :
    CexplSafeable 1 1 0 1 1 1 (-1) (-4) (-1) 1 (-1) 0 (-1) 0 := by
  norm_num [CexplSafeable, LexplSafeable, UexplSafeable, lowerExit, upperExit,
    LexplBounded, UexplBounded, Lexpl, maxI]

namespace Printed

/-- Fig. 12 upper endpoint with the printed accelerating height. -/
@[reducible]
def upperEndpoint (aup τ hn vn v w vup : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vup / aup ∧
    hn = w * aup / 2 * τ ^ 2 + vup * τ ∧ vn = w * aup * τ + v) ∨
  (maxI v w vup / aup ≤ τ ∧
    hn = w * max (w * vup) (w * v) * τ - w * maxI v w vup ^ 2 / (2 * aup) ∧
    vn = w * max (w * vup) (w * v))


/- These preserve the problematic printed expressions for comparison with the
current implicit model. In particular, they are not the corrected definitions above. -/

/-- Fig. 10's original non-strict cutoff for case 6. -/
@[reducible]
def LexplBounded (rp hp rv alo tl r h v w vlo : ℝ) : Prop :=
  ACASX.LexplBounded rp hp rv alo tl r h v w vlo ∧
    (w * vlo < 0 →
      -rp + rv * maxI v w vlo / alo ≤ r ∧ (tl < 0 ∨ r ≤ -rp + rv * tl) →
        (rv = 0 ∧ rp < r) ∨
          w * rv * h < w * vlo * (r + rp) - rv * maxI v w vlo ^ 2 / (2 * alo) - rv * hp)

/-- Fig. 10's original non-strict cutoff for case 13. -/
@[reducible]
def UexplBounded (rp hp rv aup tl r h v w vup : ℝ) : Prop :=
  ACASX.UexplBounded rp hp rv aup tl r h v w vup ∧
    (0 < max (w * vup) (w * v) →
      -rp + rv * maxI v w vup / aup ≤ r ∧ (tl < 0 ∨ r ≤ -rp + rv * tl) →
        (rv = 0 ∧ rp < r) ∨
          max (w * vup) (w * v) * (r + rp) - rv * maxI v w vup ^ 2 / (2 * aup) +
            rv * hp < w * rv * h)

/-- Fig. 10 bound15 literally uses the initial velocity in its linear branch. -/
@[reducible]
def bound15 (hp alo tl h v w vlo : ℝ) : Prop :=
  (tl ≤ maxI v w vlo / alo → w * h < alo / 2 * tl ^ 2 + w * v * tl - hp) ∧
  (maxI v w vlo / alo < tl → w * h < w * v * tl - maxI v w vlo ^ 2 / (2 * alo) - hp)

/-- Fig. 10 bound16, with its printed switching-time partition. -/
@[reducible]
def bound16 (hp aup tl h v w vup : ℝ) : Prop :=
  (tl ≤ maxI v w vup / aup → aup / 2 * tl ^ 2 + w * v * tl + hp < w * h) ∧
  (maxI v w vup / aup < tl →
    max (w * vup) (w * v) * tl - maxI v w vup ^ 2 / (2 * aup) + hp < w * h)

/-- Fig. 10's printed lower hat has the additional sign guard. -/
@[reducible]
def LexplBoundedHat (rp hp rv alo tl r h v w vlo : ℝ) : Prop :=
  LexplBounded rp hp rv alo tl r h v w vlo ∧
    (w * vlo < 0 → horizonCase rp rv tl r → bound15 hp alo tl h v w vlo)

/-- Fig. 10's printed upper hat has the additional sign guard. -/
@[reducible]
def UexplBoundedHat (rp hp rv aup tl r h v w vup : ℝ) : Prop :=
  UexplBounded rp hp rv aup tl r h v w vup ∧
    (max (w * vup) (w * v) ≤ 0 → horizonCase rp rv tl r → bound16 hp aup tl h v w vup)

@[reducible]
def CexplBoundedHat (rp hp rv alo aup tl r h v w vlo vup : ℝ) : Prop :=
  LexplBoundedHat rp hp rv alo tl r h v w vlo ∨
    UexplBoundedHat rp hp rv aup tl r h v w vup

/-- Fig. 12 literally uses `vlo * tl` during acceleration. -/
noncomputable def lowerExit (alo tl v w vlo : ℝ) : ℝ × ℝ :=
  if tl < maxI v w vlo / alo then
    (w * alo / 2 * tl ^ 2 + vlo * tl, w * alo * tl + v)
  else
    (vlo * tl - w * maxI v w vlo ^ 2 / (2 * alo), vlo)

/-- Fig. 12 literally uses `vup * tl` during acceleration. -/
noncomputable def upperExit (aup tl v w vup : ℝ) : ℝ × ℝ :=
  if tl < maxI v w vup / aup then
    (w * aup / 2 * tl ^ 2 + vup * tl, w * aup * tl + v)
  else
    (w * max (w * vup) (w * v) * tl - w * maxI v w vup ^ 2 / (2 * aup),
      w * max (w * vup) (w * v))

/-- Fig. 12's explicit safeable region with the printed endpoint heights. -/
@[reducible]
def CexplSafeable (rp hp rv alo aup tl r h v w vlo vloEx vup vupEx : ℝ) : Prop :=
  (let ex := lowerExit alo tl v w vlo
   LexplBounded rp hp rv alo tl r h v w vlo ∧
     Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 w vloEx) ∨
  (let ex := upperExit aup tl v w vup
   UexplBounded rp hp rv aup tl r h v w vup ∧
     Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 (-w) vupEx)

end Printed

/-- Source-comparison variant: nominal lower endpoint and printed upper endpoint.
The main model uses nominal endpoints for both. -/
@[reducible]
def CimplSafeableUpperPrinted (rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx : ℝ) : Prop :=
  (LimplBounded rp hp rv alo tl t r h v w vlo ∧
    ∀ hn vn : ℝ, lowerEndpoint alo (tl - t) hn vn v w vlo →
      Limpl rp hp rv alo (r - rv * (tl - t)) (h - hn) vn w vloEx) ∨
  (UimplBounded rp hp rv aup tl t r h v w vup ∧
    ∀ hn vn : ℝ, Printed.upperEndpoint aup (tl - t) hn vn v w vup →
      Limpl rp hp rv alo (r - rv * (tl - t)) (h - hn) vn (-w) vupEx)

/-- The printed upper height lies above the nominal height in signed coordinates. -/
theorem upperEndpoint_le_printed (aup τ hn vn v w vup : ℝ)
    (he : upperEndpoint aup τ hn vn v w vup) :
    ∃ hp, Printed.upperEndpoint aup τ hp vn v w vup ∧ w * hn ≤ w * hp := by
  rcases he with ⟨ht, hs, rfl, rfl⟩ | ⟨hs, rfl, rfl⟩
  · have hgap : 0 ≤ w * (vup - v) := by
      by_contra hg
      have hm : maxI v w vup = 0 := max_eq_left (le_of_not_ge hg)
      rw [hm, zero_div] at hs
      linarith
    refine ⟨w * aup / 2 * τ ^ 2 + vup * τ, Or.inl ⟨ht, hs, rfl, rfl⟩, ?_⟩
    nlinarith [mul_nonneg hgap ht]
  · exact ⟨_, Or.inr ⟨hs, rfl, rfl⟩, le_rfl⟩

/-- Using the printed upper height strengthens the model's nominal safeable condition. -/
theorem printed_upper_safeable_implies_nominal
    (rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx : ℝ)
    (ha : 0 < alo) (hw : Sense w)
    (hsafe : CimplSafeableUpperPrinted rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx) :
    CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx := by
  rcases hsafe with hlo | ⟨hbounded, hescape⟩
  · exact Or.inl hlo
  · right
    refine ⟨hbounded, ?_⟩
    intro hn vn he
    obtain ⟨hp, hprinted, hheight⟩ := upperEndpoint_le_printed _ _ _ _ _ _ _ he
    have hw' : Sense (-w) := by rcases hw with rfl | rfl <;> norm_num [Sense]
    exact lower_region_mono _ _ _ _ _ (h - hp) (h - hn) vn vn (-w) vupEx ha hw'
      (by nlinarith) le_rfl (hescape hp vn hprinted)

/-! ## Checked counterexamples to printed formulas -/

/-- Lemma 4: the lower endpoint is missed when `w * vlo = 0`. -/
theorem printed_lower_hat_counterexample :
    Printed.CexplBoundedHat 1 1 1 1 1 1 (1/2) (-2) (-10) 1 0 0 ∧
      ¬ CimplBounded 1 1 1 1 1 1 0 (1/2) (-2) (-10) 1 0 0 := by
  constructor
  · norm_num [Printed.CexplBoundedHat, Printed.LexplBoundedHat, Printed.UexplBoundedHat,
      Printed.LexplBounded, Printed.UexplBounded, LexplBounded, UexplBounded, maxI]
  · rintro (hs | hs)
    · have hx := hs 1 1 (-19/2) (by norm_num [A, maxI])
      norm_num at hx
    · have hx := hs 0 0 0 (by norm_num [Aup, maxI])
      norm_num at hx

/-- Lemma 4: the upper endpoint is also needed for positive terminal slope. -/
theorem printed_upper_hat_counterexample :
    Printed.CexplBoundedHat 1 1 1 1 1 1 1 (5/4) 0 1 0 10 ∧
      ¬ CimplBounded 1 1 1 1 1 1 0 1 (5/4) 0 1 0 10 := by
  constructor
  · norm_num [Printed.CexplBoundedHat, Printed.LexplBoundedHat, Printed.UexplBoundedHat,
      Printed.LexplBounded, Printed.UexplBounded, LexplBounded, UexplBounded, maxI]
  · rintro (hs | hs)
    · have hx := hs 0 0 0 (by norm_num [A, maxI])
      norm_num at hx
    · have hx := hs 1 1 (1/2) (by norm_num [Aup, maxI])
      norm_num at hx

/-- Lemma 5: a safe strengthening does not imply the printed linear bound15.
The endpoint here is in the linear branch, where Fig. 12 agrees with the nominal trajectory. -/
theorem printed_bound15_counterexample :
    (let ex := Printed.lowerExit 1 3 (-4) 1 (-2)
     Lexpl 1 1 0 1 0 (-12 - ex.1) ex.2 1 0) ∧
      horizonCase 1 0 3 0 ∧ ¬ Printed.bound15 1 1 3 (-12) (-4) 1 (-2) := by
  norm_num [Printed.lowerExit, Lexpl, horizonCase, Printed.bound15, maxI]

/-- Lemma 6: the printed accelerating endpoint can accept an unsafe follow-up. -/
theorem printed_safeable_endpoint_counterexample :
    Printed.CexplSafeable 1 1 0 1 1 1 0 (-45) (-10) 1 0 0 0 0 ∧
      ¬ CimplSafeable 1 1 0 1 1 1 0 0 (-45) (-10) 1 0 0 0 0 := by
  constructor
  · norm_num [Printed.CexplSafeable, Printed.LexplBounded, Printed.UexplBounded,
      Printed.lowerExit, Printed.upperExit, LexplBounded, UexplBounded, Lexpl, maxI]
  · rintro (⟨_, hfollow⟩ | ⟨hs, _⟩)
    · have hx := hfollow (-19/2) (-9) (by norm_num [lowerEndpoint, maxI])
      have hsep := hx 9 0 (-81/2) (by norm_num [A, maxI])
      norm_num at hsep
    · have hx := hs 0 0 0 (by norm_num [Aup, maxI])
      norm_num at hx

/-- Lemma 6: even after fixing the endpoint heights, the non-strict case6 cutoff
rejects a safe stationary-horizontal encounter at `r = -rp`. -/
theorem printed_stationary_boundary_counterexample :
    CimplSafeable 1 1 0 1 1 1 0 (-1) (-4) (-1) 1 (-1) 0 (-1) 0 ∧
      ¬ Printed.CexplSafeable 1 1 0 1 1 1 (-1) (-4) (-1) 1 (-1) 0 (-1) 0 := by
  constructor
  · left
    constructor
    · intro tn rn hn ⟨ht, _hr, hA⟩
      norm_num [A, maxI] at hA
      rcases hA with ⟨htn, htlt, _⟩ | ⟨_htn, rfl⟩
      · linarith
      · right
        norm_num at ht ⊢
        linarith
    · intro hn vn he
      norm_num [lowerEndpoint, maxI] at he
      obtain ⟨rfl, rfl⟩ := he
      apply (immediate_regions_equivalent _ _ _ _ _ _ _ _ _
        (by norm_num [Bounds]) (by norm_num [Sense])).mp
      norm_num [Lexpl, maxI]
  · norm_num [Printed.CexplSafeable, Printed.LexplBounded, Printed.UexplBounded,
      Printed.lowerExit, Printed.upperExit, LexplBounded, UexplBounded, Lexpl, maxI]

end ACASX
