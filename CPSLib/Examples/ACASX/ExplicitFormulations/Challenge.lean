import CPSLib.Examples.ACASX.ExplicitFormulations.Model

open CPSLib

namespace ACASX

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

/-- The explicit lower region equals `LoSafeFor`. (see Lemma 1) -/
theorem immediate_regions_equivalent :
    ∀ (rp hp rv alo : ℝ) (encounter : Encounter) (advisory : Advisory),
      Bounds rp hp rv alo →
        (advisory.LoSafeForExplicit encounter rp hp rv alo ↔
          advisory.LoSafeFor encounter rp hp rv alo) := sorry

/-- The explicit delayed region equals `DelayedSafeFor`. (see Lemma 2) -/
theorem delayed_regions_equivalent :
    ∀ (rp hp rv alo ad : ℝ) (encounter : Encounter) (advisory : Advisory) (d : ℝ),
      Bounds rp hp rv alo → 0 ≤ ad →
        (advisory.DelayedSafeForExplicit encounter rp hp rv alo ad d ↔
          advisory.DelayedSafeFor encounter rp hp rv alo ad d) := sorry

/-- The explicit two-sided region equals `SafeFor`. (see Lemma 3) -/
theorem two_sided_regions_equivalent :
    ∀ (rp hp rv alo aup : ℝ) (encounter : Encounter) (advisory : TwoSidedAdvisory),
      Bounds rp hp rv alo → alo ≤ aup →
        (advisory.SafeForExplicit encounter rp hp rv alo aup ↔
          advisory.SafeFor encounter rp hp rv alo aup) := sorry

/-- The explicit bounded region equals `SafeForWithin` at clock zero. (see Lemma 4) -/
theorem bounded_regions_equivalent :
    ∀ (rp hp rv alo aup : ℝ) (limit : TimeHorizon) (encounter : Encounter)
      (advisory : TwoSidedAdvisory),
      Bounds rp hp rv alo → alo ≤ aup →
        (advisory.SafeForWithinExplicit encounter rp hp rv alo aup limit ↔
          advisory.SafeForWithin encounter rp hp rv alo aup limit 0) := sorry

/-- A safe strengthening or reversal implies the corresponding endpoint bound. (see Lemma 5) -/
theorem endpoint_cases_redundant :
    ∀ (rp hp rv alo aup : ℝ) (duration : Duration) (encounter : Encounter)
      (advisory : TwoSidedAdvisory) (vloEx vupEx : ℝ),
      Bounds rp hp rv alo → alo ≤ aup →
        (∀ hn vn, advisory.lowerAdvisory.EndpointLo alo encounter.v duration.val hn vn →
          let next : Advisory := { direction := advisory.direction, targetv := vloEx }
          let nextEncounter : Encounter :=
            { r := encounter.r - rv * duration.val, h := encounter.h - hn, v := vn }
          next.LoSafeForExplicit nextEncounter rp hp rv alo →
            horizonCase rp rv duration.val encounter.r →
              bound15 hp alo duration.val encounter.h encounter.v advisory.direction.sign
                advisory.lower) ∧
        (∀ hn vn, advisory.upperAdvisory.EndpointUp aup encounter.v duration.val hn vn →
          let reverse := if advisory.direction = .down then .up else .down
          let next : Advisory := { direction := reverse, targetv := vupEx }
          let nextEncounter : Encounter :=
            { r := encounter.r - rv * duration.val, h := encounter.h - hn, v := vn }
          next.LoSafeForExplicit nextEncounter rp hp rv alo →
            horizonCase rp rv duration.val encounter.r →
              bound16 hp aup duration.val encounter.h encounter.v advisory.direction.sign
                advisory.upper) := sorry

/-- The explicit safeable region equals `SafeableFor` at clock zero. (see Lemma 6) -/
theorem safeable_regions_equivalent :
    ∀ (rp hp rv alo aup : ℝ) (duration : Duration) (encounter : Encounter)
      (advisory : TwoSidedAdvisory) (vloEx vupEx : ℝ),
      Bounds rp hp rv alo → alo ≤ aup →
        (advisory.SafeableForExplicit encounter rp hp rv alo aup duration vloEx vupEx ↔
          advisory.SafeableFor encounter rp hp rv alo aup duration 0 vloEx vupEx) := sorry

/-!
## Horizontal reduction preserves the separation test
-/

/--
The planar horizontal-separation test is equivalent to the reduced-coordinate test
throughout the constant-velocity evolution, assuming the initial coordinate relations.
See Proposition 1.
-/
theorem horizontal_reduction :
    ∀ rp rx ry rv x y s n,
      HorizontalCoordinates rx ry rv x y s n →
        ∀ x_res y_res s_res n_res,
          (x_res, y_res, s_res, n_res) ∈
            SetM.run (evolve (motionHorizontalODE rx ry rv) (fun _ => True) (x, y, s, n)) →
            (rp ^ 2 < x_res ^ 2 + y_res ^ 2 ↔ rp ^ 2 - n_res ^ 2 < s_res ^ 2) := sorry

end ACASX
