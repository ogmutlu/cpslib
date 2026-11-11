import CPSLib.Examples.ACASX.Model

/-!
# Safety specifications for the ACASX advisory models (STTT17)
-/

open CPSLib

namespace ACASX

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

@[reducible]
def NoNMAC (rp hp : ℝ) (encounter : Encounter) : Prop :=
  rp < |encounter.r| ∨ hp < |encounter.h|

/-!
## Model 1: immediate response preserves the lower safe region
-/

/--
Immediate response avoids a near mid-air collision and preserves the lower safe
region, assuming the initial encounter is safe and the parameter bounds hold.
See Theorem 1.
-/
theorem immediate_safe :
    ∀ (rp hp rv alo : ℝ) (encounter : Encounter) (advisory : Advisory),
      Bounds rp hp rv alo →
        advisory.LoSafeFor encounter rp hp rv alo →
          ∀ res ∈ SetM.run (immediateResponseProg rp hp rv alo encounter advisory),
            NoNMAC rp hp res.encounter ∧
            res.advisory.LoSafeFor res.encounter rp hp rv alo := sorry

/-!
## Model 2: delayed response preserves its remaining-delay region
-/

/--
Delayed response avoids a near mid-air collision and preserves the delayed safe
region for the returned encounter, advisory, and remaining delay, under the stated bounds.
See Theorem 2.
-/
theorem delayed_safe :
    ∀ (rp hp rv alo ad δ ε : ℝ) (encounter : Encounter) (advisory : Advisory) (d : ℝ),
      Bounds rp hp rv alo → (0 ≤ ad ∧ 0 ≤ δ ∧ 0 ≤ ε) →
        advisory.DelayedSafeFor encounter rp hp rv alo ad d →
          ∀ res ∈ SetM.run (delayedResponseProg rp hp rv alo ad δ ε encounter advisory d),
            NoNMAC rp hp res.encounter ∧
            res.advisory.DelayedSafeFor res.encounter rp hp rv alo ad res.d := sorry

/-!
## Model 3: two-sided compliance prevents a collision
-/

/--
Two-sided response avoids a near mid-air collision from a safe initial encounter,
assuming the parameter bounds and `alo ≤ aup`. See Theorem 3.
-/
theorem two_sided_safe :
    ∀ (rp hp rv alo aup : ℝ) (encounter : Encounter) (advisory : TwoSidedAdvisory),
      Bounds rp hp rv alo → alo ≤ aup →
        advisory.SafeFor encounter rp hp rv alo aup →
          ∀ res ∈ SetM.run (twoSidedResponseProg rp hp rv alo aup encounter advisory),
            NoNMAC rp hp res.encounter := sorry

/-!
## Model 4: preserve safety for the remaining time horizon
-/

/--
Bounded-time response avoids a near mid-air collision and preserves safety for the
remaining horizon, assuming an initially safe encounter within the horizon. See Theorem 4.
-/
theorem bounded_safe :
    ∀ (rp hp rv alo aup : ℝ) (limit : TimeHorizon) (encounter : Encounter)
      (advisory : TwoSidedAdvisory) (t : ℝ),
      Bounds rp hp rv alo ∧ 0 < aup → limit.includes 0 t →
        advisory.SafeForWithin encounter rp hp rv alo aup limit t →
          ∀ res ∈ SetM.run (boundedResponseProg rp hp rv alo aup limit encounter advisory t),
            NoNMAC rp hp res.encounter ∧ limit.includes 0 res.t ∧
            res.advisory.SafeForWithin res.encounter rp hp rv alo aup limit res.t := sorry

/-!
## Model 5: preserve the possibility of a safe follow-up
-/

/--
Safeable response avoids a near mid-air collision and preserves the clock bound
and availability of an unlimited-time safe follow-up, under the stated assumptions.
See Theorem 5.
-/
theorem safeable_safe :
    ∀ (rp hp rv alo aup : ℝ) (duration : Duration) (vloEx vupEx : ℝ)
      (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ),
      Bounds rp hp rv alo → alo ≤ aup → t ≤ duration.val →
        advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx →
          ∀ res ∈ SetM.run (safeableResponseProg
              rp hp rv alo aup duration vloEx vupEx encounter advisory t),
            NoNMAC rp hp res.encounter ∧ res.t ≤ duration.val ∧
            res.advisory.SafeableFor
              res.encounter rp hp rv alo aup duration res.t vloEx vupEx := sorry

end ACASX
