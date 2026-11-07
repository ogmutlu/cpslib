import dLean.Examples.FM11.Model

open dLean

namespace FM11

/-- Local lane control (Model 1): in a single lane, two-car scenario, a follower
initially behind its leader remains behind after any run. -/
theorem llc_safe :
    ∀ (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → Behind b B x v f l →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          Behind b B res.x res.v f l := sorry

/-- Global lane control (Model 2): for a fixed set of cars in a single lane, each run
preserves lane safety and every car is safely behind all of its successive leaders. -/
theorem glc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (glc A b B ε C x v a),
          LaneSafe C b B res.x res.v ∧
            (∀ i ∈ C, BehindLStar C b B res.x res.v i) := sorry

/-- Local highway control (Model 3): lane safety and separation from successive leaders
hold for the current set of cars, in the presence of dynamic creation and deletion. -/
theorem lhc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε C x v a),
          LaneSafe res.C b B res.x res.v ∧
            (∀ i ∈ res.C, BehindLStar res.C b B res.x res.v i) := sorry

/-- Global highway control (Model 4): in the presence of multi-lanes and dynamic creation
and deletion, each lane is safe and its cars are safely behind their successive leaders
in that lane. -/
theorem ghc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (lanes : Finset Lane) (C : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (C l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes C x v a),
          ∀ l ∈ lanes, LaneSafe (res.C l) b B res.x res.v ∧
            (∀ i ∈ res.C l, BehindLStar (res.C l) b B res.x res.v i) := sorry

end FM11
