import CPSLib.Examples.FM11.Model

open CPSLib

namespace FM11

/-!
## Model 1: Local Lane Control
-/

/--
Preserve safe following: in a single lane, two-car scenario, a follower
initially behind its leader remains behind after any run.
-/
theorem llc_safe :
    ∀ (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → f.IsBehind l b B x v →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          f.IsBehind l b B res.x res.v := sorry

/-!
## Model 2: Global Lane Control
-/

/--
Preserve a fixed lane: for a fixed set of cars in a single lane, each run
preserves lane safety and every car is safely behind all of its successive leaders.
-/
theorem glc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (cars : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe cars b B x v →
        ∀ res ∈ SetM.run (glc A b B ε cars x v a),
          LaneSafe cars b B res.x res.v ∧
            (∀ i ∈ cars, i.IsBehindLStar cars b B res.x res.v) := sorry

/-!
## Model 3: Local Highway Control
-/

/--
Preserve safety as cars enter and leave: lane safety and separation from successive
leaders hold for the current set of cars, in the presence of dynamic creation and
deletion.
-/
theorem lhc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (cars : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe cars b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε cars x v a),
          LaneSafe res.cars b B res.x res.v ∧
            (∀ i ∈ res.cars, i.IsBehindLStar res.cars b B res.x res.v) := sorry

/-!
## Model 4: Global Highway Control
-/

/--
Preserve each selected lane: in the presence of multi-lanes and dynamic creation and
deletion, each lane is safe and its cars are safely behind their successive leaders
in that lane.
-/
theorem ghc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (cars l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes cars x v a),
          ∀ l ∈ lanes, LaneSafe (res.cars l) b B res.x res.v ∧
            (∀ i ∈ res.cars l, i.IsBehindLStar (res.cars l) b B res.x res.v) := sorry

end FM11
