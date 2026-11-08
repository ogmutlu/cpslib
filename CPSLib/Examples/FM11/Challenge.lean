import CPSLib.Examples.FM11.Model

/-!
# Safety specifications for the highway controllers

The four specifications follow the progression of `FM11.Model`: two cars, a fixed
lane population, a changing lane population, and multiple lanes.

All share the parameter assumptions `0 ≤ A`, `0 < b ≤ B`, and `0 < ε`.
Each claim quantifies over every successful result in `SetM.run`, including all
permitted control choices, cycle counts, and continuous stopping times.
The claims establish safety; they do not require a positive number of cycles
or assert that every controller choice can continue.

The theorem bodies are challenges for the separate `CPSLib.Examples.FM11.Proof`.
-/

open CPSLib

namespace FM11

/-!
## Model 1: preserve safe following

The local controller starts with a follower safely behind its leader. The
postcondition preserves the full `Behind` relation, including its braking-distance
margin and, for distinct cars, strict position order and nonnegative velocities.
-/

/-- Local lane control (Model 1): in a single lane, two-car scenario, a follower
initially behind its leader remains behind after any run. -/
theorem llc_safe :
    ∀ (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → Behind b B x v f l →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          Behind b B res.x res.v f l := sorry

/-!
## Model 2: preserve a fixed lane

The lane begins in `LaneSafe`: velocities are nonnegative, positions are distinct,
and every car safely follows its immediate leader. The result must preserve these
properties and establish safe following of every successive leader through
`BehindLStar`. The participating set `C` is fixed throughout the run.
-/

/-- Global lane control (Model 2): for a fixed set of cars in a single lane, each run
preserves lane safety and every car is safely behind all of its successive leaders. -/
theorem glc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (glc A b B ε C x v a),
          LaneSafe C b B res.x res.v ∧
            (∀ i ∈ C, BehindLStar C b B res.x res.v i) := sorry

/-!
## Model 3: preserve safety as cars enter and leave

Creation and deletion can change the lane population. The specification therefore
uses the returned set `res.C` in its postcondition. Every car still participating
at the observation point must satisfy lane safety and safe following along its
current chain of leaders.
-/

/-- Local highway control (Model 3): lane safety and separation from successive leaders
hold for the current set of cars, in the presence of dynamic creation and deletion. -/
theorem lhc_safe :
    ∀ (A b B ε : ℝ) (x v a : Car → ℝ) (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε C x v a),
          LaneSafe res.C b B res.x res.v ∧
            (∀ i ∈ res.C, BehindLStar res.C b B res.x res.v i) := sorry

/-!
## Model 4: preserve each selected lane

Initially, every selected lane is safe. After a global highway run, the same
requirement holds for each lane's returned population, together with safe following
of successive leaders within that lane.

Cars share their physical state across lanes. The controller must therefore choose
accelerations compatible with all applicable lane controllers before the common
motion segment.
-/

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
