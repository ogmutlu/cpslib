import dLean.Examples.FM11.Model

open dLean

namespace FM11

theorem llc_safe :
    ∀ A b B ε f l x v a,
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → Behind b B x v f l →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          Behind b B res.x res.v f l := sorry

theorem glc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (glc A b B ε C x v a),
          LaneSafe C b B res.x res.v ∧
            (∀ i ∈ C, BehindLStar C b B res.x res.v i) := sorry

theorem lhc_safe :
    ∀ A b B ε x v a (C : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe C b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε C x v a),
          LaneSafe res.C b B res.x res.v ∧
            (∀ i ∈ res.C, BehindLStar res.C b B res.x res.v i) := sorry

theorem ghc_safe :
    ∀ A b B ε x v a (lanes : Finset Lane) (C : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (C l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes C x v a),
          ∀ l ∈ lanes, LaneSafe (res.C l) b B res.x res.v ∧
            (∀ i ∈ res.C l, BehindLStar (res.C l) b B res.x res.v i) := sorry

end FM11
