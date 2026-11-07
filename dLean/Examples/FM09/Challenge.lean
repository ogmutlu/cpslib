import dLean.Examples.FM09.Model

open dLean

namespace FM09

/-- For any fleet size, initially mutually separated aircraft
remain separated after any NTRM run. -/
theorem ntrm_many_safe :
    ∀ (n : ℕ) (p : ℝ) (x d : Fin n → Vec2), SeparatedMany p x →
      ∀ res ∈ SetM.run (ntrm_many p x d), SeparatedMany p res := sorry

/-- For any fleet size, initially mutually separated aircraft
remain separated after any FTRM run. -/
theorem ftrm_many_end_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ res ∈ SetM.run (ftrm_many p r x d), SeparatedMany p res.x := sorry

/-- Throughout safety for the FTRM for any fleet size: after any number of (incl. zero)
FTRM iterations, running any prefix of another FTRM iteration is safe. -/
theorem ftrm_many_throughout_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ st ∈ SetM.run (ftrm_many p r x d), ∀ k : Fin 5,
          ∀ res ∈ SetM.run (ftrmPrefix_many p st.r k st.x st.d),
          SeparatedMany p res := sorry

end FM09
