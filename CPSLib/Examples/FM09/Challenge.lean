import CPSLib.Examples.FM09.Model

open CPSLib

namespace FM09

/-!
## NTRM preserves pairwise separation
-/

/--
For any fleet size, initially mutually separated aircraft
remain separated after any NTRM run.
-/
theorem ntrm_safe :
    ∀ (n : ℕ) (p : ℝ) (x d : Fin n → Vec2),
      SeparatedMany p x →
        ∀ res ∈ SetM.run (ntrmProg p x d),
          SeparatedMany p res := sorry

/-!
## FTRM safety after complete iterations
-/

/--
For any fleet size, initially far-separated aircraft with equal speeds
remain separated by the protected distance after any complete FTRM run.
-/
theorem ftrm_end_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ res ∈ SetM.run (ftrmProg p r x d),
          SeparatedMany p res.x := sorry

/-!
## FTRM safety within all intermediate states
-/

/--
Throughout safety for the FTRM for any fleet size: after any number of (incl. zero)
FTRM iterations, running any prefix of another FTRM iteration is safe.
-/
theorem ftrm_throughout_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ st ∈ SetM.run (ftrmProg p r x d), ∀ k : Fin 5,
          ∀ res ∈ SetM.run (ftrmPrefixProg p st.r k st.x st.d),
          SeparatedMany p res := sorry

end FM09
