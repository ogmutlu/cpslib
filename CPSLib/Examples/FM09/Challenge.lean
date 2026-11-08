import CPSLib.Examples.FM09.Model

open CPSLib

namespace FM09

/-!
## NTRM preserves pairwise separation

The simplified controller starts from a fleet whose distinct aircraft are
separated by the protected distance `p`. No restriction on the initial velocities
is needed: instantaneous entry assigns tangential velocities before circular flight.

The following statement generalizes the NTRM safety specification in Fig. 5 to
any finite fleet size.
-/

/-- For any fleet size, initially mutually separated aircraft
remain separated after any NTRM run. -/
theorem ntrm_many_safe :
    ∀ (n : ℕ) (p : ℝ) (x d : Fin n → Vec2), SeparatedMany p x →
      ∀ res ∈ SetM.run (ntrm_many p x d), SeparatedMany p res := sorry

/-!
## FTRM safety after complete iterations

Curved entry needs a larger initial margin than the protected distance alone.
We assume a nonnegative protected distance, equal linear speeds, a positive
initial radius, and pairwise separation by `far p r`.

Under these assumptions, every completed FTRM run ends with pairwise separation
by `p`. This endpoint claim alone does not describe states inside an iteration.
The exit program omits the final far-separation test from Fig. 10, which makes
the theorem trivial.
-/

/-- For any fleet size, initially far-separated aircraft with equal speeds
remain separated by the protected distance after any complete FTRM run. -/
theorem ftrm_many_end_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ res ∈ SetM.run (ftrm_many p r x d), SeparatedMany p res.x := sorry

/-!
## FTRM safety within an iteration

To include intermediate states, first execute any number of complete iterations,
including zero. From the returned state `st`, observe a prefix of the next
iteration using `ftrmPrefix_many`. The new iteration uses the returned radius
`st.r`, since negotiation may have changed it.

The five prefix choices cover free flight, negotiation, entry, circular flight,
and exit. In particular, entry and circular prefixes stop before their completion
tests, so the specification includes their intermediate continuous states.
Every such observation must still satisfy pairwise protected separation.
-/

/-- Throughout safety for the FTRM for any fleet size: after any number of (incl. zero)
FTRM iterations, running any prefix of another FTRM iteration is safe. -/
theorem ftrm_many_throughout_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ st ∈ SetM.run (ftrm_many p r x d), ∀ k : Fin 5,
          ∀ res ∈ SetM.run (ftrmPrefix_many p st.r k st.x st.d),
          SeparatedMany p res := sorry

end FM09
