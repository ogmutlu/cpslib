import CPSLib.Examples.FM09.Model
import CPSLib.Tactic.OdeDeriv

open CPSLib
open Std.WP
open scoped RealInnerProductSpace
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace FM09

namespace Defs

/-- Flight equations `F(ω)` for the first aircraft (Section 4.1). -/
@[simp] def F (ω : ℝ) := fun ((_x : Vec2), d) => (d, ω • perp d)

/-- Flight equations `G(ρ)` for the second aircraft (Section 4.1). -/
@[simp] def G (ρ : ℝ) := fun ((_y : Vec2), e) => (e, ρ • perp e)

/-- Joint flight ODE, Section 4.1.
Position vectors x, y
Angular speeds ω, ρ
Linear velocity vectors d, e
-/
@[simp] def flight (ω ρ : ℝ) := fun (x, d, y, e) =>
  let (x', d') := F ω (x, d)
  let (y', e') := G ρ (y, e)
  (x', d', y', e')

/-- Entry geometry condition `C` for the common center and radius (Fig. 10, Eq. (3)). -/
@[reducible]
def C (r : ℝ) (x d y e c : Vec2) : Prop :=
  ‖x - c‖ = √3 * r ∧ ∃ lx ≥ (0: ℝ), x + lx • d = c ∧
  ‖y - c‖ = √3 * r ∧ ∃ ly ≥ (0: ℝ), y + ly • e = c

/-- Tangential roundabout configuration `R` (Eq. (2)). -/
@[reducible]
def R (ω : ℝ) (c : Vec2) (x d y e : Vec2) : Prop :=
  d = ω • perp (x - c) ∧ e = ω • perp (y - c)


/-- All velocities are tangential to the same roundabout. -/
@[reducible] def RMany {n : ℕ} (ω : ℝ) (c : Vec2) (x d : Fin n → Vec2) : Prop :=
  ∀ i, d i = ω • perp (x i - c)

end Defs

open Defs

@[simp] theorem perp_sub (u v : Vec2) : perp (u - v) = perp u - perp v := by
  ext i
  fin_cases i
  · simp [perp, PiLp.toLp_apply]
    ring
  · simp [perp, PiLp.toLp_apply]

theorem inner_perp_self (v : Vec2) : ⟪v, perp v⟫ = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, perp]
  ring

theorem evolve_prefix_closed {α σ : Type} [Evolvable α σ]
    (ode : α) (domain : σ → Prop) (st : σ) (T : ℝ) (trajectory : ℝ → σ)
    (_hT : 0 ≤ T) (hevol : IsEvolution trajectory (Evolvable.denotation ode) domain st T) :
    ∀ t ∈ Set.Icc 0 T, trajectory t ∈ SetM.run (evolve ode domain st) := by
  intro t ht
  apply SemanticODE.mem_evolveSemantic _ domain st t trajectory ht.1
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
  exact ⟨hevol.1, fun τ hτ => hevol.2.1 τ (hsub hτ),
    Evolvable.rest_closed ode trajectory hsub hevol.2.2⟩

noncomputable def speedGap (s : ℝ) : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (_, d, _, _) =>
  ‖d‖ ^ 2 - s ^ 2

noncomputable def otherSpeedGap (s : ℝ) : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (_, _, _, e) =>
  ‖e‖ ^ 2 - s ^ 2

theorem speedGap_hasPrime (s ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ρ)) domain (speedGap s) (fun _ => 0) := by
  ode_deriv [speedGap, flight, F, G, perp]

theorem otherSpeedGap_hasPrime (s ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ρ)) domain (otherSpeedGap s) (fun _ => 0) := by
  ode_deriv [otherSpeedGap, flight, F, G, perp]

theorem pairwise_AC2 :
    ∀ (ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      ∀ x' d' y' e',
        (x', d', y', e') ∈ SetM.run (evolve (flight ω ρ) domain (x, d, y, e)) →
          ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := by
  intro ω ρ domain x d y e xr dr yr er hrun
  have hd := dIeq (ode := flight ω ρ) (domain := domain)
    (pre := fun st => speedGap ‖d‖ st = 0)
    (speedGap ‖d‖) (fun _ => 0) (speedGap_hasPrime ‖d‖ ω ρ domain)
    (fun _ h => h) (fun _ _ => rfl) (x, d, y, e) (by simp [speedGap])
    (xr, dr, yr, er) hrun
  have he := dIeq (ode := flight ω ρ) (domain := domain)
    (pre := fun st => otherSpeedGap ‖e‖ st = 0)
    (otherSpeedGap ‖e‖) (fun _ => 0) (otherSpeedGap_hasPrime ‖e‖ ω ρ domain)
    (fun _ h => h) (fun _ _ => rfl) (x, d, y, e) (by simp [otherSpeedGap])
    (xr, dr, yr, er) hrun
  exact ⟨(sq_eq_sq₀ (norm_nonneg dr) (norm_nonneg d)).mp (sub_eq_zero.mp hd),
    (sq_eq_sq₀ (norm_nonneg er) (norm_nonneg e)).mp (sub_eq_zero.mp he)⟩

noncomputable def roundaboutEnergy (ω : ℝ) (c : Vec2) := fun (x, d, y, e) =>
  ‖d - ω • perp (x - c)‖ ^ 2 + ‖e - ω • perp (y - c)‖ ^ 2

theorem roundaboutEnergy_zero_iff (ω : ℝ) (c : Vec2) (st : Vec2 × Vec2 × Vec2 × Vec2) :
    roundaboutEnergy ω c st = 0 ↔ (let (x, d, y, e) := st; R ω c x d y e) := by
  rcases st with ⟨x, d, y, e⟩
  rw [roundaboutEnergy, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp [R, sub_eq_zero]

theorem roundaboutEnergy_hasPrime (ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ω)) domain
      (roundaboutEnergy ω c) (fun _ => 0) := by
  ode_deriv [roundaboutEnergy, flight, F, G, perp]

theorem R_preserved (ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    (fun (x, d, y, e) => R ω c x d y e)
      [[evolve (flight ω ω) domain]] (fun (x, d, y, e) => R ω c x d y e) := by
  intro initial hpre final hrun
  apply (roundaboutEnergy_zero_iff ω c final).mp
  exact dIeq (ode := flight ω ω) (domain := domain)
    (pre := fun st => roundaboutEnergy ω c st = 0)
    (roundaboutEnergy ω c) (fun _ => 0) (roundaboutEnergy_hasPrime ω c domain)
    (fun _ h => h) (fun _ _ => rfl)
    initial ((roundaboutEnergy_zero_iff ω c initial).mpr hpre) final hrun

noncomputable def separationGap (p : ℝ) : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (x, _, y, _) =>
  ‖x - y‖ ^ 2 - p ^ 2

theorem separationGap_hasPrime (p ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight ω ω))
      (fun (x, d, y, e) => domain (x, d, y, e) ∧ R ω c x d y e) (separationGap p) (fun _ => 0) := by
  ode_deriv [separationGap, R, flight, F, G, perp]

theorem pairwise_AC1_circ :
    ∀ (p ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ x' d' y' e',
          (x', d', y', e') ∈ SetM.run (evolve (flight ω ω) domain (x, d, y, e)) →
            R ω c x' d' y' e' ∧ Separated p x' y' := by
  intro p ω c domain x d y e hpre xr dr yr er hrun
  apply And.intro (R_preserved ω c domain (x, d, y, e) hpre.1 _ hrun)
  have hsafe :
      (fun (x, d, y, e) => R ω c x d y e ∧ Separated p x y)
      [[evolve (flight ω ω) domain]] (fun st => 0 ≤ separationGap p st) := by
    apply dC (cut := fun (x, d, y, e) => R ω c x d y e)
    · intro initial h
      exact R_preserved ω c domain initial h.1
    · apply dIge (separationGap p) (fun _ => 0)
      · exact separationGap_hasPrime p ω c domain
      · rintro ⟨x, d, y, e⟩ h
        exact sub_nonneg.mpr h.2
      · exact fun _ _ => le_rfl
  exact sub_nonneg.mp (hsafe (x, d, y, e) hpre (xr, dr, yr, er) hrun)

@[spec] theorem agree_spec : ⦃True⦄ agree ⦃fun _ => True⦄ := by
  constructor
  intro _ _ _
  trivial

/-- A simultaneous fleet evolution projects to the existing two-aircraft ODE. -/
theorem flight_many_pair {n : ℕ} (ω : Fin n → ℝ) (domain : (Fin n → Vec2) × (Fin n → Vec2) → Prop)
    (x d : Fin n → Vec2) (i j : Fin n)
    (res : (Fin n → Vec2) × (Fin n → Vec2))
    (hrun : res ∈ SetM.run (evolve (flight_many ω) domain (x, d))) :
    (res.1 i, res.2 i, res.1 j, res.2 j) ∈
      SetM.run (evolve (flight (ω i) (ω j)) (fun _ => True) (x i, d i, x j, d j)) := by
  apply (evolveSemantic_spec (Evolvable.denotation (flight_many ω)) domain (x, d)).le_wp
    ?_ res hrun
  intro duration hduration trajectory hevolution
  apply SemanticODE.mem_evolveSemantic _ _ _ duration
    (fun t => ((trajectory t).1 i, (trajectory t).2 i,
      (trajectory t).1 j, (trajectory t).2 j)) hduration
  apply And.intro
  · simp only [hevolution.1]
  · apply And.intro (fun _ _ => trivial)
    intro t ht
    have hx := OdeDeriv.hasDerivWithinAt_fst (hevolution.2.2 t ht)
    have hd := OdeDeriv.hasDerivWithinAt_snd (hevolution.2.2 t ht)
    exact (OdeDeriv.hasDerivWithinAt_apply i hx).prodMk
      ((OdeDeriv.hasDerivWithinAt_apply i hd).prodMk
        ((OdeDeriv.hasDerivWithinAt_apply j hx).prodMk
          (OdeDeriv.hasDerivWithinAt_apply j hd)))

/-- Every pair remains separated during the unrestricted common circular flight. -/
theorem circ_many_safe {n : ℕ} (p ω : ℝ) (c : Vec2)
    (domain : (Fin n → Vec2) × (Fin n → Vec2) → Prop) (x d : Fin n → Vec2) :
    RMany ω c x d ∧ SeparatedMany p x →
      ∀ res ∈ SetM.run (evolve (flight_many (fun _ => ω)) domain (x, d)),
        SeparatedMany p res.1 := by
  intro hpre res hrun i j hij
  exact (pairwise_AC1_circ p ω c (fun _ => True) (x i) (d i) (x j) (d j)
    ⟨⟨hpre.1 i, hpre.1 j⟩, hpre.2 i j hij⟩
    (res.1 i) (res.2 i) (res.1 j) (res.2 j)
    (flight_many_pair (fun _ => ω) domain x d i j res hrun)).2

/-- A single free-flight segment, with the same domain as the model. -/
def freeStep_many {n : ℕ} (p : ℝ) (ω : Fin n → ℝ) (x d : Fin n → Vec2) :=
  evolve (flight_many ω) (fun (x, _) => SeparatedMany p x) (x, d)

@[spec] theorem freeStep_many_spec {n : ℕ} (p : ℝ) (ω : Fin n → ℝ) (x d : Fin n → Vec2) :
    ⦃SeparatedMany p x⦄ freeStep_many p ω x d ⦃fun (xr, _) => SeparatedMany p xr⦄ := by
  exact ⟨fun hpre => dW (ode := flight_many ω)
    (pre := fun (x, _) => SeparatedMany p x) (fun _ hdomain => hdomain) (x, d) hpre⟩

/-- The free-flight loop with its mutual-separation invariant. -/
def free_many' {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) : SetM ((Fin n → Vec2) × (Fin n → Vec2))
    requires SeparatedMany p x
    ensures (xr, _) => SeparatedMany p xr
    := do
  let mut (x, d) := (x, d)
  let iterations ← choose ℕ
  for _ in [:iterations]
      invariant _pref _suff => SeparatedMany p x do
    let ω ← choose (Fin n → ℝ)
    (x, d) ← freeStep_many p ω x d
  return (x, d)

theorem free_many_eq {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) : free_many p x d = free_many' p x d := by
  rfl

/-- The unrestricted circular phase, with parameters used by its contract. -/
def circStep_many {n : ℕ} (_p ω : ℝ) (_c : Vec2) (x d : Fin n → Vec2) :=
  evolve (flight_many (fun _ => ω)) (fun _ => True) (x, d)

@[spec] theorem circStep_many_spec {n : ℕ} (p ω : ℝ) (c : Vec2) (x d : Fin n → Vec2) :
    ⦃RMany ω c x d ∧ SeparatedMany p x⦄ circStep_many p ω c x d
    ⦃fun (xr, _) => SeparatedMany p xr⦄ := by
  exact ⟨fun hpre => circ_many_safe p ω c (fun _ => True) x d hpre⟩

/-- Compose free flight, shared agreement, instant entry, and circular flight. -/
def ntrm_many' {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) : SetM (Fin n → Vec2)
    requires SeparatedMany p x
    ensures xr => SeparatedMany p xr
    := do
  let mut (x, d) := (x, d)
  let iterations ← choose ℕ
  for _ in [:iterations]
      invariant _pref _suff => SeparatedMany p x do
    (x, d) ← free_many' p x d
    let (ω, c) ← agree
    d := entry_n_many ω c x
    (x, d) ← circStep_many p ω c x d
  return x
where finally
  | spec => all_goals simp_all [entry_n_many]

theorem ntrm_many_eq {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) : ntrm_many p x d = ntrm_many' p x d := by
  rfl

/-- For any fleet size, initially mutually separated aircraft remain separated after NTRM. -/
theorem ntrm_many_safe :
    ∀ (n : ℕ) (p : ℝ) (x d : Fin n → Vec2), SeparatedMany p x →
      ∀ res ∈ SetM.run (ntrm_many p x d), SeparatedMany p res := by
  intro n p x d hpre res hrun
  exact (ntrm_many'.spec p x d).le_wp hpre res hrun

@[simp] theorem norm_perp (v : Vec2) : ‖perp v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, perp, add_comm]

theorem R_relative (ω : ℝ) (c x d y e : Vec2) (h : R ω c x d y e) :
    d - e = ω • perp (x - y) := by
  calc
    d - e = ω • (perp (x - c) - perp (y - c)) := by rw [h.1, h.2, smul_sub]
    _ = ω • perp (x - y) := by
      rw [← perp_sub]
      congr 2
      abel

noncomputable def exitInner : Vec2 × Vec2 × Vec2 × Vec2 → ℝ := fun (x, d, y, e) => ⟪x - y, d - e⟫

theorem exitInner_hasPrime (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight 0 0)) domain exitInner
      (fun (_, d, _, e) => ‖d - e‖ ^ 2) := by
  ode_deriv [exitInner, flight, F, G]

theorem exitGap_hasPrime (p : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight 0 0)) domain (separationGap p)
      (fun st => 2 * exitInner st) := by
  ode_deriv [exitInner, separationGap, flight, F, G]

theorem pairwise_AC7 :
    ∀ (p ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ x' d' y' e',
          (x', d', y', e') ∈ SetM.run (evolve (flight 0 0) (fun _ => True) (x, d, y, e)) →
            Separated p x' y' := by
  intro p ω c x d y e hpre xr dr yr er hrun
  have horth : exitInner (x, d, y, e) = 0 := by
    dsimp [exitInner]
    rw [R_relative ω c x d y e hpre.1, real_inner_smul_right, inner_perp_self, mul_zero]
  have hsafe : (fun st => 0 ≤ exitInner st ∧ 0 ≤ separationGap p st)
      [[evolve (flight 0 0) (fun _ => True)]] (fun st => 0 ≤ separationGap p st) := by
    apply dC (cut := fun st => 0 ≤ exitInner st)
    · apply dIge exitInner (fun (_, d, _, e) => ‖d - e‖ ^ 2)
      · exact exitInner_hasPrime _
      · exact fun _ h => h.1
      · exact fun _ _ => sq_nonneg _
    · apply dIge (separationGap p) (fun st => 2 * exitInner st)
      · exact exitGap_hasPrime p _
      · exact fun _ h => h.2
      · intro st h
        exact mul_nonneg (by norm_num) h.2
  exact sub_nonneg.mp (hsafe (x, d, y, e)
    ⟨horth.ge, sub_nonneg.mpr hpre.2⟩ (xr, dr, yr, er) hrun)

def straightTrajectory (x d y e : Vec2) (t : ℝ) := (x + t • d, d, y + t • e, e)

theorem straightTrajectory_evolution (x d y e : Vec2) (T : ℝ) :
    IsEvolution (straightTrajectory x d y e) (Evolvable.denotation (flight 0 0))
      (fun _ => True) (x, d, y, e) T := by
  apply And.intro (by simp [straightTrajectory])
  apply And.intro (fun _ _ => trivial)
  intro t ht
  simp only [straightTrajectory, flight, F, G, zero_smul]
  change HasDerivWithinAt (fun t => (x + t • d, d, y + t • e, e))
    (d, 0, e, 0) (Set.Icc 0 T) t
  have hx := ((hasDerivAt_id t).smul_const d).const_add x
  have hy := ((hasDerivAt_id t).smul_const e).const_add y
  simpa using (hx.prodMk ((hasDerivAt_const t d).prodMk
    (hy.prodMk (hasDerivAt_const t e)))).hasDerivWithinAt

theorem constant_of_zero_derivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f 0 (Set.Icc 0 T) t) : f T = f 0 := by
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hf
    (C := 0) (fun _ _ => by simp) T ⟨hT, le_rfl⟩
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound

noncomputable def rotate (κ t : ℝ) (v : Vec2) : Vec2 :=
  Real.cos (κ * t) • v + Real.sin (κ * t) • perp v

theorem hasDerivAt_rotate (κ t : ℝ) (v : Vec2) :
    HasDerivAt (fun τ => rotate κ τ v) (κ • perp (rotate κ t v)) t := by
  have hc := (((hasDerivAt_id t).const_mul κ).cos).smul_const v
  have hs := (((hasDerivAt_id t).const_mul κ).sin).smul_const (perp v)
  apply (hc.add hs).congr_deriv
  ext i
  fin_cases i <;> simp [rotate, perp] <;> ring

theorem velocity_solution (κ T : ℝ) (v : ℝ → Vec2) (hT : 0 ≤ T)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (κ • perp (v t)) (Set.Icc 0 T) t) :
    v T = rotate κ T (v 0) := by
  let z := fun t => v t - rotate κ t (v 0)
  have hz : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt z (κ • perp (z t)) (Set.Icc 0 T) t := by
    intro t ht
    simpa only [z, perp_sub, smul_sub] using
      (OdeDeriv.hasDerivWithinAt_sub_apply (hv t ht)
        (hasDerivAt_rotate κ t (v 0)).hasDerivWithinAt)
  have henergy : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun t => ‖z t‖ ^ 2) 0 (Set.Icc 0 T) t := by
    intro t ht
    simpa only [real_inner_smul_right, inner_perp_self, mul_zero] using (hz t ht).norm_sq
  have heq := constant_of_zero_derivative (fun t => ‖z t‖ ^ 2) T hT henergy
  simpa [z, rotate, sub_eq_zero] using heq

noncomputable def displacement (κ t : ℝ) (v : Vec2) : Vec2 :=
  (Real.sin (κ * t) / κ) • v + ((1 - Real.cos (κ * t)) / κ) • perp v

theorem hasDerivAt_displacement (κ t : ℝ) (v : Vec2) (hκ : κ ≠ 0) :
    HasDerivAt (fun τ => displacement κ τ v) (rotate κ t v) t := by
  have hs := ((((hasDerivAt_id t).const_mul κ).sin).div_const κ).smul_const v
  have hc := (((((hasDerivAt_id t).const_mul κ).cos).const_sub 1).div_const κ).smul_const
    (perp v)
  apply (hs.add hc).congr_deriv
  simp [rotate, hκ]

theorem position_solution (κ T : ℝ) (x v : ℝ → Vec2) (hκ : κ ≠ 0) (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (v t) (Set.Icc 0 T) t)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (κ • perp (v t)) (Set.Icc 0 T) t) :
    x T = x 0 + displacement κ T (v 0) := by
  have hvel : ∀ t ∈ Set.Icc 0 T, v t = rotate κ t (v 0) := by
    intro t ht
    exact velocity_solution κ t v ht.1 (fun τ hτ =>
      (hv τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2))
  have hz : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun t => x t - (x 0 + displacement κ t (v 0))) 0
        (Set.Icc 0 T) t := by
    intro t ht
    simpa only [hvel t ht, sub_self] using
      OdeDeriv.hasDerivWithinAt_sub_apply (hx t ht)
        ((hasDerivAt_displacement κ t (v 0) hκ).const_add (x 0)).hasDerivWithinAt
  have heq := constant_of_zero_derivative _ T hT hz
  simpa [displacement, sub_eq_zero] using heq

@[simp] def positionX : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (x, _, _, _) => x
@[simp] def velocityD : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (_, d, _, _) => d
@[simp] def positionY : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (_, _, y, _) => y
@[simp] def velocityE : Vec2 × Vec2 × Vec2 × Vec2 → Vec2 := fun (_, _, _, e) => e

theorem flight_components (ω ρ : ℝ) {path : ℝ → Vec2 × Vec2 × Vec2 × Vec2}
    {interval : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt path (flight ω ρ (path t)) interval t) :
    HasDerivWithinAt (fun τ => positionX (path τ)) (velocityD (path t)) interval t ∧
    HasDerivWithinAt (fun τ => velocityD (path τ)) (ω • perp (velocityD (path t))) interval t ∧
    HasDerivWithinAt (fun τ => positionY (path τ)) (velocityE (path t)) interval t ∧
    HasDerivWithinAt (fun τ => velocityE (path τ)) (ρ • perp (velocityE (path t))) interval t := by
  have hx := OdeDeriv.hasDerivWithinAt_fst h
  have hdye := OdeDeriv.hasDerivWithinAt_snd h
  have hd := OdeDeriv.hasDerivWithinAt_fst hdye
  have hye := OdeDeriv.hasDerivWithinAt_snd hdye
  have hy := OdeDeriv.hasDerivWithinAt_fst hye
  have he := OdeDeriv.hasDerivWithinAt_snd hye
  exact ⟨hx, hd, hy, he⟩

noncomputable def circularTrajectory (κ : ℝ) (x d y e : Vec2) (t : ℝ) :=
  (x + displacement κ t d, rotate κ t d, y + displacement κ t e, rotate κ t e)

theorem flight_solution (κ T : ℝ) (path : ℝ → Vec2 × Vec2 × Vec2 × Vec2) (x d y e : Vec2)
    (hκ : κ ≠ 0) (hT : 0 ≤ T) (hinit : path 0 = (x, d, y, e))
    (hODE : Evolvable.denotation (flight κ κ) path (Set.Icc 0 T)) :
    path T = circularTrajectory κ x d y e T := by
  have hc := fun t ht => flight_components κ κ (hODE t ht)
  have hx := position_solution κ T (fun t => positionX (path t))
    (fun t => velocityD (path t)) hκ hT (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1)
  have hd := velocity_solution κ T (fun t => velocityD (path t)) hT
    (fun t ht => (hc t ht).2.1)
  have hy := position_solution κ T (fun t => positionY (path t))
    (fun t => velocityE (path t)) hκ hT (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2)
  have he := velocity_solution κ T (fun t => velocityE (path t)) hT
    (fun t ht => (hc t ht).2.2.2)
  simp only [hinit, positionX, velocityD, positionY, velocityE] at hx hd hy he
  exact Prod.ext hx (Prod.ext hd (Prod.ext hy he))

theorem circularTrajectory_evolution (κ : ℝ) (x d y e : Vec2) (T : ℝ)
    (hκ : κ ≠ 0) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop)
    (hdom : ∀ t ∈ Set.Icc 0 T, domain (circularTrajectory κ x d y e t)) :
    IsEvolution (circularTrajectory κ x d y e) (Evolvable.denotation (flight κ κ))
      domain (x, d, y, e) T := by
  apply And.intro (by simp [circularTrajectory, displacement, rotate])
  apply And.intro hdom
  intro t ht
  have hx := (hasDerivAt_displacement κ t d hκ).const_add x
  have hd := hasDerivAt_rotate κ t d
  have hy := (hasDerivAt_displacement κ t e hκ).const_add y
  have he := hasDerivAt_rotate κ t e
  exact (hx.prodMk (hd.prodMk (hy.prodMk he))).hasDerivWithinAt

theorem heading_inner (x d c : Vec2) (h : ∃ l ≥ (0 : ℝ), x + l • d = c) :
    ⟪x - c, perp d⟫ = 0 ∧ ⟪x - c, d⟫ = -‖x - c‖ * ‖d‖ := by
  obtain ⟨l, hl, hh⟩ := h
  have hpos : x - c = -(l • d) := by rw [← hh]; abel
  apply And.intro
  · rw [hpos, inner_neg_left, real_inner_smul_left, inner_perp_self]
    ring
  · rw [hpos, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl]
    ring

theorem sqrt_radius (r : ℝ) (hr : 0 ≤ r) : Real.sqrt (3 * r ^ 2) = Real.sqrt 3 * r := by
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

theorem speed_radius (r ω : ℝ) (d : Vec2) (hr : 0 ≤ r)
    (h : (r * ω) ^ 2 = ‖d‖ ^ 2) : ‖d‖ = r * |ω| := by
  apply (sq_eq_sq₀ (norm_nonneg d) (mul_nonneg hr (abs_nonneg ω))).mp
  rw [mul_pow, sq_abs, ← mul_pow]
  exact h.symm

theorem motion_norm_sq (κ t : ℝ) (x d c : Vec2) :
    ‖x + displacement κ t d - c‖ ^ 2 = ‖x - c‖ ^ 2 +
      2 * (Real.sin (κ * t) / κ) * ⟪x - c, d⟫ +
      2 * ((1 - Real.cos (κ * t)) / κ) * ⟪x - c, perp d⟫ +
      2 * ((1 - Real.cos (κ * t)) / κ ^ 2) * ‖d‖ ^ 2 := by
  have hpos : x + displacement κ t d - c = (x - c) + displacement κ t d := by abel
  rw [hpos, norm_add_sq_real]
  simp only [displacement, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, norm_perp, inner_add_right, real_inner_smul_right, real_inner_smul_left,
    inner_perp_self]
  have htrig := congrArg (fun s : ℝ => s / κ ^ 2 * ‖d‖ ^ 2)
    (Real.sin_sq_add_cos_sq (κ * t))
  ring_nf at htrig ⊢
  nlinarith

theorem cos_abs_mul (ω t : ℝ) : Real.cos (ω * t) = Real.cos (|ω| * t) := by
  by_cases h : 0 ≤ ω
  · simp only [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), neg_mul, Real.cos_neg]

theorem sin_div_abs (ω t : ℝ) :
    Real.sin (ω * t) / ω = Real.sin (|ω| * t) / |ω| := by
  by_cases h : 0 ≤ ω
  · simp only [abs_of_nonneg h]
  · simp only [abs_of_neg (lt_of_not_ge h), neg_mul, Real.sin_neg, neg_div_neg_eq]

theorem entry_motion_norm_sq (r ω t : ℝ) (x d c : Vec2) (hω : ω ≠ 0)
    (hposition : ‖x - c‖ = Real.sqrt 3 * r)
    (hheading : ∃ l ≥ (0 : ℝ), x + l • d = c) (hspeed : ‖d‖ = r * |ω|) :
    ‖x + displacement (-ω) t d - c‖ ^ 2 =
      r ^ 2 * (5 - 2 * Real.cos (|ω| * t) - 2 * Real.sqrt 3 * Real.sin (|ω| * t)) := by
  obtain ⟨horth, hinner⟩ := heading_inner x d c hheading
  rw [motion_norm_sq, horth, hinner, hposition]
  simp only [mul_zero, add_zero, neg_mul, Real.cos_neg, Real.sin_neg, neg_div_neg_eq,
    neg_sq, cos_abs_mul ω t, sin_div_abs ω t]
  rw [← sq_abs ω, hspeed, mul_pow (Real.sqrt 3) r, Real.sq_sqrt (by norm_num)]
  field_simp [abs_ne_zero.mpr hω]
  ring

theorem inner_perp_flip (u v : Vec2) : ⟪u, perp v⟫ = -⟪v, perp u⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, perp]
  ring

/-- The conserved anchor geometry of (14)–(15), with the fixed anchor eliminated.
Under the speed equation, this is `ω² * (4*r² - ‖h-c‖²)` for
`h = x - ω⁻¹ • perp d`. -/
noncomputable def entryCircleInvariant (r ω : ℝ) (c : Vec2) := fun (x, d) =>
  ‖d - ω • perp (x - c)‖ ^ 2 -
    2 * ω ^ 2 * (‖x - c‖ ^ 2 - r ^ 2)

theorem entryCircleInvariant_hasPrime (r ω : ℝ) (c : Vec2) :
    HasPrime (Evolvable.denotation (F (-ω))) (fun _ => True)
      (entryCircleInvariant r ω c) (fun _ => 0) := by
  ode_deriv [entryCircleInvariant, F, perp]

theorem entryCircleInvariant_initial (r ω : ℝ) (x d c : Vec2)
    (hposition : ‖x - c‖ = Real.sqrt 3 * r)
    (hheading : ∃ l ≥ (0 : ℝ), x + l • d = c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2) :
    entryCircleInvariant r ω c (x, d) = 0 := by
  have horth : ⟪d, perp (x - c)⟫ = 0 := by
    rw [inner_perp_flip, (heading_inner x d c hheading).1, neg_zero]
  rw [entryCircleInvariant, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, norm_perp, real_inner_smul_right, horth, mul_zero, sub_zero]
  rw [hposition, mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [hspeed]

theorem entry_tangent_of_radius (r ω T : ℝ) (c : Vec2) (x d : ℝ → Vec2) (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (d t) (Set.Icc 0 T) t)
    (hd : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt d ((-ω) • perp (d t)) (Set.Icc 0 T) t)
    (hinit : entryCircleInvariant r ω c (x 0, d 0) = 0)
    (hradius : ‖x T - c‖ ^ 2 = r ^ 2) : d T = ω • perp (x T - c) := by
  have hprime := entryCircleInvariant_hasPrime r ω c (fun t => (x t, d t))
    (Set.Icc 0 T) (fun t ht => (hx t ht).prodMk (hd t ht)) (fun _ _ => trivial)
  have heq := constant_of_zero_derivative
    (fun t => entryCircleInvariant r ω c (x t, d t)) T hT hprime
  rw [hinit] at heq
  simpa only [entryCircleInvariant, hradius, sub_self, mul_zero, sub_zero,
    sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] using heq

theorem pairwise_AC4 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ (duration : ℝ) (trajectory : ℝ → Vec2 × Vec2 × Vec2 × Vec2),
          0 ≤ duration ∧ duration ≤ Real.pi * r / (3 * ‖d‖) ∧
          IsEvolution trajectory (Evolvable.denotation (flight (-ω) (-ω)))
            (fun _ => True) (x, d, y, e) duration ∧
          let xr := (trajectory duration).1
          let yr := (trajectory duration).2.2.1
          ‖xr - c‖ ^ 2 = r ^ 2 ∧ ‖yr - c‖ ^ 2 = r ^ 2 := by
  intro r ω c x d y e ⟨hr, hd, hentry, hspeed, he⟩
  obtain ⟨hx, lx, hlx, hxc, hy, ly, hly, hyc⟩ := hentry
  have hω : ω ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, zero_pow (by decide)] at hspeed
    nlinarith [sq_pos_of_pos hd]
  have hs := speed_radius r ω d hr.le hspeed
  have hes : ‖e‖ = r * |ω| := he.trans hs
  have hxp := hx
  have hyp := hy
  let T := Real.pi / (3 * |ω|)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hperiod : |ω| * T = Real.pi / 3 := by dsimp [T]; field_simp
  apply Exists.intro T
  apply Exists.intro (circularTrajectory (-ω) x d y e)
  apply And.intro hT
  apply And.intro
  · rw [hs]
    dsimp [T]
    apply le_of_eq
    field_simp
  apply And.intro
    (circularTrajectory_evolution (-ω) x d y e T (neg_ne_zero.mpr hω)
      (fun _ => True) (fun _ _ => trivial))
  change ‖x + displacement (-ω) T d - c‖ ^ 2 = r ^ 2 ∧
    ‖y + displacement (-ω) T e - c‖ ^ 2 = r ^ 2
  rw [entry_motion_norm_sq r ω T x d c hω hxp ⟨lx, hlx, hxc⟩ hs,
    entry_motion_norm_sq r ω T y e c hω hyp ⟨ly, hly, hyc⟩ hes, hperiod,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hroot : 5 - 2 * (1 / 2 : ℝ) - 2 * Real.sqrt 3 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  simp only [hroot, mul_one, and_self]

theorem entry_evolution_tangent (r ω T : ℝ) (c x d y e : Vec2)
    (path : ℝ → Vec2 × Vec2 × Vec2 × Vec2)
    (hr : 0 < r) (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (he : ‖e‖ = ‖d‖) (hT : 0 ≤ T)
    (hevo : IsEvolution path (Evolvable.denotation (flight (-ω) (-ω)))
      (fun _ => True) (x, d, y, e) T)
    (hradius : ‖positionX (path T) - c‖ ^ 2 = r ^ 2) :
    let (xr, dr, yr, er) := path T
    R ω c xr dr yr er := by
  obtain ⟨hx, lx, hlx, hxc, hy, ly, hly, hyc⟩ := hentry
  have hxp := hx
  have hyp := hy
  have hdpos : 0 < ‖d‖ := by
    by_contra! h
    have hzero : d = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg d))
    have hxc' : x = c := by simpa only [hzero, smul_zero, add_zero] using hxc
    have hpositive : 0 < ‖x - c‖ := by rw [hxp]; positivity
    simp only [hxc', sub_self, norm_zero, lt_self_iff_false] at hpositive
  have hω : ω ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, zero_pow (by decide)] at hspeed
    nlinarith [sq_pos_of_pos hdpos]
  have hs := speed_radius r ω d hr.le hspeed
  have hes : ‖e‖ = r * |ω| := he.trans hs
  have hsol := flight_solution (-ω) T path x d y e (neg_ne_zero.mpr hω) hT hevo.1 hevo.2.2
  have hnorms : ‖positionY (path T) - c‖ ^ 2 = ‖positionX (path T) - c‖ ^ 2 := by
    rw [hsol]
    change ‖y + displacement (-ω) T e - c‖ ^ 2 = ‖x + displacement (-ω) T d - c‖ ^ 2
    rw [entry_motion_norm_sq r ω T y e c hω hyp ⟨ly, hly, hyc⟩ hes,
      entry_motion_norm_sq r ω T x d c hω hxp ⟨lx, hlx, hxc⟩ hs]
  have hc := fun t ht => flight_components (-ω) (-ω) (hevo.2.2 t ht)
  have hinitX : entryCircleInvariant r ω c (positionX (path 0), velocityD (path 0)) = 0 := by
    simpa only [hevo.1, positionX, velocityD] using
      entryCircleInvariant_initial r ω x d c hxp ⟨lx, hlx, hxc⟩ hspeed
  have hinitY : entryCircleInvariant r ω c (positionY (path 0), velocityE (path 0)) = 0 := by
    simpa only [hevo.1, positionY, velocityE] using
      entryCircleInvariant_initial r ω y e c hyp ⟨ly, hly, hyc⟩ (by rw [he]; exact hspeed)
  have hX := entry_tangent_of_radius r ω T c (fun t => positionX (path t))
    (fun t => velocityD (path t)) hT (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1) hinitX hradius
  have hY := entry_tangent_of_radius r ω T c (fun t => positionY (path t))
    (fun t => velocityE (path t)) hT (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2) hinitY (hnorms.trans hradius)
  exact ⟨hX, hY⟩

theorem pairwise_AC3 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∀ x' d' y' e',
          (x', d', y', e') ∈ SetM.run (evolve (flight (-ω) (-ω)) (fun _ => True) (x, d, y, e)) →
            ‖x' - c‖ ^ 2 = r ^ 2 → R ω c x' d' y' e' := by
  intro r ω c x d y e ⟨hr, hentry, hspeed, he⟩ xr dr yr er hrun
  apply (evolveSemantic_spec (Evolvable.denotation (flight (-ω) (-ω)))
    (fun _ => True) (x, d, y, e)
    (Q := fun (xr, dr, yr, er) => ‖xr - c‖ ^ 2 = r ^ 2 → R ω c xr dr yr er)).le_wp
    ?_ (xr, dr, yr, er) hrun
  intro T hT path hevo hradius
  exact entry_evolution_tangent r ω T c x d y e path hr hentry hspeed he hT hevo hradius

theorem bind_mem {α β : Type} {p : SetM α} {q : α → SetM β} {a : α} {b : β}
    (ha : a ∈ SetM.run p) (hb : b ∈ SetM.run (q a)) : b ∈ SetM.run (p >>= q) := by
  change b ∈ ⋃ a ∈ SetM.run p, SetM.run (q a)
  exact Set.mem_iUnion_of_mem a (Set.mem_iUnion_of_mem ha hb)

theorem speed_constant_variable (ω : ℝ → ℝ) (v : ℝ → Vec2) (T : ℝ) (hT : 0 ≤ T)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (ω t • perp (v t)) (Set.Icc 0 T) t) : ‖v T‖ = ‖v 0‖ := by
  have hprime : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun t => ‖v t‖ ^ 2) 0 (Set.Icc 0 T) t := by
    intro t ht
    simpa only [real_inner_smul_right, inner_perp_self, mul_zero] using (hv t ht).norm_sq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (constant_of_zero_derivative _ T hT hprime)

/-- Equation (7): each coordinate moves by at most `b*T`, even with varying turn rates. -/
theorem coordinate_displacement (ω : ℝ → ℝ) (x v : ℝ → Vec2) (T b : ℝ) (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (v t) (Set.Icc 0 T) t)
    (hv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt v (ω t • perp (v t)) (Set.Icc 0 T) t)
    (hbound : ‖v 0‖ ≤ b) : ∀ i : Fin 2, |x T i - x 0 i| ≤ b * T := by
  have hspeed : ∀ t ∈ Set.Icc 0 T, ‖v t‖ = ‖v 0‖ := by
    intro t ht
    exact speed_constant_variable ω v t ht.1 (fun τ hτ =>
      (hv τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono (Set.Icc_subset_Icc_right ht.2))
  intro i
  have hderiv := fun t ht => OdeDeriv.hasDerivWithinAt_piLp_apply i (hx t ht)
  have hcoord : ∀ t ∈ Set.Ico 0 T, ‖v t i‖ ≤ b := by
    intro t ht
    exact (PiLp.norm_apply_le (v t) i).trans ((hspeed t ⟨ht.1, ht.2.le⟩).le.trans hbound)
  simpa only [Real.norm_eq_abs, sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hcoord T ⟨hT, le_rfl⟩

theorem far_coordinate (q : ℝ) (u : Vec2) (hq : 0 ≤ q)
    (h : (Real.sqrt 2 * q) ^ 2 ≤ ‖u‖ ^ 2) : ∃ i : Fin 2, q ≤ |u i| := by
  by_contra! hnot
  have h0 := (sq_lt_sq₀ (abs_nonneg (u 0)) hq).mpr (hnot 0)
  have h1 := (sq_lt_sq₀ (abs_nonneg (u 1)) hq).mpr (hnot 1)
  rw [sq_abs] at h0 h1
  have hnorm : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hnorm] at h
  nlinarith

/-- Appendix A.5: separation in one coordinate survives the two displacement bounds. -/
theorem separated_of_coordinate_bounds (p b T : ℝ) (x y xr yr : Vec2)
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hsep : Separated (Real.sqrt 2 * (p + 2 * b * T)) x y)
    (hx : ∀ i : Fin 2, |xr i - x i| ≤ b * T)
    (hy : ∀ i : Fin 2, |yr i - y i| ≤ b * T) : Separated p xr yr := by
  obtain ⟨i, hi⟩ := far_coordinate (p + 2 * b * T) (x - y) (by positivity) hsep
  change p + 2 * b * T ≤ |x i - y i| at hi
  have htriangle : |x i - y i| ≤ |xr i - yr i| + |xr i - x i| + |yr i - y i| := by
    have heq : x i - y i = (xr i - yr i) + (-(xr i - x i)) + (yr i - y i) := by ring
    rw [heq]
    have hab := abs_add_le (xr i - yr i) (-(xr i - x i))
    have habc := abs_add_le ((xr i - yr i) + (-(xr i - x i))) (yr i - y i)
    simp only [abs_neg] at hab habc ⊢
    linarith
  have hcoord : p ≤ |xr i - yr i| := by linarith [hx i, hy i]
  have hnorm : |xr i - yr i| ≤ ‖xr - yr‖ := PiLp.norm_apply_le (xr - yr) i
  exact (sq_le_sq₀ hp (norm_nonneg _)).mpr (hcoord.trans hnorm)

theorem pairwise_AC5 :
    ∀ (p b T : ℝ) (x d y e : Vec2) (ω ρ : ℝ → ℝ),
      0 ≤ p ∧ 0 ≤ b ∧ 0 ≤ T ∧ ‖d‖ ^ 2 ≤ ‖e‖ ^ 2 ∧ ‖e‖ ^ 2 ≤ b ^ 2 ∧
      Separated (Real.sqrt 2 * (p + 2 * b * T)) x y →
        ∀ (duration : ℝ) (trajectory : ℝ → Vec2 × Vec2 × Vec2 × Vec2),
          0 ≤ duration → duration ≤ T →
          IsEvolution trajectory
            (Evolvable.denotation
              (fun (t : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2) => flight (ω t) (ρ t) st))
            (fun _ => True) (x, d, y, e) duration →
          let x' := (trajectory duration).1
          let y' := (trajectory duration).2.2.1
          Separated p x' y' := by
  intro p b T x d y e ω ρ ⟨hp, hb, hT, hde, he, hsep⟩ duration path h0 hduration hevo
  have hc := fun t ht => flight_components (ω t) (ρ t) (hevo.2.2 t ht)
  have hdbound : ‖d‖ ≤ b := (sq_le_sq₀ (norm_nonneg d) hb).mp (hde.trans he)
  have hebound : ‖e‖ ≤ b := (sq_le_sq₀ (norm_nonneg e) hb).mp he
  have hx := coordinate_displacement ω (fun t => positionX (path t))
    (fun t => velocityD (path t)) duration b h0 (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1) (by simpa only [hevo.1, velocityD] using hdbound)
  have hy := coordinate_displacement ρ (fun t => positionY (path t))
    (fun t => velocityE (path t)) duration b h0 (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2) (by simpa only [hevo.1, velocityE] using hebound)
  rcases hfinal : path duration with ⟨xr, dr, yr, er⟩
  simp only [hevo.1, hfinal, positionX, positionY] at hx hy
  apply separated_of_coordinate_bounds p b T x y xr yr hp hb hT hsep
  · exact fun i => (hx i).trans (mul_le_mul_of_nonneg_left hduration hb)
  · exact fun i => (hy i).trans (mul_le_mul_of_nonneg_left hduration hb)

theorem separated_mono (p q : ℝ) (x y : Vec2) (hp : 0 ≤ p) (hpq : p ≤ q)
    (h : Separated q x y) : Separated p x y :=
  ((sq_le_sq₀ hp (hp.trans hpq)).mpr hpq).trans h

theorem stationary_flight (ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x y : Vec2) :
    ∀ res ∈ SetM.run (evolve (flight ω ρ) domain (x, 0, y, 0)),
      res = (x, 0, y, 0) := by
  apply (evolveSemantic_spec (Evolvable.denotation (flight ω ρ)) domain (x, 0, y, 0)
    (Q := fun res => res = (x, 0, y, 0))).le_wp
  intro T hT path hevo
  have hc := fun t ht => flight_components ω ρ (hevo.2.2 t ht)
  have hx := coordinate_displacement (fun _ => ω) (fun t => positionX (path t))
    (fun t => velocityD (path t)) T 0 hT (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2.1) (by simp [hevo.1, velocityD])
  have hy := coordinate_displacement (fun _ => ρ) (fun t => positionY (path t))
    (fun t => velocityE (path t)) T 0 hT (fun t ht => (hc t ht).2.2.1)
    (fun t ht => (hc t ht).2.2.2) (by simp [hevo.1, velocityE])
  have hd := speed_constant_variable (fun _ => ω) (fun t => velocityD (path t))
    T hT (fun t ht => (hc t ht).2.1)
  have he := speed_constant_variable (fun _ => ρ) (fun t => velocityE (path t))
    T hT (fun t ht => (hc t ht).2.2.2)
  rcases hfinal : path T with ⟨xr, dr, yr, er⟩
  simp only [hevo.1, hfinal, positionX, velocityD, positionY, velocityE, norm_zero,
    norm_eq_zero, zero_mul, abs_nonpos_iff, sub_eq_zero] at hx hy hd he
  exact Prod.ext (by ext i; exact hx i) (Prod.ext hd (Prod.ext (by ext i; exact hy i) he))

theorem far_ge (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) : p ≤ far p r := by
  have hroot : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hoffset : 0 ≤ (2 / 3 : ℝ) * Real.pi * r := by positivity
  unfold far
  nlinarith [mul_nonneg (sub_nonneg.mpr hroot) (add_nonneg hp hoffset)]

theorem separated_of_far (p r : ℝ) (x y : Vec2) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (h : Separated (far p r) x y) : Separated p x y :=
  separated_mono p (far p r) x y hp (far_ge p r hp hr) h

/-! ## Unrestricted entry: safety for arbitrarily many entry turns -/

/-- Equal entry radii and speeds imply a common time to the negotiated center. -/
theorem entry_common_heading (r ω : ℝ) (c x d y e : Vec2) (hr : 0 < r)
    (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (hde : ‖e‖ = ‖d‖) :
    ∃ l : ℝ, 0 ≤ l ∧ x + l • d = c ∧ y + l • e = c ∧ (l * ω) ^ 2 = 3 := by
  obtain ⟨hx, l, hl, hxc, hy, m, hm, hyc⟩ := hentry
  have hxp : ‖x - c‖ = Real.sqrt 3 * r := hx
  have hyp : ‖y - c‖ = Real.sqrt 3 * r := hy
  have hposx : x - c = -(l • d) := by rw [← hxc]; abel
  have hposy : y - c = -(m • e) := by rw [← hyc]; abel
  have hlnorm : l * ‖d‖ = Real.sqrt 3 * r := by
    simpa only [hposx, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl] using hxp
  have hmnorm : m * ‖d‖ = Real.sqrt 3 * r := by
    simpa only [hposy, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm, hde] using hyp
  have hd : ‖d‖ ≠ 0 := by
    intro hz
    have hroot : 0 < Real.sqrt (3 : ℝ) := by positivity
    rw [hz, mul_zero] at hlnorm
    nlinarith
  have hlm : l = m := mul_right_cancel₀ hd (hlnorm.trans hmnorm.symm)
  apply Exists.intro l
  apply And.intro hl
  apply And.intro hxc
  apply And.intro (by simpa only [hlm] using hyc)
  apply mul_right_cancel₀ (pow_ne_zero 2 hr.ne')
  calc
    (l * ω) ^ 2 * r ^ 2 = l ^ 2 * (r * ω) ^ 2 := by ring
    _ = (l * ‖d‖) ^ 2 := by rw [hspeed, mul_pow]
    _ = (Real.sqrt 3 * r) ^ 2 := congrArg (fun a : ℝ => a ^ 2) hlnorm
    _ = 3 * r ^ 2 := by rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

noncomputable def relativeEntryInvariant (q ω : ℝ) := fun (x, d, y, e) =>
  ‖d - e - ω • perp (x - y)‖ ^ 2 -
    2 * ω ^ 2 * (‖x - y‖ ^ 2 - q)

theorem relativeEntryInvariant_hasPrime (q ω : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    HasPrime (Evolvable.denotation (flight (-ω) (-ω))) domain
      (relativeEntryInvariant q ω) (fun _ => 0) := by
  ode_deriv [relativeEntryInvariant, flight, F, G, perp]

theorem relativeEntryInvariant_initial (l ω : ℝ) (x d y e : Vec2)
    (hpos : x - y = -(l • (d - e))) (hsq : (l * ω) ^ 2 = 3) :
    relativeEntryInvariant (‖x - y‖ ^ 2 / 3) ω (x, d, y, e) = 0 := by
  have horth : ⟪d - e, perp (x - y)⟫ = 0 := by
    rw [inner_perp_flip, hpos, inner_neg_left, real_inner_smul_left, inner_perp_self]
    ring
  have hspeed : ω ^ 2 * ‖x - y‖ ^ 2 = 3 * ‖d - e‖ ^ 2 := by
    rw [hpos, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc
      _ = (l * ω) ^ 2 * ‖d - e‖ ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [relativeEntryInvariant, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_perp,
    real_inner_smul_right, horth, mul_zero, sub_zero]
  nlinarith

/-- Relative anchor geometry bounds distance throughout every complete entry circle.
The duration is arbitrary; no first-hit domain or final radius test is used. -/
theorem unrestricted_entry_distance (r ω : ℝ) (c x d y e : Vec2) (hr : 0 < r)
    (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (hde : ‖e‖ = ‖d‖) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    ∀ res ∈ SetM.run (evolve (flight (-ω) (-ω)) domain (x, d, y, e)),
      let (xr, _, yr, _) := res
      ‖x - y‖ ^ 2 ≤ 3 * ‖xr - yr‖ ^ 2 := by
  obtain ⟨l, _, hxc, hyc, hsq⟩ := entry_common_heading r ω c x d y e hr hentry hspeed hde
  have hpos : x - y = -(l • (d - e)) := by
    calc
      _ = (x + l • d) - (y + l • e) - l • (d - e) := by rw [smul_sub]; abel
      _ = _ := by rw [hxc, hyc, sub_self, zero_sub]
  have hω : ω ≠ 0 := by
    intro hz
    norm_num [hz] at hsq
  intro ⟨xr, dr, yr, er⟩ hrun
  have hinv := dIeq (ode := flight (-ω) (-ω)) (domain := domain)
    (pre := fun st => relativeEntryInvariant (‖x - y‖ ^ 2 / 3) ω st = 0)
    (relativeEntryInvariant (‖x - y‖ ^ 2 / 3) ω) (fun _ => 0)
    (relativeEntryInvariant_hasPrime _ ω domain) (fun _ h => h) (fun _ _ => rfl)
    (x, d, y, e) (relativeEntryInvariant_initial l ω x d y e hpos hsq) (xr, dr, yr, er) hrun
  change ‖dr - er - ω • perp (xr - yr)‖ ^ 2 -
    2 * ω ^ 2 * (‖xr - yr‖ ^ 2 - ‖x - y‖ ^ 2 / 3) = 0 at hinv
  have hprod : 0 ≤ 2 * ω ^ 2 * (‖xr - yr‖ ^ 2 - ‖x - y‖ ^ 2 / 3) := by
    rw [← sub_eq_zero.mp hinv]
    exact sq_nonneg _
  have hfactor : 0 < 2 * ω ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hω)
  have hgap := nonneg_of_mul_nonneg_right hprod hfactor
  nlinarith

/-- The paper's negotiated far margin exceeds the loss allowed by the relative
entry-circle invariant. The entry radii also bound the initial distance above. -/
theorem negotiated_entry_margin (p r : ℝ) (c x d y e : Vec2) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hentry : C r x d y e c) (hsep : Separated (far p r) x y) :
    3 * p ^ 2 ≤ ‖x - y‖ ^ 2 := by
  obtain ⟨hx, _, _, _, hy, _, _, _⟩ := hentry
  have hupper : ‖x - y‖ ≤ 2 * Real.sqrt 3 * r := by
    calc
      _ = ‖(x - c) - (y - c)‖ := by congr 1; abel
      _ ≤ ‖x - c‖ + ‖y - c‖ := norm_sub_le _ _
      _ = _ := by rw [hx, hy]; ring
  have hupperSq : ‖x - y‖ ^ 2 ≤ 12 * r ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (x - y)) (by positivity)).mpr hupper
    norm_num only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h
    exact h
  have hoffset : r ≤ (2 / 3 : ℝ) * Real.pi * r := by
    have hpi : (1 : ℝ) ≤ (2 / 3 : ℝ) * Real.pi := by nlinarith [Real.two_le_pi]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hr
  have hsmall : 0 ≤ Real.sqrt 2 * (p + r) := by positivity
  have hlarge : 0 ≤ far p r := by unfold far; positivity
  have hfar : Real.sqrt 2 * (p + r) ≤ far p r := by
    unfold far
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
  have hlower : 2 * (p + r) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have h := ((sq_le_sq₀ hsmall hlarge).mpr hfar).trans hsep
    simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using h
  have hprod : 0 ≤ p * r := mul_nonneg hp hr
  have hbound : p ≤ 2 * r := by
    by_contra! h
    have hpr : 2 * r ^ 2 ≤ p * r := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h.le) hr]
    have hsq : (2 * r) ^ 2 < p ^ 2 := (sq_lt_sq₀ (by positivity) hp).mpr h
    nlinarith
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hbound), sq_nonneg p]

/-- Unrestricted entry preserves separation at every intermediate time. -/
theorem unrestricted_entry_safe (p r ω : ℝ) (c x d y e : Vec2)
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hentry : C r x d y e c)
    (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2) (hde : ‖e‖ = ‖d‖)
    (hsep : Separated (far p r) x y) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) :
    ∀ res ∈ SetM.run (evolve (flight (-ω) (-ω)) domain (x, d, y, e)),
      let (xr, _, yr, _) := res
      Separated p xr yr := by
  intro ⟨xr, dr, yr, er⟩ hrun
  by_cases hrpos : 0 < r
  · have hbound := unrestricted_entry_distance r ω c x d y e hrpos hentry hspeed hde
      domain (xr, dr, yr, er) hrun
    have hmargin := negotiated_entry_margin p r c x d y e hp hr hentry hsep
    change p ^ 2 ≤ ‖xr - yr‖ ^ 2
    nlinarith
  · have hz : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    have hd : d = 0 := by simpa [hz] using hspeed.symm
    have he : e = 0 := by simpa [hd] using hde
    have hrest := stationary_flight (-ω) (-ω) domain x y (xr, dr, yr, er)
      (by simpa only [hd, he] using hrun)
    have hx : xr = x := congrArg positionX hrest
    have hy : yr = y := congrArg positionY hrest
    rw [hx, hy]
    exact separated_of_far p r x y hp hr hsep

/-- Successful unrestricted entry establishes tangency after any number of turns. -/
theorem unrestricted_entry_tangent (r ω : ℝ) (c x d y e : Vec2) (hr : 0 ≤ r)
    (hentry : C r x d y e c) (hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2)
    (hde : ‖e‖ = ‖d‖) :
    ∀ res ∈ SetM.run (evolve (flight (-ω) (-ω)) (fun _ => True) (x, d, y, e)),
      ‖positionX res - c‖ ^ 2 = r ^ 2 →
      let (xr, dr, yr, er) := res
      R ω c xr dr yr er := by
  intro ⟨xr, dr, yr, er⟩ hrun
  by_cases hrpos : 0 < r
  · exact pairwise_AC3 r ω c x d y e ⟨hrpos, hentry, hspeed, hde⟩ xr dr yr er hrun
  · intro _
    have hz : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    obtain ⟨hx, _, _, _, hy, _, _, _⟩ := hentry
    have hxc : x = c := sub_eq_zero.mp (norm_eq_zero.mp (by simpa [hz] using hx))
    have hyc : y = c := sub_eq_zero.mp (norm_eq_zero.mp (by simpa [hz] using hy))
    have hd : d = 0 := by simpa [hz] using hspeed.symm
    have he : e = 0 := by simpa [hd] using hde
    have hrest := stationary_flight (-ω) (-ω) (fun _ => True) x y (xr, dr, yr, er)
      (by simpa only [hd, he] using hrun)
    rw [hrest]
    have hperp : perp (0 : Vec2) = 0 := by
      ext i
      fin_cases i <;> simp [perp, PiLp.toLp_apply]
    simp only [R, hxc, hyc, sub_self, hperp, smul_zero, and_self]

/-! ## Synchronized FTRM for a finite fleet -/

section

theorem flight_many_speeds {n : ℕ} (ω : Fin n → ℝ)
    (domain : (Fin n → Vec2) × (Fin n → Vec2) → Prop) (x d : Fin n → Vec2)
    (res : (Fin n → Vec2) × (Fin n → Vec2))
    (hrun : res ∈ SetM.run (evolve (flight_many ω) domain (x, d))) :
    ∀ i, ‖res.2 i‖ = ‖d i‖ := by
  intro i
  exact (pairwise_AC2 (ω i) (ω i) (fun _ => True) (x i) (d i) (x i) (d i)
    (res.1 i) (res.2 i) (res.1 i) (res.2 i)
    (flight_many_pair ω domain x d i i res hrun)).1

def entrySafeStep_many {n : ℕ} (_p _r ω : ℝ) (_c : Vec2) (x d : Fin n → Vec2) :=
  entryEvol_many ω x d

@[spec] theorem entryEvol_many_spec {n : ℕ} (p r ω : ℝ) (c : Vec2) (x d : Fin n → Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ ConditionC r c x d ∧ (∀ i, (r * ω) ^ 2 = ‖d i‖ ^ 2) ∧
      EqualSpeeds d ∧ SeparatedMany (far p r) x⦄
    entrySafeStep_many p r ω c x d
    ⦃fun (xr, dr) => SeparatedMany p xr ∧
      ((∀ i, ‖xr i - c‖ ^ 2 = r ^ 2) → RMany ω c xr dr) ∧
      (∀ i, ‖dr i‖ = ‖d i‖)⦄ := by
  constructor
  rintro ⟨hp, hr, hc, hs, heq, hsep⟩ ⟨xr, dr⟩ hrun
  have hpair (i j : Fin n) : (xr i, dr i, xr j, dr j) ∈
      SetM.run (evolve (flight (-ω) (-ω)) (fun _ => True) (x i, d i, x j, d j)) :=
    flight_many_pair (fun _ => -ω) (fun _ => True) x d i j (xr, dr) hrun
  have hC (i j : Fin n) : C r (x i) (d i) (x j) (d j) c := by
    obtain ⟨hi, li, hli, hxi⟩ := hc i
    obtain ⟨hj, lj, hlj, hxj⟩ := hc j
    exact ⟨hi, li, hli, hxi, hj, lj, hlj, hxj⟩
  refine ⟨?_, ?_, flight_many_speeds (fun _ : Fin n => -ω) (fun _ => True) x d (xr, dr) hrun⟩
  · intro i j hij
    exact unrestricted_entry_safe p r ω c (x i) (d i) (x j) (d j)
      hp hr (hC i j) (hs i) (heq j i) (hsep i j hij) (fun _ => True)
      (xr i, dr i, xr j, dr j) (hpair i j)
  · intro hreach i
    exact (unrestricted_entry_tangent r ω c (x i) (d i) (x i) (d i) hr
      (hC i i) (hs i) rfl (xr i, dr i, xr i, dr i) (hpair i i) (hreach i)).1
def freeSafeStep_many {n : ℕ} (p r : ℝ) (ω : Fin n → ℝ) (x d : Fin n → Vec2) :=
  freeStep_many (far p r) ω x d

@[spec] theorem freeSafeStep_many_spec {n : ℕ} (p r : ℝ) (ω : Fin n → ℝ)
    (x d : Fin n → Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ SeparatedMany p x⦄ freeSafeStep_many p r ω x d
    ⦃fun (xr, dr) => SeparatedMany p xr ∧ ∀ i, ‖dr i‖ = ‖d i‖⦄ := by
  constructor
  rintro ⟨hp, hr, _⟩
  apply SetM.wp_and
  · exact dW (ode := flight_many ω) (pre := fun _ => True)
      (fun (xr, _) hdom i j hij => separated_of_far p r (xr i) (xr j) hp hr (hdom i j hij))
      (x, d) trivial
  · intro res hrun
    exact flight_many_speeds ω _ x d res hrun

def free_safe_many {n : ℕ} (p r : ℝ) (x d₀ : Fin n → Vec2) :
    SetM ((Fin n → Vec2) × (Fin n → Vec2))
    requires 0 ≤ p ∧ 0 ≤ r ∧ SeparatedMany p x
    ensures (xr, dr) => SeparatedMany p xr ∧ ∀ i, ‖dr i‖ = ‖d₀ i‖
    := do
  let mut (x, d) := (x, d₀)
  let iterations ← choose ℕ
  for _ in [:iterations]
      invariant _pref _suff =>
        0 ≤ p ∧ 0 ≤ r ∧ SeparatedMany p x ∧ ∀ i, ‖d i‖ = ‖d₀ i‖ do
    let ω ← choose (Fin n → ℝ)
    (x, d) ← freeSafeStep_many p r ω x d
  return (x, d)

def agree_f_many' {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) : SetM (ℝ × Vec2 × ℝ)
    requires True
    ensures (ω, c, r) => 0 ≤ r ∧ ConditionC r c x d ∧ SeparatedMany (far p r) x ∧
      ∀ i, (r * ω) ^ 2 = ‖d i‖ ^ 2
    := do
  let c ← choose Vec2
  let r ← chooseFrom {r : ℝ | r > 0}
  ensure (ConditionC r c x d)
  unless SeparatedMany (far p r) x do abort
  let ω ← choose ℝ
  unless ∀ i, (r * ω) ^ 2 = ‖d i‖ ^ 2 do abort
  return (ω, c, r)
where finally
  | spec => all_goals grind [SetM.run]

def entry_f_many' {n : ℕ} (p r ω : ℝ) (c : Vec2) (x d : Fin n → Vec2) :
    SetM ((Fin n → Vec2) × (Fin n → Vec2))
    requires 0 ≤ p ∧ 0 ≤ r ∧ ConditionC r c x d ∧ (∀ i, (r * ω) ^ 2 = ‖d i‖ ^ 2) ∧
      EqualSpeeds d ∧ SeparatedMany (far p r) x
    ensures (xr, dr) => RMany ω c xr dr ∧ SeparatedMany p xr ∧ ∀ i, ‖dr i‖ = ‖d i‖
    := do
  let (x, d) ← entrySafeStep_many p r ω c x d
  unless ∀ i, ‖x i - c‖ ^ 2 = r ^ 2 do abort
  return (x, d)

def circSafeStep_many {n : ℕ} (_p ω : ℝ) (_c : Vec2) (x₀ d₀ x d : Fin n → Vec2) :=
  circEvol_many ω x₀ d₀ x d

@[spec] theorem circEvol_many_spec {n : ℕ} (p ω : ℝ) (c : Vec2)
    (x₀ d₀ x d : Fin n → Vec2) :
    ⦃RMany ω c x d ∧ SeparatedMany p x⦄ circSafeStep_many p ω c x₀ d₀ x d
    ⦃fun (xr, dr) => RMany ω c xr dr ∧ SeparatedMany p xr ∧ ∀ i, ‖dr i‖ = ‖d i‖⦄ := by
  constructor
  rintro ⟨hR, hsep⟩ ⟨xr, dr⟩ hrun
  let D : (Fin n → Vec2) × (Fin n → Vec2) → Prop := fun (x, d) =>
    ¬ExitReadyMany x₀ d₀ x d ∨
      (x, d) ∈ frontier {st | ExitReadyMany x₀ d₀ st.1 st.2}
  have hevo : (xr, dr) ∈ SetM.run (evolve (flight_many (fun _ => ω)) D (x, d)) := hrun
  refine ⟨?_, circ_many_safe p ω c D x d ⟨hR, hsep⟩ (xr, dr) hevo,
    flight_many_speeds (fun _ : Fin n => ω) D x d (xr, dr) hevo⟩
  intro i
  exact (R_preserved ω c (fun _ => True) (x i, d i, x i, d i) ⟨hR i, hR i⟩
    (xr i, dr i, xr i, dr i)
    (flight_many_pair (fun _ => ω) D x d i i (xr, dr) hevo)).1

def exitSafeStep_many {n : ℕ} (_p _ω : ℝ) (_c : Vec2) (x d : Fin n → Vec2) :=
  exitEvol_many x d

@[spec] theorem exitEvol_many_spec {n : ℕ} (p ω : ℝ) (c : Vec2)
    (x d : Fin n → Vec2) :
    ⦃RMany ω c x d ∧ SeparatedMany p x⦄ exitSafeStep_many p ω c x d
    ⦃fun (xr, dr) => SeparatedMany p xr ∧ ∀ i, ‖dr i‖ = ‖d i‖⦄ := by
  constructor
  rintro ⟨hR, hsep⟩ ⟨xr, dr⟩ hrun
  refine ⟨?_, flight_many_speeds (fun _ : Fin n => 0) (fun _ => True) x d (xr, dr) hrun⟩
  intro i j hij
  exact pairwise_AC7 p ω c (x i) (d i) (x j) (d j) ⟨⟨hR i, hR j⟩, hsep i j hij⟩
    (xr i) (dr i) (xr j) (dr j)
    (flight_many_pair (fun _ => 0) (fun _ => True) x d i j (xr, dr) hrun)

def circ_f_many' {n : ℕ} (p ω : ℝ) (c : Vec2) (x₀ d₀ x d : Fin n → Vec2) :
    SetM ((Fin n → Vec2) × (Fin n → Vec2))
    requires RMany ω c x d ∧ SeparatedMany p x
    ensures (xr, dr) => RMany ω c xr dr ∧ SeparatedMany p xr ∧ ∀ i, ‖dr i‖ = ‖d i‖
    := do
  let (x, d) ← circSafeStep_many p ω c x₀ d₀ x d
  ensure (ExitReadyMany x₀ d₀ x d)
  return (x, d)

def ftrm_many' {n : ℕ} (p r : ℝ) (x₀ d₀ : Fin n → Vec2) : SetM (FtrmManyResult n)
    requires 0 ≤ p ∧ 0 ≤ r ∧ EqualSpeeds d₀ ∧ SeparatedMany p x₀
    ensures res => 0 ≤ res.r ∧ EqualSpeeds res.d ∧ SeparatedMany p res.x
    := do
  let mut (x, d) := (x₀, d₀)
  let mut r := r
  let iterations ← choose ℕ
  for _ in [:iterations]
      invariant _pref _suff => 0 ≤ p ∧ 0 ≤ r ∧ EqualSpeeds d ∧ SeparatedMany p x do
    (x, d) ← free_safe_many p r x d
    let (ω, c, r_new) ← agree_f_many' p x d
    r := r_new
    let (x₀, d₀) := (x, d)
    (x, d) ← entry_f_many' p r ω c x d
    (x, d) ← circ_f_many' p ω c x₀ d₀ x d
    (x, d) ← exitSafeStep_many p ω c x d
  return { x, d, r }
where finally
  | spec => all_goals simp_all [EqualSpeeds]; all_goals grind

theorem ftrm_many_eq {n : ℕ} (p r : ℝ) (x d : Fin n → Vec2) :
    ftrm_many p r x d = ftrm_many' p r x d := rfl

@[spec] theorem ftrm_many_spec {n : ℕ} (p r : ℝ) (x d : Fin n → Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ EqualSpeeds d ∧ SeparatedMany p x⦄ ftrm_many p r x d
    ⦃fun res => 0 ≤ res.r ∧ EqualSpeeds res.d ∧ SeparatedMany p res.x⦄ :=
  ftrm_many'.spec p r x d

def ftrmPrefix_many' {n : ℕ} (p r : ℝ) (k : Fin 5) (x d : Fin n → Vec2) :
    SetM (Fin n → Vec2)
    requires 0 ≤ p ∧ 0 ≤ r ∧ EqualSpeeds d ∧ SeparatedMany p x
    ensures xr => SeparatedMany p xr
    := do
  let (x, d) ← free_safe_many p r x d
  if k = 0 then return x
  let (ω, c, r) ← agree_f_many' p x d
  if k = 1 then return x
  let (x₀, d₀) := (x, d)
  let (x, d) ← entrySafeStep_many p r ω c x d
  if k = 2 then return x
  unless ∀ i, ‖x i - c‖ ^ 2 = r ^ 2 do abort
  let (x, d) ← circSafeStep_many p ω c x₀ d₀ x d
  if k = 3 then return x
  ensure (ExitReadyMany x₀ d₀ x d)
  let (x, _) ← exitSafeStep_many p ω c x d
  return x
where finally
  | spec => all_goals simp_all [EqualSpeeds]; all_goals grind

theorem ftrmPrefix_many_eq {n : ℕ} (p r : ℝ) (k : Fin 5) (x d : Fin n → Vec2) :
    ftrmPrefix_many p r k x d = ftrmPrefix_many' p r k x d := rfl

@[spec] theorem ftrmPrefix_many_spec {n : ℕ} (p r : ℝ) (k : Fin 5) (x d : Fin n → Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ EqualSpeeds d ∧ SeparatedMany p x⦄ ftrmPrefix_many p r k x d
    ⦃fun xr => SeparatedMany p xr⦄ := ftrmPrefix_many'.spec p r k x d

theorem ftrm_many_end_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ res ∈ SetM.run (ftrm_many p r x d), SeparatedMany p res.x := by
  intro n p r x d ⟨hp, hspeed, hr, hfar⟩ res hrun
  have hsep : SeparatedMany p x := by
    intro i j hij
    exact separated_of_far p r (x i) (x j) hp hr.le (hfar i j hij)
  exact ((ftrm_many_spec p r x d).le_wp ⟨hp, hr.le, hspeed, hsep⟩ res hrun).2.2

theorem ftrm_many_throughout_safe :
    ∀ (n : ℕ) (p r : ℝ) (x d : Fin n → Vec2),
      0 ≤ p ∧ EqualSpeeds d ∧ 0 < r ∧ SeparatedMany (far p r) x →
        ∀ st ∈ SetM.run (ftrm_many p r x d), ∀ k : Fin 5,
          ∀ res ∈ SetM.run (ftrmPrefix_many p st.r k st.x st.d), SeparatedMany p res := by
  intro n p r x d ⟨hp, hspeed, hr, hfar⟩ st hrun k res hprefix
  have hsep : SeparatedMany p x := by
    intro i j hij
    exact separated_of_far p r (x i) (x j) hp hr.le (hfar i j hij)
  obtain ⟨hr', hs', hsep'⟩ := (ftrm_many_spec p r x d).le_wp ⟨hp, hr.le, hspeed, hsep⟩ st hrun
  exact (ftrmPrefix_many_spec p st.r k st.x st.d).le_wp ⟨hp, hr', hs', hsep'⟩ res hprefix

end

end FM09
