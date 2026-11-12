import CPSLib.Examples.FM09.Extra.Model
import CPSLib.Examples.FM09.Proof

open CPSLib
open Std.WP
open scoped RealInnerProductSpace
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace FM09

open Defs

theorem AC1_circ :
    ∀ (p ω : ℝ) (c : Vec2) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ x' d' y' e',
          (x', d', y', e') ∈ SetM.run (evolve (flight ω ω) domain (x, d, y, e)) →
            R ω c x' d' y' e' ∧ Separated p x' y' := pairwise_AC1_circ

theorem AC2 :
    ∀ (ω ρ : ℝ) (domain : Vec2 × Vec2 × Vec2 × Vec2 → Prop) (x d y e : Vec2),
      ∀ x' d' y' e',
        (x', d', y', e') ∈ SetM.run (evolve (flight ω ρ) domain (x, d, y, e)) →
          ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := pairwise_AC2

theorem AC3 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∀ x' d' y' e',
          (x', d', y', e') ∈ SetM.run (evolve (flight (-ω) (-ω)) (fun _ => True) (x, d, y, e)) →
            ‖x' - c‖ ^ 2 = r ^ 2 → R ω c x' d' y' e' := pairwise_AC3

theorem AC4 :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ (duration : ℝ) (trajectory : ℝ → Vec2 × Vec2 × Vec2 × Vec2),
          0 ≤ duration ∧ duration ≤ Real.pi * r / (3 * ‖d‖) ∧
          IsEvolution trajectory (Evolvable.denotation (flight (-ω) (-ω)))
            (fun _ => True) (x, d, y, e) duration ∧
          let xr := (trajectory duration).1
          let yr := (trajectory duration).2.2.1
          ‖xr - c‖ ^ 2 = r ^ 2 ∧ ‖yr - c‖ ^ 2 = r ^ 2 := pairwise_AC4

theorem AC5 :
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
          Separated p x' y' := pairwise_AC5

theorem AC7 :
    ∀ (p ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ Separated p x y →
        ∀ x' d' y' e',
          (x', d', y', e') ∈ SetM.run (evolve (flight 0 0) (fun _ => True) (x, d, y, e)) →
            Separated p x' y' := pairwise_AC7

/-! ## Two-aircraft instances of the fleet safety results -/

theorem separatedMany_pair (p : ℝ) (x y : Vec2) :
    SeparatedMany p ![x, y] ↔ Separated p x y := by
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Separated, norm_sub_rev]

theorem equalSpeedsMany_pair (d e : Vec2) :
    EqualSpeeds ![d, e] ↔ ‖d‖ = ‖e‖ := by
  constructor
  · intro h
    exact h 0 1
  · intro h i j
    fin_cases i <;> fin_cases j <;> simp_all

theorem ntrm_many_two_safe (p : ℝ) (x d y e : Vec2)
    (h : Separated p x y) :
    ∀ res ∈ SetM.run (ntrmProg p ![x, y] ![d, e]), Separated p (res 0) (res 1) := by
  intro res hrun
  exact ntrm_safe 2 p ![x, y] ![d, e] ((separatedMany_pair p x y).2 h)
    res hrun 0 1 (by decide)

theorem ftrm_many_two_end_safe (p r : ℝ) (x d y e : Vec2)
    (h : 0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y) :
    ∀ res ∈ SetM.run (ftrmProg p r ![x, y] ![d, e]), Separated p (res.x 0) (res.x 1) := by
  intro res hrun
  exact ftrm_end_safe 2 p r ![x, y] ![d, e]
    ⟨h.1, (equalSpeedsMany_pair d e).2 h.2.1, h.2.2.1,
      (separatedMany_pair (far p r) x y).2 h.2.2.2⟩ res hrun 0 1 (by decide)

theorem ftrm_many_two_throughout_safe (p r : ℝ) (x d y e : Vec2)
    (h : 0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y) :
    ∀ st ∈ SetM.run (ftrmProg p r ![x, y] ![d, e]), ∀ k : Fin 5,
      ∀ res ∈ SetM.run (ftrmPrefixProg p st.r k st.x st.d),
        Separated p (res 0) (res 1) := by
  intro st hrun k res hprefix
  exact ftrm_throughout_safe 2 p r ![x, y] ![d, e]
    ⟨h.1, (equalSpeedsMany_pair d e).2 h.2.1, h.2.2.1,
      (separatedMany_pair (far p r) x y).2 h.2.2.2⟩ st hrun k res hprefix 0 1 (by decide)

/-! ## Original two-aircraft controllers -/

def freeStep (p ω ρ : ℝ) (x d y e : Vec2) :=
  evolve (flight ω ρ) (fun (x, _, y, _) => Separated p x y) (x, d, y, e)

@[spec] theorem freeStep_spec (p ω ρ : ℝ) (x d y e : Vec2) :
    ⦃Separated p x y⦄ freeStep p ω ρ x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  intro hpre
  apply SetM.wp_and
  · exact dW (ode := flight ω ρ)
      (pre := fun (x, (_ : Vec2), y, (_ : Vec2)) => Separated p x y)
      (fun _ hdom => hdom) (x, d, y, e) hpre
  · intro ⟨xr, dr, yr, er⟩ hrun
    exact AC2 ω ρ _ x d y e xr dr yr er hrun

def free' (p : ℝ) (x d₀ y e₀ : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires Separated p x y
    ensures (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d₀‖ ∧ ‖er‖ = ‖e₀‖
    := do
  let mut (x, d, y, e) := (x, d₀, y, e₀)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => Separated p x y ∧ ‖d‖ = ‖d₀‖ ∧ ‖e‖ = ‖e₀‖ do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← freeStep p ω ρ x d y e
  return (x, d, y, e)

theorem AC1_free :
    ∀ (p r : ℝ) (x d y e : Vec2), Separated (far p r) x y →
      ∀ x' d' y' e', (x', d', y', e') ∈ SetM.run (free_f p r x d y e) →
        Separated (far p r) x' y' ∧ ‖d'‖ = ‖d‖ ∧ ‖e'‖ = ‖e‖ := by
  intro p r x d y e hpre x' d' y' e' hrun
  exact (free'.spec (far p r) x d y e).le_wp hpre (x', d', y', e') hrun

def agree_f' (p : ℝ) (x d y e : Vec2) : SetM (ℝ × Vec2 × ℝ)
    requires True
    ensures (ω, c, r) => 0 ≤ r ∧ C r x d y e c ∧ Separated (far p r) x y ∧
      (r * ω) ^ 2 = ‖d‖ ^ 2
    := do
  let c ← choose Vec2
  let r ← chooseFrom {r : ℝ | r > 0}
  ensure (C r x d y e c)
  unless Separated (far p r) x y do abort
  let ω ← choose ℝ
  unless (r * ω) ^ 2 = ‖d‖ ^ 2 do abort
  return (ω, c, r)
where finally
  | spec => all_goals grind [SetM.run]

theorem AC6 :
    ∀ (p : ℝ) (x d y e : Vec2),
      ∀ ω c r, (ω, c, r) ∈ SetM.run (agree_f p x d y e) →
        0 ≤ r ∧ C r x d y e c ∧ Separated (far p r) x y ∧
          (r * ω) ^ 2 = ‖d‖ ^ 2 := by
  intro p x d y e ω c r hrun
  exact (agree_f'.spec p x d y e).le_wp trivial (ω, c, r) hrun

theorem AC7_live :
    ∀ (ω : ℝ) (c x d y e : Vec2),
      R ω c x d y e ∧ d ≠ e →
        ∀ a : ℝ, ∃ x' d' y' e', (x', d', y', e') ∈ SetM.run (exitEvol (x, d, y, e)) ∧
          a ^ 2 < ‖x' - y'‖ ^ 2 := by
  intro ω c x d y e hpre a
  have hv : 0 < ‖d - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpre.2)
  let T := (|a| + ‖x - y‖ + 1) / ‖d - e‖
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have htime : T * ‖d - e‖ = |a| + ‖x - y‖ + 1 := by
    dsimp [T]
    exact div_mul_cancel₀ _ hv.ne'
  have hdiff : (x + T • d) - (y + T • e) = x - y + T • (d - e) := by
    simp only [smul_sub]
    abel
  have htriangle := norm_sub_le (x - y + T • (d - e)) (x - y)
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT,
    htime] at htriangle
  refine ⟨x + T • d, d, y + T • e, e, ?_, ?_⟩
  · exact SemanticODE.mem_evolveSemantic _ _ _ T _ hT
      (straightTrajectory_evolution x d y e T)
  · rw [hdiff]
    nlinarith [sq_abs a, norm_nonneg (x - y + T • (d - e)), abs_nonneg a]

theorem AC4_live :
    ∀ (r ω : ℝ) (c x d y e : Vec2),
      0 < r ∧ 0 < ‖d‖ ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ →
        ∃ x' d' y' e', (x', d', y', e') ∈ SetM.run (entry_f ω r c x d y e) ∧
          ‖x' - c‖ ^ 2 = r ^ 2 ∧ ‖y' - c‖ ^ 2 = r ^ 2 := by
  intro r ω c x d y e hpre
  obtain ⟨T, path, hT, _, hevo, hradii⟩ := AC4 r ω c x d y e hpre
  have hrun : path T ∈ SetM.run (entryEvol ω (x, d, y, e)) :=
    SemanticODE.mem_evolveSemantic _ _ _ T path hT hevo
  rcases hfinal : path T with ⟨xr, dr, yr, er⟩
  simp only [hfinal] at hradii hrun
  refine ⟨xr, dr, yr, er, ?_, hradii⟩
  unfold entry_f
  apply bind_mem hrun
  simp only [hradii.1, ite_true]
  rfl

theorem AC6_feasible :
    ∀ (p l : ℝ) (x d y e : Vec2),
      0 < l ∧ x + l • d = y + l • e ∧ ‖d‖ = ‖e‖ ∧ 0 < ‖d‖ ∧
      Separated (far p (l * ‖d‖ / Real.sqrt 3)) x y →
        ∃ ω : ℝ, (ω, x + l • d, l * ‖d‖ / Real.sqrt 3) ∈ SetM.run (agree_f p x d y e) := by
  intro p l x d y e ⟨hl, hinter, hde, hd, hsep⟩
  let c := x + l • d
  let r := l * ‖d‖ / Real.sqrt 3
  let ω := Real.sqrt 3 / l
  have hroot : 0 < Real.sqrt 3 := by positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrad : Real.sqrt 3 * r = l * ‖d‖ := by dsimp [r]; field_simp
  have hx : ‖x - c‖ = l * ‖d‖ := by
    have hvec : x - c = -(l • d) := by dsimp [c]; abel
    rw [hvec, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  have hy : ‖y - c‖ = l * ‖d‖ := by
    have hvec : y - c = -(l • e) := by dsimp [c]; rw [hinter]; abel
    rw [hvec, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hl, ← hde]
  have hentry : C r x d y e c :=
    ⟨by rw [hx, hrad], l, hl.le, rfl,
      by rw [hy, hrad], l, hl.le, hinter.symm⟩
  have hspeed : (r * ω) ^ 2 = ‖d‖ ^ 2 := by
    have hmul : r * ω = ‖d‖ := by dsimp [r, ω]; field_simp
    rw [hmul]
  apply Exists.intro ω
  unfold agree_f
  apply bind_mem (a := c)
  · trivial
  apply bind_mem (a := r)
  · exact hr
  apply bind_mem (a := ())
  · exact hentry
  simp only [show Separated (far p r) x y from hsep, ite_true]
  apply bind_mem (a := ω)
  · trivial
  simp only [hspeed, ite_true]
  rfl

def freeSafeStep (p r ω ρ : ℝ) (x d y e : Vec2) := freeStep (far p r) ω ρ x d y e

@[spec] theorem freeSafeStep_spec (p r ω ρ : ℝ) (x d y e : Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ Separated p x y⦄ freeSafeStep p r ω ρ x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  rintro ⟨hp, hr, _⟩
  apply SetM.wp_and
  · exact dW (ode := flight ω ρ) (pre := fun _ => True)
      (fun (xr, _, yr, _) hdom => separated_of_far p r xr yr hp hr hdom)
      (x, d, y, e) trivial
  · intro ⟨xr, dr, yr, er⟩ hrun
    exact AC2 ω ρ _ x d y e xr dr yr er hrun

/-- Free flight preserves ordinary separation even when no positive-duration
flight is possible. Its zero-iteration branch simply retains the safe state. -/
def free_safe (p r : ℝ) (x d₀ y e₀ : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires 0 ≤ p ∧ 0 ≤ r ∧ Separated p x y
    ensures (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d₀‖ ∧ ‖er‖ = ‖e₀‖
    := do
  let mut (x, d, y, e) := (x, d₀, y, e₀)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        0 ≤ p ∧ 0 ≤ r ∧ Separated p x y ∧ ‖d‖ = ‖d₀‖ ∧ ‖e‖ = ‖e₀‖ do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← freeSafeStep p r ω ρ x d y e
  return (x, d, y, e)

def safeCirc (_p ω : ℝ) (_c x₀ d₀ y₀ e₀ x d y e : Vec2) :=
  circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)

@[spec] theorem safeCirc_spec (p ω : ℝ) (c x₀ d₀ y₀ e₀ x d y e : Vec2) :
    ⦃R ω c x d y e ∧ Separated p x y⦄
    safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
    ⦃fun (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  intro hpre ⟨xr, dr, yr, er⟩ hrun
  obtain ⟨hR, hsep⟩ := AC1_circ p ω c _ x d y e hpre xr dr yr er hrun
  exact ⟨hR, hsep, AC2 ω ω _ x d y e xr dr yr er hrun⟩

def safeExit (_p _ω : ℝ) (_c x d y e : Vec2) := exitEvol (x, d, y, e)

@[spec] theorem safeExit_spec (p ω : ℝ) (c x d y e : Vec2) :
    ⦃R ω c x d y e ∧ Separated p x y⦄ safeExit p ω c x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  intro hpre ⟨xr, dr, yr, er⟩ hrun
  exact ⟨AC7 p ω c x d y e hpre xr dr yr er hrun,
    AC2 0 0 (fun _ => True) x d y e xr dr yr er hrun⟩

def circ_f' (p ω : ℝ) (c x₀ d₀ y₀ e₀ x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires R ω c x d y e ∧ Separated p x y
    ensures (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let (x, d, y, e) ← safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
  ensure (ExitReadyPair x₀ d₀ y₀ e₀ (x, d, y, e))
  return (x, d, y, e)

def exit_f' (p ω : ℝ) (c x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires R ω c x d y e ∧ Separated p x y
    ensures (xr, dr, yr, er) => Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let (x, d, y, e) ← safeExit p ω c x d y e
  return (x, d, y, e)

theorem AC5_entry :
    ∀ (p r ω : ℝ) (c x d y e : Vec2),
      0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧ ‖e‖ = ‖d‖ ∧
      Separated (far p r) x y →
        ∀ x' d' y' e', (x', d', y', e') ∈ SetM.run (entryEvol ω (x, d, y, e)) →
          Separated p x' y' := by
  intro p r ω c x d y e ⟨hp, hr, hentry, hspeed, hde, hsep⟩ x' d' y' e' hrun
  exact unrestricted_entry_safe p r ω c x d y e hp hr hentry hspeed hde hsep
    (fun _ => True) (x', d', y', e') hrun

def unrestrictedEntryStep (_p _r ω : ℝ) (_c x d y e : Vec2) :=
  entryEvol ω (x, d, y, e)

@[spec] theorem unrestrictedEntryStep_spec (p r ω : ℝ) (c x d y e : Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y⦄
    unrestrictedEntryStep p r ω c x d y e
    ⦃fun (xr, dr, yr, er) => Separated p xr yr ∧
      (‖xr - c‖ ^ 2 = r ^ 2 → R ω c xr dr yr er) ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖⦄ := by
  constructor
  rintro ⟨hp, hr, hentry, hspeed, hde, hsep⟩ ⟨xr, dr, yr, er⟩ hrun
  exact ⟨AC5_entry p r ω c x d y e ⟨hp, hr, hentry, hspeed, hde, hsep⟩ xr dr yr er hrun,
    unrestricted_entry_tangent r ω c x d y e hr hentry hspeed hde (xr, dr, yr, er) hrun,
    AC2 (-ω) (-ω) (fun _ => True) x d y e xr dr yr er hrun⟩

/-- A contract for the unchanged `entry_f`, including every permitted extra turn. -/
def unrestrictedEntry (p r ω : ℝ) (c x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires 0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y
    ensures (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let (x, d, y, e) ← unrestrictedEntryStep p r ω c x d y e
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  return (x, d, y, e)

theorem entry_f_safe (p r ω : ℝ) (c x d y e : Vec2)
    (hpre : 0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y) :
    ∀ res ∈ SetM.run (entry_f ω r c x d y e),
      let (xr, dr, yr, er) := res
      R ω c xr dr yr er ∧ Separated p xr yr ∧ ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖ := by
  intro res hrun
  exact (unrestrictedEntry.spec p r ω c x d y e).le_wp hpre res hrun



/-- The unrestricted circular phase of the NTRM controller. -/
def circStep (_p ω : ℝ) (_c x d y e : Vec2) :=
  evolve (flight ω ω) (fun _ => True) (x, d, y, e)

@[spec] theorem circStep_spec (p ω : ℝ) (c x d y e : Vec2) :
    ⦃R ω c x d y e ∧ Separated p x y⦄ circStep p ω c x d y e
    ⦃fun (xr, _, yr, _) => Separated p xr yr⦄ := by
  constructor
  intro hpre ⟨xr, dr, yr, er⟩ hrun
  exact (AC1_circ p ω c _ x d y e hpre xr dr yr er hrun).2

/-- Figure 5: compose the AC1 phase contracts with instantaneous entry. -/
def ntrm' (p : ℝ) (x d y e : Vec2) : SetM Result
    requires Separated p x y
    ensures res => Separated p res.x res.y
    := do
  let mut (x, d, y, e) := (x, d, y, e)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => Separated p x y do
    (x, d, y, e) ← free' p x d y e
    let (ω, c) ← agree
    (d, e) := entry_n ω c x y
    (x, d, y, e) ← circStep p ω c x d y e
  return { x, y }
where finally
  | spec => all_goals simp_all [entry_n]

theorem ntrm_pair_safe :
    ∀ (p : ℝ) (x d y e : Vec2), Separated p x y →
      ∀ res ∈ SetM.run (ntrm p x d y e),
        Separated p res.x res.y := by
  intro p x d y e hpre res hrun
  exact (ntrm'.spec p x d y e).le_wp hpre res hrun

/-- The full-state FTRM preserves separation and equal speeds, carrying the
latest negotiated radius into the next iteration and the returned state. -/
def ftrm' (p r : ℝ) (x₀ d₀ y₀ e₀ : Vec2) : SetM FtrmPairResult
    requires 0 ≤ p ∧ 0 ≤ r ∧ ‖d₀‖ = ‖e₀‖ ∧ Separated p x₀ y₀
    ensures res => 0 ≤ res.r ∧ ‖res.d‖ = ‖res.e‖ ∧ Separated p res.x res.y
    := do
  let mut (x, d, y, e) := (x₀, d₀, y₀, e₀)
  let mut r := r
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y do
    (x, d, y, e) ← free_safe p r x d y e
    let (ω, c, r_new) ← agree_f' p x d y e
    r := r_new
    let (x₀, d₀, y₀, e₀) := (x, d, y, e)
    (x, d, y, e) ← unrestrictedEntry p r ω c x d y e
    (x, d, y, e) ← circ_f' p ω c x₀ d₀ y₀ e₀ x d y e
    (x, d, y, e) ← exit_f' p ω c x d y e
  return { x, d, y, e, r }

@[spec] theorem ftrm_spec (p r : ℝ) (x d y e : Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y⦄ ftrm p r x d y e
    ⦃fun res => 0 ≤ res.r ∧ ‖res.d‖ = ‖res.e‖ ∧ Separated p res.x res.y⦄ := by
  exact ftrm'.spec p r x d y e

def ftrmPrefix' (p r : ℝ) (k : Fin 5) (x d y e : Vec2) : SetM Result
    requires 0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y
    ensures res => Separated p res.x res.y
    := do
  let (x, d, y, e) ← free_safe p r x d y e
  if k = 0 then return { x, y }
  let (ω, c, r) ← agree_f' p x d y e
  if k = 1 then return { x, y }
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← unrestrictedEntryStep p r ω c x d y e
  if k = 2 then return { x, y }
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  let (x, d, y, e) ← safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
  if k = 3 then return { x, y }
  ensure (ExitReadyPair x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← safeExit p ω c x d y e
  return { x, y }

@[spec] theorem ftrmPrefix_spec (p r : ℝ) (k : Fin 5) (x d y e : Vec2) :
    ⦃0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y⦄ ftrmPrefix p r k x d y e
    ⦃fun res => Separated p res.x res.y⦄ := by
  exact ftrmPrefix'.spec p r k x d y e

theorem ftrm_pair_end_safe :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ res ∈ SetM.run (ftrm p r x d y e),
          Separated p res.x res.y := by
  rintro p r x d y e ⟨hp, hde, hr, hsep⟩ res hrun
  have hpost := (ftrm_spec p r x d y e).le_wp
    ⟨hp, hr.le, hde, separated_of_far p r x y hp hr.le hsep⟩ res hrun
  exact hpost.2.2

theorem ftrm_pair_throughout_safe :
    ∀ (p r : ℝ) (x d y e : Vec2),
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ st ∈ SetM.run (ftrm p r x d y e),
          ∀ k : Fin 5, ∀ res ∈ SetM.run (ftrmPrefix p st.r k st.x st.d st.y st.e),
            Separated p res.x res.y := by
  rintro p r x d y e ⟨hp, hde, hr, hsep⟩ st hrun k res hprefix
  obtain ⟨hri, hdi, hsafe⟩ := (ftrm_spec p r x d y e).le_wp
    ⟨hp, hr.le, hde, separated_of_far p r x y hp hr.le hsep⟩ st hrun
  exact (ftrmPrefix_spec p st.r k st.x st.d st.y st.e).le_wp ⟨hp, hri, hdi, hsafe⟩ res hprefix

/-! ## Theorem 1: arbitrary modified entry procedures -/

/-- AC2 for a clocked entry with independent, time-varying turn rates. -/
theorem entryDynamics_speeds (turnX turnY : ℝ → ℝ) (T : ℝ) (x d y e : Vec2) :
    wp (evolve (entryDynamics turnX turnY) (entryDomain T)
      ((x, d, y, e), (0 : ℝ)))
      (fun res => ‖res.1.2.1‖ = ‖d‖ ∧ ‖res.1.2.2.2‖ = ‖e‖) estack⟨⟩ := by
  apply (evolveSemantic_spec (Evolvable.denotation (entryDynamics turnX turnY))
    (entryDomain T) ((x, d, y, e), (0 : ℝ))
    (Q := fun res => ‖res.1.2.1‖ = ‖d‖ ∧ ‖res.1.2.2.2‖ = ‖e‖)).le_wp
  intro duration htime path hevo
  have hc := fun t ht => flight_components (turnX t) (turnY t) (hevo.2.2.1 t ht)
  simpa only [hevo.1, velocityD, velocityE] using
    And.intro
      (speed_constant_variable turnX (fun t => velocityD (path t).1) duration htime
        (fun t ht => (hc t ht).2.1))
      (speed_constant_variable turnY (fun t => velocityE (path t).1) duration htime
        (fun t ht => (hc t ht).2.2.2))

theorem modifiedEntryEvol_speeds (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) :
    wp (modifiedEntryEvol entry bound r ω c x d y e)
      (fun res => ‖res.1.2.1‖ = ‖d‖ ∧ ‖res.1.2.2.2‖ = ‖e‖) estack⟨⟩ := by
  exact WPMonad.bind_le_wp_bind (entry r ω c x d y e)
    (fun (turnX, turnY) =>
      evolve (entryDynamics turnX turnY) (entryDomain (bound r ω c x d y e))
        ((x, d, y, e), (0 : ℝ)))
    (fun res => ‖res.1.2.1‖ = ‖d‖ ∧ ‖res.1.2.2.2‖ = ‖e‖) estack⟨⟩
    (fun (turnX, turnY) _ => entryDynamics_speeds turnX turnY _ x d y e)

def modifiedEntryEvolSafe (entry : EntryProcedure) (bound : EntryTimeBound)
    (_p r ω : ℝ) (c x d y e : Vec2) :=
  modifiedEntryEvol entry bound r ω c x d y e

@[spec] theorem modifiedEntryEvolSafe_spec (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r ω : ℝ) (c x d y e : Vec2) :
    ⦃ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y⦄
    modifiedEntryEvolSafe entry bound p r ω c x d y e
    ⦃fun (st, t) => Separated p st.1 st.2.2.1 ∧
      (t = bound r ω c x d y e → R ω c st.1 st.2.1 st.2.2.1 st.2.2.2) ∧
      ‖st.2.1‖ = ‖d‖ ∧ ‖st.2.2.2‖ = ‖e‖⦄ := by
  exact ⟨fun ⟨hcontract, hpre⟩ res hrun =>
    let hs := (hcontract r ω c x d y e hpre).2 res hrun
    ⟨hs.1, hs.2, modifiedEntryEvol_speeds entry bound r ω c x d y e res hrun⟩⟩

def modifiedEntryCompleteSafe (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r ω : ℝ) (c x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y
    ensures (xr, dr, yr, er) => R ω c xr dr yr er ∧ Separated p xr yr ∧
      ‖dr‖ = ‖d‖ ∧ ‖er‖ = ‖e‖
    := do
  let T := bound r ω c x d y e
  let (st, t) ← modifiedEntryEvolSafe entry bound p r ω c x d y e
  ensure (t = T)
  return st

def modifiedEntryPrefixSafe (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r ω : ℝ) (c x d y e : Vec2) : SetM (Vec2 × Vec2 × Vec2 × Vec2)
    requires ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y
    ensures (xr, _, yr, _) => Separated p xr yr
    := do
  let (st, _t) ← modifiedEntryEvolSafe entry bound p r ω c x d y e
  return st

def ftrmModified' (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (x₀ d₀ y₀ e₀ : Vec2) : SetM FtrmPairResult
    requires ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ ‖d₀‖ = ‖e₀‖ ∧ Separated p x₀ y₀
    ensures res => 0 ≤ res.r ∧ ‖res.d‖ = ‖res.e‖ ∧ Separated p res.x res.y
    := do
  let mut (x, d, y, e) := (x₀, d₀, y₀, e₀)
  let mut r := r
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => ModifiedEntryContract entry bound p ∧
        0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y do
    (x, d, y, e) ← free_safe p r x d y e
    let (ω, c, r_new) ← agree_f' p x d y e
    r := r_new
    let (x₀, d₀, y₀, e₀) := (x, d, y, e)
    (x, d, y, e) ← modifiedEntryCompleteSafe entry bound p r ω c x d y e
    (x, d, y, e) ← circ_f' p ω c x₀ d₀ y₀ e₀ x d y e
    (x, d, y, e) ← exit_f' p ω c x d y e
  return { x, d, y, e, r }

theorem ftrmModified_eq (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (x d y e : Vec2) :
    ftrmModified entry bound p r x d y e = ftrmModified' entry bound p r x d y e := rfl

@[spec] theorem ftrmModified_spec (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (x d y e : Vec2) :
    ⦃ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y⦄
    ftrmModified entry bound p r x d y e
    ⦃fun res => 0 ≤ res.r ∧ ‖res.d‖ = ‖res.e‖ ∧ Separated p res.x res.y⦄ :=
  ftrmModified'.spec entry bound p r x d y e

def ftrmModifiedPrefix' (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (k : Fin 5) (x d y e : Vec2) : SetM Result
    requires ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y
    ensures res => Separated p res.x res.y
    := do
  let (x, d, y, e) ← free_safe p r x d y e
  if k = 0 then return { x, y }
  let (ω, c, r) ← agree_f' p x d y e
  if k = 1 then return { x, y }
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  if k = 2 then
    let (x, _, y, _) ← modifiedEntryPrefixSafe entry bound p r ω c x d y e
    return { x, y }
  let (x, d, y, e) ← modifiedEntryCompleteSafe entry bound p r ω c x d y e
  let (x, d, y, e) ← safeCirc p ω c x₀ d₀ y₀ e₀ x d y e
  if k = 3 then return { x, y }
  ensure (ExitReadyPair x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← safeExit p ω c x d y e
  return { x, y }

theorem ftrmModifiedPrefix_eq (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (k : Fin 5) (x d y e : Vec2) :
    ftrmModifiedPrefix entry bound p r k x d y e =
      ftrmModifiedPrefix' entry bound p r k x d y e := rfl

@[spec] theorem ftrmModifiedPrefix_spec (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (k : Fin 5) (x d y e : Vec2) :
    ⦃ModifiedEntryContract entry bound p ∧
      0 ≤ p ∧ 0 ≤ r ∧ ‖d‖ = ‖e‖ ∧ Separated p x y⦄
    ftrmModifiedPrefix entry bound p r k x d y e
    ⦃fun res => Separated p res.x res.y⦄ :=
  ftrmModifiedPrefix'.spec entry bound p r k x d y e

/-- Theorem 1 (modified entry): every complete modified FTRM run is safe whenever
the replacement entry satisfies the bounded-time safety and tangency contract. -/
theorem ftrm_modified_end_safe :
    ∀ (entry : EntryProcedure) (bound : EntryTimeBound) (p r : ℝ) (x d y e : Vec2),
      ModifiedEntryContract entry bound p →
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ res ∈ SetM.run (ftrmModified entry bound p r x d y e),
          Separated p res.x res.y := by
  exact fun entry bound p r x d y e hcontract ⟨hp, hde, hr, hsep⟩ res hrun =>
    ((ftrmModified_spec entry bound p r x d y e).le_wp
      ⟨hcontract, hp, hr.le, hde, separated_of_far p r x y hp hr.le hsep⟩ res hrun).2.2

/-- Theorem 1 (modified entry), throughout: after any number of complete cycles,
every phase prefix remains safe, including every entry time between zero and `T`. -/
theorem ftrm_modified_throughout_safe :
    ∀ (entry : EntryProcedure) (bound : EntryTimeBound) (p r : ℝ) (x d y e : Vec2),
      ModifiedEntryContract entry bound p →
      0 ≤ p ∧ ‖d‖ = ‖e‖ ∧ 0 < r ∧ Separated (far p r) x y →
        ∀ st ∈ SetM.run (ftrmModified entry bound p r x d y e),
          ∀ k : Fin 5,
          ∀ res ∈ SetM.run (ftrmModifiedPrefix entry bound p st.r k st.x st.d st.y st.e),
            Separated p res.x res.y := by
  exact fun entry bound p r x d y e hcontract ⟨hp, hde, hr, hsep⟩
      st hrun k res hprefix =>
    let hs := (ftrmModified_spec entry bound p r x d y e).le_wp
      ⟨hcontract, hp, hr.le, hde, separated_of_far p r x y hp hr.le hsep⟩
      st hrun
    (ftrmModifiedPrefix_spec entry bound p st.r k st.x st.d st.y st.e).le_wp
      ⟨hcontract, hp, hs.1, hs.2.1, hs.2.2⟩ res hprefix

end FM09
