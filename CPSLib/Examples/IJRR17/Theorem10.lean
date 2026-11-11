import CPSLib.Examples.IJRR17.Proof

/-!
# Audit of journal Theorem 10

This file keeps the shared model and challenge unchanged. Model 12 permits zero
obstacle-control updates, so an initially unbounded obstacle velocity can survive
the controller. The concrete trajectory below checks that obstruction against
the actual quantified dynamics, including the printed negative angular sign.
-/

open CPSLib Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace IJRR17
namespace Theorem10

noncomputable def e₀ : Vec2 := !₂[1, 0]
noncomputable def e₁ : Vec2 := !₂[0, 1]

noncomputable def robotPosition (t : ℝ) : Vec2 :=
  Real.sin (t ^ 2 / 2) • e₀ + (Real.cos (t ^ 2 / 2) - 1) • e₁

noncomputable def robotDirection (t : ℝ) : Vec2 :=
  Real.cos (t ^ 2 / 2) • e₀ - Real.sin (t ^ 2 / 2) • e₁

noncomputable def obstacleStart : Vec2 := 2 • e₀
noncomputable def obstacleVelocity : Vec2 := robotPosition 1 - obstacleStart
noncomputable def obstaclePosition (t : ℝ) : Vec2 := obstacleStart + t • obstacleVelocity

theorem initial_velocity_exceeds_zero_bound : 0 < ‖obstacleVelocity‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hx := congrArg (fun u : Vec2 => u 0) hzero
  norm_num [obstacleVelocity, robotPosition, obstacleStart, e₀, e₁] at hx
  nlinarith [Real.sin_le_one (1 / 2)]

theorem position_derivative (t : ℝ) :
    HasDerivAt robotPosition (t • robotDirection t) t := by
  have hangle : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
    convert ((hasDerivAt_id t).pow 2).div_const 2 using 1
    · rfl
    · dsimp
      ring
  have h := (hangle.sin.smul_const e₀).add ((hangle.cos.sub_const 1).smul_const e₁)
  apply h.congr_deriv
  ext i
  fin_cases i <;> simp [robotDirection, e₀, e₁] <;> ring

theorem direction_derivative (t : ℝ) :
    HasDerivAt robotDirection ((-t) • perp (robotDirection t)) t := by
  have hangle : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
    convert ((hasDerivAt_id t).pow 2).div_const 2 using 1
    · rfl
    · dsimp
      ring
  have h := (hangle.cos.smul_const e₀).sub (hangle.sin.smul_const e₁)
  apply h.congr_deriv
  ext i
  fin_cases i <;> simp [robotDirection, e₀, e₁, perp] <;> ring

theorem collision_evolution :
    (((robotPosition 1, robotDirection 1, (1 : ℝ), (1 : ℝ)),
        (fun _ : Obstacle => robotPosition 1)), (1 : ℝ)) ∈
      SetM.run (evolve
        ((robotMotionNobs 1 1, obstaclesMotionNobs Set.univ (fun _ => obstacleVelocity)), time)
        (nobsDomain 1)
        (((robotPosition 0, robotDirection 0, 0, 0), (fun _ => obstacleStart)), 0)) := by
  have hevol : IsEvolution
      (fun t => (((robotPosition t, robotDirection t, t, t),
        (fun _ : Obstacle => obstaclePosition t)), t))
      (Evolvable.denotation
        ((robotMotionNobs 1 1, obstaclesMotionNobs Set.univ (fun _ => obstacleVelocity)), time))
      (nobsDomain 1)
      (((robotPosition 0, robotDirection 0, 0, 0), (fun _ => obstacleStart)), 0) 1 := by
    constructor
    · simp [obstaclePosition]
    · constructor
      · intro t ht
        exact ⟨ht.1, ht.2⟩
      · constructor
        · constructor
          · intro t ht
            simpa [robotMotionNobs] using
              ((position_derivative t).prodMk ((direction_derivative t).prodMk
                ((hasDerivAt_id t).prodMk (hasDerivAt_id t)))).hasDerivWithinAt
                (s := Set.Icc 0 1)
          · intro t ht i hi
            simpa [obstaclesMotionNobs, obstaclePosition] using
              (((hasDerivAt_id t).smul_const obstacleVelocity).const_add
                obstacleStart).hasDerivWithinAt (s := Set.Icc 0 1)
        · intro t ht
          exact (hasDerivAt_id t).hasDerivWithinAt
  have h := SemanticODE.mem_evolveSemantic _ _ _ 1 _ (by norm_num) hevol
  have hend : obstaclePosition 1 = robotPosition 1 := by
    simp only [obstaclePosition, obstacleVelocity, one_smul]
    abel
  simpa only [evolve, hend] using h

theorem obstacle_control_zero_updates (O : Set Obstacle) (V : Obstacle → ℝ)
    (v : Obstacle → Vec2) : v ∈ SetM.run (ctrl_o_nobs O V v) := by
  unfold ctrl_o_nobs
  apply run_bind _ _ 0 _ (Set.mem_univ _)
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using
    (show v ∈ SetM.run (pure v) from Set.mem_singleton _)

theorem accelerating_control :
    ((1 : ℝ), (0 : ℝ), (1 : ℝ)) ∈ SetM.run
      (ctrl_r_nobs 1 1 0 1 Set.univ (fun _ => 0)
        (robotPosition 0) (fun _ => obstacleStart) 0 0 1) := by
  apply Or.inr
  apply Or.inr
  apply run_bind _ _ 1 _ (driveActual_mem 1 1 1 (by norm_num) le_rfl)
  apply run_bind _ _ 0 _ (Set.mem_univ _)
  apply run_bind _ _ () _ (show () ∈ SetM.run (ensure (-(0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0)) from
    ⟨by norm_num, le_rfl⟩)
  apply run_bind _ _ 1 _ (Set.mem_univ _)
  apply run_bind _ _ () _ ?_
  · exact Set.mem_singleton _
  · change Curve 0 0 1 ∧ SafeNobs 1 1 Set.univ (fun _ => 0)
      (robotPosition 0) (fun _ => obstacleStart) 0 1
    norm_num [Curve, SafeNobs, actualMargin, stoppingMargin, stopDist, infNorm,
      robotPosition, obstacleStart, e₀, e₁]

noncomputable def step (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ) :
    (Vec2 × Vec2 × (Obstacle → Vec2) × ℝ × ℝ × ℝ × (Obstacle → Vec2)) →
    SetM (Vec2 × Vec2 × (Obstacle → Vec2) × ℝ × ℝ × ℝ × (Obstacle → Vec2)) :=
  fun (p, d, o, s, ω, r, v) => do
    let v ← ctrl_o_nobs O V v
    let (a, ω, r) ← ctrl_r_nobs A b Ω ε O V p o s ω r
    let (p, d, o, s, ω) ← dyn_nobs ε a r O v p d o s ω
    return (p, d, o, s, ω, r, v)

theorem program_eq_loop (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o v : Obstacle → Vec2) (s ω r : ℝ) :
    dwnobs A b Ω ε O V p d o v s ω r = (do
      let (p, d, o, s, ω, r, v) ← finiteLoop (step A b Ω ε O V) (p, d, o, s, ω, r, v)
      return ({ p, d, o, s, ω, r, v } : NobsResult)) := by
  unfold dwnobs finiteLoop
  simp only [← forIn_range_repeat]
  simp only [step, bind_assoc, pure_bind, Prod.mk.eta]

theorem collision_dynamics :
    (robotPosition 1, robotDirection 1, (fun _ : Obstacle => robotPosition 1),
      (1 : ℝ), (1 : ℝ)) ∈
      SetM.run (dyn_nobs 1 1 1 Set.univ (fun _ => obstacleVelocity)
        (robotPosition 0) (robotDirection 0) (fun _ => obstacleStart) 0 0) := by
  unfold dyn_nobs
  apply run_bind _ _ (((robotPosition 1, robotDirection 1, (1 : ℝ), (1 : ℝ)),
    (fun _ : Obstacle => robotPosition 1)), (1 : ℝ)) _ collision_evolution
  exact Set.mem_singleton _

theorem collision_step :
    (robotPosition 1, robotDirection 1, (fun _ : Obstacle => robotPosition 1),
      (1 : ℝ), (1 : ℝ), (1 : ℝ), (fun _ : Obstacle => obstacleVelocity)) ∈
      SetM.run (step 1 1 0 1 Set.univ (fun _ => 0)
        (robotPosition 0, robotDirection 0, (fun _ => obstacleStart), 0, 0, 1,
          (fun _ => obstacleVelocity))) := by
  unfold step
  apply run_bind _ _ (fun _ => obstacleVelocity) _ (obstacle_control_zero_updates _ _ _)
  apply run_bind _ _ ((1 : ℝ), (0 : ℝ), (1 : ℝ)) _ accelerating_control
  apply run_bind _ _ (robotPosition 1, robotDirection 1, (fun _ => robotPosition 1),
    (1 : ℝ), (1 : ℝ)) _ collision_dynamics
  exact Set.mem_singleton _

/-- A successful run with every obstacle colliding with a moving robot at time one. -/
theorem collision_run :
    ({ p := robotPosition 1, d := robotDirection 1,
       o := fun _ : Obstacle => robotPosition 1,
       s := 1, ω := 1, r := 1,
       v := fun _ : Obstacle => obstacleVelocity } : NobsResult) ∈
      SetM.run (dwnobs 1 1 0 1 Set.univ (fun _ => 0)
        (robotPosition 0) (robotDirection 0) (fun _ => obstacleStart)
        (fun _ => obstacleVelocity) 0 0 1) := by
  rw [program_eq_loop]
  apply run_bind _ _ (robotPosition 1, robotDirection 1, (fun _ => robotPosition 1),
    1, 1, 1, (fun _ => obstacleVelocity)) _
    (reach_run _ _ _ (reach_prepend _ _ _ _ collision_step (reach_refl _ _)))
  exact Set.mem_singleton _

/-- This is a counterexample to the exact supplied challenge, rather than a
failure of one proposed loop invariant. The model and challenge are untouched. -/
theorem journal_claim_false : ¬(
    ∀ A b Ω ε (O : Set Obstacle) (V : Obstacle → ℝ)
      (p d : Vec2) (o v : Obstacle → Vec2) s ω r,
      (0 ≤ A ∧ 0 < b ∧ 0 ≤ Ω ∧ 0 < ε) → (∀ i ∈ O, 0 ≤ V i) →
      (s = 0 ∧ r ≠ 0 ∧ UnitDirection d) →
        ∀ res ∈ SetM.run (dwnobs A b Ω ε O V p d o v s ω r),
          res.s ≠ 0 → ∀ i ∈ O, 0 < infNorm (res.p - res.o i)) := by
  intro hclaim
  have h := hclaim 1 1 0 1 Set.univ (fun _ => 0)
    (robotPosition 0) (robotDirection 0) (fun _ => obstacleStart)
    (fun _ => obstacleVelocity) 0 0 1 (by norm_num) (by simp)
    (by norm_num [UnitDirection, robotDirection, e₀, e₁])
    _ collision_run (by norm_num) 0 (Set.mem_univ _)
  simp [infNorm] at h

def projectObstacle (i : Obstacle) :
    ((Vec2 × Vec2 × ℝ × ℝ) × (Obstacle → Vec2)) × ℝ →
      (Vec2 × Vec2 × Vec2 × ℝ × ℝ) × ℝ :=
  fun (((p, d, s, ω), o), t) => ((p, d, o i, s, -ω), t)

/-- Negating angular velocity and radius maps the printed negative-sign robot
equation to the ordinary motion equation used by the actual-acceleration proof.
Only active obstacle coordinates are projected. -/
theorem obstacle_projection (ε a r : ℝ) (O : Set Obstacle) (v : Obstacle → Vec2)
    (p d : Vec2) (o : Obstacle → Vec2) (s ω : ℝ) (i : Obstacle) (hi : i ∈ O) :
    ∀ res ∈ SetM.run (evolve ((robotMotionNobs a r, obstaclesMotionNobs O v), time)
      (nobsDomain ε) (((p, d, s, ω), o), 0)),
      projectObstacle i res ∈ SetM.run (evolve (motion a (-r) (v i), time) (domain ε)
        ((p, d, o i, s, -ω), 0)) := by
  exact (evolveSemantic_spec
    (Evolvable.denotation ((robotMotionNobs a r, obstaclesMotionNobs O v), time))
    (nobsDomain ε) (((p, d, s, ω), o), 0)).le_wp (by
    intro T hT path hevol
    apply SemanticODE.mem_evolveSemantic _ (domain ε) ((p, d, o i, s, -ω), 0) T
      (fun t => projectObstacle i (path t)) hT
    constructor
    · exact congrArg (projectObstacle i) hevol.1
    · constructor
      · intro t ht
        have h := hevol.2.1 t ht
        exact ⟨h.2, h.1⟩
      · constructor
        · intro t ht
          have hr := hevol.2.2.1.1 t ht
          have ho := hevol.2.2.1.2 t ht i hi
          have hp := OdeDeriv.hasDerivWithinAt_fst hr
          have hrest := OdeDeriv.hasDerivWithinAt_snd hr
          have hd := OdeDeriv.hasDerivWithinAt_fst hrest
          have hsw := OdeDeriv.hasDerivWithinAt_snd hrest
          have hs := OdeDeriv.hasDerivWithinAt_fst hsw
          have hw := OdeDeriv.hasDerivWithinAt_neg_apply (OdeDeriv.hasDerivWithinAt_snd hsw)
          simpa [projectObstacle, robotMotionNobs, motion, obstaclesMotionNobs, div_neg] using
            hp.prodMk (hd.prodMk (ho.prodMk (hs.prodMk hw)))
        · exact hevol.2.2.2)

@[reducible]
def VelocityBounds (O : Set Obstacle) (V : Obstacle → ℝ) (v : Obstacle → Vec2) : Prop :=
  ∀ i ∈ O, ‖v i‖ ≤ V i

noncomputable def obstacleControl' (O : Set Obstacle) (V : Obstacle → ℝ)
    (v : Obstacle → Vec2) : SetM (Obstacle → Vec2)
    requires VelocityBounds O V v
    ensures v => VelocityBounds O V v
    := do
  let mut v := v
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => VelocityBounds O V v do
    let i ← chooseFrom O
    let vi ← choose Vec2
    ensure (‖vi‖ ≤ V i)
    v := Function.update v i vi
  return v

theorem obstacleControl_eq (O : Set Obstacle) (V : Obstacle → ℝ) (v : Obstacle → Vec2) :
    ctrl_o_nobs O V v = obstacleControl' O V v := by rfl

@[spec] theorem obstacleControl_spec (O : Set Obstacle) (V : Obstacle → ℝ)
    (v : Obstacle → Vec2) :
    ⦃VelocityBounds O V v⦄ ctrl_o_nobs O V v ⦃fun v => VelocityBounds O V v⦄ :=
  obstacleControl'.spec O V v

theorem velocity_sq (V : ℝ) (v : Vec2) (hV : 0 ≤ V) (hv : ‖v‖ ≤ V) :
    v 0 ^ 2 + v 1 ^ 2 ≤ V ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg v) hV).mpr hv
  simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using h

noncomputable def unitEnergy :
    ((Vec2 × Vec2 × ℝ × ℝ) × (Obstacle → Vec2)) × ℝ → ℝ :=
  fun (((_p, d, _s, _ω), _o), _t) => d 0 ^ 2 + d 1 ^ 2 - 1

theorem unit_preserved (ε a r : ℝ) (O : Set Obstacle) (v : Obstacle → Vec2) :
    (fun (((_p, d, _s, _ω), _o), _t) => UnitDirection d)
    [[evolve ((robotMotionNobs a r, obstaclesMotionNobs O v), time) (nobsDomain ε)]]
    (fun (((_p, d, _s, _ω), _o), _t) => UnitDirection d) := by
  have hprime : HasPrime
      (Evolvable.denotation ((robotMotionNobs a r, obstaclesMotionNobs O v), time))
      (nobsDomain ε) unitEnergy (fun _ => 0) := by
    ode_deriv [unitEnergy, robotMotionNobs, obstaclesMotionNobs, time, perp]
  simpa only [unitEnergy, sub_eq_zero, UnitDirection] using
    (dIeq (ode := ((robotMotionNobs a r, obstaclesMotionNobs O v), time))
      (domain := nobsDomain ε)
      (pre := fun (((_p, d, _s, _ω), _o), _t) => UnitDirection d)
      unitEnergy (fun _ => 0) hprime (fun _ h => sub_eq_zero.mpr h) (fun _ _ => rfl))

@[reducible]
def PhysicalInv (b : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o : Obstacle → Vec2) (s : ℝ) : Prop :=
  0 ≤ s ∧ UnitDirection d ∧
    ∀ i ∈ O, 0 < s → stopDist b s + V i * s / b < infNorm (p - o i)

@[reducible]
def Ready (b ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o : Obstacle → Vec2) (s a : ℝ) : Prop :=
  (a = -b ∧ PhysicalInv b O V p d o s) ∨
  (s = 0 ∧ a = 0 ∧ UnitDirection d) ∨
  (-b ≤ a ∧ 0 ≤ s ∧ UnitDirection d ∧ SafeNobs b ε O V p o s a)

noncomputable def robotControl (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p _d : Vec2) (o : Obstacle → Vec2) (s ω r : ℝ) :=
  ctrl_r_nobs A b Ω ε O V p o s ω r

@[spec] theorem robotControl_spec (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o : Obstacle → Vec2) (s ω r : ℝ) :
    ⦃PhysicalInv b O V p d o s⦄ robotControl A b Ω ε O V p d o s ω r
    ⦃fun (a, _ω, _r) => Ready b ε O V p d o s a⦄ := by
  unfold robotControl ctrl_r_nobs
  vcgen
  constructor
  · vcgen
    simp_all
  · vcgen
    constructor
    all_goals vcgen
    all_goals simp_all

theorem ready_direction (b ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o : Obstacle → Vec2) (s a : ℝ)
    (hready : Ready b ε O V p d o s a) : UnitDirection d := by
  rcases hready with ⟨_, _, hd, _⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd, _⟩ <;> exact hd

theorem dynamics_preserved (b ε a r : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (v : Obstacle → Vec2) (p d : Vec2) (o : Obstacle → Vec2) (s ω : ℝ)
    (hb : 0 < b) (hε : 0 < ε) (hV : ∀ i ∈ O, 0 ≤ V i)
    (hv : VelocityBounds O V v) (hready : Ready b ε O V p d o s a) :
    ∀ res ∈ SetM.run (evolve ((robotMotionNobs a r, obstaclesMotionNobs O v), time)
      (nobsDomain ε) (((p, d, s, ω), o), 0)),
      let (((pr, dr, sr, _ωr), or_), _t) := res
      PhysicalInv b O V pr dr or_ sr := by
  rintro ⟨⟨⟨pr, dr, sr, ωr⟩, or_⟩, t⟩ hrun
  have hdom := dW (ode := ((robotMotionNobs a r, obstaclesMotionNobs O v), time))
    (domain := nobsDomain ε) (pre := fun _ => True) (fun _ h => h)
    (((p, d, s, ω), o), 0) trivial (((pr, dr, sr, ωr), or_), t) hrun
  have hd := unit_preserved ε a r O v (((p, d, s, ω), o), 0)
    (ready_direction b ε O V p d o s a hready) (((pr, dr, sr, ωr), or_), t) hrun
  apply And.intro hdom.1 (And.intro hd ?_)
  intro i hi hpos
  have hproj := obstacle_projection ε a r O v p d o s ω i hi (((pr, dr, sr, ωr), or_), t) hrun
  have hlocal : ActualReady b (V i) ε p d (o i) s a := by
    rcases hready with ⟨ha, hs, hd, hclear⟩ | ⟨hs, ha, hd⟩ | ⟨ha, hs, hd, hsafe⟩
    · exact Or.inl ⟨ha, hs, hd, hclear i hi⟩
    · exact Or.inr (Or.inl ⟨hs, ha, hd⟩)
    · exact Or.inr (Or.inr ⟨ha, hs, hd, hsafe i hi⟩)
  have hdy : (pr, dr, or_ i, sr, -ωr) ∈
      SetM.run (actualDyn b (V i) ε a (-r) (v i) p d (o i) s (-ω)) := by
    unfold actualDyn dyn
    apply run_bind _ _ ((pr, dr, or_ i, sr, -ωr), t) _ hproj
    exact Set.mem_singleton _
  have hinv := (actualDyn_spec b (V i) ε a (-r) hb (hV i hi) hε
    (v i) p d (o i) s (-ω)).le_wp ⟨velocity_sq (V i) (v i) (hV i hi) (hv i hi), hlocal⟩ _ hdy
  exact hinv.2.2 hpos

noncomputable def dynamics (_b ε a r : ℝ) (O : Set Obstacle) (_V : Obstacle → ℝ)
    (v : Obstacle → Vec2) (p d : Vec2) (o : Obstacle → Vec2) (s ω : ℝ) :=
  dyn_nobs ε a r O v p d o s ω

@[spec] theorem dynamics_spec (b ε a r : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (v : Obstacle → Vec2) (p d : Vec2) (o : Obstacle → Vec2) (s ω : ℝ)
    (hb : 0 < b) (hε : 0 < ε) (hV : ∀ i ∈ O, 0 ≤ V i) :
    ⦃VelocityBounds O V v ∧ Ready b ε O V p d o s a⦄ dynamics b ε a r O V v p d o s ω
    ⦃fun (p, d, o, s, _ω) => PhysicalInv b O V p d o s⦄ := by
  unfold dynamics dyn_nobs
  vcgen (errorOnMissingSpec := false)
  rename_i hpre
  simp only [SetM.wp_pure, binderNameHint]
  exact dynamics_preserved b ε a r O V v p d o s ω hb hε hV hpre.1 hpre.2

noncomputable def dwnobs' (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o v : Obstacle → Vec2) (s ω r : ℝ)
    (hb : 0 < b) (hε : 0 < ε) (hV : ∀ i ∈ O, 0 ≤ V i) :
    SetM NobsResult
    requires PhysicalInv b O V p d o s ∧ VelocityBounds O V v
    ensures res => PhysicalInv b O V res.p res.d res.o res.s ∧ VelocityBounds O V res.v
    := do
  let mut (p, d, o, s, ω, r, v) := (p, d, o, s, ω, r, v)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => PhysicalInv b O V p d o s ∧ VelocityBounds O V v do
    v ← ctrl_o_nobs O V v
    let (a, ω_new, r_new) ← robotControl A b Ω ε O V p d o s ω r
    ω := ω_new
    r := r_new
    (p, d, o, s, ω) ← dynamics b ε a r O V v p d o s ω
  return { p, d, o, s, ω, r, v }

theorem dwnobs_eq (A b Ω ε : ℝ) (O : Set Obstacle) (V : Obstacle → ℝ)
    (p d : Vec2) (o v : Obstacle → Vec2) (s ω r : ℝ)
    (hb : 0 < b) (hε : 0 < ε) (hV : ∀ i ∈ O, 0 ≤ V i) :
    dwnobs A b Ω ε O V p d o v s ω r = dwnobs' A b Ω ε O V p d o v s ω r hb hε hV := by rfl

/-- A corrected version of Theorem 10 for exactly the same hybrid program.
The extra premise bounds every initially active obstacle velocity. It is not
the supplied challenge theorem, which `journal_claim_false` refutes. -/
theorem safe_of_initial_velocity_bounds :
    ∀ A b Ω ε (O : Set Obstacle) (V : Obstacle → ℝ)
      (p d : Vec2) (o v : Obstacle → Vec2) s ω r,
      (0 ≤ A ∧ 0 < b ∧ 0 ≤ Ω ∧ 0 < ε) → (∀ i ∈ O, 0 ≤ V i) →
      (s = 0 ∧ r ≠ 0 ∧ UnitDirection d) → (∀ i ∈ O, ‖v i‖ ≤ V i) →
        ∀ res ∈ SetM.run (dwnobs A b Ω ε O V p d o v s ω r),
          res.s ≠ 0 → ∀ i ∈ O, 0 < infNorm (res.p - res.o i) := by
  intro A b Ω ε O V p d o v s ω r hbounds hV hinit hv res hrun hspeed i hi
  rw [dwnobs_eq A b Ω ε O V p d o v s ω r hbounds.2.1 hbounds.2.2.2 hV] at hrun
  have hstart : PhysicalInv b O V p d o s ∧ VelocityBounds O V v := by
    rcases hinit with ⟨rfl, _, hd⟩
    exact ⟨⟨le_rfl, hd, by simp⟩, hv⟩
  have hinv := (dwnobs'.spec A b Ω ε O V p d o v s ω r hbounds.2.1 hbounds.2.2.2 hV).le_wp
    hstart res hrun
  have hpos : 0 < res.s := lt_of_le_of_ne hinv.1.1 hspeed.symm
  have hclear := hinv.1.2.2 i hi hpos
  have hstop : 0 ≤ stopDist b res.s :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hbounds.2.1.le)
  have hmove := div_nonneg (mul_nonneg (hV i hi) hinv.1.1) hbounds.2.1.le
  linarith

end Theorem10
end IJRR17
