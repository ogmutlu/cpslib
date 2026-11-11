import CPSLib.Examples.ACASX.Model
import CPSLib.Tactic.OdeDeriv

open CPSLib
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true

namespace ACASX

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

@[reducible]
def NoNMAC (rp hp : ℝ) (encounter : Encounter) : Prop :=
  rp < |encounter.r| ∨ hp < |encounter.h|

/-!
The scalar arithmetic kernel retains the original case-study formulas. The typed
model is connected to these formulas below; controller proofs use the typed model.
-/
namespace Scalar

@[reducible]
def maxI (v w target : ℝ) : ℝ := max 0 (w * (target - v))

/-- Fig. 3 : A -/
@[reducible]
def A (alo t hn v w vlo : ℝ) : Prop :=
  (0 ≤ t ∧ t < maxI v w vlo / alo ∧ hn = w * alo / 2 * t ^ 2 + v * t) ∨
  (maxI v w vlo / alo ≤ t ∧ hn = vlo * t - w * maxI v w vlo ^ 2 / (2 * alo))

/-- Fig. 3 : L⁻¹_impl -/
@[reducible]
def Limpl (rp hp rv alo r h v w vlo : ℝ) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ A alo t hn v w vlo →
    rp < |r - rn| ∨ w * (h - hn) < -hp

@[reducible]
def advisoryLo (alo v w vlo a : ℝ) : Prop := w * vlo ≤ w * v ∨ alo ≤ w * a

/-- From Eq. (1) -/
def motion (rv a : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun (_r, _h, v) => (-rv, -v, a)

/-- From Eq. (1) -/
def lowerDomain (alo w vlo a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a

/-- Fig. 5 : Dᵈ_impl, follows `safe_delay_implicit.kyx`.
the paper (fixed version: `vd` instead of `v` inside `A`) -/
@[reducible]
def Dimpl (rp hp rv alo ad r h v w vlo d : ℝ) : Prop :=
  ∀ t rn hn hd vd : ℝ,
    rn = rv * t ∧
      ((0 ≤ t ∧ t < max 0 d ∧ hn = -(w * ad) / 2 * t ^ 2 + v * t) ∨
        ((hd = -(w * ad) / 2 * (max 0 d) ^ 2 + v * max 0 d ∧ vd - v = -w * ad * max 0 d) ∧
          A alo (t - max 0 d) (hn - hd) vd w vlo)
      ) →
      rp < |r - rn| ∨ w * (h - hn) < -hp

/-- From Eq. (4) -/
def delayedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _d, _t) => (-rv, -v, a, -1, 1)

/-- From Eq. (4) -/
def delayedDomain (alo ε w vlo a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, d, t) => t ≤ ε ∧ (d ≤ 0 → advisoryLo alo v w vlo a)

/-- Fig. 8 : A_up -/
@[reducible]
def Aup (aup t hn v w vup : ℝ) : Prop :=
  (0 ≤ t ∧ t < maxI v w vup / aup ∧ hn = w * aup / 2 * t ^ 2 + v * t) ∨
  (maxI v w vup / aup ≤ t ∧
    hn = w * max (w * vup) (w * v) * t - w * maxI v w vup ^ 2 / (2 * aup))

/-- Fig. 8 : U⁻¹_impl -/
@[reducible]
def Uimpl (rp hp rv aup r h v w vup : ℝ) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ Aup aup t hn v w vup →
    rp < |r - rn| ∨ hp < w * (h - hn)

/-- Fig. 8 : C⁻¹_impl -/
@[reducible]
def Cimpl (rp hp rv alo aup r h v w vlo vup : ℝ) : Prop :=
  Limpl rp hp rv alo r h v w vlo ∨ Uimpl rp hp rv aup r h v w vup

@[reducible]
def advisoryUp (aup v w vup a : ℝ) : Prop := (w * v ≤ w * vup ∧ w * a ≤ aup) ∨ w * a ≤ 0

/-- From Eq. (5) -/
def twoSidedDomain (alo aup w vlo vup a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

/-- Fig. 10 : Lε_impl (equivalent to paper for `t=0`), follows `bounded_implicit.kyx`
(fixed typo from paper: `hp` to `-hp`) -/
@[reducible]
def LimplBounded (rp hp rv alo tl t r h v w vlo : ℝ) : Prop :=
  ∀ tn rn hn : ℝ, (tn ≤ tl - t ∨ tl < 0) ∧ rn = rv * tn ∧ A alo tn hn v w vlo →
    rp < |r - rn| ∨ w * (h - hn) < -hp

/-- Fig. 10 : Uε_impl (equivalent to paper for `t=0`) -/
@[reducible]
def UimplBounded (rp hp rv aup tl t r h v w vup : ℝ) : Prop :=
  ∀ tn rn hn : ℝ, (tn ≤ tl - t ∨ tl < 0) ∧ rn = rv * tn ∧ Aup aup tn hn v w vup →
    rp < |r - rn| ∨ hp < w * (h - hn)

/-- Fig. 10 : Cε_impl (equivalent to paper for `t=0`) -/
@[reducible]
def CimplBounded (rp hp rv alo aup tl t r h v w vlo vup : ℝ) : Prop :=
  LimplBounded rp hp rv alo tl t r h v w vlo ∨
    UimplBounded rp hp rv aup tl t r h v w vup

/-- From Eq. (8) -/
def clockedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _t) => (-rv, -v, a, 1)

/-- From Eq. (8) -/
def clockedDomain (alo aup tl w vlo vup a : ℝ) : ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, t) => (t ≤ tl ∨ tl < 0) ∧
    advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

/-- Fig. 12 : lower endpoint, follows `condImplSafeableLo` in `AcasXSafeable.scala`
(fixed typo from paper: `vlo * τ` to `v * τ` in the first disjunct). -/
@[reducible]
def lowerEndpoint (alo τ hn vn v w vlo : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vlo / alo ∧
    hn = w * alo / 2 * τ ^ 2 + v * τ ∧ vn = w * alo * τ + v) ∨
  (maxI v w vlo / alo ≤ τ ∧
    hn = vlo * τ - w * maxI v w vlo ^ 2 / (2 * alo) ∧ vn = vlo)

/-- Fig. 12 : upper endpoint, follows `condImplSafeableUp` in `AcasXSafeable.scala`
(fixed typo from paper: `vup * τ` to `v * τ` in the first disjunct). -/
@[reducible]
def upperEndpoint (aup τ hn vn v w vup : ℝ) : Prop :=
  (0 ≤ τ ∧ τ < maxI v w vup / aup ∧
    hn = w * aup / 2 * τ ^ 2 + v * τ ∧ vn = w * aup * τ + v) ∨
  (maxI v w vup / aup ≤ τ ∧
    hn = w * max (w * vup) (w * v) * τ - w * maxI v w vup ^ 2 / (2 * aup) ∧
    vn = w * max (w * vup) (w * v))

/-- Fig. 12 : Csafeable(ε)_impl, following `condImplSafeable` in `AcasXSafeable.scala`.
The upper follow-up uses reversed sense and `vupEx`; upper terminal speed is normalized
using `(w = -1 ∨ w = 1)`. The paper is specialized to `t=0` and prints different
endpoint heights. -/
@[reducible]
def CimplSafeable (rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx : ℝ) : Prop :=
  (LimplBounded rp hp rv alo tl t r h v w vlo ∧
    ∀ hn vn : ℝ, lowerEndpoint alo (tl - t) hn vn v w vlo →
      Limpl rp hp rv alo (r - rv * (tl - t)) (h - hn) vn w vloEx) ∨
  (UimplBounded rp hp rv aup tl t r h v w vup ∧
    ∀ hn vn : ℝ, upperEndpoint aup (tl - t) hn vn v w vup →
      Limpl rp hp rv alo (r - rv * (tl - t)) (h - hn) vn (-w) vupEx)

@[reducible]
def NoNMAC (rp hp r h : ℝ) : Prop := rp < |r| ∨ hp < |h|

/-- Twice the signed nominal height relative to the target-speed line.
The time argument has been rescaled by `alo`; `gap` is the signed velocity shortfall. -/
noncomputable def lowerRelative (gap t : ℝ) : ℝ :=
  if t < max 0 gap then t ^ 2 - 2 * gap * t else -(max 0 gap) ^ 2

/-- The nominal comparison underlying the archive's "Safe lower bound" lemma.
`u = alo*T`, `z = w*a*T`, and `q = alo*tn`. The two compliance assumptions
are the evolution domain at the start and end of the actual flight segment. -/
theorem lowerRelative_comp (gap u z q : ℝ) (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hstart : gap ≤ 0 ∨ u ≤ z) (hfinish : gap - z ≤ 0 ∨ u ≤ z) :
    lowerRelative gap (u + q) ≤ z * u - 2 * gap * u + lowerRelative (gap - z) q := by
  by_cases hfast : u ≤ z
  · by_cases hg : gap ≤ 0
    · simp only [lowerRelative, max_eq_left hg,
        max_eq_left (show gap - z ≤ 0 by linarith),
        ite_eq_right (not_lt_of_ge (add_nonneg hu hq)), ite_eq_right (not_lt_of_ge hq)]
      nlinarith [mul_nonneg hu (show 0 ≤ z - 2 * gap by linarith)]
    · by_cases hgz : gap - z ≤ 0
      · simp only [lowerRelative, max_eq_right (le_of_not_ge hg), max_eq_left hgz]
        split_ifs with hold
        all_goals nlinarith [mul_nonneg (sub_nonneg.mpr hfast) hu, sq_nonneg (gap - u)]
      · simp only [lowerRelative, max_eq_right (le_of_not_ge hg),
          max_eq_right (le_of_not_ge hgz)]
        split_ifs with hold hnew
        all_goals
          nlinarith [mul_nonneg (sub_nonneg.mpr hfast) hu,
            mul_nonneg (sub_nonneg.mpr hfast) hq,
            mul_nonneg (sub_nonneg.mpr hfast) (show 0 ≤ 2 * gap - z by linarith)]
  · simp only [lowerRelative, max_eq_left (hstart.resolve_right hfast),
      max_eq_left (hfinish.resolve_right hfast),
      ite_eq_right (not_lt_of_ge (add_nonneg hu hq)), ite_eq_right (not_lt_of_ge hq)]
    nlinarith [mul_nonneg hu (show 0 ≤ z - 2 * gap by
      have := hstart.resolve_right hfast
      have := hfinish.resolve_right hfast
      linarith)]

theorem A_time_nonneg (alo t hn v w vlo : ℝ) (ha : 0 < alo)
    (hA : A alo t hn v w vlo) : 0 ≤ t := by
  rcases hA with ⟨ht, _, _⟩ | ⟨ht, _⟩
  · exact ht
  · exact (div_nonneg (le_max_left 0 _) ha.le).trans ht

theorem A_exists (alo t v w vlo : ℝ) (ht : 0 ≤ t) : ∃ hn, A alo t hn v w vlo := by
  by_cases h : t < maxI v w vlo / alo
  · exact ⟨w * alo / 2 * t ^ 2 + v * t, Or.inl ⟨ht, h, rfl⟩⟩
  · exact ⟨vlo * t - w * maxI v w vlo ^ 2 / (2 * alo), Or.inr ⟨le_of_not_gt h, rfl⟩⟩

theorem A_scaled (alo t hn v w vlo : ℝ) (ha : 0 < alo) (hw : (w = -1 ∨ w = 1))
    (hA : A alo t hn v w vlo) :
    2 * alo * (w * hn) = 2 * (w * vlo) * (alo * t) +
      lowerRelative (w * (vlo - v)) (alo * t) := by
  rcases hA with ⟨ht, hs, rfl⟩ | ⟨hs, rfl⟩
  · rw [lowerRelative, ite_eq_left (show alo * t < max 0 (w * (vlo - v)) by
      simpa [maxI, mul_comm] using (lt_div_iff₀ ha).mp hs)]
    rcases hw with rfl | rfl <;> ring
  · rw [lowerRelative, ite_eq_right (show ¬alo * t < max 0 (w * (vlo - v)) by
      have := (div_le_iff₀ ha).mp hs
      simpa [maxI, mul_comm] using not_lt_of_ge this)]
    rcases hw with rfl | rfl <;> simp only [maxI] <;> field_simp <;> ring

/-- At time `T + tn`, the original nominal height is below the actual displacement
at `T` plus the new nominal height. This is the archive's shifted-time argument. -/
theorem nominal_dominates (alo T tn oldHeight newHeight v w vlo a : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T) (htn : 0 ≤ tn)
    (hstart : advisoryLo alo v w vlo a) (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hold : A alo (T + tn) oldHeight v w vlo)
    (hnew : A alo tn newHeight (v + a * T) w vlo) :
    w * oldHeight ≤ w * (a / 2 * T ^ 2 + v * T + newHeight) := by
  have hcomp := lowerRelative_comp (w * (vlo - v)) (alo * T) (w * a * T) (alo * tn)
    (mul_nonneg ha.le hT) (mul_nonneg ha.le htn)
    (by rcases hstart with h | h
        · left; nlinarith
        · right; exact mul_le_mul_of_nonneg_right h hT)
    (by rcases hfinish with h | h
        · left; nlinarith
        · right; exact mul_le_mul_of_nonneg_right h hT)
  rw [show alo * T + alo * tn = alo * (T + tn) by ring,
    show w * (vlo - v) - w * a * T = w * (vlo - (v + a * T)) by ring] at hcomp
  nlinarith [A_scaled alo (T + tn) oldHeight v w vlo ha hw hold,
    A_scaled alo tn newHeight (v + a * T) w vlo ha hw hnew]

theorem lower_kinematic_preserved (rp hp rv alo r h v w vlo a T : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T)
    (hstart : advisoryLo alo v w vlo a) (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hsafe : Limpl rp hp rv alo r h v w vlo) :
    Limpl rp hp rv alo (r - rv * T) (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vlo := by
  intro tn rn hn ⟨hrn, hA⟩
  obtain ⟨oldHeight, hold⟩ := A_exists alo (T + tn) v w vlo
    (add_nonneg hT (A_time_nonneg alo tn hn (v + a * T) w vlo ha hA))
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [nominal_dominates alo T tn oldHeight hn v w vlo a ha hw hT
      (A_time_nonneg alo tn hn (v + a * T) w vlo ha hA) hstart hfinish hold hA]

/-- Scalar uniqueness on a closed interval, including zero-duration intervals. -/
theorem trajectory_eq (T : ℝ) (f g df : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (df t) (Set.Icc 0 T) t)
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt g (df t) (Set.Icc 0 T) t)
    (h0 : f 0 = g 0) : Set.EqOn f g (Set.Icc 0 T) := by
  intro t ht
  have heq := SemanticODE.preservedByDerivative_eq t ht.1 (fun τ => f τ - g τ) (fun _ => 0)
    (fun τ hτ => by
      have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
      convert! ((hf τ (hsub hτ)).mono hsub).sub ((hg τ (hsub hτ)).mono hsub) using 1; simp)
    (fun _ _ => rfl)
  linarith

/-- Exact polynomial solution of the archive ODE with fixed acceleration. -/
theorem motion_solution (rv a r h v T : ℝ) (D : ℝ × ℝ × ℝ → Prop)
    (path : ℝ → ℝ × ℝ × ℝ)
    (hevo : IsEvolution path (Evolvable.denotation (motion rv a)) D (r, h, v) T) :
    ∀ t ∈ Set.Icc 0 T,
      path t = (r - rv * t, h - (a / 2 * t ^ 2 + v * t), v + a * t) := by
  have hv : Set.EqOn (fun t => (path t).2.2) (fun t => v + a * t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => a)
    · exact fun t ht => (hevo.2.2 t ht).snd.snd
    · intro t _
      convert! ((hasDerivAt_const t v).add ((hasDerivAt_id t).const_mul a)).hasDerivWithinAt
        using 1; ring
    · simp [hevo.1]
  have hr : Set.EqOn (fun t => (path t).1) (fun t => r - rv * t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => -rv)
    · exact fun t ht => (hevo.2.2 t ht).fst
    · intro t _
      convert! ((hasDerivAt_const t r).sub ((hasDerivAt_id t).const_mul rv)).hasDerivWithinAt
        using 1; ring
    · simp [hevo.1]
  have hh : Set.EqOn (fun t => (path t).2.1)
      (fun t => h - (a / 2 * t ^ 2 + v * t)) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun t => -(v + a * t))
    · intro t ht
      have hv_t : (path t).2.2 = v + a * t := hv ht
      rw [← hv_t]
      exact (hevo.2.2 t ht).snd.fst
    · intro t _
      convert! ((hasDerivAt_const t h).sub
        ((((hasDerivAt_id t).pow 2).const_mul (a / 2)).add
          ((hasDerivAt_id t).const_mul v))).hasDerivWithinAt using 1; simp; ring
    · simp [hevo.1]
  exact fun t ht => Prod.ext (hr ht) (Prod.ext (hh ht) (hv ht))

def lowerStep (_rp _hp rv alo w vlo a r h v : ℝ) :=
  evolve (motion rv a) (lowerDomain alo w vlo a) (r, h, v)

@[spec] theorem lowerStep_spec (rp hp rv alo w vlo a r h v : ℝ) :
    ⦃0 < alo ∧ (w = -1 ∨ w = 1) ∧ Limpl rp hp rv alo r h v w vlo⦄
    lowerStep rp hp rv alo w vlo a r h v
    ⦃fun (r, h, v) => Limpl rp hp rv alo r h v w vlo⦄ := by
  constructor
  intro ⟨ha, hw, hsafe⟩
  unfold lowerStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (motion rv a)) (lowerDomain alo w vlo a)
    (r, h, v) (Q := fun (r, h, v) => Limpl rp hp rv alo r h v w vlo)).le_wp
  intro T hT path hevo
  rw [motion_solution rv a r h v T _ path hevo T ⟨hT, le_rfl⟩]
  apply lower_kinematic_preserved rp hp rv alo r h v w vlo a T ha hw hT
  · simpa only [hevo.1, lowerDomain] using hevo.2.1 0 ⟨le_rfl, hT⟩
  · have hdom := hevo.2.1 T ⟨hT, le_rfl⟩
    rw [motion_solution rv a r h v T _ path hevo T ⟨hT, le_rfl⟩] at hdom
    exact hdom
  · exact hsafe

theorem A_zero (alo v w vlo : ℝ) (ha : 0 < alo) : A alo 0 0 v w vlo := by
  by_cases hm : maxI v w vlo = 0
  · right
    simp [hm]
  · left
    exact ⟨le_rfl, div_pos (lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hm)) ha, by ring⟩

theorem lower_implies_noNMAC (rp hp rv alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hsafe : Limpl rp hp rv alo r h v w vlo) :
    NoNMAC rp hp r h := by
  rcases hsafe 0 0 0 ⟨by ring, A_zero alo v w vlo ha⟩ with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

/-- Signed height gained over the initial velocity line by the capped upper
trajectory. Its final slope uses `max (w*vup) (w*v)` as in the newer archive. -/
noncomputable def upperGain (gap t : ℝ) : ℝ :=
  if t < max 0 gap then t ^ 2 else 2 * max 0 gap * t - (max 0 gap) ^ 2

/-- The archive's upper-bound comparison at shifted time `T + tn`.
The hypotheses are upper compliance at the two endpoints of the actual phase. -/
theorem upperGain_comp (gap u z q : ℝ) (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hstart : z ≤ 0 ∨ (0 ≤ gap ∧ z ≤ u))
    (hfinish : z ≤ 0 ∨ (0 ≤ gap - z ∧ z ≤ u)) :
    z * u + 2 * z * q + upperGain (gap - z) q ≤ upperGain gap (u + q) := by
  have hzu : z ≤ u := hstart.elim (fun hz => hz.trans hu) And.right
  by_cases hg : 0 ≤ gap
  · have hgz : 0 ≤ gap - z := hfinish.elim (fun hz => by linarith) And.left
    simp only [upperGain, max_eq_right hg, max_eq_right hgz]
    split_ifs with hnew hold
    · nlinarith [mul_nonneg (sub_nonneg.mpr hzu) (show 0 ≤ u + 2 * q by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ gap + q by linarith)
        (show 0 ≤ gap - q - z by linarith),
        mul_nonneg (show 0 ≤ 2 * gap - z by linarith)
          (show 0 ≤ u + q - gap by linarith)]
    · linarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr hzu) (show 0 ≤ 2 * gap - z by linarith)]
  · have hz : z ≤ 0 := hstart.elim id (fun h => False.elim (hg h.1))
    by_cases hgz : 0 ≤ gap - z
    · simp only [upperGain, max_eq_left (le_of_not_ge hg), max_eq_right hgz,
        ite_eq_right (not_lt_of_ge (add_nonneg hu hq))]
      split_ifs with hnew
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hu,
          mul_nonpos_of_nonpos_of_nonneg (show 2 * z + q ≤ 0 by linarith) hq]
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hu,
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hg) hq, sq_nonneg (gap - z)]
    · simp only [upperGain, max_eq_left (le_of_not_ge hg),
        max_eq_left (le_of_not_ge hgz), ite_eq_right (not_lt_of_ge (add_nonneg hu hq)),
        ite_eq_right (not_lt_of_ge hq)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hu,
        mul_nonpos_of_nonpos_of_nonneg hz hq]

theorem Aup_time_nonneg (aup t hn v w vup : ℝ) (ha : 0 < aup)
    (hA : Aup aup t hn v w vup) : 0 ≤ t := by
  rcases hA with ⟨ht, _, _⟩ | ⟨ht, _⟩
  · exact ht
  · exact (div_nonneg (le_max_left 0 _) ha.le).trans ht

theorem Aup_exists (aup t v w vup : ℝ) (ht : 0 ≤ t) :
    ∃ hn, Aup aup t hn v w vup := by
  by_cases h : t < maxI v w vup / aup
  · exact ⟨w * aup / 2 * t ^ 2 + v * t, Or.inl ⟨ht, h, rfl⟩⟩
  · exact ⟨w * max (w * vup) (w * v) * t - w * maxI v w vup ^ 2 / (2 * aup),
      Or.inr ⟨le_of_not_gt h, rfl⟩⟩

theorem Aup_scaled (aup t hn v w vup : ℝ) (ha : 0 < aup) (hw : (w = -1 ∨ w = 1))
    (hA : Aup aup t hn v w vup) :
    2 * aup * (w * hn) = 2 * (w * v) * (aup * t) +
      upperGain (w * (vup - v)) (aup * t) := by
  have hmax : max (w * vup) (w * v) = w * v + max 0 (w * (vup - v)) := by
    rw [mul_sub]
    rcases le_total (w * v) (w * vup) with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rcases hA with ⟨ht, hs, rfl⟩ | ⟨hs, rfl⟩
  · rw [upperGain, ite_eq_left (show aup * t < max 0 (w * (vup - v)) by
      simpa [maxI, mul_comm] using (lt_div_iff₀ ha).mp hs)]
    rcases hw with rfl | rfl <;> ring
  · rw [upperGain, ite_eq_right (show ¬aup * t < max 0 (w * (vup - v)) by
      have := (div_le_iff₀ ha).mp hs
      simpa [maxI, mul_comm] using not_lt_of_ge this), hmax]
    rcases hw with rfl | rfl <;> simp only [maxI] <;> field_simp <;> ring

theorem upper_nominal_dominates (aup T tn oldHeight newHeight v w vup a : ℝ)
    (ha : 0 < aup) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T) (htn : 0 ≤ tn)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hold : Aup aup (T + tn) oldHeight v w vup)
    (hnew : Aup aup tn newHeight (v + a * T) w vup) :
    w * (a / 2 * T ^ 2 + v * T + newHeight) ≤ w * oldHeight := by
  have hcomp := upperGain_comp (w * (vup - v)) (aup * T) (w * a * T) (aup * tn)
    (mul_nonneg ha.le hT) (mul_nonneg ha.le htn)
    (by rcases hstart with ⟨hv, ha⟩ | ha
        · right
          exact ⟨by nlinarith, mul_le_mul_of_nonneg_right ha hT⟩
        · left
          exact mul_nonpos_of_nonpos_of_nonneg ha hT)
    (by rcases hfinish with ⟨hv, ha⟩ | ha
        · right
          exact ⟨by nlinarith, mul_le_mul_of_nonneg_right ha hT⟩
        · left
          exact mul_nonpos_of_nonpos_of_nonneg ha hT)
  rw [show aup * T + aup * tn = aup * (T + tn) by ring,
    show w * (vup - v) - w * a * T = w * (vup - (v + a * T)) by ring] at hcomp
  nlinarith [Aup_scaled aup (T + tn) oldHeight v w vup ha hw hold,
    Aup_scaled aup tn newHeight (v + a * T) w vup ha hw hnew]

theorem upper_kinematic_preserved (rp hp rv aup r h v w vup a T : ℝ)
    (ha : 0 < aup) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hsafe : Uimpl rp hp rv aup r h v w vup) :
    Uimpl rp hp rv aup (r - rv * T) (h - (a / 2 * T ^ 2 + v * T))
      (v + a * T) w vup := by
  intro tn rn hn ⟨hrn, hA⟩
  obtain ⟨oldHeight, hold⟩ := Aup_exists aup (T + tn) v w vup
    (add_nonneg hT (Aup_time_nonneg aup tn hn (v + a * T) w vup ha hA))
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [upper_nominal_dominates aup T tn oldHeight hn v w vup a ha hw hT
      (Aup_time_nonneg aup tn hn (v + a * T) w vup ha hA) hstart hfinish hold hA]

def twoSidedStep (_rp _hp rv alo aup w vlo vup a r h v : ℝ) :=
  evolve (motion rv a) (twoSidedDomain alo aup w vlo vup a) (r, h, v)

@[spec] theorem twoSidedStep_spec (rp hp rv alo aup w vlo vup a r h v : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ (w = -1 ∨ w = 1) ∧ Cimpl rp hp rv alo aup r h v w vlo vup⦄
    twoSidedStep rp hp rv alo aup w vlo vup a r h v
    ⦃fun (r, h, v) => Cimpl rp hp rv alo aup r h v w vlo vup⦄ := by
  constructor
  intro ⟨ha, haup, hw, hsafe⟩
  unfold twoSidedStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (motion rv a))
    (twoSidedDomain alo aup w vlo vup a) (r, h, v)
    (Q := fun (r, h, v) => Cimpl rp hp rv alo aup r h v w vlo vup)).le_wp
  intro T hT path hevo
  have hstart := hevo.2.1 0 ⟨le_rfl, hT⟩
  rw [hevo.1] at hstart
  have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
  rw [motion_solution rv a r h v T _ path hevo T ⟨hT, le_rfl⟩] at hfinish ⊢
  rcases hsafe with hsafe | hsafe
  · exact Or.inl (lower_kinematic_preserved rp hp rv alo r h v w vlo a T ha hw hT
      hstart.1 hfinish.1 hsafe)
  · exact Or.inr (upper_kinematic_preserved rp hp rv aup r h v w vup a T haup hw hT
      hstart.2 hfinish.2 hsafe)

theorem Aup_zero (aup v w vup : ℝ) (ha : 0 < aup) : Aup aup 0 0 v w vup := by
  by_cases hm : maxI v w vup = 0
  · right
    simp [hm]
  · left
    exact ⟨le_rfl, div_pos (lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hm)) ha, by ring⟩

theorem upper_implies_noNMAC (rp hp rv aup r h v w vup : ℝ)
    (ha : 0 < aup) (hw : (w = -1 ∨ w = 1)) (hsafe : Uimpl rp hp rv aup r h v w vup) :
    NoNMAC rp hp r h := by
  rcases hsafe 0 0 0 ⟨by ring, Aup_zero aup v w vup ha⟩ with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

/-- Project the physical coordinates to the already solved three-coordinate ODE;
the persistent issue clock evolves at unit rate. -/
theorem clocked_solution (rv a r h v clock T : ℝ) (D : ℝ × ℝ × ℝ × ℝ → Prop)
    (path : ℝ → ℝ × ℝ × ℝ × ℝ)
    (hevo : IsEvolution path (Evolvable.denotation (clockedMotion rv a)) D (r, h, v, clock) T) :
    ∀ t ∈ Set.Icc 0 T,
      path t = (r - rv * t, h - (a / 2 * t ^ 2 + v * t), v + a * t, clock + t) := by
  let project := fun s : ℝ × ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2.1)
  have hmotion : IsEvolution (fun t => project (path t))
      (Evolvable.denotation (motion rv a)) (fun _ => True) (r, h, v) T := by
    refine ⟨?_, fun _ _ => trivial, ?_⟩
    · simp [project, hevo.1]
    · intro t ht
      convert! (hevo.2.2 t ht).fst.prodMk
        ((hevo.2.2 t ht).snd.fst.prodMk (hevo.2.2 t ht).snd.snd.fst) using 1
  have hclock : Set.EqOn (fun t => (path t).2.2.2) (fun t => clock + t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => 1)
    · exact fun t ht => (hevo.2.2 t ht).snd.snd.snd
    · intro t _
      convert! ((hasDerivAt_const t clock).add (hasDerivAt_id t)).hasDerivWithinAt using 1
      simp
    · simp [hevo.1]
  intro t ht
  have hm := motion_solution rv a r h v T _ _ hmotion t ht
  have hc := hclock ht
  dsimp only [project] at hm
  have hr : (path t).1 = r - rv * t := congrArg (fun s => s.1) hm
  have hh : (path t).2.1 = h - (a / 2 * t ^ 2 + v * t) :=
    congrArg (fun s => s.2.1) hm
  have hv : (path t).2.2.1 = v + a * t := congrArg (fun s => s.2.2) hm
  exact Prod.ext hr (Prod.ext hh (Prod.ext hv hc))

/-- The same shifted-time lower comparison, restricted to the remaining horizon.
No initial clock lower bound or `alo ≤ aup` assumption is needed. -/
theorem lower_bounded_preserved (rp hp rv alo tl clock r h v w vlo a T : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T)
    (hstart : advisoryLo alo v w vlo a) (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hsafe : LimplBounded rp hp rv alo tl clock r h v w vlo) :
    LimplBounded rp hp rv alo tl (clock + T) (r - rv * T)
      (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vlo := by
  intro tn rn hn ⟨horizon, hrn, hA⟩
  have htn := A_time_nonneg alo tn hn (v + a * T) w vlo ha hA
  obtain ⟨oldHeight, hold⟩ := A_exists alo (T + tn) v w vlo (add_nonneg hT htn)
  have hor : T + tn ≤ tl - clock ∨ tl < 0 := horizon.imp (by intro hx; linarith) id
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨hor, rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [nominal_dominates alo T tn oldHeight hn v w vlo a ha hw hT
      htn hstart hfinish hold hA]

theorem upper_bounded_preserved (rp hp rv aup tl clock r h v w vup a T : ℝ)
    (ha : 0 < aup) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hsafe : UimplBounded rp hp rv aup tl clock r h v w vup) :
    UimplBounded rp hp rv aup tl (clock + T) (r - rv * T)
      (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vup := by
  intro tn rn hn ⟨horizon, hrn, hA⟩
  have htn := Aup_time_nonneg aup tn hn (v + a * T) w vup ha hA
  obtain ⟨oldHeight, hold⟩ := Aup_exists aup (T + tn) v w vup (add_nonneg hT htn)
  have hor : T + tn ≤ tl - clock ∨ tl < 0 := horizon.imp (by intro hx; linarith) id
  rcases hsafe (T + tn) (rv * (T + tn)) oldHeight ⟨hor, rfl, hold⟩ with hsep | hsep
  · left
    simpa only [hrn, show r - rv * T - rv * tn = r - rv * (T + tn) by ring] using hsep
  · right
    nlinarith [upper_nominal_dominates aup T tn oldHeight hn v w vup a ha hw hT
      htn hstart hfinish hold hA]

def boundedStep (_rp _hp rv alo aup tl w vlo vup a r h v clock : ℝ) :=
  evolve (clockedMotion rv a) (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)

@[spec] theorem boundedStep_spec (rp hp rv alo aup tl w vlo vup a r h v clock : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ (w = -1 ∨ w = 1) ∧ CimplBounded rp hp rv alo aup tl clock r h v w vlo vup⦄
    boundedStep rp hp rv alo aup tl w vlo vup a r h v clock
    ⦃fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplBounded rp hp rv alo aup tl clock r h v w vlo vup⦄ := by
  constructor
  intro ⟨ha, haup, hw, hsafe⟩
  unfold boundedStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (clockedMotion rv a))
    (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)
    (Q := fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplBounded rp hp rv alo aup tl clock r h v w vlo vup)).le_wp
  intro T hT path hevo
  have hstart := hevo.2.1 0 ⟨le_rfl, hT⟩
  rw [hevo.1] at hstart
  have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
  rw [clocked_solution rv a r h v clock T _ path hevo T ⟨hT, le_rfl⟩] at hfinish ⊢
  refine ⟨hfinish.1, ?_⟩
  rcases hsafe with hsafe | hsafe
  · exact Or.inl (lower_bounded_preserved rp hp rv alo tl clock r h v w vlo a T
      ha hw hT hstart.2.1 hfinish.2.1 hsafe)
  · exact Or.inr (upper_bounded_preserved rp hp rv aup tl clock r h v w vup a T
      haup hw hT hstart.2.2 hfinish.2.2 hsafe)

theorem lower_bounded_noNMAC (rp hp rv alo tl clock r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : LimplBounded rp hp rv alo tl clock r h v w vlo) : NoNMAC rp hp r h := by
  have hval := hsafe 0 0 0 ⟨ht.imp (by intro hx; linarith) id, by ring, A_zero alo v w vlo ha⟩
  rcases hval with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

theorem upper_bounded_noNMAC (rp hp rv aup tl clock r h v w vup : ℝ)
    (ha : 0 < aup) (hw : (w = -1 ∨ w = 1)) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : UimplBounded rp hp rv aup tl clock r h v w vup) : NoNMAC rp hp r h := by
  have hval := hsafe 0 0 0 ⟨ht.imp (by intro hx; linarith) id, by ring, Aup_zero aup v w vup ha⟩
  rcases hval with hsep | hsep
  · left
    simpa only [sub_zero] using hsep
  · right
    rcases hw with rfl | rfl <;> simp only [sub_zero, neg_one_mul, one_mul] at hsep
    all_goals linarith [le_abs_self h, neg_le_abs h]

theorem lowerRelative_antitone_gap (g₀ g₁ t : ℝ) (ht : 0 ≤ t) (hg : g₁ ≤ g₀) :
    lowerRelative g₀ t ≤ lowerRelative g₁ t := by
  by_cases hg₀ : g₀ ≤ 0
  · simp [lowerRelative, max_eq_left hg₀, max_eq_left (hg.trans hg₀), not_lt_of_ge ht]
  · by_cases hg₁ : g₁ ≤ 0
    · simp only [lowerRelative, max_eq_right (le_of_not_ge hg₀), max_eq_left hg₁,
        ite_eq_right (not_lt_of_ge ht)]
      split_ifs with h
      · nlinarith [mul_nonneg ht (show 0 ≤ 2 * g₀ - t by linarith)]
      · nlinarith [sq_nonneg g₀]
    · simp only [lowerRelative, max_eq_right (le_of_not_ge hg₀),
        max_eq_right (le_of_not_ge hg₁)]
      split_ifs with h₀ h₁
      · nlinarith [mul_nonneg (sub_nonneg.mpr hg) ht]
      · nlinarith [mul_nonneg (show 0 ≤ t - g₁ by linarith)
          (show 0 ≤ t + g₁ by linarith),
          mul_nonneg ht (show 0 ≤ g₀ - t by linarith)]
      · linarith
      · nlinarith [mul_nonneg (sub_nonneg.mpr hg) (show 0 ≤ g₀ + g₁ by linarith)]

/-- The supplement's escape propagation: lowering signed relative altitude and
increasing signed initial velocity preserves a lower escape region. -/
theorem lower_region_mono (rp hp rv alo r h₀ h₁ v₀ v₁ w vlo : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hh : w * h₁ ≤ w * h₀) (hv : w * v₀ ≤ w * v₁)
    (hsafe : Limpl rp hp rv alo r h₀ v₀ w vlo) :
    Limpl rp hp rv alo r h₁ v₁ w vlo := by
  intro t rn hn ⟨hrn, hA⟩
  have ht := A_time_nonneg alo t hn v₁ w vlo ha hA
  obtain ⟨oldHeight, hold⟩ := A_exists alo t v₀ w vlo ht
  rcases hsafe t rn oldHeight ⟨hrn, hold⟩ with hsep | hsep
  · exact Or.inl hsep
  · right
    have hc := lowerRelative_antitone_gap (w * (vlo - v₀)) (w * (vlo - v₁))
      (alo * t) (mul_nonneg ha.le ht) (by nlinarith)
    nlinarith [A_scaled alo t oldHeight v₀ w vlo ha hw hold,
      A_scaled alo t hn v₁ w vlo ha hw hA]

theorem lowerEndpoint_A (alo τ hn vn v w vlo : ℝ)
    (he : lowerEndpoint alo τ hn vn v w vlo) : A alo τ hn v w vlo := by
  rcases he with ⟨ht, hs, hh, _⟩ | ⟨hs, hh, _⟩
  · exact Or.inl ⟨ht, hs, hh⟩
  · exact Or.inr ⟨hs, hh⟩

theorem lowerEndpoint_velocity (alo τ hn vn v w vlo : ℝ) (ha : 0 < alo)
    (hw : (w = -1 ∨ w = 1)) (ht : 0 ≤ τ) (he : lowerEndpoint alo τ hn vn v w vlo) :
    w * vn = min (w * vlo) (w * v + alo * τ) := by
  have hw2 : w * w = 1 := by rcases hw with rfl | rfl <;> norm_num
  rcases he with ⟨_, hs, _, hv⟩ | ⟨hs, _, hv⟩
  · have hbound := (lt_div_iff₀ ha).mp hs
    by_cases hg : 0 ≤ w * (vlo - v)
    · rw [maxI, max_eq_right hg] at hbound
      rw [min_eq_right (by nlinarith)]
      rw [hv]
      nlinarith [hw2]
    · rw [maxI, max_eq_left (le_of_not_ge hg)] at hbound
      nlinarith
  · have hbound := (div_le_iff₀ ha).mp hs
    have hM : w * (vlo - v) ≤ maxI v w vlo := le_max_right _ _
    rw [min_eq_left (by nlinarith), hv]

theorem lowerEndpoint_velocity_compare (alo T q oldH oldV newH newV v w vlo a : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hold : lowerEndpoint alo (T + q) oldH oldV v w vlo)
    (hnew : lowerEndpoint alo q newH newV (v + a * T) w vlo) : w * oldV ≤ w * newV := by
  rw [lowerEndpoint_velocity alo (T + q) oldH oldV v w vlo ha hw (add_nonneg hT hq) hold,
    lowerEndpoint_velocity alo q newH newV (v + a * T) w vlo ha hw hq hnew]
  rcases hfinish with hf | hf
  · rw [min_eq_left (by nlinarith : w * vlo ≤ w * (v + a * T) + alo * q)]
    exact min_le_left _ _
  · apply min_le_min_left
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) hT]

theorem upper_speed (v w vup : ℝ) (hw : (w = -1 ∨ w = 1)) :
    v + w * maxI v w vup = w * max (w * vup) (w * v) := by
  have hm : max (w * vup) (w * v) = w * v + maxI v w vup := by
    unfold maxI
    rw [mul_sub]
    rcases le_total (w * v) (w * vup) with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rw [hm]
  rcases hw with rfl | rfl <;> ring

theorem upperEndpoint_Aup (aup τ hn vn v w vup : ℝ) (_hw : (w = -1 ∨ w = 1))
    (he : upperEndpoint aup τ hn vn v w vup) : Aup aup τ hn v w vup := by
  rcases he with ⟨ht, hs, hh, _⟩ | ⟨hs, hh, _⟩
  · exact Or.inl ⟨ht, hs, hh⟩
  · exact Or.inr ⟨hs, hh⟩

theorem upperEndpoint_velocity (aup τ hn vn v w vup : ℝ) (ha : 0 < aup)
    (hw : (w = -1 ∨ w = 1)) (_ht : 0 ≤ τ) (he : upperEndpoint aup τ hn vn v w vup) :
    w * vn = min (w * v + aup * τ) (max (w * vup) (w * v)) := by
  have hw2 : w * w = 1 := by rcases hw with rfl | rfl <;> norm_num
  have hm : max (w * vup) (w * v) = w * v + maxI v w vup := by
    have heq := congrArg (fun x => w * x) (upper_speed v w vup hw)
    simpa only [mul_add, ← mul_assoc, hw2, one_mul] using heq.symm
  rw [hm]
  rcases he with ⟨_, hs, _, hv⟩ | ⟨hs, _, hv⟩
  · have hbound := (lt_div_iff₀ ha).mp hs
    rw [min_eq_left (by linarith), hv]
    rcases hw with rfl | rfl <;> ring
  · have hbound := (div_le_iff₀ ha).mp hs
    rw [min_eq_right (by linarith), hv, hm]
    rcases hw with rfl | rfl <;> ring

theorem upperEndpoint_velocity_compare (aup T q oldH oldV newH newV v w vup a : ℝ)
    (ha : 0 < aup) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hstart : advisoryUp aup v w vup a)
    (hfinish : advisoryUp aup (v + a * T) w vup a)
    (hold : upperEndpoint aup (T + q) oldH oldV v w vup)
    (hnew : upperEndpoint aup q newH newV (v + a * T) w vup) : w * newV ≤ w * oldV := by
  rw [upperEndpoint_velocity aup (T + q) oldH oldV v w vup ha hw (add_nonneg hT hq) hold,
    upperEndpoint_velocity aup q newH newV (v + a * T) w vup ha hw hq hnew]
  by_cases hz : w * a ≤ 0
  · apply min_le_min
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hT]
    · apply max_le_max_left
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hT]
  · obtain ⟨hv₀, ha₀⟩ := hstart.resolve_right hz
    obtain ⟨hv₁, _⟩ := hfinish.resolve_right hz
    rw [max_eq_left hv₀, max_eq_left hv₁]
    apply min_le_min_right
    nlinarith [mul_nonneg (sub_nonneg.mpr ha₀) hT]

theorem lowerEndpoint_exists (alo τ v w vlo : ℝ) (ht : 0 ≤ τ) :
    ∃ hn vn, lowerEndpoint alo τ hn vn v w vlo := by
  by_cases hs : τ < maxI v w vlo / alo
  · exact ⟨_, _, Or.inl ⟨ht, hs, rfl, rfl⟩⟩
  · exact ⟨_, _, Or.inr ⟨le_of_not_gt hs, rfl, rfl⟩⟩

theorem upperEndpoint_exists (aup τ v w vup : ℝ) (ht : 0 ≤ τ) :
    ∃ hn vn, upperEndpoint aup τ hn vn v w vup := by
  by_cases hs : τ < maxI v w vup / aup
  · exact ⟨_, _, Or.inl ⟨ht, hs, rfl, rfl⟩⟩
  · exact ⟨_, _, Or.inr ⟨le_of_not_gt hs, rfl, rfl⟩⟩

/-- Preserve the escape condition at the fixed advisory horizon using the
nominal endpoint height and velocity comparisons, separately for each sense. -/
theorem safeable_kinematic_preserved
    (rp hp rv alo aup tl clock vloEx vupEx r h v w vlo vup a T : ℝ)
    (ha : 0 < alo) (haup : 0 < aup) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T)
    (horizon : clock + T ≤ tl)
    (hstart : advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a)
    (hfinish : advisoryLo alo (v + a * T) w vlo a ∧ advisoryUp aup (v + a * T) w vup a)
    (hsafe : CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx) :
    CimplSafeable rp hp rv alo aup tl (clock + T) (r - rv * T)
      (h - (a / 2 * T ^ 2 + v * T)) (v + a * T) w vlo vloEx vup vupEx := by
  have hq : 0 ≤ tl - (clock + T) := sub_nonneg.mpr horizon
  have hs : 0 ≤ tl - clock := by linarith
  have htime : T + (tl - (clock + T)) = tl - clock := by ring
  rcases hsafe with ⟨hbounded, hescape⟩ | ⟨hbounded, hescape⟩
  · left
    refine ⟨lower_bounded_preserved rp hp rv alo tl clock r h v w vlo a T
      ha hw hT hstart.1 hfinish.1 hbounded, ?_⟩
    intro newH newV hnew
    obtain ⟨oldH, oldV, hold⟩ := lowerEndpoint_exists alo (tl - clock) v w vlo hs
    have hold' : lowerEndpoint alo (T + (tl - (clock + T))) oldH oldV v w vlo := by
      rwa [htime]
    have hh := nominal_dominates alo T (tl - (clock + T)) oldH newH v w vlo a
      ha hw hT hq hstart.1 hfinish.1 (lowerEndpoint_A _ _ _ _ _ _ _ hold')
      (lowerEndpoint_A _ _ _ _ _ _ _ hnew)
    have hv := lowerEndpoint_velocity_compare alo T (tl - (clock + T))
      oldH oldV newH newV v w vlo a ha hw hT hq hfinish.1 hold' hnew
    rw [show r - rv * T - rv * (tl - (clock + T)) = r - rv * (tl - clock) by ring]
    exact lower_region_mono rp hp rv alo _ (h - oldH)
      (h - (a / 2 * T ^ 2 + v * T) - newH) oldV newV w vloEx ha hw
      (by nlinarith) hv (hescape oldH oldV hold)
  · right
    refine ⟨upper_bounded_preserved rp hp rv aup tl clock r h v w vup a T
      haup hw hT hstart.2 hfinish.2 hbounded, ?_⟩
    intro newH newV hnew
    obtain ⟨oldH, oldV, hold⟩ := upperEndpoint_exists aup (tl - clock) v w vup hs
    have hold' : upperEndpoint aup (T + (tl - (clock + T))) oldH oldV v w vup := by
      rwa [htime]
    have hh := upper_nominal_dominates aup T (tl - (clock + T)) oldH newH v w vup a
      haup hw hT hq hstart.2 hfinish.2 (upperEndpoint_Aup _ _ _ _ _ _ _ hw hold')
      (upperEndpoint_Aup _ _ _ _ _ _ _ hw hnew)
    have hv := upperEndpoint_velocity_compare aup T (tl - (clock + T))
      oldH oldV newH newV v w vup a haup hw hT hq hstart.2 hfinish.2 hold' hnew
    have hwneg : (-w = -1 ∨ -w = 1) := by rcases hw with rfl | rfl <;> norm_num
    rw [show r - rv * T - rv * (tl - (clock + T)) = r - rv * (tl - clock) by ring]
    exact lower_region_mono rp hp rv alo _ (h - oldH)
      (h - (a / 2 * T ^ 2 + v * T) - newH) oldV newV (-w) vupEx ha hwneg
      (by nlinarith) (by nlinarith) (hescape oldH oldV hold)

def safeableStep (_rp _hp rv alo aup tl _vloEx _vupEx w vlo vup a r h v clock : ℝ) :=
  evolve (clockedMotion rv a) (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)

@[spec] theorem safeableStep_spec
    (rp hp rv alo aup tl vloEx vupEx w vlo vup a r h v clock : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ 0 ≤ tl ∧ (w = -1 ∨ w = 1) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx⦄
    safeableStep rp hp rv alo aup tl vloEx vupEx w vlo vup a r h v clock
    ⦃fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx⦄ := by
  constructor
  intro ⟨ha, haup, htl, hw, hsafe⟩
  unfold safeableStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (clockedMotion rv a))
    (clockedDomain alo aup tl w vlo vup a) (r, h, v, clock)
    (Q := fun (r, h, v, clock) => (clock ≤ tl ∨ tl < 0) ∧
      CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx)).le_wp
  intro T hT path hevo
  have hstart := hevo.2.1 0 ⟨le_rfl, hT⟩
  rw [hevo.1] at hstart
  have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
  rw [clocked_solution rv a r h v clock T _ path hevo T ⟨hT, le_rfl⟩] at hfinish ⊢
  exact ⟨hfinish.1, safeable_kinematic_preserved rp hp rv alo aup tl clock vloEx vupEx
    r h v w vlo vup a T ha haup hw hT (hfinish.1.resolve_right (not_lt_of_ge htl))
    hstart.2 hfinish.2 hsafe⟩

/-- Collision exclusion along the worst permitted delay acceleration, including
its endpoint. That endpoint is also the origin of the resolution trajectory. -/
def delayPrefix (rp hp rv ad D r h v w : ℝ) : Prop :=
  ∀ t, 0 ≤ t → t ≤ D →
    rp < |r - rv * t| ∨ w * (h - (-(w * ad) / 2 * t ^ 2 + v * t)) < -hp

/-- The selected delayed kyx uses the velocity after the delay in `A`.
Split its quantified graph into the delay prefix and that shifted lower region. -/
theorem delayed_decomposition (rp hp rv alo ad r h v w vlo d : ℝ) (ha : 0 < alo) :
    Dimpl rp hp rv alo ad r h v w vlo d ↔
      delayPrefix rp hp rv ad (max 0 d) r h v w ∧
      Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo := by
  constructor
  · intro hs
    have hres : Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo := by
      intro t rn hn ⟨hrn, hA⟩
      have hval := hs (max 0 d + t) (rv * (max 0 d + t))
        (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d + hn)
        (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d)
        (v - w * ad * max 0 d)
        ⟨rfl, Or.inr ⟨⟨rfl, by ring⟩, by convert hA using 1 <;> ring⟩⟩
      rw [hrn]
      convert hval using 1 <;> ring_nf
    refine ⟨?_, hres⟩
    intro t ht htd
    by_cases hs' : t < max 0 d
    · exact hs t (rv * t) (-(w * ad) / 2 * t ^ 2 + v * t) 0 0
        ⟨rfl, Or.inl ⟨ht, hs', rfl⟩⟩
    · have heq : t = max 0 d := le_antisymm htd (le_of_not_gt hs')
      subst t
      have hval := hres 0 0 0 ⟨by ring, A_zero alo _ w vlo ha⟩
      simpa only [mul_zero, sub_zero, zero_add] using hval
  · rintro ⟨hpre, hres⟩ t rn hn hd vd ⟨hrn, hdelay | ⟨⟨hhd, hvd⟩, hA⟩⟩
    · rcases hdelay with ⟨ht, htd, rfl⟩
      simpa only [hrn] using hpre t ht htd.le
    · have hvel : vd = v - w * ad * max 0 d := by linarith
      rw [hvel] at hA
      have hval := hres (t - max 0 d) (rv * (t - max 0 d)) (hn - hd) ⟨rfl, hA⟩
      rw [hhd] at hval
      rw [hrn]
      convert hval using 1 <;> ring_nf

theorem delayed_nonpos (rp hp rv alo ad r h v w vlo d : ℝ) (ha : 0 < alo) (hd : d ≤ 0) :
    Dimpl rp hp rv alo ad r h v w vlo d ↔ Limpl rp hp rv alo r h v w vlo := by
  rw [delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha, max_eq_left hd]
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero]
  constructor
  · exact And.right
  · intro hs
    refine ⟨?_, hs⟩
    intro t ht hu
    have heq : t = 0 := le_antisymm hu ht
    subst t
    simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] using
      hs 0 0 0 ⟨by ring, A_zero alo v w vlo ha⟩

theorem delay_height_compare (ad T q v w a : ℝ) (hw : (w = -1 ∨ w = 1))
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hacc : -ad ≤ w * a) :
    w * (-(w * ad) / 2 * (T + q) ^ 2 + v * (T + q)) ≤
      w * (a / 2 * T ^ 2 + v * T + (-(w * ad) / 2 * q ^ 2 + (v + a * T) * q)) := by
  have hprod := mul_nonneg (mul_nonneg (show 0 ≤ w * a + ad by linarith) hT)
    (show 0 ≤ T + 2 * q by linarith)
  rcases hw with rfl | rfl <;> norm_num at hprod ⊢ <;> nlinarith

theorem delay_actual_bounds (ad T v w a : ℝ) (hw : (w = -1 ∨ w = 1))
    (hT : 0 ≤ T) (hacc : -ad ≤ w * a) :
    w * (-(w * ad) / 2 * T ^ 2 + v * T) ≤ w * (a / 2 * T ^ 2 + v * T) ∧
      w * (v - w * ad * T) ≤ w * (v + a * T) := by
  have hh := delay_height_compare ad T 0 v w a hw hT le_rfl hacc
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
  refine ⟨hh, ?_⟩
  have hprod := mul_nonneg (show 0 ≤ w * a + ad by linarith) hT
  rcases hw with rfl | rfl <;> norm_num at hprod ⊢ <;> nlinarith

/-- While delay remains, the acceleration test bounds both future delay heights
and the resolution's starting velocity. Propagate the shifted lower region. -/
theorem delayed_before_preserved (rp hp rv alo ad r h v w vlo d a T : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hT : 0 ≤ T) (hTd : T ≤ d)
    (hacc : -ad ≤ w * a) (hsafe : Dimpl rp hp rv alo ad r h v w vlo d) :
    Dimpl rp hp rv alo ad (r - rv * T) (h - (a / 2 * T ^ 2 + v * T))
      (v + a * T) w vlo (d - T) := by
  rw [delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha,
    max_eq_right (show 0 ≤ d - T by linarith)]
  have hs := (delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha).mp hsafe
  rw [max_eq_right (hT.trans hTd)] at hs
  constructor
  · intro t ht htd
    have hval := hs.1 (T + t) (add_nonneg hT ht) (by linarith)
    rcases hval with hsep | hsep
    · left
      simpa only [show r - rv * T - rv * t = r - rv * (T + t) by ring] using hsep
    · right
      nlinarith [delay_height_compare ad T t v w a hw hT ht hacc]
  · have hh := delay_height_compare ad T (d - T) v w a hw hT
      (sub_nonneg.mpr hTd) hacc
    rw [show T + (d - T) = d by ring] at hh
    have hv : w * (v - w * ad * d) ≤ w * (v + a * T - w * ad * (d - T)) := by
      have hp := mul_nonneg (show 0 ≤ w * a + ad by linarith) hT
      rcases hw with rfl | rfl <;> norm_num at hp ⊢ <;> nlinarith
    rw [show r - rv * T - rv * (d - T) = r - rv * d by ring]
    exact lower_region_mono rp hp rv alo _ _ _ _ _ w vlo ha hw
      (by nlinarith) hv hs.2

/-- Once delay expires, first compare the actual state at expiry with the delay
endpoint, then apply immediate preservation over the remaining actual motion. -/
theorem delayed_after_preserved (rp hp rv alo ad r h v w vlo d a T : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hTd : max 0 d ≤ T)
    (hacc : -ad ≤ w * a)
    (hstart : advisoryLo alo (v + a * max 0 d) w vlo a)
    (hfinish : advisoryLo alo (v + a * T) w vlo a)
    (hsafe : Dimpl rp hp rv alo ad r h v w vlo d) :
    Dimpl rp hp rv alo ad (r - rv * T) (h - (a / 2 * T ^ 2 + v * T))
      (v + a * T) w vlo (d - T) := by
  rw [delayed_nonpos _ _ _ _ _ _ _ _ _ _ _ ha
    (show d - T ≤ 0 by linarith [le_max_right 0 d])]
  have hs := ((delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha).mp hsafe).2
  obtain ⟨hh, hv⟩ := delay_actual_bounds ad (max 0 d) v w a hw (le_max_left 0 d) hacc
  have hm := lower_region_mono rp hp rv alo (r - rv * max 0 d)
    (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
    (h - (a / 2 * max 0 d ^ 2 + v * max 0 d))
    (v - w * ad * max 0 d) (v + a * max 0 d) w vlo ha hw (by nlinarith) hv hs
  have hc := lower_kinematic_preserved rp hp rv alo (r - rv * max 0 d)
    (h - (a / 2 * max 0 d ^ 2 + v * max 0 d)) (v + a * max 0 d) w vlo a
    (T - max 0 d) ha hw (sub_nonneg.mpr hTd) hstart
    (by convert hfinish using 1; ring) hm
  convert hc using 1 <;> ring_nf

theorem delayed_solution (rv a r h v d T : ℝ) (D : ℝ × ℝ × ℝ × ℝ × ℝ → Prop)
    (path : ℝ → ℝ × ℝ × ℝ × ℝ × ℝ)
    (hevo : IsEvolution path (Evolvable.denotation (delayedMotion rv a)) D (r, h, v, d, 0) T) :
    ∀ t ∈ Set.Icc 0 T,
      path t = (r - rv * t, h - (a / 2 * t ^ 2 + v * t), v + a * t, d - t, t) := by
  let project := fun s : ℝ × ℝ × ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2.1, s.2.2.2.2)
  have hmotion : IsEvolution (fun t => project (path t))
      (Evolvable.denotation (clockedMotion rv a)) (fun _ => True) (r, h, v, 0) T := by
    refine ⟨?_, fun _ _ => trivial, ?_⟩
    · simp [project, hevo.1]
    · intro t ht
      convert! (hevo.2.2 t ht).fst.prodMk
        ((hevo.2.2 t ht).snd.fst.prodMk
          ((hevo.2.2 t ht).snd.snd.fst.prodMk (hevo.2.2 t ht).snd.snd.snd.snd)) using 1
  have hdelay : Set.EqOn (fun t => (path t).2.2.2.1) (fun t => d - t) (Set.Icc 0 T) := by
    apply trajectory_eq T _ _ (fun _ => -1)
    · exact fun t ht => (hevo.2.2 t ht).snd.snd.snd.fst
    · intro t _
      convert! ((hasDerivAt_const t d).sub (hasDerivAt_id t)).hasDerivWithinAt using 1
      norm_num
    · simp [hevo.1]
  intro t ht
  have hm := clocked_solution rv a r h v 0 T _ _ hmotion t ht
  have hd := hdelay ht
  dsimp only [project] at hm
  have hr : (path t).1 = r - rv * t := congrArg (fun s => s.1) hm
  have hh : (path t).2.1 = h - (a / 2 * t ^ 2 + v * t) := congrArg (fun s => s.2.1) hm
  have hv : (path t).2.2.1 = v + a * t := congrArg (fun s => s.2.2.1) hm
  have hc : (path t).2.2.2.2 = t := by simpa using congrArg (fun s => s.2.2.2) hm
  exact Prod.ext hr (Prod.ext hh (Prod.ext hv (Prod.ext hd hc)))

def delayedStep (_rp _hp rv alo _ad ε w vlo a r h v d : ℝ) :=
  evolve (delayedMotion rv a) (delayedDomain alo ε w vlo a) (r, h, v, d, 0)

@[spec] theorem delayedStep_spec (rp hp rv alo ad ε w vlo a r h v d : ℝ) :
    ⦃0 < alo ∧ (w = -1 ∨ w = 1) ∧ -ad ≤ w * a ∧ Dimpl rp hp rv alo ad r h v w vlo d⦄
    delayedStep rp hp rv alo ad ε w vlo a r h v d
    ⦃fun (r, h, v, d, _) => Dimpl rp hp rv alo ad r h v w vlo d⦄ := by
  constructor
  intro ⟨ha, hw, hacc, hsafe⟩
  unfold delayedStep evolve
  apply (evolveSemantic_spec (Evolvable.denotation (delayedMotion rv a))
    (delayedDomain alo ε w vlo a) (r, h, v, d, 0)
    (Q := fun (r, h, v, d, _) => Dimpl rp hp rv alo ad r h v w vlo d)).le_wp
  intro T hT path hevo
  rw [delayed_solution rv a r h v d T _ path hevo T ⟨hT, le_rfl⟩]
  by_cases hTd : T < max 0 d
  · have hd : 0 ≤ d := by
      by_contra hn
      rw [max_eq_left (le_of_not_ge hn)] at hTd
      linarith
    exact delayed_before_preserved rp hp rv alo ad r h v w vlo d a T ha hw hT
      (by rw [max_eq_right hd] at hTd; exact hTd.le) hacc hsafe
  · have hDT : max 0 d ≤ T := le_of_not_gt hTd
    have hstart := hevo.2.1 (max 0 d) ⟨le_max_left 0 d, hDT⟩
    have hfinish := hevo.2.1 T ⟨hT, le_rfl⟩
    rw [delayed_solution rv a r h v d T _ path hevo (max 0 d)
      ⟨le_max_left 0 d, hDT⟩] at hstart
    rw [delayed_solution rv a r h v d T _ path hevo T ⟨hT, le_rfl⟩] at hfinish
    exact delayed_after_preserved rp hp rv alo ad r h v w vlo d a T ha hw hDT hacc
      (hstart.2 (by linarith [le_max_right 0 d]))
      (hfinish.2 (by linarith [le_max_right 0 d])) hsafe

theorem delayed_noNMAC (rp hp rv alo ad r h v w vlo d : ℝ)
    (ha : 0 < alo) (hw : (w = -1 ∨ w = 1)) (hsafe : Dimpl rp hp rv alo ad r h v w vlo d) :
    NoNMAC rp hp r h := by
  have hval := ((delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ ha).mp hsafe).1 0
    le_rfl (le_max_left 0 d)
  rcases hval with hsep | hsep
  · left
    simpa using hsep
  · right
    rcases hw with rfl | rfl <;>
      norm_num at hsep ⊢ <;> linarith [le_abs_self h, neg_le_abs h]

/-- An admissible remaining-time region excludes a collision at its current state. -/
theorem bounded_region_noNMAC (rp hp rv alo aup tl clock r h v w vlo vup : ℝ)
    (ha : 0 < alo) (haup : 0 < aup) (hw : (w = -1 ∨ w = 1)) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : CimplBounded rp hp rv alo aup tl clock r h v w vlo vup) :
    NoNMAC rp hp r h := by
  rcases hsafe with hlo | hup
  · exact lower_bounded_noNMAC rp hp rv alo tl clock r h v w vlo ha hw ht hlo
  · exact upper_bounded_noNMAC rp hp rv aup tl clock r h v w vup haup hw ht hup

/-- The bounded component of either safeable branch implies present safety. -/
theorem safeable_region_noNMAC (rp hp rv alo aup tl clock vloEx vupEx r h v w vlo vup : ℝ)
    (ha : 0 < alo) (haup : 0 < aup) (hw : (w = -1 ∨ w = 1)) (ht : clock ≤ tl ∨ tl < 0)
    (hsafe : CimplSafeable rp hp rv alo aup tl clock r h v w vlo vloEx vup vupEx) :
    NoNMAC rp hp r h := by
  apply bounded_region_noNMAC rp hp rv alo aup tl clock r h v w vlo vup ha haup hw ht
  exact hsafe.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

end Scalar

/-! The record-based predicates are equivalent to the original scalar formulas. -/
namespace Representation

theorem direction_valid (direction : Direction) :
    direction.sign = -1 ∨ direction.sign = 1 := by
  cases direction <;> simp [Direction.sign]

def horizonValue : TimeHorizon → ℝ
  | .unlimited => -1
  | .bounded duration => duration.val

theorem includes_iff (limit : TimeHorizon) (t tn : ℝ) :
    limit.includes t tn ↔ tn ≤ horizonValue limit - t ∨ horizonValue limit < 0 := by
  cases limit with
  | unlimited => simp [TimeHorizon.includes, horizonValue]
  | bounded duration => simp [TimeHorizon.includes, horizonValue, not_lt.mpr duration.property]

theorem displacementLo_iff (advisory : Advisory) (alo v t hn : ℝ) :
    advisory.DisplacementLo alo v t hn ↔
      Scalar.A alo t hn v advisory.direction.sign advisory.targetv := Iff.rfl

theorem displacementUp_iff (advisory : Advisory) (aup v t hn : ℝ) :
    advisory.DisplacementUp aup v t hn ↔
      Scalar.Aup aup t hn v advisory.direction.sign advisory.targetv := Iff.rfl

theorem loSafeFor_iff (advisory : Advisory) (encounter : Encounter) (rp hp rv alo : ℝ) :
    advisory.LoSafeFor encounter rp hp rv alo ↔
      Scalar.Limpl rp hp rv alo encounter.r encounter.h encounter.v
        advisory.direction.sign advisory.targetv := by
  constructor
  · intro h t rn hn ⟨hrn, hA⟩
    subst rn
    exact h t hn hA
  · intro h t hn hA
    exact h t (rv * t) hn ⟨rfl, hA⟩

theorem upSafeFor_iff (advisory : Advisory) (encounter : Encounter) (rp hp rv aup : ℝ) :
    advisory.UpSafeFor encounter rp hp rv aup ↔
      Scalar.Uimpl rp hp rv aup encounter.r encounter.h encounter.v
        advisory.direction.sign advisory.targetv := by
  constructor
  · intro h t rn hn ⟨hrn, hA⟩
    subst rn
    exact h t hn hA
  · intro h t hn hA
    exact h t (rv * t) hn ⟨rfl, hA⟩

theorem delayedSafeFor_iff (advisory : Advisory) (encounter : Encounter)
    (rp hp rv alo ad d : ℝ) :
    advisory.DelayedSafeFor encounter rp hp rv alo ad d ↔
      Scalar.Dimpl rp hp rv alo ad encounter.r encounter.h encounter.v
        advisory.direction.sign advisory.targetv d := by
  simp only [Advisory.DelayedSafeFor, AircraftSeparatedLo, displacement,
    displacementLo_iff, Scalar.Dimpl, neg_mul]
  constructor
  · intro h t rn hn hd vd ⟨hrn, hA⟩
    subst rn
    exact h t hn hd vd hA
  · intro h t hn hd vd hA
    exact h t (rv * t) hn hd vd ⟨rfl, hA⟩

theorem safeFor_iff (advisory : TwoSidedAdvisory) (encounter : Encounter)
    (rp hp rv alo aup : ℝ) :
    advisory.SafeFor encounter rp hp rv alo aup ↔
      Scalar.Cimpl rp hp rv alo aup encounter.r encounter.h encounter.v
        advisory.direction.sign advisory.lower advisory.upper := by
  simp only [TwoSidedAdvisory.SafeFor, loSafeFor_iff, upSafeFor_iff]
  rfl

theorem loSafeForWithin_iff (advisory : Advisory) (encounter : Encounter)
    (rp hp rv alo : ℝ) (limit : TimeHorizon) (t : ℝ) :
    advisory.LoSafeForWithin encounter rp hp rv alo limit t ↔
      Scalar.LimplBounded rp hp rv alo (horizonValue limit) t
        encounter.r encounter.h encounter.v advisory.direction.sign advisory.targetv := by
  simp only [Advisory.LoSafeForWithin, AircraftSeparatedLo, includes_iff,
    displacementLo_iff, Scalar.LimplBounded]
  constructor
  · intro h tn rn hn ⟨ht, hrn, hA⟩
    subst rn
    exact h tn hn ⟨ht, hA⟩
  · intro h tn hn ⟨ht, hA⟩
    exact h tn (rv * tn) hn ⟨ht, rfl, hA⟩

theorem upSafeForWithin_iff (advisory : Advisory) (encounter : Encounter)
    (rp hp rv aup : ℝ) (limit : TimeHorizon) (t : ℝ) :
    advisory.UpSafeForWithin encounter rp hp rv aup limit t ↔
      Scalar.UimplBounded rp hp rv aup (horizonValue limit) t
        encounter.r encounter.h encounter.v advisory.direction.sign advisory.targetv := by
  simp only [Advisory.UpSafeForWithin, AircraftSeparatedUp, includes_iff,
    displacementUp_iff, Scalar.UimplBounded]
  constructor
  · intro h tn rn hn ⟨ht, hrn, hA⟩
    subst rn
    exact h tn hn ⟨ht, hA⟩
  · intro h tn hn ⟨ht, hA⟩
    exact h tn (rv * tn) hn ⟨ht, rfl, hA⟩

theorem safeForWithin_iff (advisory : TwoSidedAdvisory) (encounter : Encounter)
    (rp hp rv alo aup : ℝ) (limit : TimeHorizon) (t : ℝ) :
    advisory.SafeForWithin encounter rp hp rv alo aup limit t ↔
      Scalar.CimplBounded rp hp rv alo aup (horizonValue limit) t
        encounter.r encounter.h encounter.v advisory.direction.sign
        advisory.lower advisory.upper := by
  simp only [TwoSidedAdvisory.SafeForWithin, loSafeForWithin_iff, upSafeForWithin_iff]
  rfl

theorem endpointLo_iff (advisory : Advisory) (alo v τ hn vn : ℝ) :
    advisory.EndpointLo alo v τ hn vn ↔
      Scalar.lowerEndpoint alo τ hn vn v advisory.direction.sign advisory.targetv := by
  by_cases h : τ < advisory.shortfallOf v / alo
  · simp only [Advisory.EndpointLo, Advisory.DisplacementLo, Scalar.lowerEndpoint,
      displacement, Advisory.shortfallOf, Scalar.maxI, h, not_le_of_gt h,
      true_and, false_and, or_false, and_assoc]
    tauto
  · simp only [Advisory.EndpointLo, Advisory.DisplacementLo, Scalar.lowerEndpoint,
      displacement, Advisory.shortfallOf, Scalar.maxI, h, le_of_not_gt h,
      true_and, and_false, false_and, false_or]

theorem endpointUp_iff (advisory : Advisory) (aup v τ hn vn : ℝ) :
    advisory.EndpointUp aup v τ hn vn ↔
      Scalar.upperEndpoint aup τ hn vn v advisory.direction.sign advisory.targetv := by
  by_cases h : τ < advisory.shortfallOf v / aup
  · simp only [Advisory.EndpointUp, Advisory.DisplacementUp, Scalar.upperEndpoint,
      displacement, Advisory.shortfallOf, Scalar.maxI, h, not_le_of_gt h,
      true_and, false_and, or_false, and_assoc]
    tauto
  · simp only [Advisory.EndpointUp, Advisory.DisplacementUp, Scalar.upperEndpoint,
      displacement, Advisory.shortfallOf, Scalar.maxI, h, le_of_not_gt h,
      true_and, and_false, false_and, false_or]

theorem safeableFor_iff (advisory : TwoSidedAdvisory) (encounter : Encounter)
    (rp hp rv alo aup : ℝ) (duration : Duration) (t vloEx vupEx : ℝ) :
    advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx ↔
      Scalar.CimplSafeable rp hp rv alo aup duration.val t
        encounter.r encounter.h encounter.v advisory.direction.sign
        advisory.lower vloEx advisory.upper vupEx := by
  simp only [TwoSidedAdvisory.SafeableFor, loSafeForWithin_iff, upSafeForWithin_iff,
    endpointLo_iff, endpointUp_iff, loSafeFor_iff, horizonValue,
    Scalar.CimplSafeable, TwoSidedAdvisory.lowerAdvisory, TwoSidedAdvisory.upperAdvisory]
  cases advisory.direction <;> simp [Direction.sign]

end Representation


namespace Controller

open Representation

def lowerStep (_rp _hp rv alo a : ℝ) (encounter : Encounter) (advisory : Advisory) :=
  evolve (motionODE rv a) (domainLo alo a advisory) (encounter.r, encounter.h, encounter.v)

@[spec] theorem lowerStep_spec (rp hp rv alo a : ℝ) (encounter : Encounter)
    (advisory : Advisory) :
    ⦃0 < alo ∧ advisory.LoSafeFor encounter rp hp rv alo⦄
    lowerStep rp hp rv alo a encounter advisory
    ⦃fun (r, h, v) => advisory.LoSafeFor ⟨r, h, v⟩ rp hp rv alo⦄ := by
  constructor
  intro ⟨ha, hs⟩ result hrun
  exact (loSafeFor_iff ..).mpr
    ((Scalar.lowerStep_spec rp hp rv alo advisory.direction.sign advisory.targetv a
      encounter.r encounter.h encounter.v).le_wp
      ⟨ha, direction_valid _, (loSafeFor_iff ..).mp hs⟩ result hrun)

def delayedStep (_rp _hp rv alo _ad ε a : ℝ) (encounter : Encounter)
    (advisory : Advisory) (d : ℝ) :=
  evolve (withDelayODE rv a) (domainDelayed alo ε a advisory)
    (encounter.r, encounter.h, encounter.v, d, 0)

@[spec] theorem delayedStep_spec (rp hp rv alo ad ε a : ℝ) (encounter : Encounter)
    (advisory : Advisory) (d : ℝ) :
    ⦃0 < alo ∧ -ad ≤ advisory.direction.sign * a ∧
      advisory.DelayedSafeFor encounter rp hp rv alo ad d⦄
    delayedStep rp hp rv alo ad ε a encounter advisory d
    ⦃fun (r, h, v, d, _) => advisory.DelayedSafeFor ⟨r, h, v⟩ rp hp rv alo ad d⦄ := by
  constructor
  intro ⟨ha, hacc, hs⟩ result hrun
  exact (delayedSafeFor_iff ..).mpr
    ((Scalar.delayedStep_spec rp hp rv alo ad ε advisory.direction.sign advisory.targetv a
      encounter.r encounter.h encounter.v d).le_wp
      ⟨ha, direction_valid _, hacc, (delayedSafeFor_iff ..).mp hs⟩ result hrun)

def twoSidedStep (_rp _hp rv alo aup a : ℝ) (encounter : Encounter) (advisory : TwoSidedAdvisory) :=
  evolve (motionODE rv a) (domainTwoSided alo aup a advisory)
    (encounter.r, encounter.h, encounter.v)

@[spec] theorem twoSidedStep_spec (rp hp rv alo aup a : ℝ) (encounter : Encounter)
    (advisory : TwoSidedAdvisory) :
    ⦃0 < alo ∧ 0 < aup ∧ advisory.SafeFor encounter rp hp rv alo aup⦄
    twoSidedStep rp hp rv alo aup a encounter advisory
    ⦃fun (r, h, v) => advisory.SafeFor ⟨r, h, v⟩ rp hp rv alo aup⦄ := by
  constructor
  intro ⟨ha, haup, hs⟩ result hrun
  exact (safeFor_iff ..).mpr
    ((Scalar.twoSidedStep_spec rp hp rv alo aup advisory.direction.sign advisory.lower
      advisory.upper a encounter.r encounter.h encounter.v).le_wp
      ⟨ha, haup, direction_valid _, (safeFor_iff ..).mp hs⟩ result hrun)

theorem domainClocked_eq (alo aup : ℝ) (limit : TimeHorizon) (a : ℝ)
    (advisory : TwoSidedAdvisory) :
    domainClocked alo aup limit a advisory =
      Scalar.clockedDomain alo aup (horizonValue limit) advisory.direction.sign
        advisory.lower advisory.upper a := by
  funext ⟨r, h, v, t⟩
  apply propext
  simp only [domainClocked, Scalar.clockedDomain, includes_iff, sub_zero]
  rfl

def boundedStep (_rp _hp rv alo aup : ℝ) (limit : TimeHorizon) (a : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) :=
  evolve (motionClockedODE rv a) (domainClocked alo aup limit a advisory)
    (encounter.r, encounter.h, encounter.v, t)

@[spec] theorem boundedStep_spec (rp hp rv alo aup : ℝ) (limit : TimeHorizon) (a : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ advisory.SafeForWithin encounter rp hp rv alo aup limit t⦄
    boundedStep rp hp rv alo aup limit a encounter advisory t
    ⦃fun (r, h, v, t) => limit.includes 0 t ∧
      advisory.SafeForWithin ⟨r, h, v⟩ rp hp rv alo aup limit t⦄ := by
  constructor
  intro ⟨ha, haup, hs⟩ result hrun
  rw [boundedStep, domainClocked_eq] at hrun
  have h := (Scalar.boundedStep_spec rp hp rv alo aup (horizonValue limit)
    advisory.direction.sign advisory.lower advisory.upper a
    encounter.r encounter.h encounter.v t).le_wp
    ⟨ha, haup, direction_valid _, (safeForWithin_iff ..).mp hs⟩ result hrun
  exact ⟨(includes_iff ..).mpr (by simpa only [sub_zero] using h.1),
    (safeForWithin_iff ..).mpr h.2⟩

def safeableStep (_rp _hp rv alo aup : ℝ) (duration : Duration) (_vloEx _vupEx a : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) :=
  evolve (motionClockedODE rv a) (domainClocked alo aup (.bounded duration) a advisory)
    (encounter.r, encounter.h, encounter.v, t)

@[spec] theorem safeableStep_spec (rp hp rv alo aup : ℝ) (duration : Duration)
    (vloEx vupEx a : ℝ) (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) :
    ⦃0 < alo ∧ 0 < aup ∧ advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx⦄
    safeableStep rp hp rv alo aup duration vloEx vupEx a encounter advisory t
    ⦃fun (r, h, v, t) => t ≤ duration.val ∧
      advisory.SafeableFor ⟨r, h, v⟩ rp hp rv alo aup duration t vloEx vupEx⦄ := by
  constructor
  intro ⟨ha, haup, hs⟩ result hrun
  rw [safeableStep, domainClocked_eq] at hrun
  have h := (Scalar.safeableStep_spec rp hp rv alo aup duration.val vloEx vupEx
    advisory.direction.sign advisory.lower advisory.upper a
    encounter.r encounter.h encounter.v t).le_wp
    ⟨ha, haup, duration.property, direction_valid _, (safeableFor_iff ..).mp hs⟩ result hrun
  exact ⟨h.1.resolve_right (not_lt.mpr duration.property), (safeableFor_iff ..).mpr h.2⟩

end Controller

namespace Controller

-- Keep VC matching from unfolding the trajectory let-bindings inside safe-region predicates.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Advisory.LoSafeFor Advisory.UpSafeFor
  Advisory.DelayedSafeFor TwoSidedAdvisory.SafeFor Advisory.LoSafeForWithin
  Advisory.UpSafeForWithin TwoSidedAdvisory.SafeForWithin TwoSidedAdvisory.SafeableFor

def immediateResponseProgAnnotated
    (rp hp rv alo : ℝ) (encounter : Encounter) (advisory : Advisory) : SetM Result
    requires 0 < alo ∧ advisory.LoSafeFor encounter rp hp rv alo
    ensures res => res.advisory.LoSafeFor res.encounter rp hp rv alo
    := do
  let mut (encounter, advisory) := (encounter, advisory)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ advisory.LoSafeFor encounter rp hp rv alo do
    let replace ← choose Bool
    if replace then
      advisory ← choose Advisory
      ensure (advisory.LoSafeFor encounter rp hp rv alo)
    let a ← choose ℝ
    let (r, h, v) ← lowerStep rp hp rv alo a encounter advisory
    encounter := { r, h, v }
  return { encounter, advisory }

theorem immediateResponseProg_eq
    (rp hp rv alo : ℝ) (encounter : Encounter) (advisory : Advisory) :
    ACASX.immediateResponseProg rp hp rv alo encounter advisory =
      immediateResponseProgAnnotated rp hp rv alo encounter advisory := rfl

def delayedResponseProgAnnotated (rp hp rv alo ad δ ε : ℝ)
    (encounter : Encounter) (advisory : Advisory) (d : ℝ) : SetM DelayedResult
    requires 0 < alo ∧ advisory.DelayedSafeFor encounter rp hp rv alo ad d
    ensures res => res.advisory.DelayedSafeFor res.encounter rp hp rv alo ad res.d
    := do
  let mut (encounter, advisory, d) := (encounter, advisory, d)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ advisory.DelayedSafeFor encounter rp hp rv alo ad d do
    let replace ← choose Bool
    if replace then
      advisory ← choose Advisory
      d ← chooseFrom {δ, δ + ε}
      ensure (advisory.DelayedSafeFor encounter rp hp rv alo ad d)
    let a ← choose ℝ
    unless -ad ≤ advisory.direction.sign * a do abort
    let (r, h, v, nextDelay, _) ← delayedStep rp hp rv alo ad ε a encounter advisory d
    encounter := { r, h, v }
    d := nextDelay
  return { encounter, advisory, d }

theorem delayedResponseProg_eq (rp hp rv alo ad δ ε : ℝ)
    (encounter : Encounter) (advisory : Advisory) (d : ℝ) :
    ACASX.delayedResponseProg rp hp rv alo ad δ ε encounter advisory d =
      delayedResponseProgAnnotated rp hp rv alo ad δ ε encounter advisory d := rfl

def twoSidedResponseProgAnnotated (rp hp rv alo aup : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) : SetM TwoSidedResult
    requires 0 < alo ∧ 0 < aup ∧ advisory.SafeFor encounter rp hp rv alo aup
    ensures res => res.advisory.SafeFor res.encounter rp hp rv alo aup
    := do
  let mut (encounter, advisory) := (encounter, advisory)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ advisory.SafeFor encounter rp hp rv alo aup do
    let replace ← choose Bool
    if replace then
      advisory ← choose TwoSidedAdvisory
      ensure (advisory.SafeFor encounter rp hp rv alo aup)
    let a ← choose ℝ
    let (r, h, v) ← twoSidedStep rp hp rv alo aup a encounter advisory
    encounter := { r, h, v }
  return { encounter, advisory }

theorem twoSidedResponseProg_eq (rp hp rv alo aup : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) :
    ACASX.twoSidedResponseProg rp hp rv alo aup encounter advisory =
      twoSidedResponseProgAnnotated rp hp rv alo aup encounter advisory := rfl

end Controller

namespace Controller

@[simp] theorem horizon_includes_zero (limit : TimeHorizon) : limit.includes 0 0 := by
  cases limit with
  | unlimited => trivial
  | bounded duration => simpa [TimeHorizon.includes] using duration.property

def boundedResponseProgAnnotated (rp hp rv alo aup : ℝ) (limit : TimeHorizon)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult
    requires 0 < alo ∧ 0 < aup ∧ limit.includes 0 t ∧
      advisory.SafeForWithin encounter rp hp rv alo aup limit t
    ensures res => limit.includes 0 res.t ∧
      res.advisory.SafeForWithin res.encounter rp hp rv alo aup limit res.t
    := do
  let mut (encounter, advisory, t) := (encounter, advisory, t)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ limit.includes 0 t ∧
        advisory.SafeForWithin encounter rp hp rv alo aup limit t do
    advisory ← choose TwoSidedAdvisory
    ensure (advisory.SafeForWithin encounter rp hp rv alo aup limit 0)
    t := 0
    let m ← choose ℕ
    for _ in [:m]
        invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ limit.includes 0 t ∧
          advisory.SafeForWithin encounter rp hp rv alo aup limit t do
      let a ← choose ℝ
      let (r, h, v, newTime) ← boundedStep rp hp rv alo aup limit a encounter advisory t
      encounter := { r, h, v }
      t := newTime
  return { encounter, advisory, t }
where finally
  | spec => all_goals simp_all only [horizon_includes_zero, true_and]

theorem boundedResponseProg_eq (rp hp rv alo aup : ℝ) (limit : TimeHorizon)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) :
    ACASX.boundedResponseProg rp hp rv alo aup limit encounter advisory t =
      boundedResponseProgAnnotated rp hp rv alo aup limit encounter advisory t := rfl

def safeableResponseProgAnnotated (rp hp rv alo aup : ℝ) (duration : Duration) (vloEx vupEx : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult
    requires 0 < alo ∧ 0 < aup ∧ t ≤ duration.val ∧
      advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx
    ensures res => res.t ≤ duration.val ∧
      res.advisory.SafeableFor res.encounter rp hp rv alo aup duration res.t vloEx vupEx
    := do
  let mut (encounter, advisory, t) := (encounter, advisory, t)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ t ≤ duration.val ∧
        advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx do
    advisory ← choose TwoSidedAdvisory
    ensure (advisory.SafeableFor encounter rp hp rv alo aup duration 0 vloEx vupEx)
    t := 0
    let m ← choose ℕ
    for _ in [:m]
        invariant _pref _suff => 0 < alo ∧ 0 < aup ∧ t ≤ duration.val ∧
          advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx do
      let a ← choose ℝ
      let (r, h, v, newTime) ← safeableStep rp hp rv alo aup duration vloEx vupEx a
        encounter advisory t
      encounter := { r, h, v }
      t := newTime
  return { encounter, advisory, t }

theorem safeableResponseProg_eq (rp hp rv alo aup : ℝ) (duration : Duration) (vloEx vupEx : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) :
    ACASX.safeableResponseProg rp hp rv alo aup duration vloEx vupEx encounter advisory t =
      safeableResponseProgAnnotated rp hp rv alo aup duration vloEx vupEx
        encounter advisory t := rfl

end Controller

open Representation Controller

/--
Immediate response avoids a near mid-air collision and preserves the lower safe
region, assuming the initial encounter is safe and the parameter bounds hold.
See Theorem 1.
-/
theorem immediate_safe :
    ∀ (rp hp rv alo : ℝ) (encounter : Encounter) (advisory : Advisory),
      Bounds rp hp rv alo →
        advisory.LoSafeFor encounter rp hp rv alo →
          ∀ res ∈ SetM.run (immediateResponseProg rp hp rv alo encounter advisory),
            NoNMAC rp hp res.encounter ∧
            res.advisory.LoSafeFor res.encounter rp hp rv alo  := by
  intro rp hp rv alo encounter advisory hb hs res hrun
  rw [immediateResponseProg_eq] at hrun
  have hs' := (immediateResponseProgAnnotated.spec rp hp rv alo encounter advisory).le_wp
    ⟨hb.2.2.2, hs⟩ res hrun
  exact ⟨Scalar.lower_implies_noNMAC rp hp rv alo _ _ _ _ _
    hb.2.2.2 (direction_valid _) ((loSafeFor_iff ..).mp hs'), hs'⟩

/--
Delayed response avoids a near mid-air collision and preserves the delayed safe
region for the returned encounter, advisory, and remaining delay, under the stated bounds.
See Theorem 2.
-/
theorem delayed_safe :
    ∀ (rp hp rv alo ad δ ε : ℝ) (encounter : Encounter) (advisory : Advisory) (d : ℝ),
      Bounds rp hp rv alo → (0 ≤ ad ∧ 0 ≤ δ ∧ 0 ≤ ε) →
        advisory.DelayedSafeFor encounter rp hp rv alo ad d →
          ∀ res ∈ SetM.run (delayedResponseProg rp hp rv alo ad δ ε encounter advisory d),
            NoNMAC rp hp res.encounter ∧
            res.advisory.DelayedSafeFor res.encounter rp hp rv alo ad res.d  := by
  intro rp hp rv alo ad δ ε encounter advisory d hb _ hs res hrun
  rw [delayedResponseProg_eq] at hrun
  have hs' := (delayedResponseProgAnnotated.spec rp hp rv alo ad δ ε encounter advisory d).le_wp
    ⟨hb.2.2.2, hs⟩ res hrun
  exact ⟨Scalar.delayed_noNMAC rp hp rv alo ad _ _ _ _ _ _
    hb.2.2.2 (direction_valid _) ((delayedSafeFor_iff ..).mp hs'), hs'⟩

/--
Two-sided response avoids a near mid-air collision from a safe initial encounter,
assuming the parameter bounds and `alo ≤ aup`. See Theorem 3.
-/
theorem two_sided_safe :
    ∀ (rp hp rv alo aup : ℝ) (encounter : Encounter) (advisory : TwoSidedAdvisory),
      Bounds rp hp rv alo → alo ≤ aup →
        advisory.SafeFor encounter rp hp rv alo aup →
          ∀ res ∈ SetM.run (twoSidedResponseProg rp hp rv alo aup encounter advisory),
            NoNMAC rp hp res.encounter  := by
  intro rp hp rv alo aup encounter advisory hb haup hs res hrun
  have ha := hb.2.2.2
  rw [twoSidedResponseProg_eq] at hrun
  have hs' := (twoSidedResponseProgAnnotated.spec rp hp rv alo aup encounter advisory).le_wp
    ⟨ha, ha.trans_le haup, hs⟩ res hrun
  rcases (safeFor_iff ..).mp hs' with hlo | hup
  · exact Scalar.lower_implies_noNMAC rp hp rv alo _ _ _ _ _ ha (direction_valid _) hlo
  · exact Scalar.upper_implies_noNMAC rp hp rv aup _ _ _ _ _
      (ha.trans_le haup) (direction_valid _) hup

/--
Bounded-time response avoids a near mid-air collision and preserves safety for the
remaining horizon, assuming an initially safe encounter within the horizon. See Theorem 4.
-/
theorem bounded_safe :
    ∀ (rp hp rv alo aup : ℝ) (limit : TimeHorizon) (encounter : Encounter)
      (advisory : TwoSidedAdvisory) (t : ℝ),
      Bounds rp hp rv alo ∧ 0 < aup → limit.includes 0 t →
        advisory.SafeForWithin encounter rp hp rv alo aup limit t →
          ∀ res ∈ SetM.run (boundedResponseProg rp hp rv alo aup limit encounter advisory t),
            NoNMAC rp hp res.encounter ∧ limit.includes 0 res.t ∧
            res.advisory.SafeForWithin res.encounter rp hp rv alo aup limit res.t  := by
  intro rp hp rv alo aup limit encounter advisory t hb ht hs res hrun
  rw [boundedResponseProg_eq] at hrun
  have hs' := (boundedResponseProgAnnotated.spec rp hp rv alo aup limit encounter advisory t).le_wp
    ⟨hb.1.2.2.2, hb.2, ht, hs⟩ res hrun
  refine ⟨?_, hs'⟩
  exact Scalar.bounded_region_noNMAC rp hp rv alo aup (horizonValue limit) res.t
    _ _ _ _ _ _ hb.1.2.2.2 hb.2 (direction_valid _)
    (by simpa only [sub_zero] using (includes_iff ..).mp hs'.1)
    ((safeForWithin_iff ..).mp hs'.2)

/--
Safeable response avoids a near mid-air collision and preserves the clock bound
and availability of an unlimited-time safe follow-up, under the stated assumptions.
See Theorem 5.
-/
theorem safeable_safe :
    ∀ (rp hp rv alo aup : ℝ) (duration : Duration) (vloEx vupEx : ℝ)
      (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ),
      Bounds rp hp rv alo → alo ≤ aup → t ≤ duration.val →
        advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx →
          ∀ res ∈ SetM.run (safeableResponseProg
              rp hp rv alo aup duration vloEx vupEx encounter advisory t),
            NoNMAC rp hp res.encounter ∧ res.t ≤ duration.val ∧
            res.advisory.SafeableFor
              res.encounter rp hp rv alo aup duration res.t vloEx vupEx  := by
  intro rp hp rv alo aup duration vloEx vupEx encounter advisory t hb haup ht hs res hrun
  have ha := hb.2.2.2
  rw [safeableResponseProg_eq] at hrun
  have hs' := (safeableResponseProgAnnotated.spec rp hp rv alo aup duration vloEx vupEx
    encounter advisory t).le_wp ⟨ha, ha.trans_le haup, ht, hs⟩ res hrun
  refine ⟨?_, hs'⟩
  exact Scalar.safeable_region_noNMAC rp hp rv alo aup duration.val res.t vloEx vupEx
    _ _ _ _ _ _ ha (ha.trans_le haup) (direction_valid _) (Or.inl hs'.1)
    ((safeableFor_iff ..).mp hs'.2)

end ACASX
