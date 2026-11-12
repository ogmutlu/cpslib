import CPSLib.Examples.FM11.Model
import CPSLib.Tactic.OdeDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open CPSLib
open Std.WP
set_option experimental.vcgen true
set_option experimental.intrinsic true
namespace FM11

theorem behind_refl (b B : ℝ) (x v : Car → ℝ) (i : Car) : i.IsBehind i b B x v := by
  simp [Car.IsBehind]

/-- The algebraic transitivity used in FM11 Appendix A.2, Lemma 2. -/
theorem behind_trans (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (i j k : Car)
    (hij : i.IsBehind j b B x v) (hjk : j.IsBehind k b B x v) :
    i.IsBehind k b B x v := by
  by_cases heq : i = j
  · simpa [heq] using hjk
  · by_cases heq' : j = k
    · simpa [← heq'] using hij
    · have hstop := div_le_div_of_nonneg_left (sq_nonneg (v j))
        (show 0 < 2 * b by positivity) (show 2 * b ≤ 2 * B by linarith)
      rcases hij.2 heq with ⟨hxij, hsij, hvi, hvj⟩
      grind

/-- A trajectory cannot cross zero if its derivative points strictly inward there. -/
theorem no_cross (T : ℝ) (hT : 0 ≤ T) (f f' : ℝ → ℝ)
    (hd : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (f' t) (Set.Icc 0 T) t)
    (h0 : f 0 < 0) (hin : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t → f' t < 0) : f T < 0 := by
  have hc : ContinuousOn f (Set.Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hc
  by_contra hbad
  have hft : 0 ≤ f t := (not_lt.mp hbad).trans (hm ⟨hT, le_rfl⟩)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
  have hcone : (0 : ℝ) - t ∈ posTangentConeAt (Set.Icc 0 T) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) T).segment_subset ht ⟨le_rfl, hT⟩)
  have hsign := hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
    (hd t ht).hasFDerivWithinAt hcone
  have hmul : -t * f' t ≤ 0 := by simpa using hsign
  nlinarith [hin t ht hft]

@[simp] def stoppingMargin (b B : ℝ) (f l : Car) : xva × ℝ → ℝ
  | ((x, v, _), _) => 2 * b * B * (x l - x f) + b * v l ^ 2 - B * v f ^ 2

@[simp] def responseMargin (A b B ε : ℝ) (f l : Car) : xva × ℝ → ℝ
  | ((x, v, a), t) => stoppingMargin b B f l ((x, v, a), t) -
      B * (A + b) * (A * (ε - t) ^ 2 + 2 * (ε - t) * v f)

theorem stoppingMargin_hasPrime (cars : Finset Car) (b B : ℝ) (f l : Car)
    (hf : f ∈ cars) (hl : l ∈ cars) (D : xva × ℝ → Prop) :
    HasPrime (Evolvable.denotation (motion cars, time)) D
      (stoppingMargin b B f l)
      (fun ((_, v, a), _) => 2 * b * v l * (B + a l) - 2 * B * v f * (b + a f)) := by
  ode_deriv [stoppingMargin, motion, time]

theorem responseMargin_hasPrime (cars : Finset Car) (A b B ε : ℝ) (f l : Car)
    (hf : f ∈ cars) (hl : l ∈ cars) (D : xva × ℝ → Prop) :
    HasPrime (Evolvable.denotation (motion cars, time)) D
      (responseMargin A b B ε f l)
      (fun ((_, v, a), t) => 2 * b * v l * (B + a l) +
        2 * B * (A - a f) * (v f + (A + b) * (ε - t))) := by
  ode_deriv [responseMargin, stoppingMargin, motion, time]

/-- Accelerations are constant during each continuous phase. -/
theorem acceleration_preserved (cars : Finset Car) (ε value : ℝ) (i : Car) (hi : i ∈ cars) :
    (fun ((_, _, a), _) => a i = value)
    [[evolve (motion cars, time) (domain ε cars)]]
    (fun ((_, _, a), _) => a i = value) := by
  have hinvariant := dIeq (ode := (motion cars, time)) (domain := domain ε cars)
    (pre := fun ((_, _, a), _) => a i = value)
    (fun ((_, _, a), _) => a i - value) (fun _ => 0)
    (by ode_deriv [motion, time]) (fun _ h => sub_eq_zero.mpr h) (fun _ _ => rfl)
  simpa only [sub_eq_zero] using hinvariant

/-- Braking cannot decrease the stopping-distance margin (Appendix A.1). -/
theorem braking_margin_preserved (cars : Finset Car) (ε b B : ℝ)
    (hb : 0 < b) (hB : 0 < B) (f l : Car) (hf : f ∈ cars) (hl : l ∈ cars) :
    (fun st => 0 < stoppingMargin b B f l st)
    [[evolve (motion cars, time)
      (fun st => let ((_, _, a), _) := st; domain ε cars st ∧ -B ≤ a l ∧ a f ≤ -b)]]
    (fun st => 0 < stoppingMargin b B f l st) := by
  apply dIgt (stoppingMargin b B f l)
    (fun ((_, v, a), _) => 2 * b * v l * (B + a l) - 2 * B * v f * (b + a f))
  · exact stoppingMargin_hasPrime cars b B f l hf hl _
  · exact fun _ h => h
  · intro ((x, v, a), t) h
    have hlead : 0 ≤ 2 * b * v l * (B + a l) :=
      mul_nonneg (mul_nonneg (by positivity) (h.1.1 l hl)) (by linarith [h.2.1])
    have hfollow : 2 * B * v f * (b + a f) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (h.1.1 f hf))
        (by linarith [h.2.2])
    exact sub_nonneg.mpr (hfollow.trans hlead)

/-- The response-time reserve makes every permitted acceleration safe until ε. -/
theorem response_margin_preserved (cars : Finset Car) (A b B ε : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (hf : f ∈ cars) (hl : l ∈ cars) :
    (fun st => 0 < responseMargin A b B ε f l st)
    [[evolve (motion cars, time)
      (fun st => let ((_, _, a), _) := st; domain ε cars st ∧ -B ≤ a l ∧ a f ≤ A)]]
    (fun st => 0 < responseMargin A b B ε f l st) := by
  apply dIgt (responseMargin A b B ε f l)
    (fun ((_, v, a), t) => 2 * b * v l * (B + a l) +
      2 * B * (A - a f) * (v f + (A + b) * (ε - t)))
  · exact responseMargin_hasPrime cars A b B ε f l hf hl _
  · exact fun _ h => h
  · intro ((x, v, a), t) h
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (h.1.1 l hl)) (by linarith [h.2.1]))
      (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h.2.2))
        (add_nonneg (h.1.1 f hf)
          (mul_nonneg (by positivity) (sub_nonneg.mpr h.1.2))))

/-- Positive stopping margin rules out crossing, including at the evolution endpoint. -/
theorem order_preserved (cars : Finset Car) (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (f l : Car) (hf : f ∈ cars) (hl : l ∈ cars) (D : xva × ℝ → Prop)
    (hD : ∀ st, D st → let ((_, v, _), _) := st;
      0 ≤ v f ∧ 0 ≤ v l ∧ 0 < stoppingMargin b B f l st) :
    (fun ((x, _, _), _) => x f < x l)
    [[evolve (motion cars, time) D]] (fun ((x, _, _), _) => x f < x l) := by
  intro initial hinit
  unfold evolve
  apply Triple.iff.mp (evolveSemantic_spec
    (Q := fun ((x, _, _), _) => x f < x l)
    (Evolvable.denotation (motion cars, time)) D initial)
  intro duration hduration path hevo
  have hp : HasPrime (Evolvable.denotation (motion cars, time)) D
      (fun ((x, _, _), _) => x f - x l) (fun ((_, v, _), _) => v f - v l) := by
    ode_deriv [motion, time]
  apply sub_neg.mp
  apply no_cross duration hduration _ _ (hp path _ hevo.2.2 hevo.2.1)
  · simpa only [hevo.1, sub_neg] using hinit
  · intro t ht hgap
    rcases hD (path t) (hevo.2.1 t ht) with ⟨hvf, hvl, hmargin⟩
    rcases hstate : path t with ⟨⟨xt, vt, a_t⟩, tt⟩
    simp only [hstate] at hvf hvl hmargin hgap ⊢
    by_contra hbad
    have hsq : vt l ^ 2 ≤ vt f ^ 2 := by
      nlinarith
    change 0 < 2 * b * B * (xt l - xt f) + b * vt l ^ 2 - B * vt f ^ 2 at hmargin
    have hdist := mul_nonneg
      (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hb.le)
        (hb.le.trans hbB)) hgap
    nlinarith [mul_nonneg (sub_nonneg.mpr hbB) (sq_nonneg (vt f)),
      mul_nonneg hb.le (sub_nonneg.mpr hsq)]

theorem stoppingMargin_pos_iff (b B : ℝ) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (st : xva × ℝ) :
    0 < stoppingMargin b B f l st ↔
      (let ((x, v, _), _) := st
       x f + v f ^ 2 / (2 * b) < x l + v l ^ 2 / (2 * B)) := by
  rcases st with ⟨⟨x, v, a⟩, t⟩
  have heq : stoppingMargin b B f l ((x, v, a), t) = 2 * b * B *
      (x l + v l ^ 2 / (2 * B) - (x f + v f ^ 2 / (2 * b))) := by
    dsimp [stoppingMargin]
    field_simp
    ring
  rw [heq, mul_pos_iff_of_pos_left (show 0 < 2 * b * B by positivity), sub_pos]

/-- Contract for the leader's nondeterministic acceleration assignment. -/
def l_ctrl' (A B : ℝ) (l : Car) (a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => -B ≤ a_res l ∧ a_res l ≤ A ∧
      ∀ i, i ≠ l → a_res i = a i
    := do
  let al ← choose ℝ
  unless (-B ≤ al ∧ al ≤ A) do abort
  return Function.update a l al

@[spec] theorem choice_spec {α : Type} (p q : SetM α) (Q : α → Prop) :
    ⦃wp p Q estack⟨⟩ ∧ wp q Q estack⟨⟩⦄ p <|> q ⦃Q⦄ := by
  exact ⟨fun h => SetM.wp_orElse p q h.1 h.2⟩

@[reducible] def FollowerChoice (A b B ε : ℝ) (f l : Car)
    (x v : Car → ℝ) (af : ℝ) : Prop :=
  (-B ≤ af ∧ af ≤ -b) ∨
  (Safe_ε A b B ε x v f l ∧ -B ≤ af ∧ af ≤ A) ∨
  (v f = 0 ∧ af = 0)

/-- The three follower choices, with their exact acceleration and frame contract. -/
def f_ctrl' (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => FollowerChoice A b B ε f l x v (a_res f) ∧
      ∀ i, i ≠ f → a_res i = a i
    :=
  (do
    let af ← choose ℝ
    unless (-B ≤ af ∧ af ≤ -b) do abort
    return Function.update a f af)
    <|>
  (do
    unless Safe_ε A b B ε x v f l do abort
    let af ← choose ℝ
    unless (-B ≤ af ∧ af ≤ A) do abort
    return Function.update a f af)
    <|>
  (do
    unless v f = 0 do abort
    return Function.update a f 0)
where finally
  | spec =>
    constructor
    · vcgen
      simp_all
    · vcgen
      constructor
      all_goals vcgen
      all_goals simp_all

theorem acceleration_pair_preserved (cars : Finset Car) (ε : ℝ) (f l : Car)
    (hf : f ∈ cars) (hl : l ∈ cars) (P : ℝ → ℝ → Prop) :
    (fun ((_, _, a), _) => P (a f) (a l))
    [[evolve (motion cars, time) (domain ε cars)]]
    (fun ((_, _, a), _) => P (a f) (a l)) := by
  rintro ⟨⟨xi, vi, ai⟩, ti⟩ hpre ⟨⟨xf, vf, af⟩, tf⟩ hrun
  have hfrozen := acceleration_preserved cars ε (ai f) f hf ((xi, vi, ai), ti) rfl
    ((xf, vf, af), tf) hrun
  have hlfrozen := acceleration_preserved cars ε (ai l) l hl ((xi, vi, ai), ti) rfl
    ((xf, vf, af), tf) hrun
  simpa only [hfrozen, hlfrozen] using hpre

theorem behind_of_margin (b B : ℝ) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (st : xva × ℝ)
    (horder : let ((x, _, _), _) := st; x f < x l)
    (hmargin : 0 < stoppingMargin b B f l st)
    (hvf : let ((_, v, _), _) := st; 0 ≤ v f)
    (hvl : let ((_, v, _), _) := st; 0 ≤ v l) :
    let ((x, v, _), _) := st; f.IsBehind l b B x v := by
  exact ⟨horder.le, fun _ => ⟨horder,
    (stoppingMargin_pos_iff b B hb hB f l st).mp hmargin, hvf, hvl⟩⟩

/-- A positive stopping margin and the velocity domain establish local safety. -/
theorem behind_preserved_of_margin (cars : Finset Car) (b B : ℝ) (hb : 0 < b)
    (hbB : b ≤ B) (f l : Car) (hf : f ∈ cars) (hl : l ∈ cars)
    (D pre : xva × ℝ → Prop)
    (hvel : ∀ st, D st → let ((_, v, _), _) := st; 0 ≤ v f ∧ 0 ≤ v l)
    (hinit : ∀ st, pre st → let ((x, _, _), _) := st; x f < x l)
    (hmargin : pre [[evolve (motion cars, time) D]]
      (fun st => 0 < stoppingMargin b B f l st)) :
    pre [[evolve (motion cars, time) D]]
      (fun ((x, v, _), _) => f.IsBehind l b B x v) := by
  apply dC (cut := fun st => 0 < stoppingMargin b B f l st)
  · exact hmargin
  · apply dC (cut := fun ((x, _, _), _) => x f < x l)
    · intro initial hpre
      exact order_preserved cars b B hb hbB f l hf hl _
        (fun st h => ⟨(hvel st h.1).1, (hvel st h.1).2, h.2⟩)
        initial (hinit initial hpre)
    · apply dW
      intro st h
      exact behind_of_margin b B hb (hb.trans_le hbB) f l st h.2 h.1.2
        (hvel st h.1.1).1 (hvel st h.1.1).2

@[simp] def BrakingPre (b B : ℝ) (f l : Car) (st : xva × ℝ) : Prop :=
  let ((x, _, a), _) := st
  0 < stoppingMargin b B f l st ∧ x f < x l ∧ -B ≤ a l ∧ a f ≤ -b

theorem braking_phase_safe (cars : Finset Car) (ε b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (f l : Car) (hf : f ∈ cars) (hl : l ∈ cars) :
    BrakingPre b B f l [[evolve (motion cars, time) (domain ε cars)]]
      (fun ((x, v, _), _) => f.IsBehind l b B x v) := by
  apply dC (cut := fun ((_, _, a), _) => -B ≤ a l ∧ a f ≤ -b)
  · intro initial hpre
    exact acceleration_pair_preserved cars ε f l hf hl
      (fun af al => -B ≤ al ∧ af ≤ -b) initial hpre.2.2
  · apply behind_preserved_of_margin cars b B hb hbB f l hf hl _ _
    · exact fun st h => ⟨h.1.1 f hf, h.1.1 l hl⟩
    · exact fun _ h => h.2.1
    · intro initial hpre
      exact braking_margin_preserved cars ε b B hb (hb.trans_le hbB) f l hf hl
        initial hpre.1

theorem responseMargin_le_stoppingMargin (cars : Finset Car) (A b B ε : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hB : 0 < B) (f l : Car) (hf : f ∈ cars)
    (st : xva × ℝ) (h : domain ε cars st) :
    responseMargin A b B ε f l st ≤ stoppingMargin b B f l st := by
  rcases st with ⟨⟨x, v, a⟩, t⟩
  have hremaining : 0 ≤ ε - t := sub_nonneg.mpr h.2
  have hvf : 0 ≤ v f := h.1 f hf
  have hreserve : 0 ≤ B * (A + b) * (A * (ε - t) ^ 2 + 2 * (ε - t) * v f) := by
    positivity
  exact sub_le_self _ hreserve

@[simp] def ResponsePre (A b B ε : ℝ) (f l : Car) (st : xva × ℝ) : Prop :=
  let ((x, _, a), _) := st
  0 < responseMargin A b B ε f l st ∧ x f < x l ∧ -B ≤ a l ∧ a f ≤ A

theorem response_phase_safe (cars : Finset Car) (A b B ε : ℝ)
    (hA : 0 ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (f l : Car) (hf : f ∈ cars) (hl : l ∈ cars) :
    ResponsePre A b B ε f l [[evolve (motion cars, time) (domain ε cars)]]
      (fun ((x, v, _), _) => f.IsBehind l b B x v) := by
  apply dC (cut := fun ((_, _, a), _) => -B ≤ a l ∧ a f ≤ A)
  · intro initial hpre
    exact acceleration_pair_preserved cars ε f l hf hl
      (fun af al => -B ≤ al ∧ af ≤ A) initial hpre.2.2
  · apply behind_preserved_of_margin cars b B hb hbB f l hf hl _ _
    · exact fun st h => ⟨h.1.1 f hf, h.1.1 l hl⟩
    · exact fun _ h => h.2.1
    · intro initial hpre final hrun
      have hresponse := response_margin_preserved cars A b B ε hA hb (hb.trans_le hbB)
        f l hf hl initial hpre.1 final hrun
      have hdomain := SemanticODE.evolveSemantic_domain_at_end
        (Evolvable.denotation (motion cars, time)) _ hrun
      exact hresponse.trans_le
        (responseMargin_le_stoppingMargin cars A b B ε hA hb (hb.trans_le hbB) f l hf
          final hdomain.1)

theorem responseMargin_initial_pos_iff (A b B ε : ℝ) (hb : 0 < b) (hB : 0 < B)
    (f l : Car) (x v a : Car → ℝ) :
    0 < responseMargin A b B ε f l ((x, v, a), 0) ↔ Safe_ε A b B ε x v f l := by
  have heq : responseMargin A b B ε f l ((x, v, a), 0) = 2 * b * B *
      ((x l + v l ^ 2 / (2 * B)) -
        (x f + v f ^ 2 / (2 * b) + (A / b + 1) * (A / 2 * ε ^ 2 + ε * v f))) := by
    dsimp [responseMargin, stoppingMargin]
    field_simp
    ring
  rw [heq, mul_pos_iff_of_pos_left (show 0 < 2 * b * B by positivity), sub_pos]

@[spec] theorem dyn_local_spec (cars : Finset Car) (A b B ε : ℝ) (f l : Car)
    (hf : f ∈ cars) (hl : l ∈ cars) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ f.IsBehind l b B x v ∧
      -B ≤ a l ∧ FollowerChoice A b B ε f l x v (a f)⦄
    dyn ε cars x v a
    ⦃fun (x_res, v_res, _) => f.IsBehind l b B x_res v_res⦄ := by
  constructor
  intro h
  unfold dyn
  vcgen (errorOnMissingSpec := false)
  simp only [SetM.wp_pure, binderNameHint]
  by_cases heq : f = l
  · intro final _
    simp [heq]
  · rcases h with ⟨⟨hA, hb, hbB, hε⟩, hbehind, hal, hchoice⟩
    have hmargin := (stoppingMargin_pos_iff b B hb (hb.trans_le hbB) f l
      ((x, v, a), 0)).mpr (hbehind.2 heq).2.1
    rcases hchoice with hbrake | hsafe | hstop
    · exact braking_phase_safe cars ε b B hb hbB f l hf hl ((x, v, a), 0)
        ⟨hmargin, (hbehind.2 heq).1, hal, hbrake.2⟩
    · exact response_phase_safe cars A b B ε hA hb hbB f l hf hl ((x, v, a), 0)
        ⟨(responseMargin_initial_pos_iff A b B ε hb (hb.trans_le hbB) f l x v a).mpr
          hsafe.1, (hbehind.2 heq).1, hal, hsafe.2.2⟩
    · exact response_phase_safe cars 0 b B ε (by norm_num) hb hbB f l hf hl
        ((x, v, a), 0)
        ⟨by simpa [responseMargin, hstop.1] using hmargin,
          (hbehind.2 heq).1, hal, by simp [hstop.2]⟩

def dyn_llc (_A _b _B ε : ℝ) (f l : Car) (x v a : Car → ℝ) :=
  dyn ε {f, l} x v a

@[spec] theorem dyn_llc_spec (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ f.IsBehind l b B x v ∧
      -B ≤ a l ∧ FollowerChoice A b B ε f l x v (a f)⦄
    dyn_llc A b B ε f l x v a
    ⦃fun (x_res, v_res, _) => f.IsBehind l b B x_res v_res⦄ := by
  exact dyn_local_spec {f, l} A b B ε f l (by simp) (by simp) x v a

def llc' (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM LaneResult
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ f.IsBehind l b B x v
    ensures res => f.IsBehind l b B res.x res.v
    := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ f.IsBehind l b B x v do
    a ← l_ctrl' A B l a
    a ← f_ctrl' A b B ε f l x v a
    (x, v, a) ← dyn_llc A b B ε f l x v a
  return { x, v }

theorem llc_eq (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) :
    llc A b B ε f l x v a = llc' A b B ε f l x v a := rfl

/-- FM11 Proposition 1, using the local invariant from Appendix A.1. -/
theorem llc_safe :
    ∀ A b B ε f l x v a,
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → f.IsBehind l b B x v →
        ∀ res ∈ SetM.run (llc A b B ε f l x v a),
          f.IsBehind l b B res.x res.v := by
  intro A b B ε f l x v a hp hbehind res hrun
  rw [llc_eq] at hrun
  exact (llc'.spec A b B ε f l x v a).le_wp ⟨hp, hbehind⟩ res hrun

theorem laneSafe_pairwise (cars : Finset Car) (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (hsafe : LaneSafe cars b B x v) :
    ∀ i ∈ cars, ∀ l ∈ cars, x i ≤ x l → i.IsBehind l b B x v := by
  classical
  intro i
  induction i using
      (measure (fun i : Car => (cars.filter (fun k => x i < x k)).card)).wf.induction with
  | h i ih =>
    intro hi l hl hil
    by_cases heq : i = l
    · simpa [heq] using behind_refl b B x v l
    · have hil' : x i < x l := lt_of_le_of_ne hil (hsafe.2.1 i hi l hl heq)
      obtain ⟨j, hj, hmin⟩ := (cars.filter (fun k => x i < x k)).exists_min_image x
        ⟨l, Finset.mem_filter.mpr ⟨hl, hil'⟩⟩
      simp only [Finset.mem_filter] at hj hmin
      have hleader : j.IsLeaderOf i cars x := by
        apply And.intro hi
        apply And.intro hj.1
        apply And.intro hj.2
        intro k hk hneq
        by_cases hki : x k < x i
        · exact Or.inl hki
        · have hik : x i < x k := lt_of_le_of_ne (le_of_not_gt hki)
            (hsafe.2.1 i hi k hk hneq.1.symm)
          exact Or.inr (lt_of_le_of_ne (hmin k ⟨hk, hik⟩)
            (hsafe.2.1 j hj.1 k hk hneq.2.symm))
      have hsub : cars.filter (fun k => x j < x k) ⊆ cars.filter (fun k => x i < x k) := by
        intro k hk
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hk).1, hj.2.trans (Finset.mem_filter.mp hk).2⟩
      have hrank : (cars.filter (fun k => x j < x k)).card <
          (cars.filter (fun k => x i < x k)).card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
          ⟨j, Finset.mem_filter.mpr hj, by simp⟩)
      exact behind_trans b B hb hbB x v i j l (hsafe.2.2 i hi j hj.1 hleader)
        (ih j hrank hj.1 l hl (hmin l ⟨hl, hil'⟩))

def leaders' (cars : Finset Car) (x : Car → ℝ) (i : Car) : SetM Car
    requires i ∈ cars
    ensures k => k ∈ cars ∧ x i ≤ x k
    := do
  let mut k := i
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => k ∈ cars ∧ x i ≤ x k do
    let l ← chooseFrom {l | l.IsLeaderOf k cars x}
    k := l
  return k
where finally
  | spec => all_goals simp_all [SetM.run]; all_goals grind

theorem laneSafe_star (cars : Finset Car) (b B : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (hsafe : LaneSafe cars b B x v) :
    ∀ i ∈ cars, i.IsBehindLStar cars b B x v := by
  intro i hi k hk
  have hpath := (leaders'.spec cars x i).le_wp hi k hk
  exact laneSafe_pairwise cars b B hb hbB x v hsafe i hi k hpath.1 hpath.2

theorem safe_ahead (cars : Finset Car) (A b B ε : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (x v : Car → ℝ) (hsafe : LaneSafe cars b B x v) (f k l : Car)
    (hk : k.IsLeaderOf f cars x) (hl : l ∈ cars) (hfl : x f < x l)
    (hguard : Safe_ε A b B ε x v f k) : Safe_ε A b B ε x v f l := by
  have hkl : x k ≤ x l := by grind
  have hbehind := laneSafe_pairwise cars b B hb hbB x v hsafe k hk.2.1 l hl hkl
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (v k))
    (show 0 < 2 * b by positivity) (show 2 * b ≤ 2 * B by linarith)
  by_cases heq : k = l
  · simpa [heq] using hguard
  · have hstop := (hbehind.2 heq).2.1
    dsimp [Safe_ε] at *
    linarith

@[reducible] def CarChoice (A b B ε : ℝ) (cars : Finset Car) (i : Car)
    (x v : Car → ℝ) (ai : ℝ) : Prop :=
  (-B ≤ ai ∧ ai ≤ -b) ∨
  (∃ l ∈ cars, l.IsLeaderOf i cars x ∧ Safe_ε A b B ε x v i l ∧ -B ≤ ai ∧ ai ≤ A) ∨
  (v i = 0 ∧ ai = 0)

def ctrl_i' (A b B ε : ℝ) (cars : Finset Car) (i : Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => CarChoice A b B ε cars i x v (a_res i)
    :=
  (do
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ -b) do abort
    return Function.update a i ai)
    <|>
  (do
    let l ← chooseFrom {l | l.IsLeaderOf i cars x}
    unless Safe_ε A b B ε x v i l do abort
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ A) do abort
    return Function.update a i ai)
    <|>
  (do
    unless v i = 0 do abort
    return Function.update a i 0)
where finally
  | spec =>
    constructor
    · vcgen
      simp_all
    · vcgen
      constructor
      all_goals vcgen
      all_goals simp_all [SetM.run]
      all_goals grind

theorem ctrl_i_eq (A b B ε : ℝ) (cars : Finset Car) (i : Car) (x v a : Car → ℝ) :
    ctrl_i A b B ε cars i x v a = ctrl_i' A b B ε cars i x v a := rfl

theorem carChoice_bounds (A b B ε : ℝ) (cars : Finset Car) (i : Car)
    (x v : Car → ℝ) (ai : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (hchoice : CarChoice A b B ε cars i x v ai) : -B ≤ ai ∧ ai ≤ A := by
  grind

theorem carChoice_follower (A b B ε : ℝ) (cars : Finset Car) (f l : Car)
    (x v : Car → ℝ) (af : ℝ) (hb : 0 < b) (hbB : b ≤ B)
    (hsafe : LaneSafe cars b B x v) (hl : l ∈ cars) (hfl : x f < x l)
    (hchoice : CarChoice A b B ε cars f x v af) : FollowerChoice A b B ε f l x v af := by
  rcases hchoice with hbrake | ⟨k, hk, hleader, hguard, hbounds⟩ | hstop
  · exact Or.inl hbrake
  · exact Or.inr (Or.inl
      ⟨safe_ahead cars A b B ε hb hbB x v hsafe f k l hleader hl hfl hguard, hbounds⟩)
  · exact Or.inr (Or.inr hstop)

def ctrl_n' (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => ∀ i ∈ cars, CarChoice A b B ε cars i x v (a_res i)
    := do
  let mut a_res := a
  for i in cars.toList
      invariant pref _suff => ∀ j ∈ pref, CarChoice A b B ε cars j x v (a_res j) do
    let ai ← ctrl_i' A b B ε cars i x v a
    a_res := Function.update a_res i (ai i)
  return a_res
where finally
  | spec => all_goals simp_all

theorem dyn_nonnegative (cars : Finset Car) (ε : ℝ) (x v a : Car → ℝ) :
    ⦃True⦄ dyn ε cars x v a ⦃fun (_, v_res, _) => ∀ i ∈ cars, 0 ≤ v_res i⦄ := by
  constructor
  intro _
  unfold dyn
  vcgen (errorOnMissingSpec := false)
  simp only [SetM.wp_pure, binderNameHint]
  apply dW (pre := fun _ => True)
  · intro st h
    exact h.1
  · trivial

theorem dyn_laneSafe (active cars : Finset Car) (hsub : cars ⊆ active)
    (A b B ε : ℝ) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v ∧
      (∀ i ∈ cars, CarChoice A b B ε cars i x v (a i))⦄
    dyn ε active x v a
    ⦃fun (x_res, v_res, _) => LaneSafe cars b B x_res v_res⦄ := by
  apply Triple.iff.mpr
  rintro ⟨hp, hsafe, hchoice⟩ ⟨xr, vr, ar⟩ hrun
  rcases hp with ⟨hA, hb, hbB, hε⟩
  have hpairs : ∀ i ∈ cars, ∀ j ∈ cars, x i < x j → i.IsBehind j b B xr vr := by
    intro i hi j hj hij
    exact (dyn_local_spec active A b B ε i j (hsub hi) (hsub hj) x v a).le_wp
      ⟨⟨hA, hb, hbB, hε⟩, laneSafe_pairwise cars b B hb hbB x v hsafe i hi j hj hij.le,
        (carChoice_bounds A b B ε cars j x v (a j) hA hb hbB (hchoice j hj)).1,
        carChoice_follower A b B ε cars i j x v (a i) hb hbB hsafe hj hij
          (hchoice i hi)⟩ (xr, vr, ar) hrun
  have hordered : ∀ i ∈ cars, ∀ j ∈ cars, i ≠ j →
      i.IsBehind j b B xr vr ∨ j.IsBehind i b B xr vr := by
    intro i hi j hj hneq
    rcases lt_or_gt_of_ne (hsafe.2.1 i hi j hj hneq) with hij | hji
    · exact Or.inl (hpairs i hi j hj hij)
    · exact Or.inr (hpairs j hj i hi hji)
  apply And.intro (fun i hi =>
    (dyn_nonnegative active ε x v a).le_wp trivial (xr, vr, ar) hrun i (hsub hi))
  apply And.intro
  · intro i hi j hj hneq
    rcases hordered i hi j hj hneq with hij | hji
    · exact ne_of_lt (hij.2 hneq).1
    · exact ne_of_gt (hji.2 hneq.symm).1
  · intro i hi j hj hleader
    have hneq : i ≠ j := by grind
    rcases hordered i hi j hj hneq with hij | hji
    · exact hij
    · have hji' := (hji.2 hneq.symm).1
      grind

def dyn_glc (_A _b _B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) := dyn ε cars x v a

@[spec] theorem dyn_glc_spec (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v ∧
      (∀ i ∈ cars, CarChoice A b B ε cars i x v (a i))⦄
    dyn_glc A b B ε cars x v a
    ⦃fun (x_res, v_res, _) => LaneSafe cars b B x_res v_res⦄ :=
  dyn_laneSafe cars cars (fun _ hi => hi) A b B ε x v a

def glc' (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) : SetM LaneResult
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v
    ensures res => LaneSafe cars b B res.x res.v
    := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff =>
        (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v do
    a ← ctrl_n' A b B ε cars x v a
    (x, v, a) ← dyn_glc A b B ε cars x v a
  return { x, v }

theorem glc_eq (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) :
    glc A b B ε cars x v a = glc' A b B ε cars x v a := rfl

/-- FM11 Proposition 2: local safety lifts through the finite leader chain. -/
theorem glc_safe :
    ∀ A b B ε x v a (cars : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe cars b B x v →
        ∀ res ∈ SetM.run (glc A b B ε cars x v a),
          LaneSafe cars b B res.x res.v ∧
            (∀ i ∈ cars, i.IsBehindLStar cars b B res.x res.v) := by
  intro A b B ε x v a cars hp hsafe res hrun
  rw [glc_eq] at hrun
  have hfinal := (glc'.spec A b B ε cars x v a).le_wp ⟨hp, hsafe⟩ res hrun
  exact ⟨hfinal, laneSafe_star cars b B hp.2.1 hp.2.2.1 res.x res.v hfinal⟩

theorem laneSafe_subset (cars D : Finset Car) (hsub : D ⊆ cars) (b B : ℝ)
    (hb : 0 < b) (hbB : b ≤ B) (x v : Car → ℝ) (hsafe : LaneSafe cars b B x v) :
    LaneSafe D b B x v := by
  apply And.intro (fun i hi => hsafe.1 i (hsub hi))
  apply And.intro
  · exact fun i hi j hj hneq => hsafe.2.1 i (hsub hi) j (hsub hj) hneq
  · intro i hi j hj hleader
    exact laneSafe_pairwise cars b B hb hbB x v hsafe i (hsub hi) j (hsub hj)
      hleader.2.2.1.le

theorem laneSafe_insert (cars : Finset Car) (n : Car) (b B : ℝ)
    (hb : 0 < b) (hbB : b ≤ B) (x v : Car → ℝ) (hsafe : LaneSafe cars b B x v)
    (hv : 0 ≤ v n) (hx : ∀ j ∈ cars, x n ≠ x j)
    (hfollow : n.IsAheadItsFollower (insert n cars) b B x v)
    (hlead : n.IsBehindItsLeader (insert n cars) b B x v) : LaneSafe (insert n cars) b B x v := by
  have hpairs := laneSafe_pairwise cars b B hb hbB x v hsafe
  apply And.intro
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hv
    · exact hsafe.1 i hi
  apply And.intro
  · intro i hi j hj hneq
    simp only [Finset.mem_insert] at hi hj
    grind
  · intro i hi j hj hleader
    by_cases hin : i = n
    · subst i
      exact hlead j hj hleader
    by_cases hjn : j = n
    · subst j
      exact hfollow i hi hleader
    exact hpairs i (Finset.mem_of_mem_insert_of_ne hi hin)
      j (Finset.mem_of_mem_insert_of_ne hj hjn) hleader.2.2.1.le

def delete' (cars : Finset Car) (b B : ℝ) (x v : Car → ℝ) : SetM (Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ LaneSafe cars b B x v
    ensures D => LaneSafe D b B x v
    := do
  let n ← chooseFrom {n | n ∈ cars}
  return cars.erase n
where finally
  | spec =>
    apply laneSafe_subset cars _ (Finset.erase_subset _ _) b B
    all_goals tauto

def new' (cars : Finset Car) : SetM (Car × Finset Car)
    requires True
    ensures (n, D) => n ∉ cars ∧ D = insert n cars
    := do
  let n ← chooseFrom {n | n ∉ cars}
  return (n, insert n cars)
where finally
  | spec => exact ‹_ ∈ SetM.run _›

def create' (cars : Finset Car) (b B : ℝ) (x v : Car → ℝ) : SetM (Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ LaneSafe cars b B x v
    ensures D => LaneSafe D b B x v
    := do
  let (n, cars_new) ← new' cars
  unless (0 ≤ v n ∧ ∀ j ∈ cars, x n ≠ x j) do abort
  unless n.IsAheadItsFollower cars_new b B x v do abort
  unless n.IsBehindItsLeader cars_new b B x v do abort
  return cars_new
where finally
  | spec =>
    simp only at *
    rcases ‹_ ∉ cars ∧ _ = insert _ cars› with ⟨_, rfl⟩
    apply laneSafe_insert
    all_goals tauto

def lhc' (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) :
    SetM LhcResult
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v
    ensures res => LaneSafe res.cars b B res.x res.v
    := do
  let mut (x, v, a) := (x, v, a)
  let mut cars := cars
  let i ← choose ℕ
  for _ in [:i]
      invariant _pref _suff =>
        (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v do
    let j ← choose ℕ
    for _ in [:j]
        invariant _pref _suff =>
          (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v do
      cars ← delete' cars b B x v
    let j' ← choose ℕ
    for _ in [:j']
        invariant _pref _suff =>
          (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧ LaneSafe cars b B x v do
      cars ← create' cars b B x v
    a ← ctrl_n' A b B ε cars x v a
    (x, v, a) ← dyn_glc A b B ε cars x v a
  return { cars, x, v }

theorem lhc_eq (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) :
    lhc A b B ε cars x v a = lhc' A b B ε cars x v a := rfl

/-- FM11 Proposition 3, including the current population after creation and deletion. -/
theorem lhc_safe :
    ∀ A b B ε x v a (cars : Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) → LaneSafe cars b B x v →
        ∀ res ∈ SetM.run (lhc A b B ε cars x v a),
          LaneSafe res.cars b B res.x res.v ∧
            (∀ i ∈ res.cars, i.IsBehindLStar res.cars b B res.x res.v) := by
  intro A b B ε x v a cars hp hsafe res hrun
  rw [lhc_eq] at hrun
  have hfinal := (lhc'.spec A b B ε cars x v a).le_wp ⟨hp, hsafe⟩ res hrun
  exact ⟨hfinal, laneSafe_star res.cars b B hp.2.1 hp.2.2.1 res.x res.v hfinal⟩

def delete_l' (lanes : Finset Lane) (cars : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (cars l) b B x v
    ensures D => ∀ l ∈ lanes, LaneSafe (D l) b B x v
    := do
  let mut cars := cars
  for l in lanes.toList
      invariant _pref _suff =>
        (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (cars l) b B x v do
    let j ← choose ℕ
    for _ in [:j]
        invariant _pref _suff =>
          (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (cars l) b B x v do
      let laneCars ← delete' (cars l) b B x v
      cars := Function.update cars l laneCars
  return cars
where finally
  | spec =>
    all_goals simp_all
    have hl : l ∈ lanes := Finset.mem_toList.mp (by rw [‹lanes.toList = _›]; simp)
    grind

def create_l' (lanes : Finset Lane) (cars : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car)
    requires (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (cars l) b B x v
    ensures D => ∀ l ∈ lanes, LaneSafe (D l) b B x v
    := do
  let mut cars := cars
  for l in lanes.toList
      invariant _pref _suff =>
        (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (cars l) b B x v do
    let j ← choose ℕ
    for _ in [:j]
        invariant _pref _suff =>
          (0 < b ∧ b ≤ B) ∧ ∀ l ∈ lanes, LaneSafe (cars l) b B x v do
      let laneCars ← create' (cars l) b B x v
      cars := Function.update cars l laneCars
  return cars
where finally
  | spec =>
    all_goals simp_all
    have hl : l ∈ lanes := Finset.mem_toList.mp (by rw [‹lanes.toList = _›]; simp)
    grind

theorem ctrl_i_choice (A b B ε : ℝ) (cars : Finset Car) (i : Car)
    (x v a : Car → ℝ) (ai : ℝ)
    (hrun : Function.update a i ai ∈ SetM.run (ctrl_i A b B ε cars i x v a)) :
    CarChoice A b B ε cars i x v ai := by
  rw [ctrl_i_eq] at hrun
  simpa using (ctrl_i'.spec A b B ε cars i x v a).le_wp trivial _ hrun

def ctrl_n_l' (A b B ε : ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ)
    requires True
    ensures a_res => ∀ i ∈ lanes.biUnion cars, ∀ l ∈ lanes,
      i ∈ cars l → CarChoice A b B ε (cars l) i x v (a_res i)
    := do
  let mut a_res := a
  for i in (lanes.biUnion cars).toList
      invariant pref _suff => ∀ i ∈ pref, ∀ l ∈ lanes,
        i ∈ cars l → CarChoice A b B ε (cars l) i x v (a_res i) do
    let ai ← choose ℝ
    for l in lanes.toList
        invariant pref _suff => ∀ l ∈ pref,
          i ∈ cars l → CarChoice A b B ε (cars l) i x v ai do
      if i ∈ cars l then
        let a_new := Function.update a i ai
        ensure (a_new ∈ SetM.run (ctrl_i A b B ε (cars l) i x v a))
    a_res := Function.update a_res i ai
  return a_res
where finally
  | spec =>
    all_goals simp_all
    all_goals try
      have hchoice := ctrl_i_choice A b B ε (cars l) i x v a ai
        ‹Function.update a i ai ∈ SetM.run (ctrl_i A b B ε (cars l) i x v a)›
    all_goals grind [Function.update_apply]

def dyn_ghc (_A _b _B ε : ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car)
    (x v a : Car → ℝ) := dyn ε (lanes.biUnion cars) x v a

@[spec] theorem dyn_ghc_spec (A b B ε : ℝ) (lanes : Finset Lane)
    (cars : Lane → Finset Car) (x v a : Car → ℝ) :
    ⦃(0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧
      (∀ l ∈ lanes, LaneSafe (cars l) b B x v) ∧
      (∀ i ∈ lanes.biUnion cars, ∀ l ∈ lanes,
        i ∈ cars l → CarChoice A b B ε (cars l) i x v (a i))⦄
    dyn_ghc A b B ε lanes cars x v a
    ⦃fun (x_res, v_res, _) => ∀ l ∈ lanes, LaneSafe (cars l) b B x_res v_res⦄ := by
  apply Triple.iff.mpr
  rintro ⟨hp, hsafe, hchoice⟩ ⟨xr, vr, ar⟩ hrun l hl
  have hsub : cars l ⊆ lanes.biUnion cars := fun _ hi => Finset.mem_biUnion.mpr ⟨l, hl, hi⟩
  exact (dyn_laneSafe _ (cars l) hsub A b B ε x v a).le_wp
    ⟨hp, hsafe l hl, fun i hi => hchoice i (hsub hi) l hl hi⟩ (xr, vr, ar) hrun

def ghc' (A b B ε : ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM GhcResult
    requires (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧
      ∀ l ∈ lanes, LaneSafe (cars l) b B x v
    ensures res => ∀ l ∈ lanes, LaneSafe (res.cars l) b B res.x res.v
    := do
  let mut (x, v, a) := (x, v, a)
  let mut cars := cars
  let n ← choose ℕ
  for _ in [:n]
      invariant _pref _suff => (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ 0 < ε) ∧
        ∀ l ∈ lanes, LaneSafe (cars l) b B x v do
    cars ← delete_l' lanes cars b B x v
    cars ← create_l' lanes cars b B x v
    a ← ctrl_n_l' A b B ε lanes cars x v a
    (x, v, a) ← dyn_ghc A b B ε lanes cars x v a
  return { cars, x, v }

theorem ghc_eq (A b B ε : ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car)
    (x v a : Car → ℝ) : ghc A b B ε lanes cars x v a = ghc' A b B ε lanes cars x v a := rfl

/-- FM11 Theorem 1: lane-wise safety under population changes and shared dynamics. -/
theorem ghc_safe :
    ∀ A b B ε x v a (lanes : Finset Lane) (cars : Lane → Finset Car),
      (0 ≤ A ∧ 0 < b ∧ b ≤ B ∧ ε > 0) →
      (∀ l ∈ lanes, LaneSafe (cars l) b B x v) →
        ∀ res ∈ SetM.run (ghc A b B ε lanes cars x v a),
          ∀ l ∈ lanes, LaneSafe (res.cars l) b B res.x res.v ∧
            (∀ i ∈ res.cars l, i.IsBehindLStar (res.cars l) b B res.x res.v) := by
  intro A b B ε x v a lanes cars hp hsafe res hrun
  rw [ghc_eq] at hrun
  have hfinal := (ghc'.spec A b B ε lanes cars x v a).le_wp ⟨hp, hsafe⟩ res hrun
  intro l hl
  exact ⟨hfinal l hl, laneSafe_star (res.cars l) b B hp.2.1 hp.2.2.1 res.x res.v (hfinal l hl)⟩

end FM11
