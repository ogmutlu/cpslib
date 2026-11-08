import CPSLib.Examples.ACASX.ExplicitFormulations.Model
import CPSLib.Examples.ACASX.Proof

open CPSLib

namespace ACASX

/-- Twice the signed nominal height in time coordinates scaled by `alo`.
The velocity arguments are already signed by `w`. -/
noncomputable def nominal (v target t : ℝ) : ℝ :=
  if t < max 0 (target - v) then t ^ 2 + 2 * v * t
  else 2 * target * t - max 0 (target - v) ^ 2

theorem nominal_antitone (v target s t : ℝ) (hF : target < 0)
    (hs : 0 ≤ s) (hst : s ≤ t) : nominal v target t ≤ nominal v target s := by
  by_cases hgap : 0 ≤ target - v
  · simp only [nominal, max_eq_right hgap]
    split_ifs with ht hs'
    · nlinarith [mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ -2 * v - s - t by linarith)]
    · linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF.le
        (show 0 ≤ t - (target - v) by linarith), sq_nonneg (s - (target - v))]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF.le (sub_nonneg.mpr hst)]
  · simp only [nominal, max_eq_left (le_of_not_ge hgap),
      ite_eq_right (not_lt_of_ge (hs.trans hst)), ite_eq_right (not_lt_of_ge hs)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hF.le (sub_nonneg.mpr hst)]

theorem nominal_of_le (v target t : ℝ) (ht : t ≤ max 0 (target - v)) :
    nominal v target t = t ^ 2 + 2 * v * t := by
  unfold nominal
  split_ifs with h
  · rfl
  · have heq : t = max 0 (target - v) := le_antisymm ht (le_of_not_gt h)
    rw [heq]
    rcases le_total 0 (target - v) with hg | hg
    · rw [max_eq_right hg]
      ring
    · rw [max_eq_left hg]
      ring

theorem vertex_le_switch (v target : ℝ) (hF : 0 ≤ target) :
    -(min 0 v) ≤ max 0 (target - v) := by
  rcases le_total 0 v with hv | hv
  · rw [min_eq_left hv]
    simp
  · rw [min_eq_right hv]
    exact (show -v ≤ target - v by linarith).trans (le_max_right 0 _)

theorem nominal_at_vertex (v target : ℝ) (hF : 0 ≤ target) :
    nominal v target (-(min 0 v)) = -(min 0 v) ^ 2 := by
  rw [nominal_of_le v target _ (vertex_le_switch v target hF)]
  rcases le_total 0 v with hv | hv
  · rw [min_eq_left hv]
    ring
  · rw [min_eq_right hv]
    ring

theorem nominal_global_min (v target t : ℝ) (hF : 0 ≤ target) (ht : 0 ≤ t) :
    -(min 0 v) ^ 2 ≤ nominal v target t := by
  by_cases hv : 0 ≤ v
  · rw [min_eq_left hv]
    by_cases hg : 0 ≤ target - v
    · simp only [nominal, max_eq_right hg]
      split_ifs with h
      · nlinarith [mul_nonneg hv ht, sq_nonneg t]
      · nlinarith [mul_nonneg hF (show 0 ≤ t - (target - v) by linarith),
          mul_nonneg hg (add_nonneg hF hv)]
    · simp only [nominal, max_eq_left (le_of_not_ge hg), ite_eq_right (not_lt_of_ge ht)]
      nlinarith [mul_nonneg hF ht]
  · rw [min_eq_right (le_of_not_ge hv)]
    simp only [nominal, max_eq_right (show 0 ≤ target - v by linarith)]
    split_ifs with h
    · nlinarith [sq_nonneg (t + v)]
    · nlinarith [mul_nonneg hF (show 0 ≤ t - (target - v) by linarith), sq_nonneg target]

theorem nominal_right_min (v target l t : ℝ) (hF : 0 ≤ target)
    (hl : 0 ≤ l) (hvertex : -(min 0 v) ≤ l)
    (hlswitch : l ≤ max 0 (target - v)) (hlt : l ≤ t) :
    nominal v target l ≤ nominal v target t := by
  have hslope : 0 ≤ v + l := by
    rcases le_total 0 v with hv | hv
    · linarith
    · rw [min_eq_right hv] at hvertex
      linarith
  have hjoin := nominal_of_le v target (max 0 (target - v)) le_rfl
  simp only [nominal, lt_self_iff_false, ite_false] at hjoin
  rw [nominal_of_le v target l hlswitch]
  unfold nominal
  split_ifs with h
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlt)
      (show 0 ≤ t + l + 2 * v by linarith)]
  · nlinarith [mul_nonneg hF (show 0 ≤ t - max 0 (target - v) by linarith),
      mul_nonneg (sub_nonneg.mpr hlswitch)
        (show 0 ≤ max 0 (target - v) + l + 2 * v by linarith)]

theorem nominal_left_min (v target t u : ℝ) (hF : 0 ≤ target)
    (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ -(min 0 v)) :
    nominal v target u ≤ nominal v target t := by
  have hswitch := vertex_le_switch v target hF
  rw [nominal_of_le v target u (hu.trans hswitch),
    nominal_of_le v target t (htu.trans (hu.trans hswitch))]
  rcases le_total 0 v with hv | hv
  · rw [min_eq_left hv] at hu
    have hzero : t = 0 ∧ u = 0 := by constructor <;> linarith
    simp [hzero.1, hzero.2]
  · rw [min_eq_right hv] at hu
    nlinarith [mul_nonneg (sub_nonneg.mpr htu)
      (show 0 ≤ -2 * v - t - u by linarith)]

theorem nominal_linear_min (v target l t : ℝ) (hF : 0 ≤ target)
    (hl : max 0 (target - v) ≤ l) (hlt : l ≤ t) :
    nominal v target l ≤ nominal v target t := by
  simp only [nominal, ite_eq_right (not_lt_of_ge hl),
    ite_eq_right (not_lt_of_ge (hl.trans hlt))]
  nlinarith [mul_nonneg hF (sub_nonneg.mpr hlt)]

/-- The six archive cases, in acceleration-scaled time coordinates. -/
def explicitWindow (v target l u height : ℝ) : Prop :=
  let c := -(min 0 v)
  let M := max 0 (target - v)
  (0 ≤ target →
    ((0 ≤ u ∧ u < c) → height < u ^ 2 + 2 * v * u) ∧
    ((c ≤ u ∧ l ≤ c) → height < -(min 0 v) ^ 2) ∧
    ((c < l ∧ l ≤ M) → height < l ^ 2 + 2 * v * l) ∧
    (M < l → height < 2 * target * l - M ^ 2)) ∧
  (target < 0 →
    ((0 ≤ u ∧ u < M) → height < u ^ 2 + 2 * v * u) ∧
    (M ≤ u → height < 2 * target * u - M ^ 2))

/-- Archive Lemma 1: cases 1/5 use the right horizontal boundary, case 2 the
parabola vertex, and cases 3/4 the left boundary. Case 6 uses the final line.
The backward direction evaluates the implicit condition at those same points. -/
theorem window_equivalent (v target l u height : ℝ) (hlu : l ≤ u) :
    explicitWindow v target l u height ↔
      ∀ t, 0 ≤ t → l ≤ t → t ≤ u → height < nominal v target t := by
  constructor
  · intro hex t ht hlt htu
    rcases le_or_gt 0 target with hF | hF
    · obtain ⟨h1, h2, h3, h4⟩ := hex.1 hF
      by_cases hu : u < -(min 0 v)
      · have hval := h1 ⟨ht.trans htu, hu⟩
        rw [← nominal_of_le v target u
          (hu.le.trans (vertex_le_switch v target hF))] at hval
        exact hval.trans_le (nominal_left_min v target t u hF ht htu hu.le)
      · by_cases hl : l ≤ -(min 0 v)
        · exact (h2 ⟨le_of_not_gt hu, hl⟩).trans_le (nominal_global_min v target t hF ht)
        · by_cases hM : l ≤ max 0 (target - v)
          · have hval := h3 ⟨lt_of_not_ge hl, hM⟩
            rw [← nominal_of_le v target l hM] at hval
            exact hval.trans_le (nominal_right_min v target l t hF
              ((neg_nonneg.mpr (min_le_left 0 v)).trans (le_of_not_ge hl))
              (le_of_not_ge hl) hM hlt)
          · have hval := h4 (lt_of_not_ge hM)
            have heq : nominal v target l =
                2 * target * l - max 0 (target - v) ^ 2 := by
              simp [nominal, not_lt_of_ge (le_of_not_ge hM)]
            rw [← heq] at hval
            exact hval.trans_le (nominal_linear_min v target l t hF
              (le_of_not_ge hM) hlt)
    · obtain ⟨h5, h6⟩ := hex.2 hF
      have hval : height < nominal v target u := by
        by_cases hu : u < max 0 (target - v)
        · simpa [nominal, hu] using h5 ⟨ht.trans htu, hu⟩
        · simpa [nominal, hu] using h6 (le_of_not_gt hu)
      exact hval.trans_le (nominal_antitone v target t u hF ht htu)
  · intro himp
    constructor
    · intro hF
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hu
        have hx := himp u hu.1 hlu le_rfl
        rwa [nominal_of_le v target u
          (hu.2.le.trans (vertex_le_switch v target hF))] at hx
      · intro hc
        have hx := himp (-(min 0 v)) (neg_nonneg.mpr (min_le_left 0 v)) hc.2 hc.1
        rwa [nominal_at_vertex v target hF] at hx
      · intro hl
        have hx := himp l
          ((neg_nonneg.mpr (min_le_left 0 v)).trans hl.1.le) le_rfl hlu
        rwa [nominal_of_le v target l hl.2] at hx
      · intro hl
        have hx := himp l ((le_max_left 0 _).trans hl.le) le_rfl hlu
        simpa [nominal, not_lt_of_ge hl.le] using hx
    · intro hF
      constructor
      · intro hu
        simpa [nominal, hu.2] using himp u hu.1 hlu le_rfl
      · intro hu
        simpa [nominal, not_lt_of_ge hu] using
          himp u ((le_max_left 0 _).trans hu) hlu le_rfl

theorem A_nominal (alo t hn v w vlo : ℝ) (ha : 0 < alo) (hw : Sense w)
    (hA : A alo t hn v w vlo) :
    2 * alo * (w * hn) = nominal (w * v) (w * vlo) (alo * t) := by
  have hs := A_scaled alo t hn v w vlo ha hw hA
  rw [show w * (vlo - v) = w * vlo - w * v by ring] at hs
  rw [hs]
  unfold nominal lowerRelative
  split_ifs <;> ring

/-- For positive closing speed the collision puck gives a closed time interval.
Only the time coordinate and the height inequality are rescaled. -/
theorem implicit_window (rp hp rv alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hrv : 0 < rv) :
    Limpl rp hp rv alo r h v w vlo ↔
      ∀ t, 0 ≤ t → alo * (r - rp) / rv ≤ t → t ≤ alo * (r + rp) / rv →
        2 * alo * (w * h + hp) < nominal (w * v) (w * vlo) t := by
  have ha0 := ne_of_gt ha
  constructor
  · intro hsafe t ht hl hu
    obtain ⟨hn, hA⟩ := A_exists alo (t / alo) v w vlo (div_nonneg ht ha.le)
    have hs := A_nominal alo (t / alo) hn v w vlo ha hw hA
    rw [mul_div_cancel₀ _ ha0] at hs
    have hinside : |r - rv * (t / alo)| ≤ rp := by
      rw [abs_le]
      have hl' := (div_le_iff₀ hrv).mp hl
      have hu' := (le_div_iff₀ hrv).mp hu
      have heq : alo * (rv * (t / alo)) = rv * t := by field_simp
      constructor <;> nlinarith
    have hsep := (hsafe (t / alo) (rv * (t / alo)) hn ⟨rfl, hA⟩).resolve_left
      (not_lt_of_ge hinside)
    nlinarith
  · intro hsafe t rn hn ⟨hrn, hA⟩
    rw [hrn]
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      have hs := hsafe (alo * t) (mul_nonneg ha.le (A_time_nonneg _ _ _ _ _ _ ha hA))
        (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
      have hn := A_nominal alo t hn v w vlo ha hw hA
      nlinarith
    · exact Or.inl (lt_of_not_ge hinside)

theorem positive_scale_lt (k x y X Y : ℝ) (hk : 0 < k)
    (heq : k * (y - x) = Y - X) : (x < y ↔ X < Y) := by
  calc
    (x < y) ↔ 0 < y - x := sub_pos.symm
    _ ↔ 0 < k * (y - x) := (mul_pos_iff_of_pos_left hk).symm
    _ ↔ X < Y := by rw [heq, sub_pos]

/-- Algebraic translation of all six archive conditions. Every multiplier
used to clear a denominator is positive; strict case boundaries are preserved. -/
theorem explicit_window (rp hp rv alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hrv : 0 < rv) :
    Lexpl rp hp rv alo r h v w vlo ↔
      explicitWindow (w * v) (w * vlo) (alo * (r - rp) / rv)
        (alo * (r + rp) / rv) (2 * alo * (w * h + hp)) := by
  let k := rv / alo
  have hk : 0 < k := div_pos hrv ha
  have ha0 := ne_of_gt ha
  have hr0 := ne_of_gt hrv
  have htime (z : ℝ) : alo * z / rv = z / k := by dsimp [k]; field_simp
  have hshift (z : ℝ) : rv * z / alo = k * z := by dsimp [k]; ring
  have hquad (z : ℝ) :
      (2 * alo * (w * h + hp) < (z / k) ^ 2 + 2 * (w * v) * (z / k)) ↔
      w * rv ^ 2 * h < alo / 2 * z ^ 2 + w * rv * v * z - rv ^ 2 * hp := by
    apply positive_scale_lt (rv ^ 2 / (2 * alo)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hline (z : ℝ) :
      (2 * alo * (w * h + hp) <
        2 * (w * vlo) * (z / k) - maxI v w vlo ^ 2) ↔
      w * rv * h < w * vlo * z - rv * maxI v w vlo ^ 2 / (2 * alo) - rv * hp := by
    apply positive_scale_lt (rv / (2 * alo)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hvertex :
      (2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) ↔
      w * h < -(min 0 (w * v)) ^ 2 / (2 * alo) - hp := by
    apply positive_scale_lt (1 / (2 * alo)) _ _ _ _ (by positivity)
    field_simp
    ring
  have hM : max 0 (w * vlo - w * v) = maxI v w vlo := by
    unfold maxI
    congr 1
    ring
  have h0 : (0 ≤ (r + rp) / k) ↔ -rp ≤ r := by
    rw [le_div_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have hu (z : ℝ) : ((r + rp) / k ≤ z) ↔ r ≤ -rp + k * z := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hul (z : ℝ) : ((r + rp) / k < z) ↔ r < -rp + k * z := by
    rw [div_lt_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hl (z : ℝ) : ((r - rp) / k ≤ z) ↔ r ≤ rp + k * z := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hll (z : ℝ) : ((r - rp) / k < z) ↔ r < rp + k * z := by
    rw [div_lt_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hur (z : ℝ) : (z ≤ (r + rp) / k) ↔ -rp + k * z ≤ r := by
    rw [← not_lt, hul, not_lt]
  have hlr (z : ℝ) : (z < (r - rp) / k) ↔ rp + k * z < r := by
    rw [← not_le, hl, not_le]
  unfold Lexpl explicitWindow
  dsimp only
  rw [htime, htime, hM]
  simp only [hquad, hline, hvertex, h0, hul, hl,
    hur, hlr, hshift, hr0, false_or, false_and, mul_neg, ← sub_eq_add_neg]

/-- With no horizontal exit, a negative target eventually violates every
finite altitude bound. A nonnegative target attains its minimum at the vertex. -/
theorem nominal_all_time (v target height : ℝ) :
    (∀ t, 0 ≤ t → height < nominal v target t) ↔
      0 ≤ target ∧ height < -(min 0 v) ^ 2 := by
  constructor
  · intro hs
    have hF : 0 ≤ target := by
      by_contra hneg
      have hneg : target < 0 := lt_of_not_ge hneg
      let t := max (max 0 (target - v)) (height / (2 * target))
      have ht : 0 ≤ t := (le_max_left 0 _).trans (le_max_left _ _)
      have hM : max 0 (target - v) ≤ t := le_max_left _ _
      have hval := hs t ht
      simp only [nominal, ite_eq_right (not_lt_of_ge hM)] at hval
      have hbound := (div_le_iff_of_neg (show 2 * target < 0 by linarith)).mp
        (le_max_right (max 0 (target - v)) (height / (2 * target)))
      nlinarith [sq_nonneg (max 0 (target - v))]
    have hval := hs (-(min 0 v)) (neg_nonneg.mpr (min_le_left 0 v))
    rw [nominal_at_vertex v target hF] at hval
    exact ⟨hF, hval⟩
  · rintro ⟨hF, hmin⟩ t ht
    exact hmin.trans_le (nominal_global_min v target t hF ht)

theorem implicit_stationary (rp hp alo r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) :
    Limpl rp hp 0 alo r h v w vlo ↔
      rp < |r| ∨ (0 ≤ w * vlo ∧ 2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) := by
  by_cases hsep : rp < |r|
  · simp only [hsep, true_or, iff_true]
    intro t rn hn ⟨hrn, _⟩
    left
    simpa [hrn] using hsep
  · have hinside : |r| ≤ rp := le_of_not_gt hsep
    rw [or_iff_right hsep, ← nominal_all_time]
    constructor
    · intro hsafe t ht
      obtain ⟨hn, hA⟩ := A_exists alo (t / alo) v w vlo (div_nonneg ht ha.le)
      have hs := A_nominal alo (t / alo) hn v w vlo ha hw hA
      rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hs
      have hval := (hsafe (t / alo) 0 hn ⟨by ring, hA⟩).resolve_left (by simpa using hsep)
      nlinarith
    · intro hs t rn hn ⟨hrn, hA⟩
      right
      have hval := hs (alo * t) (mul_nonneg ha.le (A_time_nonneg _ _ _ _ _ _ ha hA))
      have hn := A_nominal alo t hn v w vlo ha hw hA
      nlinarith

/-- Preserve the archive's explicit `rv = 0` disjuncts rather than dividing
by the closing speed in the degenerate case. -/
theorem explicit_stationary (rp hp alo r h v w vlo : ℝ) (ha : 0 < alo) :
    Lexpl rp hp 0 alo r h v w vlo ↔
      rp < |r| ∨ (0 ≤ w * vlo ∧ 2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) := by
  have hm : (w * h < -(min 0 (w * v)) ^ 2 / (2 * alo) - hp) ↔
      2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity : 0 < 2 * alo)]
    constructor <;> intro hx <;> nlinarith
  simp only [Lexpl, zero_mul, mul_zero, zero_div, sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    true_or, true_and]
  rw [hm]
  have himpossible₁ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  have himpossible₂ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [himpossible₁, himpossible₂, false_implies, true_and]
  by_cases hleft : r < -rp
  · have hsep : rp < |r| := (neg_le_abs r).trans_lt' (by linarith)
    simp [not_le.mpr hleft, hsep]
  · by_cases hright : rp < r
    · have hsep : rp < |r| := hright.trans_le (le_abs_self r)
      simp [hright, not_le.mpr hright, hsep]
    · have hinside : |r| ≤ rp := abs_le.mpr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      by_cases hF : 0 ≤ w * vlo
      · simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, not_lt_of_ge hF]
      · have hneg : ¬0 < w * vlo * (r + rp) := not_lt_of_ge
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hF) (by linarith))
        simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, lt_of_not_ge hF, hneg]

/-- STTT Lemma 1 / repository `acasx.kyx`. -/
theorem immediate_regions_equivalent :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → Sense w →
        (Lexpl rp hp rv alo r h v w vlo ↔ Limpl rp hp rv alo r h v w vlo) := by
  intro rp hp rv alo r h v w vlo hb hw
  by_cases hr : rv = 0
  · subst rv
    exact (explicit_stationary rp hp alo r h v w vlo hb.2.2.2).trans
      (implicit_stationary rp hp alo r h v w vlo hb.2.2.2 hw).symm
  · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
    rw [explicit_window rp hp rv alo r h v w vlo hb.2.2.2 hr,
      implicit_window rp hp rv alo r h v w vlo hb.2.2.2 hw hr]
    exact window_equivalent _ _ _ _ _ (by
      apply div_le_div_of_nonneg_right _ hr.le
      exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) hb.2.2.2.le)

noncomputable def delayPoly (ad V t : ℝ) : ℝ := -ad * t ^ 2 + 2 * V * t

/-- The signed delay parabola is concave, so its minimum on a closed collision
interval occurs at an endpoint. This also covers zero delay and `ad = 0`. -/
theorem delayPoly_min (ad V l u t : ℝ) (had : 0 ≤ ad) (hlt : l ≤ t) (htu : t ≤ u) :
    delayPoly ad V l ≤ delayPoly ad V t ∨ delayPoly ad V u ≤ delayPoly ad V t := by
  by_cases hs : 0 ≤ 2 * V - ad * (t + l)
  · left
    unfold delayPoly
    nlinarith [mul_nonneg (sub_nonneg.mpr hlt) hs]
  · right
    have hsl : 0 ≤ ad * (u + t) - 2 * V := by
      nlinarith [mul_nonneg had (show 0 ≤ u - l by linarith)]
    unfold delayPoly
    nlinarith [mul_nonneg (sub_nonneg.mpr htu) hsl]

def delayWindow (ad V D l u H : ℝ) : Prop :=
  ((l ≤ 0 ∧ 0 ≤ u) → H < 0) ∧
  ((0 < l ∧ l ≤ D) → H < delayPoly ad V l) ∧
  ((0 ≤ u ∧ u < D) → H < delayPoly ad V u) ∧
  ((l ≤ D ∧ D ≤ u) → H < delayPoly ad V D)

theorem delay_window_equivalent (ad V D l u H : ℝ) (had : 0 ≤ ad) (hD : 0 ≤ D)
    (hlu : l ≤ u) : delayWindow ad V D l u H ↔
      ∀ t, 0 ≤ t → t ≤ D → l ≤ t → t ≤ u → H < delayPoly ad V t := by
  constructor
  · rintro ⟨hzero, hleft, hright, hend⟩ t ht htd hlt htu
    have hL : H < delayPoly ad V (max 0 l) := by
      by_cases hl : l ≤ 0
      · simpa [max_eq_left hl, delayPoly] using hzero ⟨hl, ht.trans htu⟩
      · rw [max_eq_right (le_of_not_ge hl)]
        exact hleft ⟨lt_of_not_ge hl, hlt.trans htd⟩
    have hU : H < delayPoly ad V (min D u) := by
      by_cases hu : u < D
      · rw [min_eq_right hu.le]
        exact hright ⟨ht.trans htu, hu⟩
      · rw [min_eq_left (le_of_not_gt hu)]
        exact hend ⟨hlt.trans htd, le_of_not_gt hu⟩
    rcases delayPoly_min ad V (max 0 l) (min D u) t had (max_le ht hlt)
      (le_min htd htu) with h | h
    · exact hL.trans_le h
    · exact hU.trans_le h
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      simpa [delayPoly] using hs 0 le_rfl hD h.1 h.2
    · intro h
      exact hs l h.1.le h.2 le_rfl hlu
    · intro h
      exact hs u h.1 h.2.le hlu le_rfl
    · intro h
      exact hs D hD le_rfl h.1 h.2

theorem delay_height_iff (ad t h v w hp : ℝ) (hw : Sense w) :
    w * (h - (-(w * ad) / 2 * t ^ 2 + v * t)) < -hp ↔
      2 * (w * h + hp) < delayPoly ad (w * v) t := by
  unfold delayPoly
  rcases hw with rfl | rfl <;> constructor <;> intro hx <;> nlinarith

theorem delay_prefix_window (rp hp rv ad D r h v w : ℝ) (hw : Sense w) (hrv : 0 < rv) :
    delayPrefix rp hp rv ad D r h v w ↔
      ∀ t, 0 ≤ t → t ≤ D → (r - rp) / rv ≤ t → t ≤ (r + rp) / rv →
        2 * (w * h + hp) < delayPoly ad (w * v) t := by
  constructor
  · intro hs t ht htd hl hu
    have hinside : |r - rv * t| ≤ rp := by
      rw [abs_le]
      rw [div_le_iff₀ hrv] at hl
      rw [le_div_iff₀ hrv] at hu
      constructor <;> nlinarith
    exact (delay_height_iff ad t h v w hp hw).mp
      ((hs t ht htd).resolve_left (not_lt_of_ge hinside))
  · intro hs t ht htd
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      apply (delay_height_iff ad t h v w hp hw).mpr
      exact hs t ht htd (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
    · exact Or.inl (lt_of_not_ge hinside)

def delayExplicit (ad V D l u H : ℝ) : Prop :=
  ((l ≤ 0 ∧ 0 ≤ u) → H < 0) ∧
  ((0 < l ∧ l ≤ D) → H < delayPoly ad V l) ∧
  ((0 ≤ u ∧ u < D) → H < delayPoly ad V u)

theorem explicit_delay_window (rp hp rv alo ad r h v w vlo d : ℝ)
    (hb : Bounds rp hp rv alo) (hw : Sense w) (hrv : 0 < rv) :
    Dexpl rp hp rv alo ad r h v w vlo d ↔
      delayExplicit ad (w * v) (max 0 d) ((r - rp) / rv) ((r + rp) / rv)
        (2 * (w * h + hp)) ∧
      Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo := by
  have hquad (z : ℝ) :
      (2 * (w * h + hp) < delayPoly ad (w * v) (z / rv)) ↔
      w * rv ^ 2 * h < -ad / 2 * z ^ 2 + w * rv * v * z - rv ^ 2 * hp := by
    apply positive_scale_lt (rv ^ 2 / 2) _ _ _ _ (by positivity)
    unfold delayPoly
    field_simp
    ring
  have hzero : (2 * (w * h + hp) < 0) ↔ w * h < -hp := by
    constructor <;> intro hx <;> linarith
  have hc₀ : ((r - rp) / rv ≤ 0 ∧ 0 ≤ (r + rp) / rv) ↔ (-rp ≤ r ∧ r ≤ rp) := by
    rw [div_le_iff₀ hrv, le_div_iff₀ hrv]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  have hc₁ : (0 < (r - rp) / rv ∧ (r - rp) / rv ≤ max 0 d) ↔
      (rp < r ∧ r ≤ rv * max 0 d + rp) := by
    rw [lt_div_iff₀ hrv, div_le_iff₀ hrv]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  have hc₂ : (0 ≤ (r + rp) / rv ∧ (r + rp) / rv < max 0 d) ↔
      (-rp ≤ r ∧ r < rv * max 0 d - rp) := by
    rw [le_div_iff₀ hrv, div_lt_iff₀ hrv]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  unfold Dexpl delayExplicit
  dsimp only
  rw [immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw]
  simp only [hquad, hzero, hc₀, hc₁, hc₂, and_assoc]

theorem delayed_regions_pos (rp hp rv alo ad r h v w vlo d : ℝ)
    (hb : Bounds rp hp rv alo) (had : 0 ≤ ad) (hw : Sense w) (hrv : 0 < rv) :
    Dexpl rp hp rv alo ad r h v w vlo d ↔ Dimpl rp hp rv alo ad r h v w vlo d := by
  have hterminal :
      Limpl rp hp rv alo (r - rv * max 0 d)
        (h - (-(w * ad) / 2 * max 0 d ^ 2 + v * max 0 d))
        (v - w * ad * max 0 d) w vlo →
      ((r - rp) / rv ≤ max 0 d ∧ max 0 d ≤ (r + rp) / rv) →
        2 * (w * h + hp) < delayPoly ad (w * v) (max 0 d) := by
    intro hs ⟨hl, hu⟩
    have hval := hs 0 0 0 ⟨by ring, A_zero alo _ w vlo hb.2.2.2⟩
    have hinside : |r - rv * max 0 d| ≤ rp := by
      rw [abs_le]
      rw [div_le_iff₀ hrv] at hl
      rw [le_div_iff₀ hrv] at hu
      constructor <;> nlinarith
    simp only [sub_zero] at hval
    exact (delay_height_iff ad (max 0 d) h v w hp hw).mp
      (hval.resolve_left (not_lt_of_ge hinside))
  rw [explicit_delay_window _ _ _ _ _ _ _ _ _ _ _ hb hw hrv,
    delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ hb.2.2.2,
    delay_prefix_window _ _ _ _ _ _ _ _ _ hw hrv]
  have heq := delay_window_equivalent ad (w * v) (max 0 d)
    ((r - rp) / rv) ((r + rp) / rv) (2 * (w * h + hp)) had (le_max_left 0 d)
    (div_le_div_of_nonneg_right (by linarith [hb.1]) hrv.le)
  constructor
  · rintro ⟨hex, hs⟩
    exact ⟨heq.mp ⟨hex.1, hex.2.1, hex.2.2, hterminal hs⟩, hs⟩
  · rintro ⟨hpre, hs⟩
    have hwin := heq.mpr hpre
    exact ⟨⟨hwin.1, hwin.2.1, hwin.2.2.1⟩, hs⟩

theorem delayed_regions_zero (rp hp alo ad r h v w vlo d : ℝ)
    (hb : Bounds rp hp 0 alo) (had : 0 ≤ ad) (hw : Sense w) :
    Dexpl rp hp 0 alo ad r h v w vlo d ↔ Dimpl rp hp 0 alo ad r h v w vlo d := by
  rw [Dexpl]
  rw [immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw,
    delayed_decomposition _ _ _ _ _ _ _ _ _ _ _ hb.2.2.2]
  have hbad₁ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  have hbad₂ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [zero_mul, mul_zero, zero_add, sub_zero, zero_sub, hbad₁, hbad₂,
    false_implies, true_and]
  constructor
  · rintro ⟨hinit, hs⟩
    refine ⟨?_, hs⟩
    intro t ht htd
    by_cases hsep : rp < |r|
    · exact Or.inl (by simpa using hsep)
    · right
      have hinside := abs_le.mp (le_of_not_gt hsep)
      have hzero : 2 * (w * h + hp) < delayPoly ad (w * v) 0 := by
        have hx := hinit hinside
        simp only [delayPoly, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
        linarith
      have hend : 2 * (w * h + hp) < delayPoly ad (w * v) (max 0 d) := by
        have hx := hs 0 0 0 ⟨by ring, A_zero alo _ w vlo hb.2.2.2⟩
        simp only [sub_zero] at hx
        exact (delay_height_iff ad (max 0 d) h v w hp hw).mp (hx.resolve_left hsep)
      apply (delay_height_iff ad t h v w hp hw).mpr
      exact (delayPoly_min ad (w * v) 0 (max 0 d) t had ht htd).elim
        (fun hx => hzero.trans_le hx) (fun hx => hend.trans_le hx)
  · rintro ⟨hpre, hs⟩
    refine ⟨?_, hs⟩
    intro hinside
    have hx := hpre 0 le_rfl (le_max_left 0 d)
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero] at hx
    exact hx.resolve_left (not_lt_of_ge (abs_le.mpr hinside))

/-- STTT Lemma 2, Fig. 5; the explicit predicate is transcribed from the journal. -/
theorem delayed_regions_equivalent :
    ∀ rp hp rv alo ad r h v w vlo d,
      Bounds rp hp rv alo → 0 ≤ ad → Sense w →
        (Dexpl rp hp rv alo ad r h v w vlo d ↔ Dimpl rp hp rv alo ad r h v w vlo d) := by
  intro rp hp rv alo ad r h v w vlo d hb had hw
  by_cases hr : rv = 0
  · subst rv
    exact delayed_regions_zero rp hp alo ad r h v w vlo d hb had hw
  · exact delayed_regions_pos rp hp rv alo ad r h v w vlo d hb had hw
      (lt_of_le_of_ne hb.2.2.1 (Ne.symm hr))

/-- A convex capped nominal trajectory is bounded by one of the endpoints. -/
theorem upper_nominal_endpoints (v F s z t : ℝ)
    (hF : v ≤ F) (_hs : 0 ≤ s) (hsz : s ≤ z) (hzt : z ≤ t) :
    nominal v F z ≤ max (nominal v F s) (nominal v F t) := by
  have hM : max 0 (F - v) = F - v := max_eq_right (sub_nonneg.mpr hF)
  simp only [nominal, hM]
  split_ifs with hz hs' ht
  all_goals try linarith
  · by_cases h : z + v ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z - s by linarith)
        (show z + s + 2 * v ≤ 0 by linarith)]
    · apply le_max_of_le_right
      nlinarith [mul_nonneg (show 0 ≤ t - z by linarith)
        (show 0 ≤ t + z + 2 * v by linarith)]
  · by_cases h : z + v ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ z - s by linarith)
        (show z + s + 2 * v ≤ 0 by linarith)]
    · apply le_max_of_le_right
      have hFp : 0 ≤ F := by linarith
      nlinarith [mul_nonneg (show 0 ≤ F - v - z by linarith)
          (show 0 ≤ F - v + z + 2 * v by linarith),
        mul_nonneg hFp (show 0 ≤ t - (F - v) by linarith)]
  · by_cases h : F ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonneg (show 0 ≤ F - v - s by linarith)
          (show 0 ≤ -2 * v - s - (F - v) by linarith),
        mul_nonpos_of_nonpos_of_nonneg h (show 0 ≤ z - (F - v) by linarith)]
    · apply le_max_of_le_right
      nlinarith [mul_nonneg (le_of_not_ge h) (show 0 ≤ t - z by linarith)]
  · by_cases h : F ≤ 0
    · apply le_max_of_le_left
      nlinarith [mul_nonpos_of_nonpos_of_nonneg h (show 0 ≤ z - s by linarith)]
    · apply le_max_of_le_right
      nlinarith [mul_nonneg (le_of_not_ge h) (show 0 ≤ t - z by linarith)]

theorem nominal_antitone_nonpos (v target s t : ℝ) (hF : target ≤ 0)
    (hs : 0 ≤ s) (hst : s ≤ t) : nominal v target t ≤ nominal v target s := by
  by_cases hgap : 0 ≤ target - v
  · simp only [nominal, max_eq_right hgap]
    split_ifs with ht hs'
    · nlinarith [mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ -2 * v - s - t by linarith)]
    · linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF
        (show 0 ≤ t - (target - v) by linarith), sq_nonneg (s - (target - v))]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hF (sub_nonneg.mpr hst)]
  · simp only [nominal, max_eq_left (le_of_not_ge hgap),
      ite_eq_right (not_lt_of_ge (hs.trans hst)), ite_eq_right (not_lt_of_ge hs)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hF (sub_nonneg.mpr hst)]

/-- Upper-bound cases in acceleration-scaled time coordinates. -/
def upperWindow (v F l u height : ℝ) : Prop :=
  let M := max 0 (F - v)
  (0 < F →
    ((l ≤ 0 ∧ 0 ≤ u) → 0 < height) ∧
    ((0 < l ∧ l ≤ M) → l ^ 2 + 2 * v * l < height) ∧
    ((0 ≤ u ∧ u < M) → u ^ 2 + 2 * v * u < height) ∧
    (M ≤ u → 2 * F * u - M ^ 2 < height)) ∧
  (F ≤ 0 →
    ((l ≤ 0 ∧ 0 ≤ u) → 0 < height) ∧
    ((0 < l ∧ l ≤ M) → l ^ 2 + 2 * v * l < height) ∧
    (M < l → 2 * F * l - M ^ 2 < height))

theorem upper_window_equivalent (v F l u height : ℝ) (hF : v ≤ F) (hlu : l ≤ u) :
    upperWindow v F l u height ↔
      ∀ t, 0 ≤ t → l ≤ t → t ≤ u → nominal v F t < height := by
  have hM : 0 ≤ max 0 (F - v) := le_max_left 0 _
  have hzero : nominal v F 0 = 0 := by
    by_cases hm : max 0 (F - v) = 0
    · simp [nominal, hm]
    · simp [nominal, lt_of_le_of_ne hM (Ne.symm hm)]
  constructor
  · intro hex t ht hlt htu
    rcases lt_or_ge 0 F with hpos | hneg
    · obtain ⟨h10, h11, h12, h13⟩ := hex.1 hpos
      have hright : nominal v F u < height := by
        by_cases hu : u < max 0 (F - v)
        · have hx := h12 ⟨ht.trans htu, hu⟩
          rw [nominal_of_le v F u hu.le]
          exact hx
        · have hx := h13 (le_of_not_gt hu)
          simpa [nominal, not_lt_of_ge (le_of_not_gt hu)] using hx
      by_cases hl : l ≤ 0
      · have hleft : nominal v F 0 < height := by simpa [hzero] using h10 ⟨hl, ht.trans htu⟩
        exact (upper_nominal_endpoints v F 0 t u hF le_rfl ht htu).trans_lt (max_lt hleft hright)
      · have hl0 : 0 < l := lt_of_not_ge hl
        by_cases hlM : l ≤ max 0 (F - v)
        · have hleft : nominal v F l < height := by
            rw [nominal_of_le v F l hlM]
            exact h11 ⟨hl0, hlM⟩
          exact (upper_nominal_endpoints v F l t u hF hl0.le hlt htu).trans_lt
            (max_lt hleft hright)
        · have hleft : nominal v F l < height := by
            have hle : nominal v F l ≤ nominal v F u := by
              simp only [nominal, ite_eq_right (not_lt_of_ge (le_of_not_ge hlM)),
                ite_eq_right (not_lt_of_ge ((le_of_not_ge hlM).trans hlu))]
              nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hlu)]
            exact hle.trans_lt hright
          exact (upper_nominal_endpoints v F l t u hF hl0.le hlt htu).trans_lt
            (max_lt hleft hright)
    · obtain ⟨h10, h11, h14⟩ := hex.2 hneg
      by_cases hl : l ≤ 0
      · have hleft : nominal v F 0 < height := by simpa [hzero] using h10 ⟨hl, ht.trans htu⟩
        exact (nominal_antitone_nonpos v F 0 t hneg le_rfl ht).trans_lt hleft
      · have hl0 : 0 < l := lt_of_not_ge hl
        have hleft : nominal v F l < height := by
          by_cases hlM : l ≤ max 0 (F - v)
          · rw [nominal_of_le v F l hlM]
            exact h11 ⟨hl0, hlM⟩
          · simpa [nominal, not_lt_of_ge (le_of_not_ge hlM)] using h14 (lt_of_not_ge hlM)
        exact (nominal_antitone_nonpos v F l t hneg hl0.le hlt).trans_lt hleft
  · intro himp
    constructor
    · intro hpos
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨hl, hu⟩
        simpa [hzero] using himp 0 le_rfl hl hu
      · rintro ⟨hl, hM'⟩
        have h := himp l hl.le le_rfl hlu
        rwa [nominal_of_le v F l hM'] at h
      · rintro ⟨hu, hM'⟩
        have h := himp u hu hlu le_rfl
        rwa [nominal_of_le v F u hM'.le] at h
      · intro hu
        have h := himp u (hM.trans hu) hlu le_rfl
        simpa [nominal, not_lt_of_ge hu] using h
    · intro hneg
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨hl, hu⟩
        simpa [hzero] using himp 0 le_rfl hl hu
      · rintro ⟨hl, hM'⟩
        have h := himp l hl.le le_rfl hlu
        rwa [nominal_of_le v F l hM'] at h
      · intro hl
        have h := himp l (hM.trans hl.le) le_rfl hlu
        simpa [nominal, not_lt_of_ge hl.le] using h

set_option maxHeartbeats 4000000 in
-- Normalizing all scaled inequalities in the piecewise formula is expensive.
/-- Algebraic translation of the upper explicit cases for positive closing speed. -/
theorem upper_explicit_window (rp hp rv aup r h v w vup : ℝ)
    (ha : 0 < aup) (hrv : 0 < rv) :
    Uexpl rp hp rv aup r h v w vup ↔
      upperWindow (w * v) (max (w * vup) (w * v)) (aup * (r - rp) / rv)
        (aup * (r + rp) / rv) (2 * aup * (w * h - hp)) := by
  let k := rv / aup
  have hk : 0 < k := div_pos hrv ha
  have ha0 := ne_of_gt ha
  have hr0 := ne_of_gt hrv
  have htime (z : ℝ) : aup * z / rv = z / k := by dsimp [k]; field_simp
  have hshift (z : ℝ) : rv * z / aup = k * z := by dsimp [k]; ring
  have hquad (z : ℝ) :
      ((z / k) ^ 2 + 2 * (w * v) * (z / k) < 2 * aup * (w * h - hp)) ↔
      aup / 2 * z ^ 2 + w * rv * v * z + rv ^ 2 * hp < w * rv ^ 2 * h := by
    apply positive_scale_lt (rv ^ 2 / (2 * aup)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hline (z : ℝ) :
      (2 * max (w * vup) (w * v) * (z / k) - maxI v w vup ^ 2 <
        2 * aup * (w * h - hp)) ↔
      max (w * vup) (w * v) * z - rv * maxI v w vup ^ 2 / (2 * aup) + rv * hp <
        w * rv * h := by
    apply positive_scale_lt (rv / (2 * aup)) _ _ _ _ (by positivity)
    dsimp [k]
    field_simp
    ring
  have hM : max 0 (max (w * vup) (w * v) - w * v) = maxI v w vup := by
    unfold maxI
    rw [mul_sub]
    rcases le_total (w * vup) (w * v) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]
      simp
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  have hzero : (0 < 2 * aup * (w * h - hp)) ↔ hp < w * h := by
    rw [mul_pos_iff_of_pos_left (by positivity : 0 < 2 * aup), sub_pos]
  have h0u : (0 ≤ (r + rp) / k) ↔ -rp ≤ r := by
    rw [le_div_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have h0l : ((r - rp) / k ≤ 0) ↔ r ≤ rp := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have hposl : (0 < (r - rp) / k) ↔ rp < r := by
    rw [lt_div_iff₀ hk]
    constructor <;> intro hx <;> linarith
  have hl (z : ℝ) : ((r - rp) / k ≤ z) ↔ r ≤ rp + k * z := by
    rw [div_le_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hu (z : ℝ) : ((r + rp) / k < z) ↔ r < -rp + k * z := by
    rw [div_lt_iff₀ hk]
    constructor <;> intro hx <;> nlinarith
  have hur (z : ℝ) : (z ≤ (r + rp) / k) ↔ -rp + k * z ≤ r := by
    rw [← not_lt, hu, not_lt]
  have hlr (z : ℝ) : (z < (r - rp) / k) ↔ rp + k * z < r := by
    rw [← not_le, hl, not_le]
  unfold Uexpl upperWindow
  dsimp only
  rw [htime, htime, hM]
  simp only [hquad, hline, hzero, h0u, h0l, hposl, hl, hu,
    hur, hlr, hshift, hr0, false_or, false_and, and_comm]


theorem upper_nominal_eq (aup t hn v w vup : ℝ) (ha : 0 < aup) (hw : Sense w)
    (hA : Aup aup t hn v w vup) :
    2 * aup * (w * hn) = nominal (w * v) (max (w * vup) (w * v)) (aup * t) := by
  have hM : max 0 (max (w * vup) (w * v) - w * v) = max 0 (w * (vup - v)) := by
    rw [mul_sub]
    rcases le_total (w * vup) (w * v) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]
      simp
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  have hF : max (w * vup) (w * v) = w * v + max 0 (w * (vup - v)) := by
    rw [mul_sub]
    rcases le_total (w * v) (w * vup) with h | h
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rw [Aup_scaled aup t hn v w vup ha hw hA]
  unfold nominal upperGain
  rw [hM, hF]
  split_ifs <;> ring

theorem upper_implicit_window (rp hp rv aup r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hrv : 0 < rv) :
    Uimpl rp hp rv aup r h v w vup ↔
      ∀ t, 0 ≤ t → aup * (r - rp) / rv ≤ t → t ≤ aup * (r + rp) / rv →
        nominal (w * v) (max (w * vup) (w * v)) t < 2 * aup * (w * h - hp) := by
  have ha0 := ne_of_gt ha
  constructor
  · intro hsafe t ht hl hu
    obtain ⟨hn, hA⟩ := Aup_exists aup (t / aup) v w vup (div_nonneg ht ha.le)
    have hs := upper_nominal_eq aup (t / aup) hn v w vup ha hw hA
    rw [mul_div_cancel₀ _ ha0] at hs
    have hinside : |r - rv * (t / aup)| ≤ rp := by
      rw [abs_le]
      have hl' := (div_le_iff₀ hrv).mp hl
      have hu' := (le_div_iff₀ hrv).mp hu
      have heq : aup * (rv * (t / aup)) = rv * t := by field_simp
      constructor <;> nlinarith
    have hsep := (hsafe (t / aup) (rv * (t / aup)) hn ⟨rfl, hA⟩).resolve_left
      (not_lt_of_ge hinside)
    nlinarith
  · intro hsafe t rn hn ⟨hrn, hA⟩
    rw [hrn]
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      have hs := hsafe (aup * t) (mul_nonneg ha.le (Aup_time_nonneg _ _ _ _ _ _ ha hA))
        (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
      have hn := upper_nominal_eq aup t hn v w vup ha hw hA
      nlinarith
    · exact Or.inl (lt_of_not_ge hinside)

theorem upper_nominal_all_time (v F height : ℝ) :
    (∀ t, 0 ≤ t → nominal v F t < height) ↔ F ≤ 0 ∧ 0 < height := by
  have hM : 0 ≤ max 0 (F - v) := le_max_left 0 _
  have hzero : nominal v F 0 = 0 := by
    by_cases hm : max 0 (F - v) = 0
    · simp [nominal, hm]
    · simp [nominal, lt_of_le_of_ne hM (Ne.symm hm)]
  constructor
  · intro hs
    have hheight : 0 < height := by simpa [hzero] using hs 0 le_rfl
    have hF : F ≤ 0 := by
      by_contra h
      have hp : 0 < F := lt_of_not_ge h
      let M := max 0 (F - v)
      let t := max M ((height + M ^ 2) / (2 * F))
      have ht : 0 ≤ t := hM.trans (le_max_left _ _)
      have htM : M ≤ t := le_max_left _ _
      have htM' : max 0 (F - v) ≤ t := htM
      have hv : 2 * F * t - M ^ 2 < height := by
        simpa only [nominal, ite_eq_right (not_lt_of_ge htM')] using hs t ht
      have hb := (div_le_iff₀ (show 0 < 2 * F by positivity)).mp
        (le_max_right M ((height + M ^ 2) / (2 * F)))
      dsimp only [M] at hb
      nlinarith
    exact ⟨hF, hheight⟩
  · rintro ⟨hF, hheight⟩ t ht
    have h := nominal_antitone_nonpos v F 0 t (by linarith) le_rfl ht
    rw [hzero] at h
    exact h.trans_lt hheight

theorem upper_implicit_stationary (rp hp aup r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) :
    Uimpl rp hp 0 aup r h v w vup ↔
      rp < |r| ∨ (max (w * vup) (w * v) ≤ 0 ∧ hp < w * h) := by
  by_cases hsep : rp < |r|
  · simp only [hsep, true_or, iff_true]
    intro t rn hn ⟨hrn, _⟩
    left
    simpa [hrn] using hsep
  · have hzero : (0 < 2 * aup * (w * h - hp)) ↔ hp < w * h := by
      rw [mul_pos_iff_of_pos_left (by positivity : 0 < 2 * aup), sub_pos]
    rw [or_iff_right hsep, ← hzero]
    rw [← upper_nominal_all_time]
    constructor
    · intro hsafe t ht
      obtain ⟨hn, hA⟩ := Aup_exists aup (t / aup) v w vup (div_nonneg ht ha.le)
      have hs := upper_nominal_eq aup (t / aup) hn v w vup ha hw hA
      rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hs
      have hval := (hsafe (t / aup) 0 hn ⟨by ring, hA⟩).resolve_left (by simpa using hsep)
      nlinarith
    · intro hs t rn hn ⟨hrn, hA⟩
      right
      have hval := hs (aup * t) (mul_nonneg ha.le (Aup_time_nonneg _ _ _ _ _ _ ha hA))
      have hn := upper_nominal_eq aup t hn v w vup ha hw hA
      nlinarith

theorem upper_explicit_stationary (rp hp aup r h v w vup : ℝ) :
    Uexpl rp hp 0 aup r h v w vup ↔
      rp < |r| ∨ (max (w * vup) (w * v) ≤ 0 ∧ hp < w * h) := by
  simp only [Uexpl, zero_mul, mul_zero, zero_div, sub_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), true_or, true_and]
  have himpossible₁ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  have himpossible₂ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [himpossible₁, himpossible₂, false_implies, true_and, implies_true]
  by_cases hleft : r < -rp
  · have hsep : rp < |r| := (neg_le_abs r).trans_lt' (by linarith)
    simp [not_le.mpr hleft, hsep]
  · by_cases hright : rp < r
    · have hsep : rp < |r| := hright.trans_le (le_abs_self r)
      simp [hright, not_le.mpr hright, hsep]
    · have hinside : |r| ≤ rp := abs_le.mpr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      by_cases hF : 0 < max (w * vup) (w * v)
      · have hprod : ¬ max (w * vup) (w * v) * (r + rp) < 0 :=
          not_lt_of_ge (mul_nonneg hF.le (by linarith))
        simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, not_le_of_gt hF, hprod]
      · simp [le_of_not_gt hleft, le_of_not_gt hright, hright, not_lt_of_ge hinside,
          hF, le_of_not_gt hF]

/-- STTT17 Lemma 3: the explicit and implicit two-sided safe regions agree. -/
theorem two_sided_regions_equivalent :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
        (Cexpl rp hp rv alo aup r h v w vlo vup ↔
          Cimpl rp hp rv alo aup r h v w vlo vup) := by
  intro rp hp rv alo aup r h v w vlo vup hb ha hw
  have haup : 0 < aup := hb.2.2.2.trans_le ha
  have hupper : Uexpl rp hp rv aup r h v w vup ↔ Uimpl rp hp rv aup r h v w vup := by
    by_cases hr : rv = 0
    · subst rv
      exact (upper_explicit_stationary rp hp aup r h v w vup).trans
        (upper_implicit_stationary rp hp aup r h v w vup haup hw).symm
    · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
      rw [upper_explicit_window rp hp rv aup r h v w vup haup hr,
        upper_implicit_window rp hp rv aup r h v w vup haup hw hr]
      exact upper_window_equivalent _ _ _ _ _ (le_max_right _ _) (by
        apply div_le_div_of_nonneg_right _ hr.le
        exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) haup.le)
  exact or_congr (immediate_regions_equivalent rp hp rv alo r h v w vlo hb hw) hupper


/-- Bounded lower-bound cases in acceleration-scaled time coordinates, for `0 ≤ T`. -/
def boundedLowerWindow (v target T l u height : ℝ) : Prop :=
  let c := -(min 0 v)
  let M := max 0 (target - v)
  ((0 ≤ target →
    ((0 ≤ u ∧ u < c ∧ u ≤ T) → height < u ^ 2 + 2 * v * u) ∧
    ((c ≤ u ∧ l ≤ c ∧ c ≤ T) → height < -(min 0 v) ^ 2) ∧
    ((c < l ∧ l ≤ M ∧ l ≤ T) → height < l ^ 2 + 2 * v * l) ∧
    ((M < l ∧ l ≤ T) → height < 2 * target * l - M ^ 2)) ∧
  (target < 0 →
    ((0 ≤ u ∧ u < M ∧ u ≤ T) → height < u ^ 2 + 2 * v * u) ∧
    ((M ≤ u ∧ u < T) → height < 2 * target * u - M ^ 2))) ∧
  ((l ≤ T ∧ T ≤ u) → height < nominal v target T)

theorem bounded_lower_window_equivalent (v target T l u height : ℝ) (hT : 0 ≤ T) (hlu : l ≤ u) :
    boundedLowerWindow v target T l u height ↔
      ∀ t, 0 ≤ t → t ≤ T → l ≤ t → t ≤ u → height < nominal v target t := by
  have hc0 : 0 ≤ -(min 0 v) := neg_nonneg.mpr (min_le_left 0 v)
  have hM0 : 0 ≤ max 0 (target - v) := le_max_left 0 _
  constructor
  · rintro ⟨⟨hpos, hneg⟩, hend⟩ t ht htT hlt htu
    rcases le_or_gt 0 target with hF | hF
    · obtain ⟨h1, h2, h3, h4⟩ := hpos hF
      by_cases hu : min u T < -(min 0 v)
      · have htu' : t ≤ min u T := le_min htu htT
        by_cases huT : u ≤ T
        · rw [min_eq_left huT] at hu htu'
          have hval := h1 ⟨ht.trans htu, hu, huT⟩
          rw [← nominal_of_le v target u (hu.le.trans (vertex_le_switch v target hF))] at hval
          exact hval.trans_le (nominal_left_min v target t u hF ht htu' hu.le)
        · rw [min_eq_right (le_of_not_ge huT)] at hu htu'
          have hval := hend ⟨hlt.trans htT, le_of_not_ge huT⟩
          exact hval.trans_le (nominal_left_min v target t T hF ht htu' hu.le)
      · by_cases hl : l ≤ -(min 0 v)
        · have hc : -(min 0 v) ≤ min u T := le_of_not_gt hu
          exact (h2 ⟨hc.trans (min_le_left u T), hl, hc.trans (min_le_right u T)⟩).trans_le
            (nominal_global_min v target t hF ht)
        · by_cases hM : l ≤ max 0 (target - v)
          · have hval := h3 ⟨lt_of_not_ge hl, hM, hlt.trans htT⟩
            rw [← nominal_of_le v target l hM] at hval
            exact hval.trans_le (nominal_right_min v target l t hF
              (hc0.trans (le_of_not_ge hl)) (le_of_not_ge hl) hM hlt)
          · have hval := h4 ⟨lt_of_not_ge hM, hlt.trans htT⟩
            have heq : nominal v target l = 2 * target * l - max 0 (target - v) ^ 2 := by
              simp [nominal, not_lt_of_ge (le_of_not_ge hM)]
            rw [← heq] at hval
            exact hval.trans_le (nominal_linear_min v target l t hF (le_of_not_ge hM) hlt)
    · obtain ⟨h5, h6⟩ := hneg hF
      by_cases huT : u < T
      · have hval : height < nominal v target u := by
          by_cases huM : u < max 0 (target - v)
          · simpa [nominal, huM] using h5 ⟨ht.trans htu, huM, huT.le⟩
          · simpa [nominal, huM] using h6 ⟨le_of_not_gt huM, huT⟩
        exact hval.trans_le (nominal_antitone v target t u hF ht htu)
      · have hval := hend ⟨hlt.trans htT, le_of_not_gt huT⟩
        exact hval.trans_le (nominal_antitone v target t T hF ht htT)
  · intro himp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hF
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨hu0, huc, huT⟩
        have hx := himp u hu0 huT hlu le_rfl
        rwa [nominal_of_le v target u (huc.le.trans (vertex_le_switch v target hF))] at hx
      · rintro ⟨hcu, hlc, hcT⟩
        have hx := himp (-(min 0 v)) hc0 hcT hlc hcu
        rwa [nominal_at_vertex v target hF] at hx
      · rintro ⟨hcl, hlM, hlT⟩
        have hx := himp l (hc0.trans hcl.le) hlT le_rfl hlu
        rwa [nominal_of_le v target l hlM] at hx
      · rintro ⟨hMl, hlT⟩
        have hx := himp l (hM0.trans hMl.le) hlT le_rfl hlu
        simpa [nominal, not_lt_of_ge hMl.le] using hx
    · intro hF
      refine ⟨?_, ?_⟩
      · rintro ⟨hu0, huM, huT⟩
        simpa [nominal, huM] using himp u hu0 huT hlu le_rfl
      · rintro ⟨hMu, huT⟩
        simpa [nominal, not_lt_of_ge hMu] using himp u (hM0.trans hMu) huT.le hlu le_rfl
    · rintro ⟨hlT, hTu⟩
      exact himp T hT le_rfl hlT hTu

theorem bound15_iff_nominal (hp alo tl h v w vlo : ℝ) (ha : 0 < alo) :
    bound15 hp alo tl h v w vlo ↔
      2 * alo * (w * h + hp) < nominal (w * v) (w * vlo) (alo * tl) := by
  have h1 : (tl < maxI v w vlo / alo) ↔ (alo * tl < max 0 (w * vlo - w * v)) := by
    rw [lt_div_iff₀ ha, mul_comm, maxI, mul_sub]
  have h2 : (maxI v w vlo / alo ≤ tl) ↔ ¬(alo * tl < max 0 (w * vlo - w * v)) := by
    rw [← not_lt, h1]
  have hq : (w * h < alo / 2 * tl ^ 2 + w * v * tl - hp) ↔
      (2 * alo * (w * h + hp) < (alo * tl) ^ 2 + 2 * (w * v) * (alo * tl)) := by
    apply positive_scale_lt (2 * alo) _ _ _ _ (by positivity)
    field_simp
    ring
  have hl : (w * h < w * vlo * tl - maxI v w vlo ^ 2 / (2 * alo) - hp) ↔
      (2 * alo * (w * h + hp) < 2 * (w * vlo) * (alo * tl) - max 0 (w * vlo - w * v) ^ 2) := by
    have hM : maxI v w vlo = max 0 (w * vlo - w * v) := by unfold maxI; rw [mul_sub]
    rw [hM]
    apply positive_scale_lt (2 * alo) _ _ _ _ (by positivity)
    field_simp
    ring
  unfold bound15 nominal
  rw [h1, h2, hq, hl]
  by_cases hs : alo * tl < max 0 (w * vlo - w * v) <;> simp [hs]

theorem explicit_bounded_lower_window (rp hp rv alo tl r h v w vlo : ℝ)
    (ha : 0 < alo) (hrv : 0 < rv) (htl : 0 ≤ tl) :
    LexplBoundedHat rp hp rv alo tl r h v w vlo ↔
      boundedLowerWindow (w * v) (w * vlo) (alo * tl) (alo * (r - rp) / rv)
        (alo * (r + rp) / rv) (2 * alo * (w * h + hp)) := by
  let k := rv / alo
  have hk : 0 < k := div_pos hrv ha
  have ha0 := ne_of_gt ha
  have hr0 := ne_of_gt hrv
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  have htime (z : ℝ) : alo * z / rv = z / k := by dsimp [k]; field_simp
  have hshift (z : ℝ) : rv * z / alo = k * z := by dsimp [k]; ring
  have hquad (z : ℝ) :
      (2 * alo * (w * h + hp) < (z / k) ^ 2 + 2 * (w * v) * (z / k)) ↔
      w * rv ^ 2 * h < alo / 2 * z ^ 2 + w * rv * v * z - rv ^ 2 * hp := by
    apply positive_scale_lt (rv ^ 2 / (2 * alo)) _ _ _ _ (by positivity)
    dsimp [k]; field_simp; ring
  have hline (z : ℝ) :
      (2 * alo * (w * h + hp) < 2 * (w * vlo) * (z / k) - maxI v w vlo ^ 2) ↔
      w * rv * h < w * vlo * z - rv * maxI v w vlo ^ 2 / (2 * alo) - rv * hp := by
    apply positive_scale_lt (rv / (2 * alo)) _ _ _ _ (by positivity)
    dsimp [k]; field_simp; ring
  have hvertex :
      (2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) ↔
      w * h < -(min 0 (w * v)) ^ 2 / (2 * alo) - hp := by
    apply positive_scale_lt (1 / (2 * alo)) _ _ _ _ (by positivity)
    field_simp; ring
  have hM : max 0 (w * vlo - w * v) = maxI v w vlo := by unfold maxI; rw [mul_sub]
  have h0 : (0 ≤ (r + rp) / k) ↔ -rp ≤ r := by
    rw [le_div_iff₀ hk]; constructor <;> intro hx <;> linarith
  have hu (z : ℝ) : ((r + rp) / k ≤ z) ↔ r ≤ -rp + k * z := by
    rw [div_le_iff₀ hk]; constructor <;> intro hx <;> nlinarith
  have hul (z : ℝ) : ((r + rp) / k < z) ↔ r < -rp + k * z := by
    rw [div_lt_iff₀ hk]; constructor <;> intro hx <;> nlinarith
  have hl (z : ℝ) : ((r - rp) / k ≤ z) ↔ r ≤ rp + k * z := by
    rw [div_le_iff₀ hk]; constructor <;> intro hx <;> nlinarith
  have hur (z : ℝ) : (z ≤ (r + rp) / k) ↔ -rp + k * z ≤ r := by
    rw [← not_lt, hul, not_lt]
  have hlr (z : ℝ) : (z < (r - rp) / k) ↔ rp + k * z < r := by
    rw [← not_le, hl, not_le]
  have hcT : (-(min 0 (w * v)) ≤ alo * tl) ↔ -(min 0 (w * v)) / alo ≤ tl := by
    rw [div_le_iff₀ ha, mul_comm tl alo]
  have hkT : k * (alo * tl) = rv * tl := by dsimp [k]; field_simp
  have hhor : horizonCase rp rv tl r ↔
      ((r - rp) / k ≤ alo * tl ∧ alo * tl ≤ (r + rp) / k) := by
    unfold horizonCase
    rw [hl (alo * tl), hur (alo * tl), hkT, and_iff_right htl, and_comm]
  unfold LexplBoundedHat LexplBounded boundedLowerWindow
  dsimp only
  rw [bound15_iff_nominal hp alo tl h v w vlo ha, hhor, htime, htime, hM]
  simp only [htl_neg, false_or, hquad, hline, hvertex, h0, hu, hul, hl,
    hur, hlr, hcT, hkT, hshift, hr0, false_and, mul_neg, ← sub_eq_add_neg, and_assoc]

theorem implicit_bounded_lower_window (rp hp rv alo tl r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (hrv : 0 < rv) (htl : 0 ≤ tl) :
    LimplBounded rp hp rv alo tl 0 r h v w vlo ↔
      ∀ t, 0 ≤ t → t ≤ alo * tl → alo * (r - rp) / rv ≤ t → t ≤ alo * (r + rp) / rv →
        2 * alo * (w * h + hp) < nominal (w * v) (w * vlo) t := by
  have ha0 := ne_of_gt ha
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  constructor
  · intro hsafe t ht htT hl hu
    obtain ⟨hn, hA⟩ := A_exists alo (t / alo) v w vlo (div_nonneg ht ha.le)
    have hs := A_nominal alo (t / alo) hn v w vlo ha hw hA
    rw [mul_div_cancel₀ _ ha0] at hs
    have hinside : |r - rv * (t / alo)| ≤ rp := by
      rw [abs_le]
      have hl' := (div_le_iff₀ hrv).mp hl
      have hu' := (le_div_iff₀ hrv).mp hu
      have heq : alo * (rv * (t / alo)) = rv * t := by field_simp
      constructor <;> nlinarith
    have htle : t / alo ≤ tl - 0 := by
      rw [sub_zero, div_le_iff₀ ha]; linarith
    have hsep := (hsafe (t / alo) (rv * (t / alo)) hn ⟨Or.inl htle, rfl, hA⟩).resolve_left
      (not_lt_of_ge hinside)
    nlinarith
  · intro hsafe t rn hn ⟨ht, hrn, hA⟩
    rw [hrn]
    have ht' : t ≤ tl := by simpa [htl_neg] using ht
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      have hs := hsafe (alo * t) (mul_nonneg ha.le (A_time_nonneg _ _ _ _ _ _ ha hA))
        (mul_le_mul_of_nonneg_left ht' ha.le)
        (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
      have hn := A_nominal alo t hn v w vlo ha hw hA
      nlinarith
    · exact Or.inl (lt_of_not_ge hinside)

theorem nominal_bounded_time (v target T height : ℝ) (hT : 0 ≤ T) :
    (∀ t, 0 ≤ t → t ≤ T → height < nominal v target t) ↔
      ((0 ≤ target ∧ -(min 0 v) ≤ T → height < -(min 0 v) ^ 2) ∧
        height < nominal v target T) := by
  have hc0 : 0 ≤ -(min 0 v) := neg_nonneg.mpr (min_le_left 0 v)
  constructor
  · intro hs
    refine ⟨?_, hs T hT le_rfl⟩
    rintro ⟨hF, hcT⟩
    have hx := hs (-(min 0 v)) hc0 hcT
    rwa [nominal_at_vertex v target hF] at hx
  · rintro ⟨hmin, hend⟩ t ht htT
    rcases le_or_gt 0 target with hF | hF
    · by_cases hcT : -(min 0 v) ≤ T
      · exact (hmin ⟨hF, hcT⟩).trans_le (nominal_global_min v target t hF ht)
      · exact hend.trans_le (nominal_left_min v target t T hF ht htT (le_of_not_ge hcT))
    · exact hend.trans_le (nominal_antitone v target t T hF ht htT)

theorem implicit_bounded_lower_stationary (rp hp alo tl r h v w vlo : ℝ)
    (ha : 0 < alo) (hw : Sense w) (htl : 0 ≤ tl) :
    LimplBounded rp hp 0 alo tl 0 r h v w vlo ↔
      rp < |r| ∨
        ((0 ≤ w * vlo ∧ -(min 0 (w * v)) ≤ alo * tl →
            2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) ∧
          2 * alo * (w * h + hp) < nominal (w * v) (w * vlo) (alo * tl)) := by
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  by_cases hsep : rp < |r|
  · simp only [hsep, true_or, iff_true]
    intro t rn hn ⟨_, hrn, _⟩
    left
    simpa [hrn] using hsep
  · rw [or_iff_right hsep, ← nominal_bounded_time _ _ _ _ (mul_nonneg ha.le htl)]
    constructor
    · intro hsafe t ht htT
      obtain ⟨hn, hA⟩ := A_exists alo (t / alo) v w vlo (div_nonneg ht ha.le)
      have hs := A_nominal alo (t / alo) hn v w vlo ha hw hA
      rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hs
      have htle : t / alo ≤ tl - 0 := by rw [sub_zero, div_le_iff₀ ha]; linarith
      have hval := (hsafe (t / alo) 0 hn ⟨Or.inl htle, by ring, hA⟩).resolve_left
        (by simpa using hsep)
      nlinarith
    · intro hs t rn hn ⟨ht, hrn, hA⟩
      right
      have ht' : t ≤ tl := by simpa [htl_neg] using ht
      have hval := hs (alo * t) (mul_nonneg ha.le (A_time_nonneg _ _ _ _ _ _ ha hA))
        (mul_le_mul_of_nonneg_left ht' ha.le)
      have hn := A_nominal alo t hn v w vlo ha hw hA
      nlinarith

theorem explicit_bounded_lower_stationary (rp hp alo tl r h v w vlo : ℝ)
    (ha : 0 < alo) (htl : 0 ≤ tl) :
    LexplBoundedHat rp hp 0 alo tl r h v w vlo ↔
      rp < |r| ∨
        ((0 ≤ w * vlo ∧ -(min 0 (w * v)) ≤ alo * tl →
            2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2) ∧
          2 * alo * (w * h + hp) < nominal (w * v) (w * vlo) (alo * tl)) := by
  have hm : (w * h < -(min 0 (w * v)) ^ 2 / (2 * alo) - hp) ↔
      2 * alo * (w * h + hp) < -(min 0 (w * v)) ^ 2 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity : 0 < 2 * alo)]
    constructor <;> intro hx <;> nlinarith
  have hcT : (-(min 0 (w * v)) / alo ≤ tl) ↔ -(min 0 (w * v)) ≤ alo * tl := by
    rw [div_le_iff₀ ha, mul_comm tl alo]
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  unfold LexplBoundedHat
  rw [bound15_iff_nominal hp alo tl h v w vlo ha]
  simp only [LexplBounded, horizonCase, htl, htl_neg, zero_mul, mul_zero, zero_div, sub_zero,
    add_zero, zero_pow (by decide : 2 ≠ 0), true_or, false_or, true_and, hm, hcT]
  have himp₁ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  have himp₂ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [himp₁, himp₂, false_and, false_implies, true_and]
  by_cases hleft : r < -rp
  · have hsep : rp < |r| := (neg_le_abs r).trans_lt' (by linarith)
    simp [not_le.mpr hleft, hsep]
  · by_cases hright : rp < r
    · have hsep : rp < |r| := hright.trans_le (le_abs_self r)
      simp [not_le.mpr hright, hsep]
    · have hinside : |r| ≤ rp := abs_le.mpr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      by_cases hF : 0 ≤ w * vlo
      · simp [le_of_not_gt hleft, le_of_not_gt hright, not_lt_of_ge hinside,
          hF, not_lt_of_ge hF]
      · simp [le_of_not_gt hleft, le_of_not_gt hright, not_lt_of_ge hinside,
          hF, lt_of_not_ge hF]

/-- Lower component needed for STTT17 Lemma 4. -/
theorem lower_bounded_regions_equivalent :
    ∀ rp hp rv alo tl r h v w vlo,
      Bounds rp hp rv alo → Sense w →
        (LexplBoundedHat rp hp rv alo tl r h v w vlo ↔
          LimplBounded rp hp rv alo tl 0 r h v w vlo) := by
  intro rp hp rv alo tl r h v w vlo hb hw
  rcases lt_or_ge tl 0 with htl | htl
  · have hexpl : LexplBoundedHat rp hp rv alo tl r h v w vlo ↔
        Lexpl rp hp rv alo r h v w vlo := by
      simp [LexplBoundedHat, LexplBounded, Lexpl, horizonCase, htl, not_le.mpr htl]
    have himpl : LimplBounded rp hp rv alo tl 0 r h v w vlo ↔
        Limpl rp hp rv alo r h v w vlo := by
      simp [LimplBounded, Limpl, htl]
    rw [hexpl, himpl]
    exact immediate_regions_equivalent rp hp rv alo r h v w vlo hb hw
  · by_cases hr : rv = 0
    · subst rv
      exact (explicit_bounded_lower_stationary rp hp alo tl r h v w vlo hb.2.2.2 htl).trans
        (implicit_bounded_lower_stationary rp hp alo tl r h v w vlo hb.2.2.2 hw htl).symm
    · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
      rw [explicit_bounded_lower_window rp hp rv alo tl r h v w vlo hb.2.2.2 hr htl,
        implicit_bounded_lower_window rp hp rv alo tl r h v w vlo hb.2.2.2 hw hr htl]
      exact bounded_lower_window_equivalent _ _ _ _ _ _ (mul_nonneg hb.2.2.2.le htl) (by
        apply div_le_div_of_nonneg_right _ hr.le
        exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) hb.2.2.2.le)

/-- Bounded upper-bound cases in acceleration-scaled time coordinates, for `0 ≤ T`. -/
def boundedUpperWindow (v F T l u height : ℝ) : Prop :=
  let M := max 0 (F - v)
  ((0 < F →
    ((l ≤ 0 ∧ 0 ≤ u) → 0 < height) ∧
    ((0 < l ∧ l ≤ M ∧ l ≤ T) → l ^ 2 + 2 * v * l < height) ∧
    ((0 ≤ u ∧ u < M ∧ u ≤ T) → u ^ 2 + 2 * v * u < height) ∧
    ((M ≤ u ∧ u < T) → 2 * F * u - M ^ 2 < height)) ∧
  (F ≤ 0 →
    ((l ≤ 0 ∧ 0 ≤ u) → 0 < height) ∧
    ((0 < l ∧ l ≤ M ∧ l ≤ T) → l ^ 2 + 2 * v * l < height) ∧
    ((M < l ∧ l ≤ T) → 2 * F * l - M ^ 2 < height))) ∧
  ((l ≤ T ∧ T ≤ u) → nominal v F T < height)

theorem bounded_upper_window_equivalent (v F T l u height : ℝ)
    (hF : v ≤ F) (hT : 0 ≤ T) (hlu : l ≤ u) :
    boundedUpperWindow v F T l u height ↔
      ∀ t, 0 ≤ t → t ≤ T → l ≤ t → t ≤ u → nominal v F t < height := by
  have hM : 0 ≤ max 0 (F - v) := le_max_left 0 _
  have hzero : nominal v F 0 = 0 := by
    by_cases hm : max 0 (F - v) = 0
    · simp [nominal, hm]
    · simp [nominal, lt_of_le_of_ne hM (Ne.symm hm)]
  constructor
  · rintro ⟨⟨hpos, hneg⟩, hend⟩ t ht htT hlt htu
    have htu' : t ≤ min u T := le_min htu htT
    rcases lt_or_ge 0 F with hFp | hFn
    · obtain ⟨h10, h11, h12, h13⟩ := hpos hFp
      have hright : nominal v F (min u T) < height := by
        by_cases huT : u < T
        · rw [min_eq_left huT.le]
          by_cases huM : u < max 0 (F - v)
          · have hx := h12 ⟨ht.trans htu, huM, huT.le⟩
            rwa [nominal_of_le v F u huM.le]
          · have hx := h13 ⟨le_of_not_gt huM, huT⟩
            simpa [nominal, not_lt_of_ge (le_of_not_gt huM)] using hx
        · rw [min_eq_right (le_of_not_gt huT)]
          exact hend ⟨hlt.trans htT, le_of_not_gt huT⟩
      by_cases hl : l ≤ 0
      · have hleft : nominal v F 0 < height := by simpa [hzero] using h10 ⟨hl, ht.trans htu⟩
        exact (upper_nominal_endpoints v F 0 t (min u T) hF le_rfl ht htu').trans_lt
          (max_lt hleft hright)
      · have hl0 : 0 < l := lt_of_not_ge hl
        by_cases hlM : l ≤ max 0 (F - v)
        · have hleft : nominal v F l < height := by
            rw [nominal_of_le v F l hlM]
            exact h11 ⟨hl0, hlM, hlt.trans htT⟩
          exact (upper_nominal_endpoints v F l t (min u T) hF hl0.le hlt htu').trans_lt
            (max_lt hleft hright)
        · have hleft : nominal v F l < height := by
            have hle : nominal v F l ≤ nominal v F (min u T) := by
              have hlmin : l ≤ min u T := hlt.trans htu'
              simp only [nominal, ite_eq_right (not_lt_of_ge (le_of_not_ge hlM)),
                ite_eq_right (not_lt_of_ge ((le_of_not_ge hlM).trans hlmin))]
              nlinarith [mul_nonneg hFp.le (sub_nonneg.mpr hlmin)]
            exact hle.trans_lt hright
          exact (upper_nominal_endpoints v F l t (min u T) hF hl0.le hlt htu').trans_lt
            (max_lt hleft hright)
    · obtain ⟨h10, h11, h14⟩ := hneg hFn
      by_cases hl : l ≤ 0
      · have hleft : nominal v F 0 < height := by simpa [hzero] using h10 ⟨hl, ht.trans htu⟩
        exact (nominal_antitone_nonpos v F 0 t hFn le_rfl ht).trans_lt hleft
      · have hl0 : 0 < l := lt_of_not_ge hl
        have hleft : nominal v F l < height := by
          by_cases hlM : l ≤ max 0 (F - v)
          · rw [nominal_of_le v F l hlM]
            exact h11 ⟨hl0, hlM, hlt.trans htT⟩
          · simpa [nominal, not_lt_of_ge (le_of_not_ge hlM)] using
              h14 ⟨lt_of_not_ge hlM, hlt.trans htT⟩
        exact (nominal_antitone_nonpos v F l t hFn hl0.le hlt).trans_lt hleft
  · intro himp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hpos
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨hl, hu⟩
        simpa [hzero] using himp 0 le_rfl hT hl hu
      · rintro ⟨hl, hlM, hlT⟩
        have h := himp l hl.le hlT le_rfl hlu
        rwa [nominal_of_le v F l hlM] at h
      · rintro ⟨hu, huM, huT⟩
        have h := himp u hu huT hlu le_rfl
        rwa [nominal_of_le v F u huM.le] at h
      · rintro ⟨hMu, huT⟩
        have h := himp u (hM.trans hMu) huT.le hlu le_rfl
        simpa [nominal, not_lt_of_ge hMu] using h
    · intro hneg
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨hl, hu⟩
        simpa [hzero] using himp 0 le_rfl hT hl hu
      · rintro ⟨hl, hlM, hlT⟩
        have h := himp l hl.le hlT le_rfl hlu
        rwa [nominal_of_le v F l hlM] at h
      · rintro ⟨hMl, hlT⟩
        have h := himp l (hM.trans hMl.le) hlT le_rfl hlu
        simpa [nominal, not_lt_of_ge hMl.le] using h
    · rintro ⟨hlT, hTu⟩
      exact himp T hT le_rfl hlT hTu

theorem bound16_iff_nominal (hp aup tl h v w vup : ℝ) (ha : 0 < aup) :
    bound16 hp aup tl h v w vup ↔
      nominal (w * v) (max (w * vup) (w * v)) (aup * tl) < 2 * aup * (w * h - hp) := by
  have hM : max 0 (max (w * vup) (w * v) - w * v) = maxI v w vup := by
    unfold maxI
    rw [mul_sub]
    rcases le_total (w * vup) (w * v) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; simp
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  have h1 : (tl < maxI v w vup / aup) ↔ (aup * tl < max 0 (max (w * vup) (w * v) - w * v)) := by
    rw [lt_div_iff₀ ha, mul_comm, hM]
  have h2 : (maxI v w vup / aup ≤ tl) ↔ ¬(aup * tl < max 0 (max (w * vup) (w * v) - w * v)) := by
    rw [← not_lt, h1]
  have hq : (aup / 2 * tl ^ 2 + w * v * tl + hp < w * h) ↔
      ((aup * tl) ^ 2 + 2 * (w * v) * (aup * tl) < 2 * aup * (w * h - hp)) := by
    apply positive_scale_lt (2 * aup) _ _ _ _ (by positivity)
    field_simp
    ring
  have hl : (max (w * vup) (w * v) * tl - maxI v w vup ^ 2 / (2 * aup) + hp < w * h) ↔
      (2 * max (w * vup) (w * v) * (aup * tl) - max 0 (max (w * vup) (w * v) - w * v) ^ 2 <
        2 * aup * (w * h - hp)) := by
    rw [hM]
    apply positive_scale_lt (2 * aup) _ _ _ _ (by positivity)
    field_simp
    ring
  unfold bound16 nominal
  rw [h1, h2, hq, hl]
  by_cases hs : aup * tl < max 0 (max (w * vup) (w * v) - w * v)
  · simp only [hs, not_true_eq_false, ite_true, true_implies, false_implies, and_true]
  · simp only [hs, not_false_eq_true, ite_false, true_implies, false_implies, true_and]

theorem explicit_bounded_upper_window (rp hp rv aup tl r h v w vup : ℝ)
    (ha : 0 < aup) (hrv : 0 < rv) (htl : 0 ≤ tl) :
    UexplBoundedHat rp hp rv aup tl r h v w vup ↔
      boundedUpperWindow (w * v) (max (w * vup) (w * v)) (aup * tl) (aup * (r - rp) / rv)
        (aup * (r + rp) / rv) (2 * aup * (w * h - hp)) := by
  let k := rv / aup
  have hk : 0 < k := div_pos hrv ha
  have ha0 := ne_of_gt ha
  have hr0 := ne_of_gt hrv
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  have htime (z : ℝ) : aup * z / rv = z / k := by dsimp [k]; field_simp
  have hshift (z : ℝ) : rv * z / aup = k * z := by dsimp [k]; ring
  have hquad (z : ℝ) :
      ((z / k) ^ 2 + 2 * (w * v) * (z / k) < 2 * aup * (w * h - hp)) ↔
      aup / 2 * z ^ 2 + w * rv * v * z + rv ^ 2 * hp < w * rv ^ 2 * h := by
    apply positive_scale_lt (rv ^ 2 / (2 * aup)) _ _ _ _ (by positivity)
    dsimp [k]; field_simp; ring
  have hline (z : ℝ) :
      (2 * max (w * vup) (w * v) * (z / k) - maxI v w vup ^ 2 <
        2 * aup * (w * h - hp)) ↔
      max (w * vup) (w * v) * z - rv * maxI v w vup ^ 2 / (2 * aup) + rv * hp <
        w * rv * h := by
    apply positive_scale_lt (rv / (2 * aup)) _ _ _ _ (by positivity)
    dsimp [k]; field_simp; ring
  have hM : max 0 (max (w * vup) (w * v) - w * v) = maxI v w vup := by
    unfold maxI
    rw [mul_sub]
    rcases le_total (w * vup) (w * v) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h)]; simp
    · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  have hzero : (0 < 2 * aup * (w * h - hp)) ↔ hp < w * h := by
    rw [mul_pos_iff_of_pos_left (by positivity : 0 < 2 * aup), sub_pos]
  have h0lu : (r ≤ rp + k * 0 ∧ -rp ≤ r) ↔ (-rp ≤ r ∧ r ≤ rp) := by
    rw [mul_zero, add_zero, and_comm]
  have h0u : (0 ≤ (r + rp) / k) ↔ -rp ≤ r := by
    rw [le_div_iff₀ hk]; constructor <;> intro hx <;> linarith
  have hposl : (0 < (r - rp) / k) ↔ rp < r := by
    rw [lt_div_iff₀ hk]; constructor <;> intro hx <;> linarith
  have hl (z : ℝ) : ((r - rp) / k ≤ z) ↔ r ≤ rp + k * z := by
    rw [div_le_iff₀ hk]; constructor <;> intro hx <;> nlinarith
  have hu (z : ℝ) : ((r + rp) / k ≤ z) ↔ r ≤ -rp + k * z := by
    rw [div_le_iff₀ hk]; constructor <;> intro hx <;> nlinarith
  have hul (z : ℝ) : ((r + rp) / k < z) ↔ r < -rp + k * z := by
    rw [div_lt_iff₀ hk]; constructor <;> intro hx <;> nlinarith
  have hur (z : ℝ) : (z ≤ (r + rp) / k) ↔ -rp + k * z ≤ r := by
    rw [← not_lt, hul, not_lt]
  have hlr (z : ℝ) : (z < (r - rp) / k) ↔ rp + k * z < r := by
    rw [← not_le, hl, not_le]
  have hkT : k * (aup * tl) = rv * tl := by dsimp [k]; field_simp
  have hhor : horizonCase rp rv tl r ↔
      ((r - rp) / k ≤ aup * tl ∧ aup * tl ≤ (r + rp) / k) := by
    unfold horizonCase
    rw [hl (aup * tl), hur (aup * tl), hkT, and_iff_right htl, and_comm]
  unfold UexplBoundedHat UexplBounded boundedUpperWindow
  dsimp only
  rw [bound16_iff_nominal hp aup tl h v w vup ha, hhor, htime, htime, hM]
  simp only [htl_neg, false_or, hquad, hline, hzero, h0lu, h0u, hposl, hl, hu, hul,
    hur, hlr, hkT, hshift, hr0, false_and, and_assoc]

theorem implicit_bounded_upper_window (rp hp rv aup tl r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) (hrv : 0 < rv) (htl : 0 ≤ tl) :
    UimplBounded rp hp rv aup tl 0 r h v w vup ↔
      ∀ t, 0 ≤ t → t ≤ aup * tl → aup * (r - rp) / rv ≤ t → t ≤ aup * (r + rp) / rv →
        nominal (w * v) (max (w * vup) (w * v)) t < 2 * aup * (w * h - hp) := by
  have ha0 := ne_of_gt ha
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  constructor
  · intro hsafe t ht htT hl hu
    obtain ⟨hn, hA⟩ := Aup_exists aup (t / aup) v w vup (div_nonneg ht ha.le)
    have hs := upper_nominal_eq aup (t / aup) hn v w vup ha hw hA
    rw [mul_div_cancel₀ _ ha0] at hs
    have hinside : |r - rv * (t / aup)| ≤ rp := by
      rw [abs_le]
      have hl' := (div_le_iff₀ hrv).mp hl
      have hu' := (le_div_iff₀ hrv).mp hu
      have heq : aup * (rv * (t / aup)) = rv * t := by field_simp
      constructor <;> nlinarith
    have htle : t / aup ≤ tl - 0 := by
      rw [sub_zero, div_le_iff₀ ha]; linarith
    have hsep := (hsafe (t / aup) (rv * (t / aup)) hn ⟨Or.inl htle, rfl, hA⟩).resolve_left
      (not_lt_of_ge hinside)
    nlinarith
  · intro hsafe t rn hn ⟨ht, hrn, hA⟩
    rw [hrn]
    have ht' : t ≤ tl := by simpa [htl_neg] using ht
    by_cases hinside : |r - rv * t| ≤ rp
    · right
      obtain ⟨hl, hu⟩ := abs_le.mp hinside
      have hs := hsafe (aup * t) (mul_nonneg ha.le (Aup_time_nonneg _ _ _ _ _ _ ha hA))
        (mul_le_mul_of_nonneg_left ht' ha.le)
        (by rw [div_le_iff₀ hrv]; nlinarith)
        (by rw [le_div_iff₀ hrv]; nlinarith)
      have hn := upper_nominal_eq aup t hn v w vup ha hw hA
      nlinarith
    · exact Or.inl (lt_of_not_ge hinside)

theorem upper_nominal_bounded_time (v F T height : ℝ) (hF : v ≤ F) (hT : 0 ≤ T) :
    (∀ t, 0 ≤ t → t ≤ T → nominal v F t < height) ↔
      (0 < height ∧ nominal v F T < height) := by
  have hM : 0 ≤ max 0 (F - v) := le_max_left 0 _
  have hzero : nominal v F 0 = 0 := by
    by_cases hm : max 0 (F - v) = 0
    · simp [nominal, hm]
    · simp [nominal, lt_of_le_of_ne hM (Ne.symm hm)]
  constructor
  · intro hs
    exact ⟨by simpa [hzero] using hs 0 le_rfl hT, hs T hT le_rfl⟩
  · rintro ⟨h0, hT'⟩ t ht htT
    have hleft : nominal v F 0 < height := by simpa [hzero] using h0
    exact (upper_nominal_endpoints v F 0 t T hF le_rfl ht htT).trans_lt (max_lt hleft hT')

theorem implicit_bounded_upper_stationary (rp hp aup tl r h v w vup : ℝ)
    (ha : 0 < aup) (hw : Sense w) (htl : 0 ≤ tl) :
    UimplBounded rp hp 0 aup tl 0 r h v w vup ↔
      rp < |r| ∨
        (hp < w * h ∧
          nominal (w * v) (max (w * vup) (w * v)) (aup * tl) < 2 * aup * (w * h - hp)) := by
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  by_cases hsep : rp < |r|
  · simp only [hsep, true_or, iff_true]
    intro t rn hn ⟨_, hrn, _⟩
    left
    simpa [hrn] using hsep
  · have hzero : (0 < 2 * aup * (w * h - hp)) ↔ hp < w * h := by
      rw [mul_pos_iff_of_pos_left (by positivity : 0 < 2 * aup), sub_pos]
    rw [or_iff_right hsep, ← hzero,
      ← upper_nominal_bounded_time _ _ _ _ (le_max_right _ _) (mul_nonneg ha.le htl)]
    constructor
    · intro hsafe t ht htT
      obtain ⟨hn, hA⟩ := Aup_exists aup (t / aup) v w vup (div_nonneg ht ha.le)
      have hs := upper_nominal_eq aup (t / aup) hn v w vup ha hw hA
      rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hs
      have htle : t / aup ≤ tl - 0 := by rw [sub_zero, div_le_iff₀ ha]; linarith
      have hval := (hsafe (t / aup) 0 hn ⟨Or.inl htle, by ring, hA⟩).resolve_left
        (by simpa using hsep)
      nlinarith
    · intro hs t rn hn ⟨ht, hrn, hA⟩
      right
      have ht' : t ≤ tl := by simpa [htl_neg] using ht
      have hval := hs (aup * t) (mul_nonneg ha.le (Aup_time_nonneg _ _ _ _ _ _ ha hA))
        (mul_le_mul_of_nonneg_left ht' ha.le)
      have hn := upper_nominal_eq aup t hn v w vup ha hw hA
      nlinarith

theorem explicit_bounded_upper_stationary (rp hp aup tl r h v w vup : ℝ)
    (ha : 0 < aup) (htl : 0 ≤ tl) :
    UexplBoundedHat rp hp 0 aup tl r h v w vup ↔
      rp < |r| ∨
        (hp < w * h ∧
          nominal (w * v) (max (w * vup) (w * v)) (aup * tl) < 2 * aup * (w * h - hp)) := by
  have htl_neg : ¬(tl < 0) := not_lt_of_ge htl
  unfold UexplBoundedHat
  rw [bound16_iff_nominal hp aup tl h v w vup ha]
  simp only [UexplBounded, horizonCase, htl, htl_neg, zero_mul, mul_zero, zero_div, sub_zero,
    add_zero, zero_pow (by decide : 2 ≠ 0), true_or, false_or, true_and]
  have himp₁ : ¬(-rp ≤ r ∧ r < -rp) := by rintro ⟨h₁, h₂⟩; linarith
  have himp₂ : ¬(rp < r ∧ r ≤ rp) := by rintro ⟨h₁, h₂⟩; linarith
  simp only [himp₁, himp₂, false_and, false_implies, true_and, implies_true]
  by_cases hleft : r < -rp
  · have hsep : rp < |r| := (neg_le_abs r).trans_lt' (by linarith)
    simp [not_le.mpr hleft, hsep]
  · by_cases hright : rp < r
    · have hsep : rp < |r| := hright.trans_le (le_abs_self r)
      simp [not_le.mpr hright, hsep]
    · have hinside : |r| ≤ rp := abs_le.mpr ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
      by_cases hF : 0 < max (w * vup) (w * v)
      · simp [le_of_not_gt hleft, le_of_not_gt hright, not_lt_of_ge hinside,
          hF, not_le_of_gt hF]
      · simp [le_of_not_gt hleft, le_of_not_gt hright, not_lt_of_ge hinside,
          hF, le_of_not_gt hF]

/-- Upper component needed for STTT17 Lemma 4. -/
theorem upper_bounded_regions_equivalent :
    ∀ rp hp rv aup tl r h v w vup,
      Bounds rp hp rv aup → Sense w →
        (UexplBoundedHat rp hp rv aup tl r h v w vup ↔
          UimplBounded rp hp rv aup tl 0 r h v w vup) := by
  intro rp hp rv aup tl r h v w vup hb hw
  rcases lt_or_ge tl 0 with htl | htl
  · have hexpl : UexplBoundedHat rp hp rv aup tl r h v w vup ↔
        Uexpl rp hp rv aup r h v w vup := by
      simp [UexplBoundedHat, UexplBounded, Uexpl, horizonCase, htl, not_le.mpr htl]
    have himpl : UimplBounded rp hp rv aup tl 0 r h v w vup ↔
        Uimpl rp hp rv aup r h v w vup := by
      simp [UimplBounded, Uimpl, htl]
    rw [hexpl, himpl]
    by_cases hr : rv = 0
    · subst rv
      exact (upper_explicit_stationary rp hp aup r h v w vup).trans
        (upper_implicit_stationary rp hp aup r h v w vup hb.2.2.2 hw).symm
    · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
      rw [upper_explicit_window rp hp rv aup r h v w vup hb.2.2.2 hr,
        upper_implicit_window rp hp rv aup r h v w vup hb.2.2.2 hw hr]
      exact upper_window_equivalent _ _ _ _ _ (le_max_right _ _) (by
        apply div_le_div_of_nonneg_right _ hr.le
        exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) hb.2.2.2.le)
  · by_cases hr : rv = 0
    · subst rv
      exact (explicit_bounded_upper_stationary rp hp aup tl r h v w vup hb.2.2.2 htl).trans
        (implicit_bounded_upper_stationary rp hp aup tl r h v w vup hb.2.2.2 hw htl).symm
    · have hr : 0 < rv := lt_of_le_of_ne hb.2.2.1 (Ne.symm hr)
      rw [explicit_bounded_upper_window rp hp rv aup tl r h v w vup hb.2.2.2 hr htl,
        implicit_bounded_upper_window rp hp rv aup tl r h v w vup hb.2.2.2 hw hr htl]
      exact bounded_upper_window_equivalent _ _ _ _ _ _ (le_max_right _ _)
        (mul_nonneg hb.2.2.2.le htl) (by
          apply div_le_div_of_nonneg_right _ hr.le
          exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) hb.2.2.2.le)

/-- STTT17 Lemma 4, with the documented corrections. -/
theorem bounded_regions_equivalent :
    ∀ rp hp rv alo aup tl r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
        (CexplBoundedHat rp hp rv alo aup tl r h v w vlo vup ↔
          CimplBounded rp hp rv alo aup tl 0 r h v w vlo vup) := by
  intro rp hp rv alo aup tl r h v w vlo vup hb ha hw
  exact or_congr (lower_bounded_regions_equivalent _ _ _ _ _ _ _ _ _ _ hb hw)
    (upper_bounded_regions_equivalent _ _ _ _ _ _ _ _ _ _
      ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.trans_le ha⟩ hw)

/-- Lower endpoints in the current model agree with the explicit function. -/
theorem lowerEndpoint_iff_exit (alo tl hn vn v w vlo : ℝ) (ht : 0 ≤ tl) :
    lowerEndpoint alo tl hn vn v w vlo ↔
      hn = (lowerExit alo tl v w vlo).1 ∧ vn = (lowerExit alo tl v w vlo).2 := by
  by_cases hs : tl < maxI v w vlo / alo
  · simp [lowerEndpoint, lowerExit, hs, not_le.mpr hs, ht]
  · simp [lowerEndpoint, lowerExit, hs, le_of_not_gt hs]

/-- Nominal upper endpoints agree with the corrected explicit function. -/
theorem upperEndpoint_iff_exit (aup tl hn vn v w vup : ℝ) (ht : 0 ≤ tl) :
    upperEndpoint aup tl hn vn v w vup ↔
      hn = (upperExit aup tl v w vup).1 ∧ vn = (upperExit aup tl v w vup).2 := by
  by_cases hs : tl < maxI v w vup / aup
  · simp [upperEndpoint, upperExit, hs, not_le.mpr hs, ht]
  · simp [upperEndpoint, upperExit, hs, le_of_not_gt hs]

/-- A safe follow-up at horizontal overlap gives signed separation at its initial time. -/
theorem followup_initial_separation (rp hp rv alo tl r h hn vn w target : ℝ)
    (hb : Bounds rp hp rv alo) (hw : Sense w)
    (hsafe : Lexpl rp hp rv alo (r - rv * tl) (h - hn) vn w target)
    (hcase : horizonCase rp rv tl r) : w * (h - hn) < -hp := by
  have hi := (immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw).mp hsafe
  have hs := hi 0 0 0 ⟨by ring, A_zero alo vn w target hb.2.2.2⟩
  have hover : |r - rv * tl| ≤ rp := abs_le.mpr ⟨by linarith [hcase.2.1],
    by linarith [hcase.2.2]⟩
  simpa only [sub_zero, or_iff_right (not_lt.mpr hover)] using hs

/-- STTT17 Lemma 5, lower part: safe follow-up makes case 15 redundant. -/
theorem lower_endpoint_case_redundant :
    ∀ rp hp rv alo tl r h v w vlo vloEx,
      Bounds rp hp rv alo → Sense w →
        let ex := lowerExit alo tl v w vlo
        Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 w vloEx →
          horizonCase rp rv tl r → bound15 hp alo tl h v w vlo := by
  intro rp hp rv alo tl r h v w vlo vloEx hb hw
  dsimp only
  intro hsafe hcase
  have hs := followup_initial_separation _ _ _ _ _ _ _ _ _ _ _ hb hw hsafe hcase
  by_cases ht : tl < maxI v w vlo / alo
  · simp only [lowerExit, ite_eq_left ht] at hs
    simp only [bound15, ht, not_le.mpr ht, true_implies, false_implies, and_true]
    rcases hw with rfl | rfl <;> simp [neg_div] at hs ⊢ <;> linarith
  · simp only [lowerExit, ite_eq_right ht] at hs
    simp only [bound15, ht, le_of_not_gt ht, true_implies, false_implies, true_and]
    rcases hw with rfl | rfl <;> simp [neg_div] at hs ⊢ <;> linarith

/-- STTT17 Lemma 5, upper part: a safe reversal makes case 16 redundant. -/
theorem upper_endpoint_case_redundant :
    ∀ rp hp rv alo aup tl r h v w vup vupEx,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
        let ex := upperExit aup tl v w vup
        Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 (-w) vupEx →
          horizonCase rp rv tl r → bound16 hp aup tl h v w vup := by
  intro rp hp rv alo aup tl r h v w vup vupEx hb _ha hw
  dsimp only
  intro hsafe hcase
  have hw' : Sense (-w) := by rcases hw with rfl | rfl <;> norm_num [Sense]
  have hs := followup_initial_separation _ _ _ _ _ _ _ _ _ _ _ hb hw' hsafe hcase
  by_cases ht : tl < maxI v w vup / aup
  · simp only [upperExit, ite_eq_left ht] at hs
    simp only [bound16, ht, not_le.mpr ht, true_implies, false_implies, and_true]
    rcases hw with rfl | rfl <;> simp [neg_div] at hs ⊢ <;> linarith
  · simp only [upperExit, ite_eq_right ht] at hs
    simp only [bound16, ht, le_of_not_gt ht, true_implies, false_implies, true_and]
    rcases hw with rfl | rfl <;> simp [neg_div] at hs ⊢ <;> linarith

/-- STTT17 Lemma 5, both endpoint cases, with the paper's common assumptions. -/
theorem endpoint_cases_redundant :
    ∀ rp hp rv alo aup tl r h v w vlo vloEx vup vupEx,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → Sense w →
        (let ex := lowerExit alo tl v w vlo
         Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 w vloEx →
           horizonCase rp rv tl r → bound15 hp alo tl h v w vlo) ∧
        (let ex := upperExit aup tl v w vup
         Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 (-w) vupEx →
           horizonCase rp rv tl r → bound16 hp aup tl h v w vup) := by
  intro rp hp rv alo aup tl r h v w vlo vloEx vup vupEx hb ha _ht hw
  exact ⟨lower_endpoint_case_redundant _ _ _ _ _ _ _ _ _ _ _ hb hw,
    upper_endpoint_case_redundant _ _ _ _ _ _ _ _ _ _ _ _ hb ha hw⟩

/-- STTT17 Lemma 6, with corrected endpoints. -/
theorem safeable_regions_equivalent :
    ∀ rp hp rv alo aup tl r h v w vlo vloEx vup vupEx,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → Sense w →
        (CexplSafeable rp hp rv alo aup tl r h v w vlo vloEx vup vupEx ↔
          CimplSafeable rp hp rv alo aup tl 0 r h v w vlo vloEx vup vupEx) := by
  intro rp hp rv alo aup tl r h v w vlo vloEx vup vupEx hb ha ht hw
  have hw' : Sense (-w) := by rcases hw with rfl | rfl <;> norm_num [Sense]
  have hlo := lower_bounded_regions_equivalent rp hp rv alo tl r h v w vlo hb hw
  have hup := upper_bounded_regions_equivalent rp hp rv aup tl r h v w vup
    ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.trans_le ha⟩ hw
  simp only [CexplSafeable, CimplSafeable, sub_zero]
  constructor
  · rintro (⟨hbounded, hfollow⟩ | ⟨hbounded, hfollow⟩)
    · left
      constructor
      · exact hlo.mp ⟨hbounded,
          lower_endpoint_case_redundant _ _ _ _ _ _ _ _ _ _ _ hb hw hfollow⟩
      · intro hn vn he
        obtain ⟨rfl, rfl⟩ := (lowerEndpoint_iff_exit _ _ _ _ _ _ _ ht).mp he
        exact (immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw).mp hfollow
    · right
      constructor
      · exact hup.mp ⟨hbounded,
          upper_endpoint_case_redundant _ _ _ _ _ _ _ _ _ _ _ _ hb ha hw hfollow⟩
      · intro hn vn he
        obtain ⟨rfl, rfl⟩ := (upperEndpoint_iff_exit _ _ _ _ _ _ _ ht).mp he
        exact (immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw').mp hfollow
  · rintro (⟨hbounded, hfollow⟩ | ⟨hbounded, hfollow⟩)
    · left
      constructor
      · exact (hlo.mpr hbounded).1
      · apply (immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw).mpr
        exact hfollow _ _ ((lowerEndpoint_iff_exit _ _ _ _ _ _ _ ht).mpr ⟨rfl, rfl⟩)
    · right
      constructor
      · exact (hup.mpr hbounded).1
      · apply (immediate_regions_equivalent _ _ _ _ _ _ _ _ _ hb hw').mpr
        exact hfollow _ _ ((upperEndpoint_iff_exit _ _ _ _ _ _ _ ht).mpr ⟨rfl, rfl⟩)

/-- At a negative horizon, the corrected explicit region is the existing unbounded one. -/
theorem bounded_explicit_unbounded (rp hp rv alo aup tl r h v w vlo vup : ℝ)
    (ht : tl < 0) :
    CexplBoundedHat rp hp rv alo aup tl r h v w vlo vup ↔
      Cexpl rp hp rv alo aup r h v w vlo vup := by
  simp [CexplBoundedHat, LexplBoundedHat, UexplBoundedHat, LexplBounded, UexplBounded,
    Cexpl, Lexpl, Uexpl, horizonCase, ht, not_le.mpr ht]

end ACASX
