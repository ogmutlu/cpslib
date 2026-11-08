import CPSLib.Examples.FM11.Model
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A certified braking path

Two cars start at positions 0 and 20 with velocity 2. In one local-lane-control
cycle, both choose acceleration -1. The path below describes their motion for
one second. Its certificate covers every real time in the interval; a renderer
can choose sampling times independently.
-/

open CPSLib

namespace FM11.BrakingPath

def x₀ (i : Car) : ℝ := if i = 0 then 0 else 20
def v₀ (_ : Car) : ℝ := 2
def a₀ (_ : Car) : ℝ := 0

noncomputable def aLeader : Car → ℝ := Function.update a₀ 1 (-1)
noncomputable def aBoth : Car → ℝ := Function.update aLeader 0 (-1)

/-- Local time parametrizes the car state and the evolution clock. -/
noncomputable def path (t : ℝ) : xva × ℝ :=
  ((fun i => x₀ i + 2 * t - t ^ 2 / 2, fun _ => 2 - t, aBoth), t)

noncomputable def observation (t : ℝ) : Result :=
  { x := (path t).1.1, v := (path t).1.2.1 }

private theorem bind_mem {α β : Type} (p : SetM α) (f : α → SetM β)
    (x : α) (y : β) (hx : x ∈ SetM.run p) (hy : y ∈ SetM.run (f x)) :
    y ∈ SetM.run (p >>= f) :=
  Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hy⟩⟩

private theorem leader_choice :
    aLeader ∈ SetM.run (l_ctrl 1 1 1 a₀) := by
  apply bind_mem _ _ (-1) _ (Set.mem_univ _)
  norm_num only [neg_le_neg_iff, le_refl, neg_le_self_iff, zero_le_one, and_self,
    ↓reduceIte]
  exact Set.mem_singleton aLeader

private theorem follower_choice :
    aBoth ∈ SetM.run (f_ctrl 1 1 1 1 0 1 x₀ v₀ aLeader) := by
  unfold f_ctrl
  apply Or.inl
  apply bind_mem _ _ (-1) _ (Set.mem_univ _)
  simp only [le_refl, and_self, ↓reduceIte]
  exact Set.mem_singleton aBoth

private theorem position_derivative (i : Car) (t : ℝ) :
    HasDerivAt (fun s => x₀ i + 2 * s - s ^ 2 / 2) (2 - t) t := by
  convert (((hasDerivAt_id t).const_mul 2).const_add (x₀ i)).sub
    (((hasDerivAt_id t).pow 2).div_const 2) using 1
  · rfl
  · norm_num

private theorem evolution (T : ℝ) (hT : T ∈ Set.Icc 0 1) :
    IsEvolution path (Evolvable.denotation (motion {0, 1}, time))
      (domain 1 {0, 1}) ((x₀, v₀, aBoth), 0) T := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [path] using (show (fun _ : Car => (2 : ℝ)) = v₀ from rfl)
  · intro t ht
    exact ⟨fun _ _ => by dsimp [path]; linarith [ht.2, hT.2], ht.2.trans hT.2⟩
  · change (∀ t ∈ Set.Icc 0 T, _) ∧ _
    constructor
    · intro t ht
      change (∀ i ∈ ({0, 1} : Finset Car), _) ∧
        (∀ i ∈ ({0, 1} : Finset Car), _) ∧ (∀ i ∈ ({0, 1} : Finset Car), _)
      refine ⟨fun i _ => (position_derivative i t).hasDerivWithinAt, ?_, ?_⟩
      · intro i hi
        have ha : aBoth i = -1 := by
          rcases (show i = 0 ∨ i = 1 by simpa using hi) with rfl | rfl <;>
            norm_num [aBoth, aLeader]
        change HasDerivWithinAt (fun s : ℝ => 2 - s) (aBoth i) (Set.Icc 0 T) t
        rw [ha]
        convert ((hasDerivAt_id t).const_sub 2).hasDerivWithinAt
          (s := Set.Icc 0 T) using 1
        rfl
      · intro i hi
        exact (hasDerivAt_const t (aBoth i)).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_id t).hasDerivWithinAt

private theorem endpoint (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    observation t ∈ SetM.run (llc 1 1 1 1 0 1 x₀ v₀ a₀) := by
  unfold llc
  apply bind_mem _ _ 1 _ (Set.mem_univ _)
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  norm_num [List.range', List.forIn_cons, List.forIn_nil]
  apply bind_mem _ _ aLeader _ leader_choice
  apply bind_mem _ _ aBoth _ follower_choice
  rw [← bind_pure_comp]
  apply bind_mem _ _ (path t).1 _ ?_
  · exact Set.mem_singleton (observation t)
  · unfold dyn
    apply bind_mem _ _ (path t) _ ?_
    · exact Set.mem_singleton (path t).1
    · exact SemanticODE.mem_evolveSemantic _ _ _ t path ht.1 (evolution t ht)

/-- Fixed controller choices, one valid continuous path, and all its LLC endpoints. -/
theorem path_certified :
    aLeader ∈ SetM.run (l_ctrl 1 1 1 a₀) ∧
    aBoth ∈ SetM.run (f_ctrl 1 1 1 1 0 1 x₀ v₀ aLeader) ∧
    IsEvolution path
      (Evolvable.denotation (motion {0, 1}, time))
      (domain 1 {0, 1}) ((x₀, v₀, aBoth), 0) 1 ∧
    (∀ t ∈ Set.Icc 0 1,
      observation t ∈ SetM.run (llc 1 1 1 1 0 1 x₀ v₀ a₀)) := by
  exact ⟨leader_choice, follower_choice, evolution 1 ⟨by norm_num, le_rfl⟩, endpoint⟩

end FM11.BrakingPath
