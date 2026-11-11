import CPSLib.Core.QODE
open CPSLib

abbrev Car := Nat
abbrev State := (Car → ℝ) × (Car → ℝ) × (Car → ℝ)

structure Result where
  active : Finset Car
  x : Car → ℝ

@[simp] def motion (active : Finset Car) : Set Car × (State → State) :=
  (active, fun (_x, v, a) => (v, a, 0))

@[simp] def domain (_ : State) : Prop := True

@[reducible] def Ordered (x v a : Car → ℝ) (i j : Car) : Prop :=
  x i < x j ∧ v i ≤ v j ∧ a i ≤ a j

def prog (active : Finset Car) (x v a : Car → ℝ) : SetM Result := do
  let mut active := active
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    let i ← chooseFrom {i | i ∉ active}
    active := insert i active
    unless (∀ j ∈ active, i ≠ j →
            Ordered x v a i j ∨ Ordered x v a j i) do abort
    (x, v, a) ← evolve (motion active) domain (x, v, a)
  return { active, x }

theorem collision_freedom :
    ∀ active x v a,
      (∀ i ∈ active, ∀ j ∈ active,
        i ≠ j → Ordered x v a i j ∨ Ordered x v a j i) →
          ∀ res ∈ SetM.run (prog active x v a),
          ∀ i ∈ res.active, ∀ j ∈ res.active, i ≠ j → res.x i ≠ res.x j := sorry
