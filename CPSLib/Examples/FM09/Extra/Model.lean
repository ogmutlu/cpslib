import CPSLib.Examples.FM09.Model

open CPSLib

namespace FM09

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


/-- Arbitrarily many free-flight segments with mutual separation (Fig. 5). -/
def free (p : ℝ) (x d y e : Vec2) := do
  let mut (x, d, y, e) := (x, d, y, e)
  let m ← choose ℕ
  for _ in [:m] do
    let ω ← choose ℝ
    let ρ ← choose ℝ
    (x, d, y, e) ← evolve (flight ω ρ)
                   (fun (x, (_: Vec2), y, (_: Vec2)) => Separated p x y)
                   (x, d, y, e)
  return (x, d, y, e)

/-- Each aircraft's current ray meets its original flight ray (Fig. 10, `circ`). -/
@[reducible]
def ExitReady (x₀ d₀ y₀ e₀ : Vec2) := fun (x, d, y, e) =>
  ∃ lx mx : ℝ, 0 ≤ lx ∧ 0 < mx ∧ x + lx • d = x₀ + mx • d₀ ∧
  ∃ ly my : ℝ, 0 ≤ ly ∧ 0 < my ∧ y + ly • e = y₀ + my • e₀

/-- The entry flight equations `F(-ω)` and `G(-ω)` (Fig. 10). -/
def entryEvol (ω : ℝ) := evolve (flight (-ω) (-ω)) (fun _ => True)

/-- Circular flight with the `do ... until` domain (Section 3 and Fig. 10). -/
def circEvol (ω : ℝ) (x₀ d₀ y₀ e₀ : Vec2) :=
  evolve
    (flight ω ω)
    (fun (x, d, y, e) => ¬ExitReady x₀ d₀ y₀ e₀ (x, d, y, e) ∨
      (x, d, y, e) ∈ frontier {(x, d, y, e) | ExitReady x₀ d₀ y₀ e₀ (x, d, y, e)})

/-- Straight exit flight (Fig. 10, `exit`). -/
def exitEvol := evolve (flight 0 0) (fun _ => True)

/-- Free flight with far separation (Fig. 10). -/
def free_f (p r : ℝ) (x d y e : Vec2) := free (far p r) x d y e

/-- Negotiation of the roundabout center, radius and angular velocity (Fig. 10). -/
def agree_f (p : ℝ) (x d y e : Vec2) := do
  let c ← choose Vec2
  let r ← chooseS {r : ℝ | r > 0}
  ensure (C r x d y e c)
  unless Separated (far p r) x y do abort
  let ω ← choose ℝ
  unless (r * ω) ^ 2 = ‖d‖ ^ 2 do abort
  return (ω, c, r)

/-- Entry flight and its radius test (Fig. 10). -/
def entry_f (ω r : ℝ) (c x d y e : Vec2) := do
  let (x, d, y, e) ← entryEvol ω (x, d, y, e)
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  return (x, d, y, e)

/-- Circular flight followed by the exit-readiness test (Fig. 10, `circ`). -/
def circ_f (ω : ℝ) (x₀ d₀ y₀ e₀ x d y e : Vec2) := do
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  ensure (ExitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  return (x, d, y, e)

/-- Straight exit flight without the final far-separation test from Fig. 10. -/
def exit_f (x d y e : Vec2) := do
  let (x, d, y, e) ← exitEvol (x, d, y, e)
  --the test below from the paper would make the proof trivial
  --unless (far p r) ^ 2 ≤ ‖x - y‖ ^ 2 do abort
  return (x, d, y, e)

structure Result where
  x : Vec2
  y : Vec2

structure FtrmResult extends Result where
  d : Vec2
  e : Vec2
  r : ℝ

/-- Instantaneous tangential entry (Fig. 5 and Eq. (2)). -/
@[simp] def entry_n (ω : ℝ) (c : Vec2) (x y : Vec2) :=
  let d := ω • perp (x - c)
  let e := ω • perp (y - c)
  (d, e) -- direction vectors tangential to roundabout center c

/-- Two-aircraft NTRM (Fig. 5). -/
def ntrm (p : ℝ) (x d y e : Vec2) : SetM Result := do
  let mut (x, d, y, e) := (x, d, y, e)
  let m ← choose ℕ
  for _ in [:m] do
    (x, d, y, e) ← free p x d y e
    let (ω, c) ← agree
    (d, e) := entry_n ω c x y
    (x, d, y, e) ← evolve (flight ω ω) (fun _ => True) (x, d, y, e)
  return { x, y }

/-- Two-aircraft FTRM (Fig. 10), without the final far-separation test. -/
def ftrm (p r : ℝ) (x d y e : Vec2) : SetM FtrmResult := do
  let mut (x, d, y, e) := (x, d, y, e)
  let mut r := r
  let m ← choose ℕ
  for _ in [:m] do
    (x, d, y, e) ← free_f p r x d y e
    let (ω, c, r_new) ← agree_f p x d y e
    r := r_new
    let (x₀, d₀, y₀, e₀) := (x, d, y, e)
    (x, d, y, e) ← entry_f ω r c x d y e
    (x, d, y, e) ← circ_f ω x₀ d₀ y₀ e₀ x d y e
    (x, d, y, e) ← exit_f x d y e
  return { x, d, y, e, r }

/-- FTRM body breakable at intermediate points. -/
def ftrmPrefix (p r : ℝ) (k : Fin 5) (x d y e : Vec2) : SetM Result := do
  --free
  let (x, d, y, e) ← free_f p r x d y e
  if k = 0 then return { x, y }
  --agree
  let (ω, c, r) ← agree_f p x d y e
  if k = 1 then return { x, y }
  --entry
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  let (x, d, y, e) ← entryEvol ω (x, d, y, e)
  if k = 2 then return { x, y }
  --circ
  unless ‖x - c‖ ^ 2 = r ^ 2 do abort
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  if k = 3 then return { x, y }
  --exit
  ensure (ExitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← exitEvol (x, d, y, e)
  return { x, y }

/-!
## Theorem 1: replacing the flyable entry procedure

The time bound may depend on the negotiated geometry and the initial state.
`entry r ω c x d y e` chooses independent, time-varying turn-rate controls.
`modifiedEntryEvol` runs their flight dynamics together with a clock, initially zero,
in the domain `t ≤ T`. The entry contract applies before the completion test `t = T`,
so it covers every intermediate state of every permitted evolution.
-/

abbrev EntryProcedure :=
  ℝ → ℝ → Vec2 → Vec2 → Vec2 → Vec2 → Vec2 →
    SetM ((ℝ → ℝ) × (ℝ → ℝ))

abbrev EntryTimeBound := ℝ → ℝ → Vec2 → Vec2 → Vec2 → Vec2 → Vec2 → ℝ

/-- Independent entry turn rates, synchronized with the clock equation `t' = 1`. -/
def entryDynamics (turnX turnY : ℝ → ℝ) :=
  ((fun (t : ℝ) (st : Vec2 × Vec2 × Vec2 × Vec2) => flight (turnX t) (turnY t) st),
    (fun (_t : ℝ) => (1 : ℝ)))

def entryDomain (T : ℝ) : (Vec2 × Vec2 × Vec2 × Vec2) × ℝ → Prop :=
  fun (_, t) => t ≤ T

/-- Clocked entry evolution, including all stopping times up to the entry deadline.
Its domain contains no separation or tangency constraint. -/
def modifiedEntryEvol (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) := do
  let (turnX, turnY) ← entry r ω c x d y e
  evolve (entryDynamics turnX turnY) (entryDomain (bound r ω c x d y e))
    ((x, d, y, e), (0 : ℝ))

/-- Theorem 1's modified-entry premise, checked on states admitted by negotiation:
safe distance throughout `[0,T]`, and tangency at `T`. Flight dynamics and clock motion
are supplied by `evolve`, and speed preservation follows from those dynamics. As with
the paper's boxed premise, this contract does not assert existence of a complete run. -/
def ModifiedEntryContract (entry : EntryProcedure) (bound : EntryTimeBound) (p : ℝ) : Prop :=
  ∀ (r ω : ℝ) (c x d y e : Vec2),
    0 ≤ p ∧ 0 ≤ r ∧ C r x d y e c ∧ (r * ω) ^ 2 = ‖d‖ ^ 2 ∧
      ‖e‖ = ‖d‖ ∧ Separated (far p r) x y →
    let T := bound r ω c x d y e
    0 ≤ T ∧ ∀ res ∈ SetM.run (modifiedEntryEvol entry bound r ω c x d y e),
      let st := res.1
      let t := res.2
      Separated p st.1 st.2.2.1 ∧
      (t = T → R ω c st.1 st.2.1 st.2.2.1 st.2.2.2)

def modifiedEntryComplete (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) := do
  let T := bound r ω c x d y e
  let (st, t) ← modifiedEntryEvol entry bound r ω c x d y e
  ensure (t = T)
  return st

def modifiedEntryPrefix (entry : EntryProcedure) (bound : EntryTimeBound)
    (r ω : ℝ) (c x d y e : Vec2) := do
  let (st, _t) ← modifiedEntryEvol entry bound r ω c x d y e
  return st

/-- Theorem 1: the original FTRM cycle with only its entry procedure replaced. -/
def ftrmModified (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (x d y e : Vec2) : SetM FtrmResult := do
  let mut (x, d, y, e) := (x, d, y, e)
  let mut r := r
  let m ← choose ℕ
  for _ in [:m] do
    (x, d, y, e) ← free_f p r x d y e
    let (ω, c, r_new) ← agree_f p x d y e
    r := r_new
    let (x₀, d₀, y₀, e₀) := (x, d, y, e)
    (x, d, y, e) ← modifiedEntryComplete entry bound r ω c x d y e
    (x, d, y, e) ← circ_f ω x₀ d₀ y₀ e₀ x d y e
    (x, d, y, e) ← exit_f x d y e
  return { x, d, y, e, r }

/-- Observation of every phase of the modified cycle, including entry times before `T`
and circular-flight times before the exit-ready test. -/
def ftrmModifiedPrefix (entry : EntryProcedure) (bound : EntryTimeBound)
    (p r : ℝ) (k : Fin 5) (x d y e : Vec2) : SetM Result := do
  let (x, d, y, e) ← free_f p r x d y e
  if k = 0 then return { x, y }
  let (ω, c, r) ← agree_f p x d y e
  if k = 1 then return { x, y }
  let (x₀, d₀, y₀, e₀) := (x, d, y, e)
  if k = 2 then
    let (x, _, y, _) ← modifiedEntryPrefix entry bound r ω c x d y e
    return { x, y }
  let (x, d, y, e) ← modifiedEntryComplete entry bound r ω c x d y e
  let (x, d, y, e) ← circEvol ω x₀ d₀ y₀ e₀ (x, d, y, e)
  if k = 3 then return { x, y }
  ensure (ExitReady x₀ d₀ y₀ e₀ (x, d, y, e))
  let (x, _, y, _) ← exitEvol (x, d, y, e)
  return { x, y }

end FM09
