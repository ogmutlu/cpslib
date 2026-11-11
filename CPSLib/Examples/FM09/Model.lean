import CPSLib.Core.ODE
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Roundabout collision avoidance for a finite fleet

The FM09 case study separates a roundabout maneuver into free flight, negotiation,
entry, circular flight, and exit. We first model NTRM, whose entry changes velocity
instantaneously, then FTRM, whose entry follows curved flight.

The programs below generalize the two-aircraft controllers in Figs. 5 and 10 to
an arbitrary finite fleet. The paper's multiple-aircraft NTRM discussion is in
Section 4.4. The safety specifications for these programs are in
`CPSLib.Examples.FM09.Challenge`; the two-aircraft variants are in `FM09/Extra`.

## Positions, velocities, and separation

An aircraft has a planar position and a planar velocity. For a fleet of size `n`,
these are functions `x d : Fin n → Vec2`. The protected distance `p` describes
the separation to maintain. Flyable entry uses the larger initial margin
`far p r`, which also depends on the negotiated roundabout radius `r`.
-/

open CPSLib
open scoped RealInnerProductSpace

namespace FM09

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-- Safe planar separation `S(p)` of two aircraft (Eq. (1)). -/
@[reducible]
def Separated (p : ℝ) (x y : Vec2) : Prop :=
  p ^ 2 ≤ ‖x - y‖ ^ 2

/-- The perpendicular of a vector, a counterclockwise quarter-turn.
Used in the flight equations of Section 4.1. -/
@[simp] def perp (v : Vec2) : Vec2 :=
  !₂[-v 1, v 0]

/-- Far separation. (Eq. (8)) -/
noncomputable def far (p r : ℝ) : ℝ :=
  √2 * (p + (2 / 3) * Real.pi * r)

/-!
## NTRM: instantaneous tangential entry

In the simplified maneuver, all aircraft agree on a center and angular velocity.
They can then turn instantaneously to velocities tangent to the roundabout.
This idealized entry gives the circular-flight safety argument its starting point.
-/

/-- Agree on an arbitrary roundabout center `c` and angular velocity `ω` (Fig. 5). -/
def agree := do
  let ω ← choose ℝ
  let c ← choose Vec2
  return (ω, c)

/-- Pairwise planar separation for the fleet. -/
@[reducible]
def SeparatedMany {n : ℕ} (p : ℝ) (x : Fin n → Vec2) : Prop :=
  ∀ i j, i ≠ j → Separated p (x i) (x j)

/-- Simultaneous planar flight QODE, generalizing
the two aircraft ODE with `F(ω)` and `G(ρ)` from Section 4.1.
`x i` is the position vector for aircraft i.
`d i` is the linear velocity vector for aircraft i.
The QODE says: `∀ i : x(i)' = d(i)` and `∀ i : d(i)' = ω(i) • perp(d(i))`. -/
def flight_many {n : ℕ} (ω : Fin n → ℝ) :
    (Fin n → Vec2) × (Fin n → Vec2) → (Fin n → Vec2) × (Fin n → Vec2) :=
  fun (_x, d) => (d, fun i => ω i • perp (d i))

/-!
Free flight permits a different angular velocity for each aircraft. Its evolution
domain requires pairwise separation at every time of each continuous segment.
The chosen number of segments is arbitrary and may be zero.
-/

/-- Pairwise separation as the free-flight evolution domain (Figs. 5 and 10). -/
def domain_SeparatedMany {n : ℕ} (p : ℝ) : (Fin n → Vec2) × (Fin n → Vec2) → Prop :=
  fun (x, _d) => SeparatedMany p x

/-- Arbitrarily many free-flight segments with mutual separation (Fig. 5). -/
def free_many {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let mut (x, d) := (x, d)
  let m ← choose ℕ
  for _ in [:m] do
    let ω ← choose (Fin n → ℝ)
    (x, d) ← evolve (flight_many ω) (domain_SeparatedMany p) (x, d)
  return (x, d)

/-- Instantaneous tangential entry (Fig. 5 and Eq. (2)), generalized to a fleet.
Returns a function assigning a linear velocity vector for all aircrafts. -/
def entry_n_many {n : ℕ} (ω : ℝ) (c : Vec2) (x : Fin n → Vec2) : Fin n → Vec2 :=
  fun i => ω • perp (x i - c)

/-!
One NTRM iteration combines free flight, agreement, tangential entry, and circular
flight. The circular phase has no separation constraint in its evolution domain:
its safety must follow from the geometry established by entry.
As with free flight, the number of complete iterations is chosen nondeterministically.
-/

/-- Fleet generalization of NTRM (NTRM is in Fig. 5). -/
def ntrm_many {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let mut (x, d) := (x, d)
  let m ← choose ℕ
  for _ in [:m] do
    (x, d) ← free_many p x d
    let (ω, c) ← agree
    d := entry_n_many ω c x
    -- Circular flight, every aircraft has the same angular velocity
    (x, d) ← evolve (flight_many (fun _ => ω)) (fun _ => True) (x, d)
  return x

/-!
## FTRM: curved entry, circular flight, and straight exit

FTRM replaces the instantaneous turn with a curved entry. All aircraft switch
phases together. Negotiation must therefore find a common center, positive radius,
and angular velocity compatible with every aircraft.

The returned state includes velocities and the latest negotiated radius, since
both are needed when another maneuver begins.
-/

structure FtrmManyResult (n : ℕ) where
  x : Fin n → Vec2 -- position vectors for all aircrafts
  d : Fin n → Vec2 -- linear velocity vectors for all aircrafts
  r : ℝ -- roundabout radius

/-- Equal linear speeds, generalizing the FTRM assumption in Fig. 10 to a fleet. -/
def EqualSpeeds {n : ℕ} (d : Fin n → Vec2) : Prop :=
  ∀ i j, ‖d i‖ = ‖d j‖

/-!
### Negotiating the entry geometry

Condition `C` places every aircraft at distance `sqrt(3) * r` from the common
center. Each aircraft's forward flight ray must reach that center; the witness
`l` may differ between aircraft. Negotiation also checks the far-separation
margin and the relation between radius, angular velocity, and linear speed.

A failed test aborts that choice. The model describes all successful choices;
it does not assert that negotiation succeeds from every initial configuration.
-/

/-- Fleet entry geometry condition `C` for
the common center and radius (Fig. 10, Eq. (3)). -/
def ConditionC {n : ℕ} (r : ℝ) (c : Vec2) (x d : Fin n → Vec2) : Prop :=
  ∀ i, ‖x i - c‖ = √3 * r ∧ ∃ l ≥ (0 : ℝ), x i + l • d i = c

/-- Each aircraft's current ray meets its original flight ray (Fig. 10, `circ`). -/
def ExitReadyMany {n : ℕ} (x₀ d₀ x d : Fin n → Vec2) : Prop :=
  ∀ i, ∃ l m : ℝ, 0 ≤ l ∧ 0 < m ∧ x i + l • d i = x₀ i + m • d₀ i

/-- Fleet negotiation, based on `agree` in Fig. 10, with speed compatibility
checked for every aircraft. -/
def agree_f_many {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let c ← choose Vec2
  let r ← chooseFrom {r : ℝ | r > 0}
  ensure (ConditionC r c x d)
  unless SeparatedMany (far p r) x do abort
  let ω ← choose ℝ
  unless ∀ i, (r * ω) ^ 2 = ‖d i‖ ^ 2 do abort
  return (ω, c, r)

/-!
### Following the negotiated maneuver

Entry uses angular velocity `-ω`; circular flight uses `ω`; straight exit uses
zero angular velocity. The bare evolution programs also expose intermediate
stopping times for the throughout-safety specification.

Here, entry may evolve for any duration before the radius test is checked.
This differs from the `do ... until` entry in Fig. 10. Circular flight uses the
paper's `do ... until` construction from Section 3, followed by its readiness test.
-/

/-- The entry flight equations `F(-ω)` from Fig. 10, synchronized across the fleet. -/
def entryEvol_many {n : ℕ} (ω : ℝ) (x d : Fin n → Vec2) :=
  evolve (flight_many (fun _ => -ω)) (fun _ => True) (x, d)

/-- Fleet entry and its radius test, based on `entry` in Fig. 10 -/
def entry_f_many {n : ℕ} (ω r : ℝ) (c : Vec2) (x d : Fin n → Vec2) := do
  let (x, d) ← entryEvol_many ω x d
  unless ∀ i, ‖x i - c‖ ^ 2 = r ^ 2 do abort
  return (x, d)

/-- Circular flight with the `do ... until` domain from Section 3 and Fig. 10,
using joint exit readiness for the fleet. -/
def circEvol_many {n : ℕ} (ω : ℝ) (x₀ d₀ x d : Fin n → Vec2) :=
  evolve (flight_many (fun _ => ω))
    (fun (x, d) => ¬ExitReadyMany x₀ d₀ x d ∨
      (x, d) ∈ frontier {(x, d) | ExitReadyMany x₀ d₀ x d}) (x, d)

/-- Circular flight followed by the joint exit-readiness test (Fig. 10, `circ`). -/
def circ_f_many {n : ℕ} (ω : ℝ) (x₀ d₀ x d : Fin n → Vec2) := do
  let (x, d) ← circEvol_many ω x₀ d₀ x d
  ensure (ExitReadyMany x₀ d₀ x d)
  return (x, d)

/-- Straight exit flight (Fig. 10, `exit`), without its final far-separation test. -/
def exitEvol_many {n : ℕ} (x d : Fin n → Vec2) :=
  evolve (flight_many (fun _ => 0)) (fun _ => True) (x, d)

/-- Synchronized fleet generalization of FTRM (Fig. 10 and Section 6).
The exit phase omits Fig. 10's final far-separation test. -/
def ftrm_many {n : ℕ} (p r : ℝ) (x d : Fin n → Vec2) : SetM (FtrmManyResult n) := do
  let mut (x, d) := (x, d)
  let mut r := r
  let m ← choose ℕ
  for _ in [:m] do
    (x, d) ← free_many (far p r) x d
    let (ω, c, r_new) ← agree_f_many p x d
    r := r_new
    let (x₀, d₀) := (x, d)
    (x, d) ← entry_f_many ω r c x d
    (x, d) ← circ_f_many ω x₀ d₀ x d
    (x, d) ← exitEvol_many x d
  return { x, d, r }

/-!
### Observing intermediate states

A result of `ftrm_many` describes a completed sequence of maneuver iterations.
To state safety during an iteration, `ftrmPrefix_many` exposes five stopping points:

* `k = 0`: after free flight;
* `k = 1`: after negotiation;
* `k = 2`: during entry, before the radius test;
* `k = 3`: during circular flight, before the exit-readiness test;
* `k = 4`: during straight exit.

The continuous evolutions allow arbitrary stopping times within their domains.
Thus the entry and circular observations include prefixes that need not extend
to a successful complete iteration.
-/

/-- FTRM body breakable at intermediate points. -/
def ftrmPrefix_many {n : ℕ} (p r : ℝ) (k : Fin 5) (x d : Fin n → Vec2) := do
  let (x, d) ← free_many (far p r) x d
  if k = 0 then return x
  let (ω, c, r) ← agree_f_many p x d
  if k = 1 then return x
  let (x₀, d₀) := (x, d)
  let (x, d) ← entryEvol_many ω x d
  if k = 2 then return x
  unless ∀ i, ‖x i - c‖ ^ 2 = r ^ 2 do abort
  let (x, d) ← circEvol_many ω x₀ d₀ x d
  if k = 3 then return x
  ensure (ExitReadyMany x₀ d₀ x d)
  let (x, _) ← exitEvol_many x d
  return x

end FM09
