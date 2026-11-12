import CPSLib.Core.ODE
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Roundabout Collision Avoidance Case Study (FM09), Generalized to a Fleet of Planes

The FM09 case study separates a roundabout maneuver into free flight, negotiation,
entry, circular flight, and exit. We first model NTRM (non-flyable tangential
roundabout manuevour), whose entry changes velocity instantaneously, then FTRM
(fully-flyable tangential roundabout manuevour), whose entry follows curved flight.
The programs below generalize the two-aircraft controllers in Figs. 5 and 10 to
an arbitrary finite fleet.
-/

open CPSLib
open scoped RealInnerProductSpace

namespace FM09

/-!
## Positions, velocities, and separation

An aircraft has a planar position and a planar velocity. For a fleet of size `n`,
these are functions `x d : Fin n → Vec2`. The protected distance `p` describes
the separation to maintain. Flyable entry uses the larger initial margin
`far p r`, which also depends on the negotiated roundabout radius `r`.
-/

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/--
Safe planar separation `S(p)` of two aircraft (Eq. (1)).
-/
@[reducible]
def Separated (p : ℝ) (x y : Vec2) : Prop := p ^ 2 ≤ ‖x - y‖ ^ 2

/--
The perpendicular of a vector, a counterclockwise quarter-turn.
Used in the flight equations of Section 4.1.
-/
@[simp] def perp (v : Vec2) : Vec2 := !₂[-v 1, v 0]

/--
Far separation. (Eq. (8))
-/
noncomputable def far (p r : ℝ) : ℝ := √2 * (p + (2 / 3) * Real.pi * r)

/-!
## NTRM: instantaneous tangential entry

In the simplified maneuver, all aircraft agree on a center and angular velocity.
They can then turn instantaneously to velocities tangent to the roundabout.
This idealized entry gives the circular-flight safety argument its starting point.
-/

/--
Agree on an arbitrary roundabout center `c` and angular velocity `ω` (Fig. 5).
-/
def agree := do
  let ω ← choose ℝ
  let c ← choose Vec2
  return (ω, c)

/--
Pairwise planar separation for the fleet.
-/
@[reducible]
def SeparatedMany {n : ℕ} (p : ℝ) (x : Fin n → Vec2) : Prop :=
  ∀ i j, i ≠ j → Separated p (x i) (x j)

/--
Type of `x : Fin n → Vec2` (planar position for each aircraft) and
`d : Fin n → Vec2` (planar for each aircraft)
-/
abbrev xd (n : ℕ) := (Fin n → Vec2) × (Fin n → Vec2)

/--
Simultaneous planar flight QODE, generalizing the two aircraft ODE from Section 4.1.
The QODE says: `∀ i : x(i)' = d(i)` and `∀ i : d(i)' = ω(i) • perp(d(i))`.
-/
def flightQODE {n : ℕ} (ω : Fin n → ℝ) : xd n → xd n
  | (_x, d) => (d, fun i => ω i • perp (d i))

/-!
Free flight permits a different angular velocity for each aircraft. Its evolution
domain requires pairwise separation at every time of each continuous segment.
The chosen number of segments is arbitrary and may be zero.
-/

/--
Pairwise separation as the free-flight evolution domain (Figs. 5 and 10).
-/
def domainSeparatedMany {n : ℕ} (p : ℝ) : (Fin n → Vec2) × (Fin n → Vec2) → Prop :=
  fun (x, _d) => SeparatedMany p x

/--
Arbitrarily many free-flight segments with pairwise separation (Fig. 5).
-/
def freeFlight {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let mut (x, d) := (x, d)
  let m ← choose ℕ
  for _ in [:m] do
    let ω ← choose (Fin n → ℝ)
    (x, d) ← evolve (flightQODE ω) (domainSeparatedMany p) (x, d)
  return (x, d)

/--
Instantaneous tangential entry (Fig. 5 and Eq. (2)), generalized to a fleet.
Returns a function assigning a linear velocity vector for all aircrafts.
-/
def entryNtrm {n : ℕ} (ω : ℝ) (c : Vec2) (x : Fin n → Vec2) : Fin n → Vec2 :=
  fun i => ω • perp (x i - c)

/-!
One NTRM iteration combines free flight, agreement, tangential entry, and circular
flight. The circular phase has no separation constraint in its evolution domain:
its safety must follow from the geometry established by entry.
As with free flight, the number of complete iterations is chosen nondeterministically.
-/

/--
Fleet generalization of NTRM.
-/
def ntrmProg {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let mut (x, d) := (x, d)
  let m ← choose ℕ
  for _ in [:m] do
    (x, d) ← freeFlight p x d
    let (ω, c) ← agree -- on angular velocity and roundabout center
    d := entryNtrm ω c x
    -- Circular flight, every aircraft has the same angular velocity
    (x, d) ← evolve (flightQODE (fun _ => ω)) (fun _ => True) (x, d)
  return x

/-!
## FTRM: curved entry, circular flight, and straight exit

FTRM replaces the instantaneous turn with a curved entry. All aircraft switch
phases together. Negotiation must therefore find a common center, positive radius,
and angular velocity compatible with every aircraft.
-/

/--
Equal linear speeds, generalizing the FTRM assumption in Fig. 10 to a fleet.
-/
def EqualSpeeds {n : ℕ} (d : Fin n → Vec2) : Prop := ∀ i j, ‖d i‖ = ‖d j‖

/-!
### Negotiating the entry geometry

Condition `C` requires every aircraft to be exactly `√3 * r` away from the common center
`c` and heading directly toward it. Formally, each aircraft has some `l ≥ 0` such that
`x i + l • d i = c`. The value of `l` may differ between aircraft. Negotiation
additionally checks that all aircraft are sufficiently far apart and that each aircraft’s
speed equals `r * |ω|`, as required for circular flight with radius `r` and angular
velocity `ω`.
-/

/--
Fleet entry geometry condition `C` for the common center `c` and radius `r`
(Fig. 10, Eq. (3)).
-/
def ConditionC {n : ℕ} (r : ℝ) (c : Vec2) (x d : Fin n → Vec2) : Prop :=
  ∀ i, ‖x i - c‖ = √3 * r ∧ ∃ l ≥ (0 : ℝ), x i + l • d i = c

/--
Each aircraft's current ray meets its original flight ray (Fig. 10).
-/
def ExitReady {n : ℕ} (x₀ d₀ x d : Fin n → Vec2) : Prop :=
  ∀ i, ∃ l m : ℝ,
    0 ≤ l ∧ 0 < m ∧ (x i + l • d i = x₀ i + m • d₀ i)

/--
Fleet negotiation, based on `agree` in Fig. 10, with speed compatibility
checked for every aircraft.
-/
def agreeFtrm {n : ℕ} (p : ℝ) (x d : Fin n → Vec2) := do
  let c ← choose Vec2
  let r ← chooseFrom {r : ℝ | r > 0}
  ensure (ConditionC r c x d)
  unless SeparatedMany (far p r) x do abort
  let ω ← choose ℝ
  unless ∀ i, (r * ω) ^ 2 = ‖d i‖ ^ 2 do abort
  return (ω, c, r)

/-!
### Following the negotiated maneuver
-/

/--
Fleet entry and its radius test, based on `entry` in Fig. 10
-/
def entryFtrm {n : ℕ} (ω r : ℝ) (c : Vec2) (x d : Fin n → Vec2) := do
  let (x, d) ← evolve (flightQODE (fun _ => -ω)) (fun _ => True) (x, d)
  unless ∀ i, ‖x i - c‖ ^ 2 = r ^ 2 do abort
  return (x, d)

/--
Circular flight with the `do ... until` domain from paper,
using joint exit readiness for the fleet. (Fig. 10, `circ`).
-/
def circFtrm {n : ℕ} (ω : ℝ) (x₀ d₀ x d : Fin n → Vec2) := do
  let (x, d) ← evolve (flightQODE (fun _ => ω))
                      (fun (x, d) => ¬ExitReady x₀ d₀ x d ∨
                        (x, d) ∈ frontier {(x, d) | ExitReady x₀ d₀ x d}) (x, d)
  ensure (ExitReady x₀ d₀ x d)
  return (x, d)

structure FtrmResult (n : ℕ) where
  x : Fin n → Vec2
  d : Fin n → Vec2
  r : ℝ

/--
Synchronized fleet generalization of FTRM (Fig. 10 and Section 6).
The exit phase omits Fig. 10's final far-separation test.
-/
def ftrmProg {n : ℕ} (p r : ℝ) (x d : Fin n → Vec2) : SetM (FtrmResult n) := do
  let mut (x, d) := (x, d)
  let mut r := r
  let m ← choose ℕ
  for _ in [:m] do
    (x, d) ← freeFlight (far p r) x d
    let (ω, c, r_new) ← agreeFtrm p x d
    r := r_new
    let (x₀, d₀) := (x, d)
    (x, d) ← entryFtrm ω r c x d
    (x, d) ← circFtrm ω x₀ d₀ x d
    (x, d) ← evolve (flightQODE (ω := fun _ => 0)) (fun _ => True) (x, d) -- exit
  return { x, d, r }

/-!
### Observing intermediate states

A result of `ftrmProg` describes a completed sequence of maneuver iterations.
To state safety during an iteration, `ftrmPrefixProg` exposes five stopping points:

* `k = 0`: after free flight;
* `k = 1`: after negotiation;
* `k = 2`: during entry, before the radius test;
* `k = 3`: during circular flight, before the exit-readiness test;
* `k = 4`: during straight exit.

The continuous evolutions allow arbitrary stopping times within their domains.
Thus the entry and circular observations include prefixes that need not extend
to a successful complete iteration.
-/

/--
FTRM body breakable at intermediate points.
-/
def ftrmPrefixProg {n : ℕ} (p r : ℝ) (k : Fin 5) (x d : Fin n → Vec2) := do
  let (x, d) ← freeFlight (far p r) x d
  if k = 0 then return x
  let (ω, c, r) ← agreeFtrm p x d
  if k = 1 then return x
  let (x₀, d₀) := (x, d)
  let (x, d) ← evolve (flightQODE (fun _ => -ω)) (fun _ => True) (x, d)
  if k = 2 then return x
  unless ∀ i, ‖x i - c‖ ^ 2 = r ^ 2 do abort
  let (x, d) ← evolve (flightQODE (fun _ => ω))
                      (fun (x, d) => ¬ExitReady x₀ d₀ x d ∨
                        (x, d) ∈ frontier {(x, d) | ExitReady x₀ d₀ x d}) (x, d) --circ
  if k = 3 then return x
  ensure (ExitReady x₀ d₀ x d)
  let (x, _) ← evolve (flightQODE (ω := fun _ => 0)) (fun _ => True) (x, d) --exit
  return x

end FM09
