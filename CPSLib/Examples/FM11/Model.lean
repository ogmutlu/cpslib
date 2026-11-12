import CPSLib.Core.QODE

/-!
# Highway Car Control Case Study (FM11)

The FM11 case study develops four controllers: a follower and leader in one lane,
a fixed population in one lane, a changing population in one lane, and a changing
population across several lanes. Each controller alternates discrete acceleration
choices with continuous car motion.
-/

open CPSLib

namespace FM11

/-!
## Car state and braking parameters

Cars are identified by natural number indices. The `Car → ℝ` functions `x`, `v`, and
`a` give their positions, velocities, and accelerations along the road. A finite set
`cars` records which cars participate in a lane.

The controller parameters are maximum acceleration `A`, minimum guaranteed braking
magnitude `b`, maximum braking magnitude `B`, and maximum time `ε` between control
updates. The safety specifications assume `0 ≤ A`, `0 < b ≤ B`, and `0 < ε`.
-/

abbrev Car := ℕ

/-!
## Safe following and lane order

Safe following depends on braking distances as well as position. For distinct cars,
`f.IsBehind l b B x v` requires the follower to be strictly behind the leader and
to stop short of the leader's stopping position under the respective braking bounds.
It also requires both velocities to be nonnegative.

The relation `l.IsLeaderOf i cars x` identifies the next car ahead, with no participating
car between the two. It is a relation rather than a total function: the frontmost car
has no leader.
-/

/--
The relation `f << l` from Section 5.2.
-/
@[reducible]
def Car.IsBehind (f l : Car) (b B : ℝ) (x v : Car → ℝ) : Prop :=
  (x f ≤ x l) ∧
    (f ≠ l →
      (x f < x l ∧ x f + (v f ^ 2) / (2 * b) < x l + (v l ^ 2) / (2 * B) ∧
      v f ≥ 0 ∧ v l ≥ 0))

/--
The car `l = L(i)` is the leader of car `i`. Represented as a relation rather than a
function. The condition `i ∈ cars ∧ l ∈ cars`, implicit in the paper, is explicit here.
-/
@[reducible]
def Car.IsLeaderOf (l i : Car) (cars : Finset Car) (x : Car → ℝ) : Prop :=
  i ∈ cars ∧ l ∈ cars ∧ x i < x l ∧ ∀ k ∈ cars,
    (k ≠ i ∧ k ≠ l) → (x k < x i ∨ x l < x k)

/--
The relation `i << L(i)` from Section 5.2. Car `i` is safely behind its leader.
-/
@[reducible]
def Car.IsBehindItsLeader (i : Car) (cars : Finset Car) (b B : ℝ)
    (x v : Car → ℝ) : Prop :=
  ∀ l ∈ cars, l.IsLeaderOf i cars x → i.IsBehind l b B x v

/--
Lane safety: nonnegative velocities, distinct positions, and each car safely
behind its leader. This combined predicate is not present in the paper.
-/
@[reducible]
def LaneSafe (cars : Finset Car) (b B : ℝ) (x v : Car → ℝ) : Prop :=
  (∀ i ∈ cars, 0 ≤ v i) ∧
  (∀ i ∈ cars, ∀ j ∈ cars, i ≠ j → x i ≠ x j) ∧
  (∀ i ∈ cars, i.IsBehindItsLeader cars b B x v)

/--
The relation `i << L*(i)` from Section 6.2.
Car `i` is safely behind every car `l = L^n(i)` for some `n ≥ 0`.
-/
@[reducible]
def Car.IsBehindLStar (i : Car) (cars : Finset Car) (b B : ℝ)
    (x v : Car → ℝ) : Prop :=
  ∀ k ∈
    (SetM.run do
    let mut k := i
    let n ← choose ℕ
    for _ in [:n] do
      let l ← chooseFrom {l | l.IsLeaderOf k cars x} -- L(k)
      k := l
    return k),
  i.IsBehind k b B x v

/-!
## Continuous motion between control updates

For participating cars, motion follows `x' = v`, `v' = a`, and `a' = 0`.
Acceleration is therefore constant during each continuous segment.
The evolution domain prevents negative velocities and limits each segment to at
most `ε` time units.
-/

/--
Type of `x : Car → ℝ`, `v : Car → ℝ` and `a : Car → ℝ`.
-/
abbrev xva := (Car → ℝ) × (Car → ℝ) × (Car → ℝ)

/--
Quantified ODE for car motion.
-/
@[simp] def motion (cars : Finset Car) : Set Car × (xva → xva) :=
  (cars, fun (_x, v, a) => (v, a, 0))

/--
ODE modelling time.
-/
@[simp] def time : ℝ → ℝ := fun _t => 1

/--
Evolution domain: velocities remain nonnegative and elapsed time is at most `ε`.
-/
@[simp] def domain (ε : ℝ) (cars : Finset Car) : xva × ℝ → Prop
  | ((_x, v, _a), t) => (∀ i ∈ cars, 0 ≤ v i) ∧ t ≤ ε

/--
Evolve the cars simultaneously with a clock starting at zero.
-/
def dyn (ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) := do
  let ((x, v, a), _t) ← evolve (motion cars, time)
                               (domain ε cars)
                               ((x, v, a), 0)
  return (x, v, a)

/--
Following-distance test allowing an acceleration choice until the next update.
-/
@[reducible]
def Safe_ε (A b B ε : ℝ) (x v : Car → ℝ) (f l : Car) : Prop :=
  x f + (v f ^ 2) / (2 * b) + (A / b + 1) * (A / 2 * ε ^ 2 + ε * v f) <
    x l + v l ^ 2 / (2 * B)

/-!
## Model 1: local lane control

The leader may choose any acceleration within its bounds. The follower has three
options: brake, use the `Safe_ε` margin to choose an acceleration within the wider
bounds, or keep zero acceleration when already stopped.
-/

/--
Update the leader's acceleration `a(l)` within `[-B, A]`.
-/
def l_ctrl (A B : ℝ) (l : Car) (a : Car → ℝ) : SetM (Car → ℝ) := do
  let al ← choose ℝ
  unless (-B ≤ al ∧ al ≤ A) do abort
  return Function.update a l al

/--
Update the follower's acceleration `a(f)`: brake, choose a safe acceleration,
or remain stopped.
-/
def f_ctrl (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM (Car → ℝ) :=
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

structure LaneResult where
  x : Car → ℝ
  v : Car → ℝ

/--
Local lane control with two cars: `f` (follower) and `l` (leader).
-/
def llc (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM LaneResult := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    a ← l_ctrl A B l a
    a ← f_ctrl A b B ε f l x v a
    (x, v, a) ← dyn ε {f, l} x v a
  return { x, v }

/-!
## Model 2: global lane control

For a fixed lane population, every car applies the follower controller relative
to its own leader. All controllers read the same initial state, and their acceleration
choices are collected before the cars move together.
-/

/--
Generalized `f_ctrl`: in the second option, `Safe_ε` must hold for `L(i)`.
This is not equivalent to:
`let l ← chooseS {l | l.IsLeaderOf i cars x} ; f_ctrl`
because that would require every car to have a leader and fail otherwise.
The frontmost car has no leader, so it must choose the first or third option.
-/
def ctrl_i (A b B ε : ℝ) (cars : Finset Car) (i : Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) :=
  (do
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ -b) do abort
    return Function.update a i ai)
    <|>
  (do
    let l ← chooseFrom {l | l.IsLeaderOf i cars x} -- leader of car i
    unless Safe_ε A b B ε x v i l do abort
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ A) do abort
    return Function.update a i ai)
    <|>
  (do
    unless v i = 0 do abort
    return Function.update a i 0)

/--
Run the controllers for all cars simultaneously: each reads the same initial
state. Each `ctrl_i` only updates `a(i)`, so a sequential loop collecting those
updates preserves the simultaneous control semantics.
-/
def ctrl_n (A b B ε : ℝ) (cars : Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) := do
  let mut a_res := a
  for i in cars.toList do
    let ai ← ctrl_i A b B ε cars i x v a
    a_res := Function.update a_res i (ai i)
  return a_res

-- def ctrl_n (A b B ε : ℝ) (cars : Finset Car)
--     (x v a : Car → ℝ) : SetM (Car → ℝ) := do
--   chooseS {a' | (∀ i ∈ cars, Function.update a i (a' i) ∈
--                   SetM.run (ctrl_i A b B ε cars i x v a)) ∧
--                   ∀ i, i ∉ cars → a' i = a i}

/--
Global lane control with a fixed set of cars.
-/
def glc (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) : SetM LaneResult := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    a ← ctrl_n A b B ε cars x v a
    (x, v, a) ← dyn ε cars x v a
  return { x, v }

/-!
## Model 3: local highway control

The population can now change between motion segments. Deletion removes a car from
the participating set. Creation selects an unused identifier and checks that the
new car fits safely between its neighbors.
-/

/--
The relation `F(n) << n` from paper. Car `n` is safely ahead of its follower.
-/
@[reducible]
def Car.IsAheadItsFollower (n : Car) (cars : Finset Car) (b B : ℝ)
    (x v : Car → ℝ) : Prop :=
  ∀ j ∈ cars, n.IsLeaderOf j cars x → j.IsBehind n b B x v

def new (cars : Finset Car) : SetM (Car × Finset Car) := do
  let n ← chooseFrom {n | n ∉ cars}
  return (n, insert n cars)

def delete (cars : Finset Car) : SetM (Finset Car) := do
  let n ← chooseFrom {n | n ∈ cars}
  return cars.erase n

/--
Create new cars and check their conformance.
-/
def create (cars : Finset Car) (b B : ℝ) (x v : Car → ℝ) := do
  let (n, cars_new) ← new cars
  unless (0 ≤ v n ∧ ∀ j ∈ cars, x n ≠ x j) do abort
  unless (n.IsAheadItsFollower cars_new b B x v) do abort -- F(n) << n
  unless (n.IsBehindItsLeader cars_new b B x v) do abort -- n << L(n)
  return cars_new

structure LhcResult extends LaneResult where
  cars : Finset Car

/--
Local highway control with a dynamic set of cars.
-/
def lhc (A b B ε : ℝ) (cars : Finset Car) (x v a : Car → ℝ) : SetM LhcResult := do
  let mut (x, v, a) := (x, v, a)
  let mut cars := cars
  let i ← choose ℕ
  for _ in [:i] do -- run i iterations
    let j ← choose ℕ
    for _ in [:j] do -- delete j cars
      cars ← delete cars
    let j' ← choose ℕ
    for _ in [:j'] do -- create j' cars
      cars ← create cars b B x v
    a ← ctrl_n A b B ε cars x v a
    (x, v, a) ← dyn ε cars x v a
  return { cars, x, v }

/-!
## Model 4: global highway control

Each lane has its own changing set of cars, while positions, velocities, and
accelerations are shared across lanes. Unlike the preceding models, GHC is not
given as an explicit program in the paper; the program below assembles its
lane-wise operations.

A car may occupy multiple lanes. Its single acceleration choice must be allowed
by every lane controller in which it participates. After the lane-wise population
changes and control choices, all cars in the selected lanes evolve together.
-/

/--
Lanes are indexed by natural numbers; `Lane → Finset Car` records their cars.
-/
abbrev Lane := ℕ

structure GhcResult extends LaneResult where
  cars : Lane → Finset Car

/--
Lane-wise deletion, corresponding to `∀ l : L, delete_l∗` from paper.
-/
def delete_l (lanes : Finset Lane) (cars : Lane → Finset Car) :
    SetM (Lane → Finset Car) := do
  let mut cars := cars
  for l in lanes.toList do
    let j ← choose ℕ
    for _ in [:j] do -- delete j cars from lane l
      let laneCars ← delete (cars l)
      cars := Function.update cars l laneCars
  return cars

/--
Lane-wise creation, corresponding to `∀ l : L, new_l∗` from paper.
-/
def create_l (lanes : Finset Lane) (cars : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car) := do
  let mut cars := cars
  for l in lanes.toList do
    let j ← choose ℕ
    for _ in [:j] do -- create j cars in lane l
      let laneCars ← create (cars l) b B x v
      cars := Function.update cars l laneCars
  return cars

/--
Lane-wise global control, corresponding to `∀ l : L, ctrl_n_l` from paper.
A car occupying multiple lanes must choose one acceleration
allowed by each of its lane controllers, all reading the same initial state.
-/
def ctrl_n_l (A b B ε : ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) := do
  let mut a_res := a
  for i in (lanes.biUnion cars).toList do -- all cars in the selected lanes
    let ai ← choose ℝ -- choose a(i) once, including when car i occupies multiple lanes
    for l in lanes.toList do
      if i ∈ cars l then -- lanes containing car i
        let a_new := Function.update a i ai
        -- Check that ai is allowed by the controller for lane l.
        ensure (a_new ∈ SetM.run (ctrl_i A b B ε (cars l) i x v a))
    a_res := Function.update a_res i ai
  return a_res

/--
Global highway control with a dynamic set of cars across multiple lanes.
-/
def ghc (A b B ε : ℝ) (lanes : Finset Lane) (cars : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM GhcResult := do
  let mut (x, v, a) := (x, v, a)
  let mut cars := cars
  let n ← choose ℕ
  for _ in [:n] do
    cars ← delete_l lanes cars
    cars ← create_l lanes cars b B x v
    a ← ctrl_n_l A b B ε lanes cars x v a
    (x, v, a) ← dyn ε (lanes.biUnion cars) x v a
  return { cars, x, v }

end FM11
