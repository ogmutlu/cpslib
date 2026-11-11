import CPSLib.Core.QODE

/-!
# Highway control with changing car populations

The FM11 case study develops four controllers: a follower and leader in one lane,
a fixed population in one lane, a changing population in one lane, and a changing
population across several lanes. Each controller alternates discrete acceleration
choices with continuous car motion.

We introduce the shared safety relations and dynamics first, then assemble the four
models. Their specifications are in `CPSLib.Examples.FM11.Challenge`, with proofs in
`CPSLib.Examples.FM11.Proof`.

## Car state and braking parameters

Cars are identified by natural numbers. The functions `x`, `v`, and `a` give their
positions, velocities, and accelerations along the road. A finite set `C` records
which cars participate in a lane.

The controller parameters are maximum acceleration `A`, minimum guaranteed braking
magnitude `b`, maximum braking magnitude `B`, and maximum time `ε` between control
updates. The safety specifications assume `0 ≤ A`, `0 < b ≤ B`, and `0 < ε`.
-/

open CPSLib

namespace FM11

abbrev Car := Nat
/- Position x, velocity v, and acceleration a for every car. -/
abbrev xva := (Car → ℝ) × (Car → ℝ) × (Car → ℝ)

structure Result where
  x : Car → ℝ
  v : Car → ℝ

structure LocalHighwayResult extends Result where
  C : Finset Car

/-!
## Safe following and lane order

Safe following depends on braking distances as well as position. For distinct cars,
`Behind b B x v f l` requires the follower to be strictly behind the leader and
to stop short of the leader's stopping position under the respective braking bounds.
It also requires both velocities to be nonnegative.

The leader relation `L` identifies the next car ahead, with no participating car
between the two. It is a relation rather than a total function: the frontmost car
has no leader.
-/

/-- The relation `f << l` from Section 5.2. -/
@[reducible]
def Behind (b B : ℝ) (x v : Car → ℝ) (f l : Car) : Prop :=
  (x f ≤ x l) ∧
    (f ≠ l →
      (x f < x l ∧ x f + (v f ^ 2) / (2 * b) < x l + (v l ^ 2) / (2 * B) ∧
      v f ≥ 0 ∧ v l ≥ 0))

/-- The car `l = L(i)` is the leader of car `i`.
Represented as a relation rather than a function.
The condition `i ∈ C ∧ l ∈ C`, implicit in the paper, is explicit here.
-/
@[reducible]
def L (C : Finset Car) (x : Car → ℝ) (i : Car) (l : Car) : Prop :=
  i ∈ C ∧ l ∈ C ∧ x i < x l ∧ ∀ k ∈ C,
    (k ≠ i ∧ k ≠ l) → (x k < x i ∨ x l < x k)

/-- The relation `i << L(i)` from Section 5.2.
Car `i` is safely behind its leader.
-/
@[reducible]
def BehindL (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) (i : Car) : Prop :=
  ∀ l ∈ C, L C x i l → Behind b B x v i l

/-- Lane safety: nonnegative velocities, distinct positions, and each car safely
behind its leader. This combined predicate is not present in the paper.
-/
@[reducible]
def LaneSafe (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) : Prop :=
  (∀ i ∈ C, 0 ≤ v i) ∧
  (∀ i ∈ C, ∀ j ∈ C, i ≠ j → x i ≠ x j) ∧
  (∀ i ∈ C, BehindL C b B x v i)

/-!
`LaneSafe` collects the lane assumptions needed by the controllers. It combines
nonnegative velocities, distinct positions, and safe following of immediate leaders.
`BehindLStar` expresses the stronger conclusion of safe following along any finite
chain of leaders. The chain may have length zero, in which case the endpoint is
the starting car itself.
-/

/-- The relation `i << L*(i)` from Section 6.2.
Car `i` is safely behind every car `l = L^n(i)` for some `n ≥ 0`.
-/
@[reducible]
def BehindLStar (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) (i : Car) : Prop :=
  ∀ k ∈
    (SetM.run do
    let mut k := i
    let n ← choose ℕ
    for _ in [:n] do
      let l ← chooseFrom {l | L C x k l} -- L(k)
      k := l
    return k),
  Behind b B x v i k

/-!
## Continuous motion between control updates

For participating cars, motion follows `x' = v`, `v' = a`, and `a' = 0`.
Acceleration is therefore constant during each continuous segment.
A clock starts at zero and evolves with derivative one. The evolution domain
prevents negative velocities and limits each segment to at most `ε` time units.
The duration is chosen nondeterministically within that domain.
-/

/-- Quantified ODE for car motion. -/
@[simp] def motion (C : Finset Car) : Set Car × (xva → xva) :=
  (C, fun (_x, v, a) => (v, a, 0))

/-- ODE modelling time. -/
@[simp] def time : ℝ → ℝ := fun _t => 1

/-- Evolution domain: velocities remain nonnegative and elapsed time is at most `ε`. -/
@[simp] def domain (ε : ℝ) (C : Finset Car) : xva × ℝ → Prop
  | ((_x, v, _a), t) => (∀ i ∈ C, 0 ≤ v i) ∧ t ≤ ε

/-- Evolve the cars simultaneously with a clock starting at zero. -/
def dyn (ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) := do
  let ((x, v, a), _t) ← evolve (motion C, time)
                               (domain ε C)
                               ((x, v, a), 0)
  return (x, v, a)

/-- Following-distance test allowing an acceleration choice until the next update. -/
@[reducible]
def Safe_ε (A b B ε : ℝ) (x v : Car → ℝ) (f l : Car) : Prop :=
  x f + (v f ^ 2) / (2 * b) + (A / b + 1) * (A / 2 * ε ^ 2 + ε * v f) <
    x l + v l ^ 2 / (2 * B)

/-!
## Model 1: local lane control

The leader may choose any acceleration within its bounds. The follower has three
options: brake, use the `Safe_ε` margin to choose an acceleration within the wider
bounds, or keep zero acceleration when already stopped.

One control cycle updates both accelerations and then evolves the two cars together.
The number of cycles is arbitrary and may be zero.
-/

/-- Update the leader's acceleration `a(l)` within `[-B, A]`. -/
def l_ctrl (A B : ℝ) (l : Car) (a : Car → ℝ) : SetM (Car → ℝ) := do
  let al ← choose ℝ
  unless (-B ≤ al ∧ al ≤ A) do abort
  return Function.update a l al

/-- Update the follower's acceleration `a(f)`: brake, choose a safe acceleration,
or remain stopped. -/
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

/-- Local lane control with two cars: `f` (follower) and `l` (leader). -/
def llc (A b B ε : ℝ) (f l : Car) (x v a : Car → ℝ) : SetM Result := do
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
to its own leader. A leader is selected only in the branch that needs one.
All controllers read the same initial state, and their acceleration choices are
collected before the cars move together.
-/

/-- Generalized `f_ctrl`: in the second option, `Safe_ε` must hold for `L(i)`.
This is not equivalent to:
`let l ← chooseS {l | L C x i l} ; f_ctrl`
because that would require every car to have a leader and fail otherwise.
The frontmost car has no leader, so it must choose the first or third option.
-/
def ctrl_i (A b B ε : ℝ) (C : Finset Car) (i : Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) :=
  (do
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ -b) do abort
    return Function.update a i ai)
    <|>
  (do
    let l ← chooseFrom {l | L C x i l} -- leader of car i
    unless Safe_ε A b B ε x v i l do abort
    let ai ← choose ℝ
    unless (-B ≤ ai ∧ ai ≤ A) do abort
    return Function.update a i ai)
    <|>
  (do
    unless v i = 0 do abort
    return Function.update a i 0)

/-- Run the controllers for all cars simultaneously: each reads the same initial
state. Each `ctrl_i` only updates `a(i)`, so a sequential loop collecting those
updates preserves the simultaneous control semantics.
-/
def ctrl_n (A b B ε : ℝ) (C : Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) := do
  let mut a_res := a
  for i in C.toList do
    let ai ← ctrl_i A b B ε C i x v a
    a_res := Function.update a_res i (ai i)
  return a_res

-- def ctrl_n (A b B ε : ℝ) (C : Finset Car)
--     (x v a : Car → ℝ) : SetM (Car → ℝ) := do
--   chooseS {a' | (∀ i ∈ C, Function.update a i (a' i) ∈
--                   SetM.run (ctrl_i A b B ε C i x v a)) ∧
--                   ∀ i, i ∉ C → a' i = a i}

/-- Global lane control with a fixed set of cars. -/
def glc (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) : SetM Result := do
  let mut (x, v, a) := (x, v, a)
  let n ← choose ℕ
  for _ in [:n] do
    a ← ctrl_n A b B ε C x v a
    (x, v, a) ← dyn ε C x v a
  return { x, v }

/-!
## Model 3: local highway control

The population can now change between motion segments. Deletion removes a car from
the participating set. Creation selects an unused identifier and checks that the
new car fits safely between its neighbors.

The functions `x` and `v` already assign values to every identifier; creation
admits a car with those values rather than assigning a new position or velocity.
The explicit nonnegative-velocity and distinct-position test supplements the
paper's neighbor tests, as marked below.
-/

/-- The relation `F(n) << n` from Section 6.2.
Car `n` is safely ahead of its follower.
-/
@[reducible]
def FBehind (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) (n : Car) : Prop :=
  ∀ j ∈ C, L C x j n → Behind b B x v j n

def new (C : Finset Car) : SetM (Car × Finset Car) := do
  let n ← chooseFrom {n | n ∉ C}
  return (n, insert n C)

def delete (C : Finset Car) : SetM (Finset Car) := do
  let n ← chooseFrom {n | n ∈ C}
  return C.erase n

def create (C : Finset Car) (b B : ℝ) (x v : Car → ℝ) := do
  let (n, C_new) ← new C
  unless (0 ≤ v n ∧ ∀ j ∈ C, x n ≠ x j) do abort -- additional test, absent from the paper
  unless (FBehind C_new b B x v n) do abort -- F(n) << n
  unless (BehindL C_new b B x v n) do abort -- n << L(n)
  return C_new

/-- Local highway control with a dynamic set of cars. -/
def lhc (A b B ε : ℝ) (C : Finset Car) (x v a : Car → ℝ) :
    SetM LocalHighwayResult := do
  let mut (x, v, a) := (x, v, a)
  let mut C := C
  let i ← choose ℕ
  for _ in [:i] do -- run i iterations
    let j ← choose ℕ
    for _ in [:j] do -- delete j cars
      C ← delete C
    let j' ← choose ℕ
    for _ in [:j'] do -- create j' cars
      C ← create C b B x v
    a ← ctrl_n A b B ε C x v a
    (x, v, a) ← dyn ε C x v a
  return { C, x, v }

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

/-- Lanes are indexed by natural numbers; `Lane → Finset Car` records their cars. -/
abbrev Lane := Nat

structure GlobalHighwayResult extends Result where
  C : Lane → Finset Car

/-- Lane-wise deletion, corresponding to `∀l : L delete_l∗`. -/
def delete_l (lanes : Finset Lane) (C : Lane → Finset Car) :
    SetM (Lane → Finset Car) := do
  let mut C := C
  for l in lanes.toList do
    let j ← choose ℕ
    for _ in [:j] do -- delete j cars from lane l
      let cars ← delete (C l)
      C := Function.update C l cars
  return C

/-- Lane-wise creation, corresponding to `∀l : L new_l∗`, with the tests in `create`. -/
def create_l (lanes : Finset Lane) (C : Lane → Finset Car)
    (b B : ℝ) (x v : Car → ℝ) : SetM (Lane → Finset Car) := do
  let mut C := C
  for l in lanes.toList do
    let j ← choose ℕ
    for _ in [:j] do -- create j cars in lane l
      let cars ← create (C l) b B x v
      C := Function.update C l cars
  return C

/-- Lane-wise global control, corresponding to `∀l : L ctrl_n_l`.
A car occupying multiple lanes must choose one acceleration
allowed by each of its lane controllers, all reading the same initial state.
-/
def ctrl_n_l (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM (Car → ℝ) := do
  let mut a_res := a
  for i in (lanes.biUnion C).toList do -- all cars in the selected lanes
    let ai ← choose ℝ -- choose a(i) once, including when car i occupies multiple lanes
    for l in lanes.toList do
      if i ∈ C l then -- lanes containing car i
        let a_new := Function.update a i ai
        -- Check that ai is allowed by the controller for lane l.
        ensure (a_new ∈ SetM.run (ctrl_i A b B ε (C l) i x v a))
    a_res := Function.update a_res i ai
  return a_res

/-- Global highway control with a dynamic set of cars across multiple lanes. -/
def ghc (A b B ε : ℝ) (lanes : Finset Lane) (C : Lane → Finset Car)
    (x v a : Car → ℝ) : SetM GlobalHighwayResult := do
  let mut (x, v, a) := (x, v, a)
  let mut C := C
  let n ← choose ℕ
  for _ in [:n] do
    C ← delete_l lanes C
    C ← create_l lanes C b B x v
    a ← ctrl_n_l A b B ε lanes C x v a
    (x, v, a) ← dyn ε (lanes.biUnion C) x v a
  return { C, x, v }

end FM11
