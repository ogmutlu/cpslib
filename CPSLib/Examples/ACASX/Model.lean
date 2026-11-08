import CPSLib.Core.ODE

/-!
# Aircraft collision avoidance with vertical advisories

The ACASX case study develops five advisory models: immediate response, delayed
response, two-sided advisories, bounded-time safety, and safeability. Each section
introduces only the additional definitions needed for its controller, then gives
the controller itself.

The specifications are in `CPSLib.Examples.ACASX.Challenge`, with independent proofs
in `CPSLib.Examples.ACASX.Proof`. Figure and theorem references below refer to STTT17;
the declaration notes retain the corrections and choices from its artifacts.
-/

open CPSLib

namespace ACASX

/-!
## Model 1: immediate response

The encounter state consists of signed horizontal separation `r`, relative altitude
`h`, and ownship vertical velocity `v`. Horizontal closing speed `rv` is constant.
An advisory specifies sense `w` and target vertical velocity `vlo`, with
`w = 1` for up and `w = -1` for down. The result retains the state and advisory.
-/

structure Result where
  r : ℝ -- horizontal distance between ownship and intruder
  h : ℝ -- height of the intruder relative to the ownship
  v : ℝ
  w : ℝ
  vlo : ℝ

/-!
### Accepting an advisory

`maxI` measures the nonnegative velocity shortfall in the advisory's sense.
The nominal trajectory `A` accelerates with signed acceleration `w * alo` until
its target is reached, then continues at `vlo`. It relates elapsed time `t` to
nominal vertical displacement `hn`.

`Limpl` is the advisory's lower safe region: at every nominal point, either
horizontal separation exceeds the protected distance `rp`, or relative altitude
lies strictly beyond the vertical boundary determined by `hp` and the sense.
The region describes encounter states, including velocity, rather than position alone.
-/

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

/-!
### Pilot response and motion

The pilot must accelerate by at least `alo` in the advisory's sense whenever the
target has not yet been reached. Relative motion follows `r' = -rv`, `h' = -v`,
and `v' = a`. Acceleration `a` is fixed within a segment, while its duration is
nondeterministic. The evolution domain enforces compliance throughout the segment.
The program `sense` chooses either advisory direction.
-/

@[reducible]
def advisoryLo (alo v w vlo a : ℝ) : Prop := w * vlo ≤ w * v ∨ alo ≤ w * a

/-- From Eq. (1) -/
def motion (rv a : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun (_r, _h, v) => (-rv, -v, a)

/-- From Eq. (1) -/
def lowerDomain (alo w vlo a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a

/-!
### The immediate-response controller

Each iteration either retains the current advisory or chooses a new sense and
target that pass the lower safe-region test. The pilot then chooses acceleration
and evolves subject to lower compliance.

An arbitrary natural number of iterations represents finite repetition, including
zero iterations. `ensure` rejects unsafe advisory choices; the model does not
assert that every proposed advisory is accepted.
-/

/-- From Theorem 1, and `acasx.kyx`. -/
def immediate (rp hp rv alo r h v w vlo : ℝ) : SetM Result := do
  let mut (r, h, v, w, vlo) := (r, h, v, w, vlo)
  let n ← choose ℕ
  for _ in [:n] do
    let bool ← choose Bool
    if bool then
      w ← chooseS {-1, 1}
      vlo ← choose ℝ
      ensure (Limpl rp hp rv alo r h v w vlo)
      -- advisory := (w, vlo)
    let a ← choose ℝ
    (r, h, v) ← evolve (motion rv a) (lowerDomain alo w vlo a) (r, h, v)
  return { r, h, v, w, vlo }

/-!
## Model 2: delayed response

Delayed response adds a remaining delay `d` to the result. Before the delay expires,
the nominal trajectory uses acceleration opposite to the advisory, with magnitude
`ad`. After `max 0 d` time units, it continues along `A` from the resulting height
`hd` and velocity `vd`. `Dimpl` requires protected separation over both parts.
A nonpositive remaining delay begins the response phase immediately.
-/

structure DelayedResult extends Result where
  d : ℝ

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

/-!
The remaining delay decreases at rate one, and a segment clock increases at rate
one. Each segment lasts at most `ε`. Lower compliance becomes mandatory when the
remaining delay is nonpositive.
-/

/-- From Eq. (4) -/
def delayedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _d, _t) => (-rv, -v, a, -1, 1)

/-- From Eq. (4) -/
def delayedDomain (alo ε w vlo a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, d, t) => t ≤ ε ∧ (d ≤ 0 → advisoryLo alo v w vlo a)

/-!
A new advisory chooses delay `δ` or `δ + ε` and must pass `Dimpl`. Keeping the
advisory also keeps its current remaining delay. The segment clock resets before
each evolution, whereas the delay continues to count down. Every acceleration
choice is bounded below by `-ad` in the advisory's sense.
-/

/-- From Theorem 2, and `safe_delay_implicit.kyx`.
Choosing d `δ` is the `advisory := (w, vlo)` case, `δ + ε` is the `advisory := COC` case.
Advisory labels have no operational use. -/
def delayed (rp hp rv alo ad δ ε r h v w vlo d : ℝ) : SetM DelayedResult := do
  let mut (r, h, v, w, vlo, d) := (r, h, v, w, vlo, d)
  let n ← choose ℕ
  for _ in [:n] do
    let bool ← choose Bool
    if bool then
      vlo ← choose ℝ
      w ← chooseS {-1, 1}
      d ← chooseS {δ, (δ + ε)}
      ensure (Dimpl rp hp rv alo ad r h v w vlo d)
    let a ← choose ℝ
    unless (-ad ≤ w * a) do abort
    (r, h, v, d, _) ←
      evolve (delayedMotion rv a) (delayedDomain alo ε w vlo a) (r, h, v, d, 0)
  return { r, h, v, w, vlo, d }

/-!
## Model 3: two-sided advisories

Two-sided advisories add an upper target velocity `vup`. The nominal upper
trajectory `Aup` uses acceleration bound `aup`; its final speed accounts for an
initial velocity already beyond `vup`. `Uimpl` checks separation along this upper
boundary, and `Cimpl` accepts either the lower or upper safe region.
-/

structure TwoSidedResult extends Result where
  vup : ℝ

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

/-!
The upper compliance condition limits acceleration in the advisory's sense and
permits acceleration away from the upper boundary. The two-sided evolution domain
imposes both lower and upper compliance on the same motion equations.
-/

@[reducible]
def advisoryUp (aup v w vup a : ℝ) : Prop := (w * v ≤ w * vup ∧ w * a ≤ aup) ∨ w * a ≤ 0

/-- From Eq. (5) -/
def twoSidedDomain (alo aup w vlo vup a : ℝ) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

/-!
A new advisory chooses a sense and both velocity targets, then checks `Cimpl`.
As in the immediate model, an iteration may instead keep the current advisory.
Motion must obey both compliance conditions throughout each segment.
-/

/-- From Theorem 3, and `acasxtwosided.kyx`. -/
def twoSided (rp hp rv alo aup r h v w vlo vup : ℝ) : SetM TwoSidedResult := do
  let mut (r, h, v, w, vlo, vup) := (r, h, v, w, vlo, vup)
  let n ← choose ℕ
  for _ in [:n] do
    let bool ← choose Bool
    if bool then
      w ← chooseS {-1, 1}
      vlo ← choose ℝ
      vup ← choose ℝ
      ensure (Cimpl rp hp rv alo aup r h v w vlo vup)
      -- advisory := (w, vlo, vup)
    let a ← choose ℝ
    (r, h, v) ← evolve (motion rv a) (twoSidedDomain alo aup w vlo vup a) (r, h, v)
  return { r, h, v, w, vlo, vup }

/-!
## Model 4: bounded-time safety

Bounded-time safety adds a clock `t` to the result and restricts nominal look-ahead
to the remaining interval `tl - t`. A negative limit `tl` removes this restriction.
The bounded lower and upper regions use the trajectories already introduced;
`CimplBounded` accepts either region.
-/

structure TimedResult extends TwoSidedResult where
  t : ℝ

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

/-!
### A shared clocked controller

The clock increases at rate one. Its domain enforces both compliance conditions
and the time limit, unless `tl` is negative.

The common `clocked` program takes its advisory-acceptance predicate as a parameter.
Each outer iteration selects new targets and sense, checks that predicate at
clock zero, and resets `t`. An arbitrary number of inner segments may then change
acceleration without changing the advisory or resetting the clock.
-/

/-- From Eq. (8) -/
def clockedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _t) => (-rv, -v, a, 1)

/-- From Eq. (8) -/
def clockedDomain (alo aup tl w vlo vup a : ℝ) : ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, t) => (t ≤ tl ∨ tl < 0) ∧
    advisoryLo alo v w vlo a ∧ advisoryUp aup v w vup a

/-- Common program from Eqs. (8)/(9) (equivalent to paper when initially `t=0`) -/
def clocked (rv alo aup tl : ℝ) (safe : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (r h v w vlo vup t : ℝ) : SetM TimedResult := do
  let mut (r, h, v, w, vlo, vup, t) := (r, h, v, w, vlo, vup, t)
  let n ← choose ℕ
  for _ in [:n] do
    vlo ← choose ℝ
    vup ← choose ℝ
    w ← chooseS {-1, 1}
    ensure (safe r h v w vlo vup 0)
    -- advisory := (w, vlo, vup)
    t := 0
    let m ← choose Nat
    for _ in [:m] do
      let a ← choose ℝ
      (r, h, v, t) ← evolve (clockedMotion rv a)
        (clockedDomain alo aup tl w vlo vup a) (r, h, v, t)
  return { r, h, v, w, vlo, vup, t }

/-!
The bounded-time controller supplies `CimplBounded` as its acceptance predicate,
requiring safety over the remaining horizon.
-/

/-- From Theorem 4 -/
def bounded (rp hp rv alo aup tl r h v w vlo vup t : ℝ) :=
  clocked rv alo aup tl
    (fun r h v w vlo vup t => CimplBounded rp hp rv alo aup tl t r h v w vlo vup)
    r h v w vlo vup t

/-!
## Model 5: safeability

Safeability adds a safe follow-up condition at the time limit. `lowerEndpoint`
and `upperEndpoint` describe nominal height and velocity there. `CimplSafeable`
combines bounded safety with an unbounded lower-region check from each corresponding
endpoint. The lower branch keeps sense `w` and uses target `vloEx`; the upper branch
reverses the sense and uses target `vupEx`.
-/

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

/-!
The safeable controller reuses `clocked` with `CimplSafeable` as its acceptance
predicate. It checks the continuation condition; it does not execute the follow-up
advisory as a separate phase.
-/

/-- From Theorem 5 -/
def safeable (rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t : ℝ) :=
  clocked rv alo aup tl
    (fun r h v w vlo vup t =>
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx)
    r h v w vlo vup t

/-!
## Safety predicates for the specifications

The controllers above use the protected horizontal and vertical distances `rp`
and `hp` in their acceptance tests. Their safety specifications additionally use
`Bounds` for parameter assumptions and `NoNMAC` to exclude a near mid-air collision:
strict separation must hold in at least one of the two dimensions.
-/

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

@[reducible]
def NoNMAC (rp hp r h : ℝ) : Prop := rp < |r| ∨ hp < |h|

/-!
## Reducing planar horizontal motion to one coordinate

The advisory models use one signed horizontal coordinate. The final definitions
relate that representation to planar relative position `(x, y)` moving at constant
velocity `(rx, ry)`. Along-track position `s` decreases at rate `rv`, while
cross-track offset `n` stays constant.

`HorizontalCoordinates` records the projection relations, the squared-distance
identity, and the speed identity. The corresponding specification shows that
the planar horizontal-separation test can be written using `s` and the fixed `n`.
-/

/-- From Eq. (11) -/
def horizontalMotion (rx ry rv : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_x, _y, _s, _n) => (rx, ry, -rv, 0)

/-- From Eq. (11) -/
@[reducible]
def HorizontalCoordinates (rx ry rv x y s n : ℝ) : Prop :=
  x * rx + y * ry = -s * rv ∧ x * ry - y * rx = n * rv ∧
    x ^ 2 + y ^ 2 = n ^ 2 + s ^ 2 ∧ rv ^ 2 = rx ^ 2 + ry ^ 2

end ACASX
