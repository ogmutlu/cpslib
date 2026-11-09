import CPSLib.Core.ODE

open CPSLib

namespace ACASX

/-!
ACAS X is an airborne collision avoidance system that gives pilots vertical guidance.
We consider two aircraft: the ownship, equipped with ACAS X, and an intruder that may
collide with it. Advisories request changes to, or maintenance of, the ownship’s
vertical velocity. The models identify the conditions under which an advisory is safe,
i.e. if the aircraft start in those conditions and the pilot follows the advisory as
assumed, a near mid-air collision (NMAC) will be avoided.

The case study STTT17 begins with a simple model assuming immediate pilot response,
then progressively extend it to account for response delays, two-sided advisories, and
advisories whose safety depends on a suitable follow-up.

Let us start with some definitions that will be useful for all models.
-/

/--
The direction of an ACAS X advisory: up or down.
Its sign is used in arithmetic expressions.
-/
inductive Direction where
  | up
  | down
deriving DecidableEq, Repr

def Direction.sign : Direction → ℝ
  | .up => 1
  | .down => -1

/--
An advisory given by ACAS X, specifying a direction and a target vertical velocity.
- `direction`: upward or downward advisory direction.
- `targetv`: target vertical velocity for ownship.
-/
structure Advisory where
  direction : Direction
  targetv : ℝ

/--
The velocity shortfall of `v` relative to the advisory's target, in the advisory's
direction. For example, a downward advisory with target `-5` and current velocity `2`
also has shortfall `7`. Zero if the target is already met or exceeded in that direction.
-/
@[reducible]
def Advisory.shortfallOf (advisory : Advisory) (v : ℝ) : ℝ :=
  max 0 (advisory.direction.sign * (advisory.targetv - v))

/--
The encounter state of the ownship and intruder.
- `r`: signed horizontal separation between ownship and intruder.
- `h`: intruder altitude relative to ownship.
- `v`: ownship's vertical velocity.
-/
structure Encounter where
  r : ℝ
  h : ℝ
  v : ℝ

/--
Holds when `hn` is the ownship's vertical displacement after time `t`
along the reference trajectory: start with vertical velocity `v`, accelerate
in the advisory's direction with magnitude `alo` until reaching the advisory's
target velocity, then keep that velocity. (Fig. 3 : `A`)
-/
@[reducible]
def A (alo t hn v : ℝ) (advisory : Advisory) : Prop :=
  let w := advisory.direction.sign
  let vlo := advisory.targetv
  let timeToTarget := advisory.shortfallOf v / alo
  -- Before reaching the target: accelerate with `w * alo`.
  (0 ≤ t ∧ t < timeToTarget ∧ hn = w * alo / 2 * t ^ 2 + v * t) ∨
  -- From the target-reaching time onward: continue at velocity `vlo`.
  (timeToTarget ≤ t ∧ hn = vlo * t - w * advisory.shortfallOf v ^ 2 / (2 * alo))

/-- Fig. 3: implicit lower safe region. -/
@[reducible]
def Limpl (rp hp rv alo : ℝ) (state : Encounter) (advisory : Advisory) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ A alo t hn state.v advisory →
    rp < |state.r - rn| ∨ advisory.direction.sign * (state.h - hn) < -hp

/-!
### Pilot response and motion

The pilot must accelerate by at least `alo` in the advisory's direction whenever
the target has not yet been reached. Relative motion follows `r' = -rv`, `h' = -v`,
and `v' = a`. Acceleration is fixed within each continuous segment.

Only the three real coordinates enter the ODE. The encounter record is converted
to a tuple before evolution and reconstructed afterward; discrete advisory values
and fixed parameters are not differentiated.
-/

@[reducible]
def advisoryLo (alo v a : ℝ) (advisory : Advisory) : Prop :=
  let w := advisory.direction.sign
  w * advisory.targetv ≤ w * v ∨ alo ≤ w * a

def Encounter.coordinates (state : Encounter) : ℝ × ℝ × ℝ :=
  (state.r, state.h, state.v)

def Encounter.ofCoordinates (coordinates : ℝ × ℝ × ℝ) : Encounter :=
  { r := coordinates.1, h := coordinates.2.1, v := coordinates.2.2 }

/-- From Eq. (1). -/
def motion (rv a : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ :=
  fun (_r, _h, v) => (-rv, -v, a)

/-- From Eq. (1): lower compliance throughout the segment. -/
def lowerDomain (alo a : ℝ) (advisory : Advisory) : ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v a advisory

/-!
## Model 1: Immediate Response

Each iteration either retains the current advisory or chooses a new direction and
target that pass `Limpl`. The pilot then chooses acceleration and evolves subject
to lower compliance. Choosing `Direction` directly permits exactly up and down.

An arbitrary natural number of iterations includes zero iterations. `ensure`
rejects unsafe choices; the model does not assert that every advisory is accepted.
-/

/--
The result of an immediate-response run.
- `state`: the final encounter state.
- `advisory`: the advisory in effect at that state.
-/
structure Result where
  state : Encounter
  advisory : Advisory

/-- From Theorem 1 and `acasx.kyx`. -/
def immediate (rp hp rv alo : ℝ) (state : Encounter) (advisory : Advisory) : SetM Result := do
  let mut state := state
  let mut advisory := advisory
  let n ← choose ℕ
  for _ in [:n] do
    let replace ← choose Bool
    if replace then
      let direction ← choose Direction
      let targetv ← choose ℝ
      advisory := { direction, targetv }
      ensure (Limpl rp hp rv alo state advisory)
    let a ← choose ℝ
    let coordinates ← evolve (motion rv a) (lowerDomain alo a advisory) state.coordinates
    state := Encounter.ofCoordinates coordinates
  return { state , advisory }

/-!
## Model 2: delayed response
-/

/--
The result of a delayed-response run, extending `Result` with a remaining delay.
- `state`: the final encounter state.
- `advisory`: the advisory in effect at that state.
- `d`: remaining response delay, which can become negative after response starts.

The model's additional real parameters are adverse acceleration bound `ad`, response
delay `δ`, and segment bound `ε`; safety specifications assume they are nonnegative.
-/
structure DelayedResult extends Result where
  d : ℝ

/-- Fig. 5: delayed safe region, following `safe_delay_implicit.kyx`.
The response phase uses `vd`, correcting the printed `v` inside `A`. -/
@[reducible]
def Dimpl (rp hp rv alo ad : ℝ) (state : Encounter) (advisory : Advisory) (d : ℝ) : Prop :=
  let w := advisory.direction.sign
  ∀ t rn hn hd vd : ℝ,
    rn = rv * t ∧
      ((0 ≤ t ∧ t < max 0 d ∧ hn = -(w * ad) / 2 * t ^ 2 + state.v * t) ∨
        ((hd = -(w * ad) / 2 * (max 0 d) ^ 2 + state.v * max 0 d ∧
          vd - state.v = -w * ad * max 0 d) ∧
          A alo (t - max 0 d) (hn - hd) vd advisory)) →
      rp < |state.r - rn| ∨ w * (state.h - hn) < -hp

/-!
The remaining delay decreases at rate one; a segment clock increases at rate one.
Each segment lasts at most `ε`. Lower compliance becomes mandatory once `d ≤ 0`.
The nominal delayed trajectory switches to `A` after `max 0 d` time units, using
the height and velocity reached during the adverse-acceleration phase.
-/

/-- From Eq. (4). -/
def delayedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _d, _t) => (-rv, -v, a, -1, 1)

/-- From Eq. (4). -/
def delayedDomain (alo ε a : ℝ) (advisory : Advisory) :
    ℝ × ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, d, t) => t ≤ ε ∧ (d ≤ 0 → advisoryLo alo v a advisory)

/-- From Theorem 2 and `safe_delay_implicit.kyx`.
A new advisory chooses delay `δ` or `δ + ε`; retaining it preserves the remaining delay.
The segment clock resets before each evolution, while the delay continues to count down. -/
def delayed (rp hp rv alo ad δ ε : ℝ) (state : Encounter) (advisory : Advisory) (d : ℝ) :
    SetM DelayedResult := do
  let mut state := state
  let mut advisory := advisory
  let mut d := d
  let n ← choose ℕ
  for _ in [:n] do
    let replace ← choose Bool
    if replace then
      let targetv ← choose ℝ
      let direction ← choose Direction
      advisory := { direction, targetv }
      d ← chooseS {δ, δ + ε}
      ensure (Dimpl rp hp rv alo ad state advisory d)
    let a ← choose ℝ
    unless -ad ≤ advisory.direction.sign * a do abort
    let (r, h, v, nextDelay, _) ← evolve (delayedMotion rv a) (delayedDomain alo ε a advisory)
      (state.r, state.h, state.v, d, 0)
    state := { r, h, v }
    d := nextDelay
  return { state, advisory, d }

/-!
## Model 3: two-sided advisories
-/

/--
A two-sided advisory, grouping its direction with lower and upper target velocities.
- `direction`: the direction shared by the lower and upper advisory views.
- `lower`: lower target velocity in the advisory's direction.
- `upper`: upper target velocity in the advisory's direction.

The additional real parameter `aup` bounds acceleration toward the upper target.
Positivity and any relation between `alo` and `aup` belong in the safety specifications.
-/
structure TwoSidedAdvisory where
  direction : Direction
  lower : ℝ
  upper : ℝ

def TwoSidedAdvisory.lowerAdvisory (advisory : TwoSidedAdvisory) : Advisory :=
  { direction := advisory.direction, targetv := advisory.lower }

def TwoSidedAdvisory.upperAdvisory (advisory : TwoSidedAdvisory) : Advisory :=
  { direction := advisory.direction, targetv := advisory.upper }

/--
The result of a two-sided-advisory run.
- `state`: the final encounter state.
- `advisory`: the two-sided advisory in effect at that state.
-/
structure TwoSidedResult where
  state : Encounter
  advisory : TwoSidedAdvisory

/-- Fig. 8: nominal upper trajectory. Its terminal speed includes an initial overshoot. -/
@[reducible]
def Aup (aup t hn v : ℝ) (advisory : Advisory) : Prop :=
  let w := advisory.direction.sign
  let vup := advisory.targetv
  (0 ≤ t ∧ t < advisory.shortfallOf v / aup ∧
    hn = w * aup / 2 * t ^ 2 + v * t) ∨
  (advisory.shortfallOf v / aup ≤ t ∧
    hn = w * max (w * vup) (w * v) * t -
      w * advisory.shortfallOf v ^ 2 / (2 * aup))

/-- Fig. 8: implicit upper safe region. -/
@[reducible]
def Uimpl (rp hp rv aup : ℝ) (state : Encounter) (advisory : Advisory) : Prop :=
  ∀ t rn hn : ℝ, rn = rv * t ∧ Aup aup t hn state.v advisory →
    rp < |state.r - rn| ∨ hp < advisory.direction.sign * (state.h - hn)

/-- Fig. 8: either lower or upper implicit safe region. -/
@[reducible]
def Cimpl (rp hp rv alo aup : ℝ) (state : Encounter) (advisory : TwoSidedAdvisory) : Prop :=
  Limpl rp hp rv alo state advisory.lowerAdvisory ∨ Uimpl rp hp rv aup state advisory.upperAdvisory

/-!
The upper compliance condition limits acceleration in the advisory's direction
and permits acceleration away from the upper boundary. The evolution domain
imposes lower and upper compliance on the same motion equations.
-/

@[reducible]
def advisoryUp (aup v a : ℝ) (advisory : Advisory) : Prop :=
  let w := advisory.direction.sign
  (w * v ≤ w * advisory.targetv ∧ w * a ≤ aup) ∨ w * a ≤ 0

/-- From Eq. (5). -/
def twoSidedDomain (alo aup a : ℝ) (advisory : TwoSidedAdvisory) :
    ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v) => advisoryLo alo v a advisory.lowerAdvisory ∧
    advisoryUp aup v a advisory.upperAdvisory

/-- From Theorem 3 and `acasxtwosided.kyx`.
Each iteration retains its advisory or chooses one that passes `Cimpl`, then flies. -/
def twoSided (rp hp rv alo aup : ℝ) (state : Encounter) (advisory : TwoSidedAdvisory) :
    SetM TwoSidedResult := do
  let mut state := state
  let mut advisory := advisory
  let n ← choose ℕ
  for _ in [:n] do
    let replace ← choose Bool
    if replace then
      let direction ← choose Direction
      let lower ← choose ℝ
      let upper ← choose ℝ
      advisory := { direction, lower, upper }
      ensure (Cimpl rp hp rv alo aup state advisory)
    let a ← choose ℝ
    let coordinates ← evolve (motion rv a) (twoSidedDomain alo aup a advisory) state.coordinates
    state := Encounter.ofCoordinates coordinates
  return { state, advisory }

/-!
## Model 4: bounded-time safety

A nonnegative `Duration` is a fixed time bound, not an evolving ODE coordinate.
`TimeLimit` distinguishes an unlimited horizon from a finite duration explicitly,
replacing the negative-number sentinel. The evolving clock `t` remains real.
-/

abbrev Duration := { duration : ℝ // 0 ≤ duration }

inductive TimeLimit where
  | unlimited
  | bounded (duration : Duration)

/-- Whether the current clock is within the selected horizon. -/
def TimeLimit.allows : TimeLimit → ℝ → Prop
  | .unlimited, _ => True
  | .bounded duration, t => t ≤ duration.val

/-- Whether a nominal future time lies within the remaining horizon. -/
def TimeLimit.includes : TimeLimit → ℝ → ℝ → Prop
  | .unlimited, _, _ => True
  | .bounded duration, t, tn => tn ≤ duration.val - t

/--
The result of a clocked run, extending `TwoSidedResult` with the advisory's clock.
- `state`: the final encounter state.
- `advisory`: the two-sided advisory in effect at that state.
- `t`: elapsed time since the most recent advisory selection and clock reset,
  or the supplied initial clock advanced by flight if no reset occurred.
-/
structure TimedResult extends TwoSidedResult where
  t : ℝ

/-- Fig. 10: bounded lower region, following `bounded_implicit.kyx`.
Uses the corrected `-hp` sign and keeps the current clock explicit. -/
@[reducible]
def LimplBounded (rp hp rv alo : ℝ) (limit : TimeLimit) (t : ℝ) (state : Encounter)
    (advisory : Advisory) : Prop :=
  ∀ tn rn hn : ℝ,
    limit.includes t tn ∧ rn = rv * tn ∧ A alo tn hn state.v advisory →
      rp < |state.r - rn| ∨ advisory.direction.sign * (state.h - hn) < -hp

/-- Fig. 10: bounded upper region. -/
@[reducible]
def UimplBounded (rp hp rv aup : ℝ) (limit : TimeLimit) (t : ℝ) (state : Encounter)
    (advisory : Advisory) : Prop :=
  ∀ tn rn hn : ℝ,
    limit.includes t tn ∧ rn = rv * tn ∧ Aup aup tn hn state.v advisory →
      rp < |state.r - rn| ∨ hp < advisory.direction.sign * (state.h - hn)

/-- Fig. 10: either bounded safe region. -/
@[reducible]
def CimplBounded (rp hp rv alo aup : ℝ) (limit : TimeLimit) (t : ℝ) (state : Encounter)
    (advisory : TwoSidedAdvisory) : Prop :=
  LimplBounded rp hp rv alo limit t state advisory.lowerAdvisory ∨
    UimplBounded rp hp rv aup limit t state advisory.upperAdvisory

/-!
### A shared clocked controller

The clock increases at rate one. Each outer iteration chooses an advisory, checks
its acceptance predicate at clock zero, and resets the clock. Inner segments may
change acceleration without changing the advisory or resetting the clock.
-/

/-- From Eq. (8). -/
def clockedMotion (rv a : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_r, _h, v, _t) => (-rv, -v, a, 1)

/-- From Eq. (8): time bound and two-sided compliance throughout a segment. -/
def clockedDomain (alo aup : ℝ) (limit : TimeLimit) (a : ℝ)
    (advisory : TwoSidedAdvisory) : ℝ × ℝ × ℝ × ℝ → Prop :=
  fun (_r, _h, v, t) => limit.allows t ∧
    advisoryLo alo v a advisory.lowerAdvisory ∧ advisoryUp aup v a advisory.upperAdvisory

/-- Common program from Eqs. (8)/(9), with a typed advisory-acceptance predicate. -/
def clocked (rv alo aup : ℝ) (limit : TimeLimit)
    (safe : Encounter → TwoSidedAdvisory → ℝ → Prop)
    (state : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult := do
  let mut state := state
  let mut advisory := advisory
  let mut t := t
  let n ← choose ℕ
  for _ in [:n] do
    let lower ← choose ℝ
    let upper ← choose ℝ
    let direction ← choose Direction
    advisory := { direction, lower, upper }
    ensure (safe state advisory 0)
    t := 0
    let m ← choose ℕ
    for _ in [:m] do
      let a ← choose ℝ
      let (r, h, v, nextTime) ← evolve (clockedMotion rv a) (clockedDomain alo aup limit a advisory)
        (state.r, state.h, state.v, t)
      state := { r, h, v }
      t := nextTime
  return { state, advisory, t }

/-- From Theorem 4: `CimplBounded` supplies the acceptance predicate. -/
def bounded (rp hp rv alo aup : ℝ) (limit : TimeLimit) (state : Encounter)
    (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult :=
  clocked rv alo aup limit
    (fun state advisory t => CimplBounded rp hp rv alo aup limit t state advisory)
    state advisory t

/-!
## Model 5: safeability

Safeability requires a finite, nonnegative duration, so there is a definite endpoint
at which to check continuation. Its real follow-up targets `vloEx` and `vupEx`
remain separate from the current advisory. The lower continuation keeps the
direction; the upper continuation reverses it.
-/

/-- Fig. 12: lower endpoint, following `condImplSafeableLo` in `AcasXSafeable.scala`.
The accelerating height uses the corrected `v * τ`, rather than `vlo * τ`. -/
@[reducible]
def lowerEndpoint (alo τ hn vn v : ℝ) (advisory : Advisory) : Prop :=
  let w := advisory.direction.sign
  let vlo := advisory.targetv
  (0 ≤ τ ∧ τ < advisory.shortfallOf v / alo ∧
    hn = w * alo / 2 * τ ^ 2 + v * τ ∧ vn = w * alo * τ + v) ∨
  (advisory.shortfallOf v / alo ≤ τ ∧
    hn = vlo * τ - w * advisory.shortfallOf v ^ 2 / (2 * alo) ∧ vn = vlo)

/-- Fig. 12: upper endpoint, following `condImplSafeableUp` in `AcasXSafeable.scala`.
The accelerating height uses the corrected `v * τ`, rather than `vup * τ`. -/
@[reducible]
def upperEndpoint (aup τ hn vn v : ℝ) (advisory : Advisory) : Prop :=
  let w := advisory.direction.sign
  let vup := advisory.targetv
  (0 ≤ τ ∧ τ < advisory.shortfallOf v / aup ∧
    hn = w * aup / 2 * τ ^ 2 + v * τ ∧ vn = w * aup * τ + v) ∨
  (advisory.shortfallOf v / aup ≤ τ ∧
    hn = w * max (w * vup) (w * v) * τ -
      w * advisory.shortfallOf v ^ 2 / (2 * aup) ∧
    vn = w * max (w * vup) (w * v))

/-- Fig. 12: safeability, following `condImplSafeable` in `AcasXSafeable.scala`.
The upper follow-up reverses direction. Endpoint heights retain the artifact corrections. -/
@[reducible]
def CimplSafeable (rp hp rv alo aup : ℝ) (duration : Duration) (t : ℝ)
    (vloEx vupEx : ℝ) (state : Encounter) (advisory : TwoSidedAdvisory) : Prop :=
  let τ := duration.val - t
  (LimplBounded rp hp rv alo (.bounded duration) t state advisory.lowerAdvisory ∧
    ∀ hn vn : ℝ, lowerEndpoint alo τ hn vn state.v advisory.lowerAdvisory →
      Limpl rp hp rv alo { r := state.r - rv * τ, h := state.h - hn, v := vn }
        { direction := advisory.direction, targetv := vloEx }) ∨
  (UimplBounded rp hp rv aup (.bounded duration) t state advisory.upperAdvisory ∧
    ∀ hn vn : ℝ, upperEndpoint aup τ hn vn state.v advisory.upperAdvisory →
      Limpl rp hp rv alo { r := state.r - rv * τ, h := state.h - hn, v := vn }
        { direction := if advisory.direction = .down then .up else .down,
          targetv := vupEx })

/-- From Theorem 5: checks safe continuation without executing it as a separate phase. -/
def safeable (rp hp rv alo aup : ℝ) (duration : Duration) (vloEx vupEx : ℝ)
    (state : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult :=
  clocked rv alo aup (.bounded duration)
    (fun state advisory t => CimplSafeable rp hp rv alo aup duration t vloEx vupEx state advisory)
    state advisory t

/-!
## Safety predicates for the specifications

`Bounds` collects the shared parameter assumptions without restricting the types
of the model's inputs. `NoNMAC` excludes a near mid-air collision by requiring strict
separation in at least one dimension.
-/

@[reducible]
def Bounds (rp hp rv alo : ℝ) : Prop := 0 ≤ rp ∧ 0 < hp ∧ 0 ≤ rv ∧ 0 < alo

@[reducible]
def NoNMAC (rp hp : ℝ) (state : Encounter) : Prop :=
  rp < |state.r| ∨ hp < |state.h|

/-!
## Reducing planar horizontal motion to one coordinate

The advisory models use one signed horizontal coordinate. The final definitions
relate it to planar relative position `(x, y)` moving at constant velocity `(rx, ry)`.
Along-track position `s` decreases at rate `rv`; cross-track offset `n` stays constant.
`HorizontalCoordinates` records the projection, distance, and speed identities.
-/

/-- From Eq. (11). -/
def horizontalMotion (rx ry rv : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
  fun (_x, _y, _s, _n) => (rx, ry, -rv, 0)

/-- From Eq. (11). -/
@[reducible]
def HorizontalCoordinates (rx ry rv x y s n : ℝ) : Prop :=
  x * rx + y * ry = -s * rv ∧ x * ry - y * rx = n * rv ∧
    x ^ 2 + y ^ 2 = n ^ 2 + s ^ 2 ∧ rv ^ 2 = rx ^ 2 + ry ^ 2

end ACASX
