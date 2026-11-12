import CPSLib.Core.ODE

/-!
# ACASX Case Study (STTT17), Implicit Formulations of Safe Regions

ACAS X is an airborne collision avoidance system that gives pilots vertical guidance.
We consider two aircraft: the ownship, equipped with ACAS X, and an intruder that may
collide with it. Advisories request changes to, or maintenance of, the ownship’s
vertical velocity. The models identify the conditions under which an advisory is safe,
i.e. if the aircraft start in those conditions and the pilot follows the advisory as
assumed, a near mid-air collision (NMAC) will be avoided. The models consider head-on
encounters: viewed from above, the aircraft approach each other along the same straight
line, with constant relative horizontal speed.

The case study STTT17 begins with a simple model assuming immediate pilot response,
then progressively extend it to account for response delays, two-sided advisories, and
advisories whose safety depends on a suitable follow-up.

Let us start with some definitions that will be useful for all models.
-/

open CPSLib

namespace ACASX

/--
Displacement after time `t`, starting at velocity `v` with constant acceleration `a`.
-/
noncomputable def displacement (a v t : ℝ) : ℝ := (a / 2) * t ^ 2 + v * t

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
- `targetv`: target vertical velocity for ownship (positive for up, negative for down).
-/
structure Advisory where
  direction : Direction
  targetv : ℝ

/--
The shortfall of `v` relative to the advisory's `targetv`, in advisory's direction.
For example, given a downward advisory with target `-5`, `v=2` has shortfall `7`.
Zero if the target is already met or exceeded in that direction.
-/
@[reducible]
def Advisory.shortfallOf (advisory : Advisory) (v : ℝ) : ℝ :=
  max 0 (advisory.direction.sign * (advisory.targetv - v))

/--
The encounter state of the ownship and intruder.
- `r`: signed horizontal separation, intruder position minus ownship position.
- `h`: signed altitude difference, intruder minus ownship.
- `v`: ownship's signed vertical velocity.
-/
structure Encounter where
  r : ℝ
  h : ℝ
  v : ℝ

/--
Holds when, after time `t` (starting from an initial `encounter` state), the intruder is
horizontally farther than `rp` from the ownship position, or vertically separated from
it by more than `hp` on the side *opposite* the advisory's direction. Here `rv` is the
constant horizontal closing speed and `hn` is the ownship's vertical displacement.
-/
def AircraftSeparatedLo
    (advisory : Advisory) (encounter : Encounter) (rp hp rv t hn : ℝ) : Prop :=
  rp < |encounter.r - rv * t| ∨ advisory.direction.sign * (encounter.h - hn) < -hp

/--
Same as `AircraftSeparatedLo`, but in the second disjunct, require the intruder to be
vertically separated from the ownship by more than `hp` on the *same* side of the
advisory's direction.
-/
def AircraftSeparatedUp
    (advisory : Advisory) (encounter : Encounter) (rp hp rv t hn : ℝ) : Prop :=
  rp < |encounter.r - rv * t| ∨ hp < advisory.direction.sign * (encounter.h - hn)

/-!
## Model 1: Immediate Response

In this first model, the pilot responds to advisories without delay.
Clear-of-Conflict (COC), which tells the pilot that no action is needed, is not allowed.
The advisory may change during the encounter, but each new advisory must be safe
even if followed forever. (see Section 3)
-/

/--
Guarantees that `hn` is a *lower* bound on the vertical displacement of the ownship in
advisory's direction.

More precisely, assuming `v` initially does not exceed the target in advisory's direction,
this predicate holds when `hn` is the ownship's signed vertical displacement after time
`t` along the reference trajectory: start with vertical velocity `v`, accelerate in the
advisory's direction with magnitude `alo` until reaching the advisory's target velocity,
then keep that velocity. If `v` already meets or exceeds the target velocity `vlo` in
advisory’s direction, ownship uses `vlo` throughout. So, `hn` is a strict lower bound
in that case. (see Fig. 3, `A`)
-/
@[reducible]
def Advisory.DisplacementLo (advisory : Advisory) (alo v t : ℝ) (hn : ℝ) : Prop :=
  let w := advisory.direction.sign
  let vlo := advisory.targetv
  let timeToTarget := (advisory.shortfallOf v) / alo
  -- Before reaching the target: accelerate with `w * alo`.
  (0 ≤ t ∧ t < timeToTarget ∧ hn = displacement (a := w * alo) v t) ∨
  -- Afterward: keep the target velocity `vlo`.
  (timeToTarget ≤ t ∧ hn = (vlo * t) - w * (advisory.shortfallOf v) ^ 2 / (2 * alo))

/--
Holds when the encounter lies in the lower safe region of the advisory. That means, the
advisory is safe to follow for unlimited time, assuming a lower bound on the displacement
of ownship in advisory's direction. (see Fig. 3, `L⁻¹_impl`)
-/
@[reducible]
def Advisory.LoSafeFor
    (advisory : Advisory) (encounter : Encounter) (rp hp rv alo : ℝ) : Prop :=
  ∀ t hn, advisory.DisplacementLo alo encounter.v t hn →
    AircraftSeparatedLo advisory encounter rp hp rv t hn

/--
The ODE describing the change of the `Encounter` state `(r, h, v)` during flight.
`r' = -rv`, `h' = -v`, `v' = a`. (see Eq. (1))
-/
def motionODE (rv a : ℝ) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)
  | (_r, _h, v) => (-rv, -v, a)

/--
The pilot must accelerate in the advisory's direction at a rate of at least `alo`
until the target velocity is reached. At or beyond the target, this condition
places no restriction on acceleration. (see Eq. (1))
-/
@[reducible]
def Advisory.IsSatisfiedLo (advisory : Advisory) (v a alo : ℝ) : Prop :=
  let w := advisory.direction.sign
  (w * advisory.targetv ≤ w * v) ∨ (alo ≤ w * a)

/--
The evolution requires this condition throughout the flight segment, so the pilot
must immediately respond and comply with the advisory. (see Eq. (1))
-/
def domainLo (alo a : ℝ) (advisory : Advisory) : ℝ × ℝ × ℝ → Prop
  | (_r, _h, v) => advisory.IsSatisfiedLo v a alo

/--
The result of an immediate-response run.
- `encounter`: the final encounter state.
- `advisory`: the advisory in effect at that state.
-/
structure Result where
  encounter : Encounter
  advisory : Advisory

/--
Program for advisory selection and flight with immediate pilot response.
Each iteration keeps the current advisory or selects one that passes `LoSafeFor`,
then follows `motionODE` for any duration permitted by `domainLo`.

Returns all possible final encounters and advisories after any finite number of
iterations, including zero. Advisory choices that fail the safety test are rejected.
(see Eq. 1 and `acasx.kyx`)

See `ACASX.immediate_safe` in `CPSLib.Examples.ACASX.Challenge` for its safety claim.
-/
def immediateResponseProg
    (rp hp rv alo : ℝ) (encounter : Encounter) (advisory : Advisory) : SetM Result := do
  let mut (encounter, advisory) := (encounter, advisory)
  let n ← choose ℕ
  for _ in [:n] do
    let replace ← choose Bool
    if replace then
      advisory ← choose Advisory
      ensure (advisory.LoSafeFor encounter rp hp rv alo)
    let a ← choose ℝ
    let (r, h, v) ← evolve (motionODE rv a) (domainLo alo a advisory)
                           (encounter.r, encounter.h, encounter.v)
    encounter := { r, h, v }
  return { encounter, advisory }

/-!
## Model 2: Delayed Response

The model now allows the pilot to respond after a delay of at most `δ`.
Before responding, the ownship may accelerate opposite to the advisory's direction,
with magnitude bounded by `ad`. Once the delay expires, the response condition from
Model 1 applies.

The model also permits COC if there is an advisory that can safely be followed after
the combined system delay `ε` and pilot delay `δ`. Each flight segment lasts at most
`ε`, allowing the system to reconsider its advisory. (see Section 4)
-/

/--
Holds when an `advisory` is safe for a given `encounter` state and
remaining response delay `d`, which can become negative after response starts.

The ownship first accelerates opposite to the advisory's direction with magnitude
`ad` for `max 0 d` time units. It then follows `DisplacementLo` from the height `hd`
and velocity `vd` reached during the delay. At every time, `AircraftSeparatedLo` must
hold. (see Fig. 5, `Dᵈ_impl` and `safe_delay_implicit.kyx`)
-/
@[reducible]
def Advisory.DelayedSafeFor
    (advisory : Advisory) (encounter : Encounter) (rp hp rv alo ad d : ℝ) : Prop :=
  let w := advisory.direction.sign
  ∀ t hn hd vd,
    let duringDelay := 0 ≤ t ∧ t < max 0 d ∧
                         hn = displacement (a := -w * ad) encounter.v t
    let afterDelay := (hd = displacement (a := -w * ad) encounter.v (max 0 d) ∧
                        vd - encounter.v = -w * ad * max 0 d) ∧
                        advisory.DisplacementLo alo vd (t - max 0 d) (hn - hd)
    duringDelay ∨ afterDelay → AircraftSeparatedLo advisory encounter rp hp rv t hn

/--
The ODE describing the encounter, remaining response delay, and segment clock
`(r, h, v, d, t)` during flight. `r' = -rv`, `h' = -v`, `v' = a`, `d' = -1`,
`t' = 1`. The delay counts down while the clock counts up. (see Eq. (4))
-/
def withDelayODE (rv a : ℝ) : (ℝ × ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ × ℝ)
  | (_r, _h, v, _d, _t) => (-rv, -v, a, -1, 1)

/--
The evolution requires this condition throughout the flight segment. The segment
clock must stay at most `ε`. Once `d ≤ 0`, the pilot must comply with advisory;
before then, compliance is not required. (see Eq. (4))
-/
def domainDelayed (alo ε a : ℝ) (advisory : Advisory) :
    ℝ × ℝ × ℝ × ℝ × ℝ → Prop
  | (_r, _h, v, d, t) => t ≤ ε ∧ (d ≤ 0 → advisory.IsSatisfiedLo v a alo)

structure DelayedResult extends Result where
  d : ℝ

/--
Program for advisory selection and flight with delayed pilot response.
Each iteration keeps the current advisory or selects one that passes `DelayedSafeFor`.

The input `d` is the remaining response delay for the advisory already in effect
at the start of the run. Keeping that advisory preserves its current countdown.
During flight, `d` decreases at rate one. A nonpositive `d` means the pilot must
already comply with the advisory.

A new advisory chooses remaining delay `δ` or `δ + ε`. The first is the ordinary
advisory case, the second represents COC backed by an advisory that can safely be
issued after the system delay `ε` and followed after the pilot delay `δ`.
(see Eq. (4), and `safe_delay_implicit.kyx`)

See `ACASX.delayed_safe` in `CPSLib.Examples.ACASX.Challenge` for its safety claim.
-/
def delayedResponseProg (rp hp rv alo ad δ ε : ℝ)
    (encounter : Encounter) (advisory : Advisory) (d : ℝ) : SetM DelayedResult := do
  let mut (encounter, advisory, d) := (encounter, advisory, d)
  let n ← choose ℕ
  for _ in [:n] do
    let replace ← choose Bool
    if replace then
      advisory ← choose Advisory
      d ← chooseFrom {δ, δ + ε}
      ensure (advisory.DelayedSafeFor encounter rp hp rv alo ad d)
    let a ← choose ℝ
    unless -ad ≤ advisory.direction.sign * a do abort
    let (r, h, v, nextDelay, _) ← evolve (withDelayODE rv a)
                                         (domainDelayed alo ε a advisory)
                                         (encounter.r, encounter.h, encounter.v, d, 0)
    encounter := { r, h, v }
    d := nextDelay
  return { encounter, advisory, d }

/-!
## Model 3: Two-Sided Advisories

An initial advisory may move the ownship toward the intruder before a later
advisory reverses its direction. For example, the ownship may first climb toward
an intruder above, then receive a downward advisory.

To reason about that reversal, we need to bound the position and vertical velocity
reached during the initial climb. Model 1 gives only a lower bound on that motion.
This model adds an upper bound, forming an envelope of possible ownship motion.

This allows more advisories to be accepted, while placing extra limits on the
pilot's response. For example, an upward advisory with an intruder above may be
safe if the upper velocity and acceleration bounds keep the ownship sufficiently
below the intruder while horizontally close. Model 1 may reject that advisory
because there we only consider a lower bound on displacement. The minimum response
accelaration bound `alo` is retained; the upper response condition also uses `aup`.

This prepares for later models with follow-up advisories. Here, each advisory
must still be safe if followed forever. (see Section 5.1)
-/

/--
A two-sided advisory
- `direction`: the direction shared by the lower and upper advisory views.
- `lower`: lower target velocity in the advisory's direction.
- `upper`: upper target velocity in the advisory's direction.
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
Counterpart of `DisplacementLo`. Guarantees that `hn` is an *upper* bound on the vertical
displacement of the ownship in advisory's direction. (see Fig. 8, `Aup`)
-/
@[reducible]
def Advisory.DisplacementUp (advisory : Advisory) (aup v t hn : ℝ) : Prop :=
  let w := advisory.direction.sign
  let vup := advisory.targetv
  let timeToTarget := advisory.shortfallOf v / aup
  -- Before reaching the target: accelerate with `w * aup`
  (0 ≤ t ∧ t < timeToTarget ∧ hn = displacement (a := w * aup) v t) ∨
  -- Afterward: keep the target velocity or the initial velocity if it already exceeds it
  (timeToTarget ≤ t ∧
    hn = w * (max (w * vup) (w * v)) * t - w * advisory.shortfallOf v ^ 2 / (2 * aup))

/--
Counterpart of `LoSafeFor`: the encounter lies in the upper safe region
of the advisory. That means, the advisory is safe to follow for unlimited time, assuming
an upper bound on the displacement of ownship in advisory's direction.
(see Fig. 8, `U⁻¹_impl`)
-/
@[reducible]
def Advisory.UpSafeFor
    (advisory : Advisory) (encounter : Encounter) (rp hp rv aup : ℝ) : Prop :=
  ∀ t hn, advisory.DisplacementUp aup encounter.v t hn →
    AircraftSeparatedUp advisory encounter rp hp rv t hn

/--
Holds when the encounter lies in the lower safe region of the lower advisory or
the upper safe region of the upper advisory. Either condition guarantees safety
for an unlimited time under the corresponding response condition.
(see Fig. 8, `C⁻¹_impl`)
-/
@[reducible]
def TwoSidedAdvisory.SafeFor
    (advisory : TwoSidedAdvisory) (encounter : Encounter) (rp hp rv alo aup : ℝ) : Prop :=
  advisory.lowerAdvisory.LoSafeFor encounter rp hp rv alo  ∨
    advisory.upperAdvisory.UpSafeFor encounter rp hp rv aup

/--
The pilot may accelerate in the advisory's direction at a rate of at most `aup`
while the target velocity has not been exceeded. Beyond the target, the pilot
must stop accelerating in that direction. (see Eq. (5))
-/
@[reducible]
def Advisory.IsSatisfiedUp (advisory : Advisory) (v a aup : ℝ) : Prop :=
  let w := advisory.direction.sign
  (w * v ≤ w * advisory.targetv ∧ w * a ≤ aup) ∨ w * a ≤ 0

/--
The evolution requires both response conditions throughout the flight segment.
The lower prevents accelarating too slowly, while the upper limits motion
in the advisory's direction. (see Eq. (5))
-/
def domainTwoSided (alo aup a : ℝ) (advisory : TwoSidedAdvisory) : ℝ × ℝ × ℝ → Prop
  | (_r, _h, v) => advisory.lowerAdvisory.IsSatisfiedLo v a alo ∧
                     advisory.upperAdvisory.IsSatisfiedUp v a aup

/--
The result of a two-sided-response run.
- `encounter`: the final encounter state.
- `advisory`: the advisory in effect at that state.
-/
structure TwoSidedResult where
  encounter : Encounter
  advisory : TwoSidedAdvisory

/--
Program for advisory selection and flight with two-sided response constraints.
Each iteration keeps the current advisory or selects one that passes `SafeFor`,
then follows `motionODE` for any duration permitted by `domainTwoSided`.

Returns all possible final encounters and two-sided advisories after any finite
number of iterations, including zero. A selected advisory must be safe even if
followed forever. (see Eq. (5), Theorem 3, and `acasxtwosided.kyx`)

See `ACASX.two_sided_safe` in `CPSLib.Examples.ACASX.Challenge` for its safety claim.
-/
def twoSidedResponseProg (rp hp rv alo aup : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) : SetM TwoSidedResult := do
  let mut (encounter, advisory) := (encounter, advisory)
  let n ← choose ℕ
  for _ in [:n] do
    let replace ← choose Bool
    if replace then
      advisory ← choose TwoSidedAdvisory
      ensure (advisory.SafeFor encounter rp hp rv alo aup)
    let a ← choose ℝ
    let (r, h, v) ← evolve (motionODE rv a) (domainTwoSided alo aup a advisory)
                           (encounter.r, encounter.h, encounter.v)
    encounter := { r, h, v }
  return { encounter, advisory }

/-!
## Model 4: Bounded-Time Safety

This model allows advisories that are safe only for a bounded time. A clock records
how long the current advisory has been followed. The same advisory may span several
flight segments, but the clock is not reset between them. To continue beyond the
horizon, the system must select an advisory and reset the clock.

Bounded-time safety alone does not ensure a safe follow-up exists at the horizon.
It is a building block for the safeable model below. (see Section 5.2)
-/

abbrev Duration := { duration : ℝ // 0 ≤ duration }

/--
The advisory's time horizon: unlimited or bounded by a nonnegative duration.
-/
inductive TimeHorizon where
  | unlimited
  | bounded (duration : Duration)

/--
Holds when future time `tn` is within the horizon remaining at clock `t`.
-/
def TimeHorizon.includes : TimeHorizon → ℝ → ℝ → Prop
  | .unlimited, _, _ => True
  | .bounded duration, t, tn => tn ≤ duration.val - t

/--
Holds when the encounter lies in the lower safe region of the advisory for the remaining
horizon.
-/
@[reducible]
def Advisory.LoSafeForWithin (advisory : Advisory) (encounter : Encounter)
    (rp hp rv alo : ℝ) (limit : TimeHorizon) (t : ℝ) : Prop :=
  ∀ tn hn,
    limit.includes t tn ∧ advisory.DisplacementLo alo encounter.v tn hn →
      AircraftSeparatedLo advisory encounter rp hp rv tn hn

/--
Holds when the encounter lies in the upper safe region of the advisory for the remaining
horizon.
-/
@[reducible]
def Advisory.UpSafeForWithin (advisory : Advisory) (encounter : Encounter)
    (rp hp rv aup : ℝ) (limit : TimeHorizon) (t : ℝ) : Prop :=
  ∀ tn hn,
    limit.includes t tn ∧ advisory.DisplacementUp aup encounter.v tn hn →
      AircraftSeparatedUp advisory encounter rp hp rv tn hn

/--
Holds when the encounter lies in the lower or upper safe region for the remaining
horizon. For a finite horizon, this condition gives no guarantee beyond its endpoint.
(see Fig. 10, `Cε_impl` and `bounded_implicit.kyx`)
-/
@[reducible]
def TwoSidedAdvisory.SafeForWithin (advisory : TwoSidedAdvisory) (encounter : Encounter)
    (rp hp rv alo aup : ℝ) (limit : TimeHorizon) (t : ℝ) : Prop :=
  advisory.lowerAdvisory.LoSafeForWithin encounter rp hp rv alo limit t ∨
    advisory.upperAdvisory.UpSafeForWithin encounter rp hp rv aup limit t

/-!
### A clocked controller for Model 4 and 5
-/

/--
The ODE describing the encounter and advisory clock `(r, h, v, t)` during flight.
`r' = -rv`, `h' = -v`, `v' = a`, `t' = 1`. The clock measures time spent following
the current advisory. (see Eq. (8))
-/
def motionClockedODE (rv a : ℝ) : (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ)
  | (_r, _h, v, _t) => (-rv, -v, a, 1)

/--
The evolution requires the advisory's clock to stay within `limit` and both
advisories are followed throughout the flight segment. (see Eq. (8))
-/
def domainClocked (alo aup : ℝ) (limit : TimeHorizon) (a : ℝ)
    (advisory : TwoSidedAdvisory) : ℝ × ℝ × ℝ × ℝ → Prop
  | (_r, _h, v, t) => limit.includes 0 t ∧
    advisory.lowerAdvisory.IsSatisfiedLo v a alo ∧
    advisory.upperAdvisory.IsSatisfiedUp v a aup

/--
The result of a clocked run, extending `TwoSidedResult` with the advisory's clock.
- `t`: elapsed time since the most recent advisory selection and clock reset,
  or the supplied initial clock advanced by flight if no reset occurred.
-/
structure TimedResult extends TwoSidedResult where
  t : ℝ

/--
The shared program for bounded-time safety and safeability.
Each outer iteration selects a new two-sided advisory, checks `Safe` at clock zero,
and resets the clock. Inner iterations choose acceleration and follow `motionClockedODE`
for any duration permitted by `domainClocked`, without resetting the clock.

Returns all possible final encounters, advisories, and clocks after any finite number
of outer and inner iterations, including zero. (see Eqs. (8) and (9))
-/
def clockedResponseProg (rv alo aup : ℝ) (limit : TimeHorizon)
    (Safe : Encounter → TwoSidedAdvisory → ℝ → Prop) (encounter : Encounter)
    (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult := do
  let mut (encounter, advisory, t) := (encounter, advisory, t)
  let n ← choose ℕ
  for _ in [:n] do
    advisory ← choose TwoSidedAdvisory
    ensure (Safe encounter advisory 0)
    t := 0
    let m ← choose ℕ
    for _ in [:m] do
      let a ← choose ℝ
      let (r, h, v, newTime) ← evolve (motionClockedODE rv a)
                                      (domainClocked alo aup limit a advisory)
                                      (encounter.r, encounter.h, encounter.v, t)
      encounter := { r, h, v }
      t := newTime
  return { encounter, advisory, t }

/--
Program for advisory selection and flight with bounded-time safety.
Uses `clockedResponseProg` with `SafeForWithin` as the advisory-acceptance condition.
A finite horizon limits each advisory's flight time; it does not guarantee that a
safe next advisory can be selected when that horizon ends. (see Eq. (8))

See `ACASX.bounded_safe` in `CPSLib.Examples.ACASX.Challenge` for its safety claim.
-/
def boundedResponseProg (rp hp rv alo aup : ℝ) (limit : TimeHorizon)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult :=
  clockedResponseProg
    rv alo aup limit
    (fun encounter advisory t =>
      advisory.SafeForWithin encounter rp hp rv alo aup limit t)
    encounter advisory t

/-!
## Model 5: Safeability

An advisory that is safe for a bounded time may leave the ownship without a safe
action when that time ends. Safeability adds the requirement that a safe follow-up
remains available at the horizon. That follow-up must be safe for an unlimited time.

To check this, we consider the position and vertical velocity the ownship can reach
at the horizon, using lower and upper bounds in the current advisory's direction.

The lower branch protects against an intruder on the opposite side of that direction.
The lower bounds describe the least displacement and vertical velocity in the
advisory's direction, which is the worst case for moving away. We check whether the
strongest available strengthening, with target `vloEx`, can safely continue moving
away. For an upward advisory, this means strengthening the climb away from an
intruder below.

The upper branch protects against an intruder on the same side as the advisory's
direction. The upper bounds describe the greatest displacement and vertical velocity
in that direction, which is the worst case for reversing away from the intruder.
We check whether the strongest available reversal, with target `vupEx`, can safely
move away. For an upward advisory, this means reversing downward to avoid an
intruder above.

If either branch provides bounded-time safety and a safe follow-up, the encounter
lies in the safeable region. The ownship can then switch to an appropriate advisory
at the horizon instead of being left without a safe continuation.
(see Section 5.3 and Figs. 11–12)
-/

/--
Extends `DisplacementLo` with velocity `vn`. Guarantees `hn` and `vn` are lower bounds
on vertical displacement and endpoint velocity in advisory's direction. (see Fig. 12)
-/
@[reducible]
def Advisory.EndpointLo (advisory : Advisory) (alo v τ hn vn : ℝ) : Prop :=
  let w := advisory.direction.sign
  let timeToTarget := advisory.shortfallOf v / alo
  advisory.DisplacementLo alo v τ hn ∧
    ((0 ≤ τ ∧ τ < timeToTarget ∧ vn = w * alo * τ + v) ∨
      (timeToTarget ≤ τ ∧ vn = advisory.targetv))

/--
Extends `DisplacementUp` with velocity `vn`. Guarantees `hn` and `vn` are upper bounds
on vertical displacement and endpoint velocity in advisory's direction. (see Fig. 12)
-/
@[reducible]
def Advisory.EndpointUp (advisory : Advisory) (aup v τ hn vn : ℝ) : Prop :=
  let w := advisory.direction.sign
  let vup := advisory.targetv
  let timeToTarget := advisory.shortfallOf v / aup
  advisory.DisplacementUp aup v τ hn ∧
    ((0 ≤ τ ∧ τ < timeToTarget ∧ vn = w * aup * τ + v) ∨
      (timeToTarget ≤ τ ∧ vn = w * max (w * vup) (w * v)))

/--
Holds when the advisory is safe for the remaining finite horizon and admits a safe
follow-up from the corresponding reference endpoint. The lower branch checks a
follow-up in the same direction with target `vloEx`. The upper branch checks a
reversed direction with target `vupEx`. Both follow-ups use the unbounded `LoSafeFor`.
(see Fig. 12, `Csafeable(ε)_impl`)

- `duration`: total finite advisory horizon.
- `t`: current clock; the endpoint is `duration - t` time units away. (`ε` in paper)
- `rv`: constant horizontal closing speed.
- `alo`, `aup`: acceleration magnitudes for the lower and upper reference trajectories.
-/
@[reducible]
def TwoSidedAdvisory.SafeableFor (advisory : TwoSidedAdvisory) (encounter : Encounter)
    (rp hp rv alo aup : ℝ) (duration : Duration) (t vloEx vupEx : ℝ) : Prop :=
  let τ := duration.val - t
  (advisory.lowerAdvisory.LoSafeForWithin encounter rp hp rv alo (.bounded duration) t ∧
    ∀ hn vn,
      advisory.lowerAdvisory.EndpointLo alo encounter.v τ hn vn →
        let nextAdv : Advisory := { direction := advisory.direction, targetv := vloEx }
        let newEnc := { r := encounter.r - rv * τ, h := encounter.h - hn, v := vn }
        nextAdv.LoSafeFor newEnc rp hp rv alo) ∨
  (advisory.upperAdvisory.UpSafeForWithin encounter rp hp rv aup (.bounded duration) t ∧
    ∀ hn vn,
      advisory.upperAdvisory.EndpointUp aup encounter.v τ hn vn →
        let reverse := if advisory.direction = .down then .up else .down
        let nextAdv : Advisory := { direction := reverse, targetv := vupEx }
        let newEnc := { r := encounter.r - rv * τ, h := encounter.h - hn, v := vn }
        nextAdv.LoSafeFor newEnc rp hp rv alo)

/--
Program for advisory selection and flight with safe follow-up conditions.
Uses `clockedResponseProg` with `SafeableFor` as the advisory-acceptance condition.
The condition checks continuation beyond the current finite horizon; the program
does not execute that follow-up as a separate phase or assert that every advisory
choice succeeds. (see Eq. (9), Theorem 5, and `AcasXSafeable.scala`)

See `ACASX.safeable_safe` in `CPSLib.Examples.ACASX.Challenge` for its safety claim.
-/
def safeableResponseProg (rp hp rv alo aup : ℝ) (duration : Duration) (vloEx vupEx : ℝ)
    (encounter : Encounter) (advisory : TwoSidedAdvisory) (t : ℝ) : SetM TimedResult :=
  clockedResponseProg
    rv alo aup (.bounded duration)
    (fun encounter advisory t =>
      advisory.SafeableFor encounter rp hp rv alo aup duration t vloEx vupEx)
    encounter advisory t

end ACASX
