# Theorem 10: checked counterexample and proved correction

The original `dwnobs_safe` challenge is false for the current direct transcription
of journal equations (55)--(60). `Theorem10.lean` proves its negation as
`IJRR17.Theorem10.journal_claim_false`, with no admitted lemmas. This is a
successful run of the actual model, not just a failed proof strategy.

The same file proves `IJRR17.Theorem10.safe_of_initial_velocity_bounds` for
the unchanged hybrid program, adding the explicit premise
`forall i in O, norm(v i) <= V i`. Model, Challenge, and config are unchanged.

## Why the original statement fails

Journal (59) initializes the robot stopped, with a nonzero radius and unit
direction. It imposes no obstacle-velocity bounds. The obstacle controller (56)
updates an arbitrary finite number of selected obstacles, possibly zero. Its
test constrains only the newly selected velocities. Unselected velocities survive
into the continuous phase, whose safety guard uses the declared bounds `V i`.

The surrounding prose calls these values maximum velocities. Treating that as a
persistent environmental assumption would rule out the counterexample. That
assumption is absent from the explicit initial formula and current Lean target.
The result here concerns that exact formal statement; it does not claim to have
replayed or refuted the predecessor KeYmaera artifact mentioned in the article.
Theorem 10 is absent from the supplied `robix.kyx` archive.

## Concrete checked run

Take `A = b = epsilon = r = 1`, steering bound `Omega = 0`, and all natural-number
obstacle IDs active. Every declared obstacle bound is zero. Initially:

- Robot position is `(0, 0)`, direction `(1, 0)`, speed and angular velocity zero.
- Every obstacle starts at `(2, 0)`.
- Let `q = (sin(1/2), cos(1/2) - 1)`. Every obstacle has initial velocity
  `q - (2, 0)`, whose norm is strictly positive.

The obstacle controller chooses zero updates. The robot chooses acceleration one,
angular velocity zero, and radius one. The actual-acceleration clearance guard
evaluates to `1 < 2`, so this controller choice succeeds.

For `0 <= t <= 1`, the robot trajectory is

```text
position(t)  = (sin(t^2/2), cos(t^2/2) - 1)
direction(t) = (cos(t^2/2), -sin(t^2/2))
speed(t) = angular_velocity(t) = t
obstacle_position(i,t) = (2,0) + t * (q - (2,0))
```

Lean checks the derivatives, evolution domain, successful controller choices,
quantified obstacle dynamics, and complete one-iteration program run. At time
one, robot speed is one and every obstacle position equals the robot position.
This violates the exact target's positive infinity-norm separation requirement.
The trajectory uses the journal's printed negative angular sign; changing that
sign does not supply the missing obstacle-speed assumption.

## What the correction proves

The additional initial bound is preserved by every permitted finite update,
including zero updates. The safety proof then:

1. Preserves nonnegative robot speed and unit direction.
2. Maintains the conditional stopping-distance invariant for each active ID.
3. Projects an arbitrary active QODE coordinate onto the ordinary motion model,
   negating angular velocity and radius to account for the printed angular sign.
4. Reuses the actual-acceleration phase proof from Theorem 5 and composes the
   unchanged controllers and loop with intrinsic contracts and `vcgen`.

No initial position separation is needed when the robot is stopped. No finite
enumeration of the obstacle population is introduced. Inactive coordinates
remain unconstrained and are outside the safety quantifiers.

## Deferred modeling choice

The original challenge is deliberately retained. A later revision can adopt the
proved initial-velocity premise, or explicitly change the program/environment
to enforce bounds before every evolution. These are different specification
choices; neither has been applied silently. No user input was requested.

## Verification

The local build and axiom checks cover the counterexample and corrected theorem.
Both use only `propext`, `Classical.choice`, and `Quot.sound`. The original eleven
targets remain proved in `Proof.lean`. Comparator was not run for this attempt,
as requested.

Rebuild with `lake build CPSLib.Examples.IJRR17.Theorem10`. The principal checked
declarations are `IJRR17.Theorem10.journal_claim_false` and
`IJRR17.Theorem10.safe_of_initial_velocity_bounds`.
