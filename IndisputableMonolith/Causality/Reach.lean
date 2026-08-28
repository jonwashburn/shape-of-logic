import Mathlib
import IndisputableMonolith.Causality.Basic
import IndisputableMonolith.Causality.BallP

/-!
# Causality.Reach (re-export)

`Kinematics`, `ReachN`, `inBall`, `Reaches`, and the reach lemmas live in
`Causality.Basic`. `ballP` and the ball-comparison lemmas live in
`Causality.BallP`. This file used to copy both APIs into the same
namespace, so it could not share an environment with either owner.
It now only imports them.
-/
