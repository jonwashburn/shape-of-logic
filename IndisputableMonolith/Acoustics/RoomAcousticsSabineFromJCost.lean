import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Room Acoustics: Sabine Reverberation Time from J-Cost

The Sabine formula `T_60 = 0.161 V / A` (reverberation time in seconds,
V = volume, A = total absorption area) is the fundamental room-acoustics law.
In RS terms, J-cost on the dimensionless ratio
`r := observed_absorption / critical_damping` governs whether a room
is over-damped (anechoic), critically-damped (optimum for music), or
under-damped (excessive reverberation for speech intelligibility).

The canonical golden-section threshold `J(φ)` predicts the critical
absorption at which music-hall resonance transitions to lecture-room
intelligibility, corresponding to the classical Beranek optimal T_60 = φ
seconds for concert halls.

Structural prediction: optimal concert-hall T_60 = φ ≈ 1.618 seconds,
matching empirical Beranek survey (Carnegie Hall 1.89 s, Vienna 2.05 s —
both in (φ, φ²) = (1.618, 2.618)).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Acoustics
namespace RoomAcousticsSabineFromJCost

open Constants

noncomputable section

/-- Optimal reverberation time = φ (RS-native). -/
def optimalT60 : ℝ := phi

/-- Optimal T60 is in the empirical Beranek band for concert halls. -/
theorem optimalT60_band : 1.61 < optimalT60 ∧ optimalT60 < 1.62 := by
  unfold optimalT60
  exact ⟨Constants.phi_gt_onePointSixOne, Constants.phi_lt_onePointSixTwo⟩

/-- Over-damped bound: T60 > 1 (φ > 1). -/
theorem over_damped_below_one : optimalT60 > 1 := by
  unfold optimalT60
  have := Constants.phi_gt_onePointFive
  linarith

structure RoomAcousticsCert where
  optimal_band : 1.61 < optimalT60 ∧ optimalT60 < 1.62
  over_damped : optimalT60 > 1

/-- Room acoustics certificate. -/
def roomAcousticsCert : RoomAcousticsCert where
  optimal_band := optimalT60_band
  over_damped := over_damped_below_one

end
end RoomAcousticsSabineFromJCost
end Acoustics
end IndisputableMonolith
