import IndisputableMonolith.Cost.Ndim.Core

/-!
# Octave (`n=8`) coefficient trajectories
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

/-- Uniform phase shift for an octave index. -/
noncomputable def octavePhase (i : Fin 8) : ℝ := 2 * Real.pi * (i : ℝ) / 8

/-- Phase-shifted cosine trajectory used in the `n=8` visualization. -/
noncomputable def octaveTrajectory (amp t : ℝ) : Vec 8 :=
  fun i => amp * Real.cos (t + octavePhase i)

theorem octaveTrajectory_periodic (amp t : ℝ) :
    octaveTrajectory amp (t + 2 * Real.pi) = octaveTrajectory amp t := by
  ext i
  unfold octaveTrajectory
  have hrew : t + 2 * Real.pi + octavePhase i = (t + octavePhase i) + 2 * Real.pi := by ring
  calc
    amp * Real.cos (t + 2 * Real.pi + octavePhase i)
        = amp * Real.cos ((t + octavePhase i) + 2 * Real.pi) := by rw [hrew]
    _ = amp * Real.cos (t + octavePhase i) := by
          rw [Real.cos_add_two_pi]

end Ndim
end Cost
end IndisputableMonolith
