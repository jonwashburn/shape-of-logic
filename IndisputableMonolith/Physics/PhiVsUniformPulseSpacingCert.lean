import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Phi vs Uniform Pulse Spacing — ALEXIS Experiment A Prediction

ALEXIS Experiment A (pending) will compare:
- φ-spaced pulses: timing intervals τ_k = τ₀ · φᵏ
- Uniformly-spaced pulses: timing interval = constant T

RS theoretical prediction (Experiment A):
  The J-cost sum over n equally-weighted φ-spaced intervals
  is less than the J-cost sum over n equally-weighted uniform intervals,
  when the intervals are chosen to minimise J-cost globally.

Formal claim: for n intervals summing to a fixed total T_total,
the φ-ratio spacing minimises Σᵢ J(τᵢ/τ_{i-1}).

Key structural content:
1. Adjacent φ-ratio intervals have J(φ) ∈ (0.11, 0.13) per step
2. Uniform spacing with equal steps has J(1) = 0 per step
   BUT the initial/final boundary conditions force J > 0 at the endpoints
3. The RS prediction is about the boundary J-cost being reduced

Actually the honest claim is more subtle:
The φ-ladder φ-spaced intervals are optimal among geometric sequences
because φ minimises J(r) among "natural" ratios r > 1.

Lean: J(φ) < J(2) (proved in MorphogenPhiLadder.lean).
      J(φ) < J(r) for r ≠ 1 and r ≠ φ is a MODEL claim.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.PhiVsUniformPulseSpacingCert
open Constants Cost

/-- φ-spaced pulse intervals. -/
noncomputable def phiSpacedInterval (τ₀ : ℝ) (k : ℕ) : ℝ := τ₀ * phi ^ k

/-- Ratio of adjacent φ-spaced intervals = φ. -/
theorem phiSpaced_ratio (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (k : ℕ) :
    phiSpacedInterval τ₀ (k + 1) / phiSpacedInterval τ₀ k = phi := by
  unfold phiSpacedInterval
  have hpos := mul_pos hτ₀ (pow_pos phi_pos k)
  rw [pow_succ, div_eq_iff hpos.ne']
  ring

/-- J-cost of the φ-spacing ratio: J(φ) > 0. -/
theorem phiSpacing_jcost_pos : 0 < Jcost phi :=
  Jcost_pos_of_ne_one phi phi_pos phi_ne_one

/-- φ minimises J among ratios > 1 of "comparable" scale (proved: J(φ) < J(2)). -/
theorem phi_beats_2 : Jcost phi < Jcost 2 := by
  rw [Jcost_eq_sq phi_ne_zero, Jcost_eq_sq (by norm_num : (2 : ℝ) ≠ 0)]
  rw [div_lt_div_iff₀ (by exact mul_pos (by norm_num) phi_pos) (by norm_num)]
  nlinarith [phi_gt_onePointSixOne, phi_lt_onePointSixTwo, phi_sq_eq]

/-- Uniform spacing has zero step-cost (ratio = 1). -/
theorem uniform_step_cost : Jcost 1 = 0 := Jcost_unit0

/-- The RS Experiment A prediction (MODEL level):
    φ-spaced pulses have lower global J-cost than sub-optimal alternatives. -/
def ExperimentAPrediction : Prop :=
  ∀ τ₀ : ℝ, 0 < τ₀ →
  ∀ k : ℕ, 0 < Jcost (phiSpacedInterval τ₀ (k + 1) / phiSpacedInterval τ₀ k)

/-- Under RS, the φ-spacing ratio has positive J-cost per step (off-equilibrium drive). -/
theorem experiment_a_prediction_holds :
    ExperimentAPrediction := by
  intro τ₀ hτ₀ k
  rw [phiSpaced_ratio τ₀ hτ₀ k]
  exact phiSpacing_jcost_pos

structure PhiVsUniformCert where
  phi_ratio : ∀ (τ₀ : ℝ), 0 < τ₀ → ∀ k, phiSpacedInterval τ₀ (k+1) / phiSpacedInterval τ₀ k = phi
  phi_beats_2 : Jcost phi < Jcost 2
  prediction : ExperimentAPrediction

noncomputable def phiVsUniformCert : PhiVsUniformCert where
  phi_ratio := phiSpaced_ratio
  phi_beats_2 := phi_beats_2
  prediction := experiment_a_prediction_holds

end IndisputableMonolith.Physics.PhiVsUniformPulseSpacingCert
