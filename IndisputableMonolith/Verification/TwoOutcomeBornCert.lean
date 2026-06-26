import Mathlib
import IndisputableMonolith.Measurement.C2ABridge
import IndisputableMonolith.Measurement.TwoBranchGeodesic

/-!
# Two-Outcome Born Certificate (normalized probabilities)

This module upgrades the two-branch measurement bridge from a weight identity
(`pathWeight = sin² θ`) to **normalized two-outcome probabilities**:

- `P_cos = exp(-C_cos) / (exp(-C_cos) + exp(-C_sin)) = cos² θ`
- `P_sin = exp(-C_sin) / (exp(-C_cos) + exp(-C_sin)) = sin² θ`

where:
- `C_sin` is the *recognition action* `pathAction (pathFromRotation rot)` (so `exp(-C_sin)` is the RS path weight),
- `C_cos` is the complementary action `-2 log(cos θ)` whose weight is `cos² θ`.

This avoids any “measurement axioms” typeclass entirely and relies only on the proven bridge theorems
in `Measurement/C2ABridge.lean` and elementary trigonometric identities.
-/

namespace IndisputableMonolith
namespace Verification
namespace TwoOutcomeBorn

open IndisputableMonolith.Measurement
open Real

/-- Complementary action producing `exp(-C_cos) = cos²(θ_s)`. -/
noncomputable def C_cos (rot : TwoBranchRotation) : ℝ :=
  -2 * Real.log (Real.cos rot.θ_s)

/-- RS action producing `exp(-C_sin) = sin²(θ_s)` via the measurement bridge. -/
noncomputable def C_sin (rot : TwoBranchRotation) : ℝ :=
  Measurement.pathAction (Measurement.pathFromRotation rot)

/-- Normalized probability for the cos-branch. -/
noncomputable def P_cos (rot : TwoBranchRotation) : ℝ :=
  Real.exp (- C_cos rot) /
    (Real.exp (- C_cos rot) + Real.exp (- C_sin rot))

/-- Normalized probability for the sin-branch. -/
noncomputable def P_sin (rot : TwoBranchRotation) : ℝ :=
  Real.exp (- C_sin rot) /
    (Real.exp (- C_cos rot) + Real.exp (- C_sin rot))

lemma exp_neg_C_cos_eq (rot : TwoBranchRotation) :
    Real.exp (- C_cos rot) = Measurement.complementAmplitudeSquared rot := by
  -- Same pattern as `born_weight_from_rate`, but for `cos`.
  unfold C_cos Measurement.complementAmplitudeSquared
  have hcos_pos : 0 < Real.cos rot.θ_s := by
    -- θ_s ∈ (0, π/2) ⇒ θ_s ∈ (-π/2, π/2) ⇒ cos θ_s > 0
    refine Real.cos_pos_of_mem_Ioo ?_
    refine ⟨?_, rot.θ_s_bounds.2⟩
    have hpi2 : (0 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_pos]
    linarith [rot.θ_s_bounds.1, hpi2]
  calc
    Real.exp (-(-2 * Real.log (Real.cos rot.θ_s)))
        = Real.exp (2 * Real.log (Real.cos rot.θ_s)) := by ring_nf
    _ = Real.exp (Real.log ((Real.cos rot.θ_s) ^ 2)) := by
        congr 1
        exact (Real.log_pow (Real.cos rot.θ_s) 2).symm
    _ = (Real.cos rot.θ_s) ^ 2 := Real.exp_log (pow_pos hcos_pos 2)

lemma exp_neg_C_sin_eq (rot : TwoBranchRotation) :
    Real.exp (- C_sin rot) = Measurement.initialAmplitudeSquared rot := by
  -- `pathWeight = exp(-pathAction)` and `weight_equals_born` gives `pathWeight = sin²`.
  have h := Measurement.weight_equals_born rot
  simpa [Measurement.pathWeight, C_sin] using h

theorem P_cos_eq (rot : TwoBranchRotation) :
    P_cos rot = Measurement.complementAmplitudeSquared rot := by
  unfold P_cos
  rw [exp_neg_C_cos_eq rot, exp_neg_C_sin_eq rot]
  -- cos² / (cos² + sin²) = cos²
  simp [Measurement.initialAmplitudeSquared, Measurement.complementAmplitudeSquared,
    Real.cos_sq_add_sin_sq rot.θ_s]

theorem P_sin_eq (rot : TwoBranchRotation) :
    P_sin rot = Measurement.initialAmplitudeSquared rot := by
  unfold P_sin
  rw [exp_neg_C_cos_eq rot, exp_neg_C_sin_eq rot]
  -- sin² / (cos² + sin²) = sin²
  simp [Measurement.initialAmplitudeSquared, Measurement.complementAmplitudeSquared,
    Real.cos_sq_add_sin_sq rot.θ_s]

structure TwoOutcomeBornCert where
  deriving Repr

/-- Verification predicate: the normalized two-outcome probabilities match cos²/sin². -/
@[simp] def TwoOutcomeBornCert.verified (_c : TwoOutcomeBornCert) : Prop :=
  ∀ rot : TwoBranchRotation,
    P_cos rot = Measurement.complementAmplitudeSquared rot
      ∧ P_sin rot = Measurement.initialAmplitudeSquared rot

@[simp] theorem TwoOutcomeBornCert.verified_any (c : TwoOutcomeBornCert) :
    TwoOutcomeBornCert.verified c := by
  intro rot
  exact ⟨P_cos_eq rot, P_sin_eq rot⟩

end TwoOutcomeBorn
end Verification
end IndisputableMonolith
