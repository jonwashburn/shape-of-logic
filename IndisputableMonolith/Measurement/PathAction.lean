import Mathlib
import IndisputableMonolith.Cost

/-!
# Recognition Path Action (Minimal Interface)

Lightweight interface for recognition paths and their action/weights. Heavy
measure-theoretic lemmas (piecewise additivity, domain shifts, etc.) are
intentionally omitted to keep the build surface stable for paper exports.
-/

namespace IndisputableMonolith
namespace Measurement

open Real Complex Cost

/-- A recognition path is a time-parameterized positive rate function. -/
structure RecognitionPath where
  T : ℝ
  T_pos : 0 < T
  rate : ℝ → ℝ
  rate_pos : ∀ t, t ∈ Set.Icc 0 T → 0 < rate t

/-- Recognition action C[γ] = ∫ J(r(t)) dt. -/
noncomputable def pathAction (γ : RecognitionPath) : ℝ :=
  ∫ t in (0)..γ.T, Cost.Jcost (γ.rate t)

/-- Positive weight w[γ] = exp(-C[γ]). -/
noncomputable def pathWeight (γ : RecognitionPath) : ℝ :=
  Real.exp (- pathAction γ)

/-- Amplitude bridge 𝒜[γ] = exp(-C[γ]/2) · exp(i φ). -/
noncomputable def pathAmplitude (γ : RecognitionPath) (φ : ℝ) : ℂ :=
  Complex.exp (- pathAction γ / 2) * Complex.exp (φ * I)

/-- Weight is positive. -/
lemma pathWeight_pos (γ : RecognitionPath) : 0 < pathWeight γ := by
  unfold pathWeight
  exact Real.exp_pos _

/-- Amplitude modulus squared equals weight. -/
theorem amplitude_mod_sq_eq_weight (γ : RecognitionPath) (φ : ℝ) :
  ‖pathAmplitude γ φ‖ ^ 2 = pathWeight γ := by
  unfold pathAmplitude pathWeight
  have h1 : ‖Complex.exp (-(pathAction γ) / 2)‖ = Real.exp (-(pathAction γ) / 2) := by
    simpa using Complex.norm_exp_ofReal (-(pathAction γ) / 2)
  have h2 := Complex.norm_exp_ofReal_mul_I φ
  rw [norm_mul]
  simp only [h1, h2, mul_one, sq]
  rw [← Real.exp_add]
  ring

end Measurement
end IndisputableMonolith
