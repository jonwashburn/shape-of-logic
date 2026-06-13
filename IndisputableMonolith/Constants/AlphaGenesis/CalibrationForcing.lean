import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.AlphaGenesis.ResummationForcing
import IndisputableMonolith.Constants.AlphaGenesis.PatternForcing
import IndisputableMonolith.Constants.AlphaGenesis.LoopCertificate
import IndisputableMonolith.Foundation.MeasureForcing

/-!
# Alpha Genesis M5: Calibration Forcing (the calibration is not an input)

**THE THEOREM.** The unit-linear-response calibration (D2) of
`ResummationForcing.DressingResponse` can be eliminated entirely. A
**self-similar dressing** is a response with three premises, none of which
is a normalization choice:

* factorization over independent loads (the inherited ledger premise),
* antitonicity on nonnegative loads (more load never helps),
* the self-similar balance `g(1) = 1/(1 + g(1))` on the single step — the
  SAME balance equation that forces the T9 measure's step (W2).

Then `g = φ⁻ᵗ` on all nonnegative loads (`selfSimilar_response_forced`),
with no derivative condition and no unit convention anywhere. The step
value `g(1) = φ⁻¹` is DERIVED (`step_forced`), not calibrated: positivity
of the step follows from factorization (`g(1) = g(1/2)² > 0`), and the
balance equation then has exactly one admissible root.

Consequently the (D1)+(D2) `DressingResponse` of M1 demotes to the
natural-units display of this object (`natural_display`), and the forward
α object is obtained from EVERY self-similar dressing
(`alphaInvGenesis_from_selfSimilar`).

This discharges the residual normalization worry: the dressing of the α
seed carries zero calibration input. Its form, its rate, and its step are
all forced by the same two structural facts (factorization, self-similar
balance) that force the recognition measure itself.

STATUS: THEOREM (0 sorry target). No CODATA reference anywhere in this file.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis

noncomputable section

open Foundation.MeasureForcing

/-- A **self-similar dressing**: survival fraction under gap load with the
two inherited ledger premises and the self-similar step balance. No
calibration field exists. -/
structure SelfSimilarDressing where
  /-- Survival fraction as a function of gap load. -/
  g : ℝ → ℝ
  /-- Factorization over independent nonnegative loads. -/
  factorizes : Foundation.MeasureForcing.Factorizes g
  /-- More load never increases survival. -/
  antitone : AntitoneOn g (Set.Ici 0)
  /-- **Self-similar balance** on the single step: the same fixed-point
  equation (W2) that forces the T9 measure's step. -/
  step_self_similar : g 1 = 1 / (1 + g 1)

namespace SelfSimilarDressing

variable (D : SelfSimilarDressing)

/-- The step is a square: `g(1) = g(1/2)²` (factorization). -/
theorem step_eq_sq : D.g 1 = D.g (1/2) ^ 2 := by
  have h := D.factorizes (1/2) (1/2) (by norm_num) (by norm_num)
  have h1 : (1/2 : ℝ) + 1/2 = 1 := by norm_num
  rw [h1] at h
  rw [h]
  ring

/-- The step is nonnegative. -/
theorem step_nonneg : 0 ≤ D.g 1 := by
  rw [D.step_eq_sq]
  exact sq_nonneg _

/-- The step is nonzero: `g(1) = 0` contradicts the balance equation. -/
theorem step_ne_zero : D.g 1 ≠ 0 := by
  intro h0
  have hbal := D.step_self_similar
  rw [h0] at hbal
  norm_num at hbal

/-- The step is strictly positive (derived, not assumed). -/
theorem step_pos : 0 < D.g 1 :=
  lt_of_le_of_ne D.step_nonneg (Ne.symm D.step_ne_zero)

/-- **STEP FORCING.** The balance equation has exactly one admissible
root: `g(1) = φ⁻¹`. The reciprocal of the step satisfies the T6
self-similarity equation `r² = r + 1`, whose unique positive root is φ. -/
theorem step_forced : D.g 1 = 1 / Constants.phi := by
  set ρ := D.g 1 with hρdef
  have hpos : 0 < ρ := D.step_pos
  have hbal : ρ = 1 / (1 + ρ) := D.step_self_similar
  have hsum_pos : 0 < 1 + ρ := by linarith
  have hsum_ne : (1 + ρ) ≠ 0 := ne_of_gt hsum_pos
  -- ρ² + ρ − 1 = 0
  have hmul : ρ * (1 + ρ) = 1 := by
    calc ρ * (1 + ρ) = (1 / (1 + ρ)) * (1 + ρ) := by rw [← hbal]
    _ = 1 := by field_simp
  have hquad : ρ ^ 2 + ρ - 1 = 0 := by nlinarith [hmul]
  -- 1/φ satisfies the same quadratic
  have hφ : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have hφpos : 0 < Constants.phi := Constants.phi_pos
  have hφne : Constants.phi ≠ 0 := ne_of_gt hφpos
  have hinv_pos : 0 < 1 / Constants.phi := by positivity
  have hinv_quad : (1 / Constants.phi) ^ 2 + (1 / Constants.phi) - 1 = 0 := by
    field_simp
    nlinarith [hφ]
  -- difference of the two quadratics factors: (ρ − 1/φ)(ρ + 1/φ + 1) = 0
  have hfactor : (ρ - 1 / Constants.phi) * (ρ + 1 / Constants.phi + 1) = 0 := by
    linear_combination hquad - hinv_quad
  have hsum2_pos : 0 < ρ + 1 / Constants.phi + 1 := by linarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith [sub_eq_zero.mp h]
  · linarith

/-- **CALIBRATION FORCING.** Every self-similar dressing is the forced
measure on nonnegative loads: `g(t) = φ⁻ᵗ`. No derivative condition, no
unit convention, no calibration input. -/
theorem response_forced : ∀ t : ℝ, 0 ≤ t →
    D.g t = Foundation.MeasureForcing.contWeight t := by
  intro t ht
  have hstep : D.g 1 = Foundation.MeasureForcing.rho := by
    rw [D.step_forced]
    rfl
  exact Foundation.MeasureForcing.continuum_weight_forced
    D.factorizes D.antitone hstep t ht

/-- Non-vacuity: the forced measure itself is a self-similar dressing. -/
def canonical : SelfSimilarDressing where
  g := Foundation.MeasureForcing.contWeight
  factorizes := Foundation.MeasureForcing.contWeight_satisfies_premises.1
  antitone := Foundation.MeasureForcing.contWeight_satisfies_premises.2.1
  step_self_similar := by
    have h1 : Foundation.MeasureForcing.contWeight 1 =
        Foundation.MeasureForcing.rho :=
      Foundation.MeasureForcing.contWeight_satisfies_premises.2.2
    rw [h1]
    unfold Foundation.MeasureForcing.rho
    have hphi := Constants.phi_pos
    have hsq := Constants.phi_sq_eq
    have hsum_pos : (0 : ℝ) < 1 + 1 / Constants.phi := by positivity
    field_simp
    nlinarith [hsq]

/-- **NATURAL-UNITS DISPLAY.** The differentiable (D1)+(D2) dressing of M1
is the same object read in natural log units: for every calibrated
response R and every self-similar dressing D,
`R.g(lnφ · t) = D.g(t)` on nonnegative loads. The calibration of M1 was
never an input; it was the natural-units coordinate of this object. -/
theorem natural_display (R : DressingResponse) (D : SelfSimilarDressing)
    (t : ℝ) (ht : 0 ≤ t) :
    R.g (Real.log Constants.phi * t) = D.g t := by
  rw [response_is_forced_measure R t, D.response_forced t ht]

/-- The forward α object is obtained from EVERY self-similar dressing:
`alphaInvGenesis = S · D.g(w₈/S)`. -/
theorem alphaInvGenesis_from_selfSimilar (D : SelfSimilarDressing) :
    alphaInvGenesis = channelBudget * D.g spectralLoad := by
  unfold alphaInvGenesis
  rw [D.response_forced spectralLoad (le_of_lt spectralLoad_pos)]

end SelfSimilarDressing

/-- **CALIBRATION FORCING CERTIFICATE.** Bundles the M5 closure:
1. the step is forced to φ⁻¹ from balance alone (no calibration);
2. every self-similar dressing is the forced measure on loads;
3. the M1 calibrated response is the natural-units display;
4. the forward α object follows from every self-similar dressing. -/
structure CalibrationForcingCert where
  deriving Inhabited

@[simp] def CalibrationForcingCert.verified (_c : CalibrationForcingCert) : Prop :=
  (∀ D : SelfSimilarDressing, D.g 1 = 1 / Constants.phi) ∧
  (∀ (D : SelfSimilarDressing) (t : ℝ), 0 ≤ t →
    D.g t = Foundation.MeasureForcing.contWeight t) ∧
  (∀ (R : DressingResponse) (D : SelfSimilarDressing) (t : ℝ), 0 ≤ t →
    R.g (Real.log Constants.phi * t) = D.g t) ∧
  (∀ D : SelfSimilarDressing,
    alphaInvGenesis = channelBudget * D.g spectralLoad)

theorem CalibrationForcingCert.verified_any (c : CalibrationForcingCert) :
    CalibrationForcingCert.verified c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D
    exact D.step_forced
  · intro D t ht
    exact D.response_forced t ht
  · intro R D t ht
    exact SelfSimilarDressing.natural_display R D t ht
  · intro D
    exact SelfSimilarDressing.alphaInvGenesis_from_selfSimilar D

end

end AlphaGenesis
end Constants
end IndisputableMonolith
