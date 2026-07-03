import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Casimir Zeta Regularization

This module supplies the analytic special-value input for the ideal
parallel-plate Casimir energy.  The hard QFT boundary-mode analysis is still a
bridge model, but the special value `ζ(-3) = 1/120` is imported from Mathlib's
Bernoulli-number theorem.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirZetaRegularization

open CasimirPlateModes
open Constants

noncomputable section

/-- Mathlib-backed special value: `ζ(-3) = 1/120`. -/
theorem zeta_neg_three_value :
    riemannZeta (-(3 : ℂ)) = (1 / 120 : ℂ) := by
  have h := riemannZeta_neg_nat_eq_bernoulli 3
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 4 ≠ 1), bernoulli'_four] at h
  norm_num at h
  simpa using h

/-- The real special value used by the scalar plate-energy expression. -/
noncomputable def zetaNegThreeReal : ℝ := 1 / 120

/-- The real special value is the real shadow of Mathlib's complex zeta value. -/
theorem zetaNegThreeReal_complex :
    (zetaNegThreeReal : ℂ) = riemannZeta (-(3 : ℂ)) := by
  rw [zeta_neg_three_value]
  unfold zetaNegThreeReal
  norm_num

/-- Regularized scalar mode sum after subtracting the continuum exterior and
retaining the finite plate-dependent term.  The `1/6` geometry factor converts
`ζ(-3)=1/120` into the standard `1/720` coefficient. -/
noncomputable def regularizedModeSum (a : PlateSeparation) : ℝ :=
  -(Real.pi ^ 2 * hbar * c / (6 * a.value ^ 3)) * zetaNegThreeReal

/-- Zeta regularization recovers the ideal parallel-plate energy density. -/
theorem idealEnergyDensity_from_zeta (a : PlateSeparation) :
    idealEnergyDensity a = regularizedModeSum a := by
  unfold idealEnergyDensity regularizedModeSum idealEnergyCoefficient zetaNegThreeReal
  have ha : a.value ≠ 0 := ne_of_gt a.pos
  have ha3 : a.value ^ 3 ≠ 0 := pow_ne_zero 3 ha
  field_simp [ha, ha3]
  ring

/-- Zeta-regularization certificate. -/
structure ZetaRegularizationCert where
  zeta_value : riemannZeta (-(3 : ℂ)) = (1 / 120 : ℂ)
  energy_density :
    ∀ a : PlateSeparation, idealEnergyDensity a = regularizedModeSum a

/-- Certificate instance for the zeta-regularized Casimir energy. -/
def zetaRegularizationCert : ZetaRegularizationCert where
  zeta_value := zeta_neg_three_value
  energy_density := idealEnergyDensity_from_zeta

end

end CasimirZetaRegularization
end QFT
end IndisputableMonolith
