import IndisputableMonolith.Relativity.Geometry.LocalRaychaudhuriReduction
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Local equilibrium area variation

This module adds the explicit area-rate MODEL `A' = θ A` to the scalar
Raychaudhuri MODEL and derives the second area variation at one equilibrium
point.

Honesty tags:

* `LocalAreaCongruenceData.areaLaw` is an explicit MODEL interface;
* the inherited Raychaudhuri law is the twist-free null-horizon germ MODEL;
* zero initial expansion and shear are equilibrium hypotheses;
* no area law is integrated, and no stress tensor, Unruh relation, all-null
  matching, EFE, ledger-to-geometry bridge, or C-gap1 claim is introduced.

The conclusion is therefore a theorem of calculus conditional on the two
explicit geometric MODEL laws. Arithmetic decoys show that zero expansion,
zero shear, and the unit normalization in `A' = θ A` are load-bearing.
-/

noncomputable section

namespace IndisputableMonolith
namespace Relativity
namespace Geometry
namespace LocalEquilibriumAreaVariation

open LocalRaychaudhuriReduction

/--
Local scalar Raychaudhuri data together with cross-sectional area. The
area-rate law is an explicit MODEL premise, not an integrated area formula.
-/
structure LocalAreaCongruenceData extends LocalRaychaudhuriData where
  area : ℝ → ℝ
  /-- MODEL: the local area rate obeys `dA/dλ = θ(λ) A(λ)`. -/
  areaLaw :
    ∀ lambda : ℝ,
      HasDerivAt area (expansion lambda * area lambda) lambda

/--
The global pointwise derivative form of the explicit area-rate MODEL.
-/
theorem deriv_area_eq_expansion_mul_area (D : LocalAreaCongruenceData) :
    deriv D.area = fun lambda => D.expansion lambda * D.area lambda :=
  deriv_eq D.areaLaw

/--
Before imposing equilibrium, the derivative of the area rate at `λ = 0` is
the product-rule expression obtained from the two MODEL laws.
-/
theorem hasDerivAt_areaRate_zero (D : LocalAreaCongruenceData) :
    HasDerivAt (fun lambda => D.expansion lambda * D.area lambda)
      (raychaudhuriSlope (D.expansion 0) (D.shearSq 0) (D.ricciNull 0) * D.area 0
        + D.expansion 0 * (D.expansion 0 * D.area 0)) 0 :=
  (D.law 0).mul (D.areaLaw 0)

/--
At local equilibrium, the derivative of the area rate is
`-A(0) * ricciNull(0)`.
-/
theorem hasDerivAt_areaRate_eq_neg_area_mul_ricciNull
    (D : LocalAreaCongruenceData)
    (hθ : D.expansion 0 = 0) (hσ : D.shearSq 0 = 0) :
    HasDerivAt (fun lambda => D.expansion lambda * D.area lambda)
      (-D.area 0 * D.ricciNull 0) 0 := by
  have h :=
    (hasDerivAt_expansion_eq_neg_ricciNull
      D.toLocalRaychaudhuriData hθ hσ).mul (D.areaLaw 0)
  have hvalue :
      -D.ricciNull 0 * D.area 0
          + D.expansion 0 * (D.expansion 0 * D.area 0) =
        -D.area 0 * D.ricciNull 0 := by
    rw [hθ]
    ring
  exact h.congr_deriv hvalue

/--
The same equilibrium result stated as differentiability of `deriv area`.
-/
theorem hasDerivAt_deriv_area_eq_neg_area_mul_ricciNull
    (D : LocalAreaCongruenceData)
    (hθ : D.expansion 0 = 0) (hσ : D.shearSq 0 = 0) :
    HasDerivAt (deriv D.area) (-D.area 0 * D.ricciNull 0) 0 := by
  rw [deriv_area_eq_expansion_mul_area D]
  exact hasDerivAt_areaRate_eq_neg_area_mul_ricciNull D hθ hσ

/--
Pointwise second-area-variation formula at local equilibrium.
-/
theorem deriv_deriv_area_zero_eq_neg_area_mul_ricciNull
    (D : LocalAreaCongruenceData)
    (hθ : D.expansion 0 = 0) (hσ : D.shearSq 0 = 0) :
    deriv (deriv D.area) 0 = -D.area 0 * D.ricciNull 0 :=
  (hasDerivAt_deriv_area_eq_neg_area_mul_ricciNull D hθ hσ).deriv

/--
The same second-area-variation formula in Mathlib's `iteratedDeriv` notation.
-/
theorem iteratedDeriv_two_area_zero_eq_neg_area_mul_ricciNull
    (D : LocalAreaCongruenceData)
    (hθ : D.expansion 0 = 0) (hσ : D.shearSq 0 = 0) :
    iteratedDeriv 2 D.area 0 = -D.area 0 * D.ricciNull 0 := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  exact deriv_deriv_area_zero_eq_neg_area_mul_ricciNull D hθ hσ

/--
Arithmetic value of the differentiated area-rate product under the unit
normalization `A' = θ A`.
-/
def areaRateSlope
    (theta shearSq ricciNull area : ℝ) : ℝ :=
  raychaudhuriSlope theta shearSq ricciNull * area
    + theta * (theta * area)

/--
Any nonzero initial expansion and nonzero initial area obstruct the reduced
second-area formula, even when the initial shear vanishes.
-/
theorem areaRateSlope_ne_neg_area_mul_ricciNull_of_nonzero_expansion
    {theta shearSq ricciNull area : ℝ}
    (hθ : theta ≠ 0) (hσ : shearSq = 0) (hA : area ≠ 0) :
    areaRateSlope theta shearSq ricciNull area ≠ -area * ricciNull := by
  intro h
  have hzero : (1 / 2 : ℝ) * (theta ^ 2 * area) = 0 := by
    calc
      (1 / 2 : ℝ) * (theta ^ 2 * area) =
          areaRateSlope theta shearSq ricciNull area + area * ricciNull := by
            simp only [areaRateSlope, raychaudhuriSlope, hσ]
            ring
      _ = 0 := by rw [h]; ring
  have hprod : theta ^ 2 * area = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hprod with hthetaSq | harea
  · exact hθ (sq_eq_zero_iff.mp hthetaSq)
  · exact hA harea

/--
Any nonzero initial shear-squared and nonzero initial area obstruct the
reduced second-area formula, even when the initial expansion vanishes.
-/
theorem areaRateSlope_ne_neg_area_mul_ricciNull_of_nonzero_shear
    {theta shearSq ricciNull area : ℝ}
    (hθ : theta = 0) (hσ : shearSq ≠ 0) (hA : area ≠ 0) :
    areaRateSlope theta shearSq ricciNull area ≠ -area * ricciNull := by
  intro h
  have hzero : shearSq * area = 0 := by
    calc
      shearSq * area =
          -(areaRateSlope theta shearSq ricciNull area + area * ricciNull) := by
            simp only [areaRateSlope, raychaudhuriSlope, hθ]
            ring
      _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp hzero with hshear | harea
  · exact hσ hshear
  · exact hA harea

/-- Concrete expansion decoy: `θ=2`, `σ²=0`, `R=1`, and `A=1`. -/
theorem decoy_nonzero_expansion_areaRate_ne :
    areaRateSlope 2 0 1 1 ≠ -(1 : ℝ) := by
  norm_num [areaRateSlope, raychaudhuriSlope]

/-- Concrete shear decoy: `θ=0`, `σ²=1`, `R=1`, and `A=1`. -/
theorem decoy_nonzero_shear_areaRate_ne :
    areaRateSlope 0 1 1 1 ≠ -(1 : ℝ) := by
  norm_num [areaRateSlope, raychaudhuriSlope]

/--
Arithmetic derivative of an area law with coefficient `c`,
`A' = c θ A`, evaluated using the Raychaudhuri slope.
-/
def scaledAreaRateSlope
    (c theta shearSq ricciNull area : ℝ) : ℝ :=
  c * (raychaudhuriSlope theta shearSq ricciNull * area
    + theta * (c * theta * area))

/--
Normalization decoy: at the equilibrium witness `θ=0`, `σ²=0`, `R=1`,
`A=1`, coefficient `c=2` yields second-area rate `-2`, not the unit-law
coefficient `-1`.
-/
theorem decoy_areaLaw_coefficient_two_changes_equilibrium :
    scaledAreaRateSlope 2 0 0 1 1 ≠ -(1 : ℝ) := by
  norm_num [scaledAreaRateSlope, raychaudhuriSlope]

end LocalEquilibriumAreaVariation
end Geometry
end Relativity
end IndisputableMonolith
