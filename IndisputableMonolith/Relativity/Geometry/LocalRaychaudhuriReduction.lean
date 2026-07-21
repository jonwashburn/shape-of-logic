import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Local Raychaudhuri equilibrium reduction

This module records the scalar 4D null-congruence slope and proves the
local-equilibrium algebraic reduction of that slope under an explicit
differential-law MODEL.

Honesty tags:

* `LocalRaychaudhuriData.law` is an explicit MODEL interface (the twist-free
  null-horizon Raychaudhuri ODE for the scalar expansion);
* zero initial expansion and shear are equilibrium hypotheses, not derived
  geometric facts;
* this module does **not** introduce a metric, null vector, Ricci tensor,
  area element, ledger, stress, Unruh, all-null equality, EFE, or C-gap1 claim.

What is proved: conditional on the MODEL law, the general initial slope at
`λ = 0`, and under `expansion 0 = 0` with `shearSq 0 = 0`, the initial
expansion derivative equals `-ricciNull 0`. Arithmetic decoys show each
equilibrium premise is load-bearing.
-/

noncomputable section

namespace IndisputableMonolith
namespace Relativity
namespace Geometry
namespace LocalRaychaudhuriReduction

/--
Scalar right-hand side of the 4D null Raychaudhuri law for expansion `θ`,
shear-squared `σ²`, and Ricci null contraction `R_{ab}k^a k^b`:

`dθ/dλ = -½ θ² - σ² - R_{ab}k^a k^b`.

The three arguments are treated as real scalars; no spacetime geometry is
imported.
-/
def raychaudhuriSlope (theta shearSq ricciNull : ℝ) : ℝ :=
  -(1 / 2) * theta ^ 2 - shearSq - ricciNull

/--
Local scalar Raychaudhuri data along an affine parameter. The differential law
is an explicit MODEL premise and is not claimed derived.
-/
structure LocalRaychaudhuriData where
  expansion : ℝ → ℝ
  shearSq : ℝ → ℝ
  ricciNull : ℝ → ℝ
  /-- MODEL: expansion obeys the twist-free null-horizon Raychaudhuri ODE. -/
  law :
    ∀ lambda : ℝ,
      HasDerivAt expansion
        (raychaudhuriSlope (expansion lambda) (shearSq lambda) (ricciNull lambda))
        lambda

/--
General initial slope: the MODEL law specializes at `λ = 0` to the
Raychaudhuri right-hand side evaluated on the initial data.
-/
theorem hasDerivAt_expansion_zero (D : LocalRaychaudhuriData) :
    HasDerivAt D.expansion
      (raychaudhuriSlope (D.expansion 0) (D.shearSq 0) (D.ricciNull 0)) 0 :=
  D.law 0

/--
Under local equilibrium `θ(0) = 0` and `σ²(0) = 0`, the MODEL law reduces to
`HasDerivAt expansion (-ricciNull 0) 0`.
-/
theorem hasDerivAt_expansion_eq_neg_ricciNull
    (D : LocalRaychaudhuriData)
    (hθ : D.expansion 0 = 0) (hσ : D.shearSq 0 = 0) :
    HasDerivAt D.expansion (-D.ricciNull 0) 0 := by
  have h := hasDerivAt_expansion_zero D
  have hslope :
      raychaudhuriSlope (D.expansion 0) (D.shearSq 0) (D.ricciNull 0) =
        -D.ricciNull 0 := by
    simp only [raychaudhuriSlope, hθ, hσ]
    ring
  exact h.congr_deriv hslope

/--
Pointwise derivative form of the equilibrium reduction.
-/
theorem deriv_expansion_zero_eq_neg_ricciNull
    (D : LocalRaychaudhuriData)
    (hθ : D.expansion 0 = 0) (hσ : D.shearSq 0 = 0) :
    deriv D.expansion 0 = -D.ricciNull 0 :=
  (hasDerivAt_expansion_eq_neg_ricciNull D hθ hσ).deriv

/--
Decoy: nonzero initial expansion with zero shear makes the Raychaudhuri
slope differ from `-ricciNull`. Explicit rationals `θ = 2`, `σ² = 0`, `R = 1`
give slope `-3 ≠ -1`.
-/
theorem decoy_nonzero_expansion_slope_ne_neg_ricciNull :
    raychaudhuriSlope (2 : ℝ) 0 1 ≠ -(1 : ℝ) := by
  have hslope : raychaudhuriSlope (2 : ℝ) 0 1 = -3 := by
    simp only [raychaudhuriSlope]
    norm_num
  rw [hslope]
  norm_num

/--
Decoy: zero initial expansion with nonzero shear likewise makes the full slope
differ from `-ricciNull`. Explicit rationals `θ = 0`, `σ² = 1`, `R = 1`
give slope `-2 ≠ -1`.
-/
theorem decoy_nonzero_shear_slope_ne_neg_ricciNull :
    raychaudhuriSlope (0 : ℝ) 1 1 ≠ -(1 : ℝ) := by
  have hslope : raychaudhuriSlope (0 : ℝ) 1 1 = -2 := by
    simp only [raychaudhuriSlope]
    norm_num
  rw [hslope]
  norm_num

/--
General arithmetic form of the expansion decoy: any nonzero `θ` with zero shear
moves the slope away from `-R`.
-/
theorem raychaudhuriSlope_ne_neg_ricciNull_of_nonzero_expansion
    {theta shearSq ricciNull : ℝ}
    (hθ : theta ≠ 0) (hσ : shearSq = 0) :
    raychaudhuriSlope theta shearSq ricciNull ≠ -ricciNull := by
  intro h
  have hslope :
      raychaudhuriSlope theta shearSq ricciNull =
        -(1 / 2) * theta ^ 2 - ricciNull := by
    simp only [raychaudhuriSlope, hσ]
    ring
  have hred : -(1 / 2) * theta ^ 2 - ricciNull = -ricciNull := by
    simpa [hslope] using h
  have hsq : -(1 / 2) * theta ^ 2 = 0 := by
    linarith
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hneg : -((1 / 2 : ℝ) * theta ^ 2) = 0 := by
    simpa [neg_mul] using hsq
  have hprod : (1 / 2 : ℝ) * theta ^ 2 = 0 := by
    linarith
  have hpow : theta ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hhalf
  exact hθ (sq_eq_zero_iff.mp hpow)

/--
General arithmetic form of the shear decoy: any nonzero shear-squared with zero
expansion moves the slope away from `-R`.
-/
theorem raychaudhuriSlope_ne_neg_ricciNull_of_nonzero_shear
    {theta shearSq ricciNull : ℝ}
    (hθ : theta = 0) (hσ : shearSq ≠ 0) :
    raychaudhuriSlope theta shearSq ricciNull ≠ -ricciNull := by
  intro h
  have hslope :
      raychaudhuriSlope theta shearSq ricciNull =
        -shearSq - ricciNull := by
    simp only [raychaudhuriSlope, hθ]
    ring
  have hred : -shearSq - ricciNull = -ricciNull := by
    simpa [hslope] using h
  have : -shearSq = 0 := by linarith
  exact hσ (neg_eq_zero.mp this)

end LocalRaychaudhuriReduction
end Geometry
end Relativity
end IndisputableMonolith
