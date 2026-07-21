import IndisputableMonolith.Gravity.ClausiusEinsteinBridge
import IndisputableMonolith.Relativity.Geometry.LocalEquilibriumAreaVariation

/-!
# Matrix Ricci adapter for local Raychaudhuri data

`LocalEquilibriumAreaVariation` already proves the equilibrium second-area
germ from the explicit area-rate and Raychaudhuri MODEL laws. This module adds
only a definitional adapter from a matrix-valued Ricci field and Lorentz-null
probes to the scalar `ricciNull` consumed there.

Honesty tags:

* `MatrixRicciRaychaudhuriData.law` is MODEL: it is the twist-free null
  Raychaudhuri ODE with the Ricci contraction written explicitly.
* No theorem equates Ricci with stress, derives the probe field from the finite
  cut, or states an Einstein equation.
-/

noncomputable section

namespace IndisputableMonolith
namespace Relativity
namespace Geometry
namespace LocalAreaRaychaudhuri

open LocalRaychaudhuriReduction
open LocalEquilibriumAreaVariation
open Gravity.ClausiusEinsteinBridge

/--
Raychaudhuri data whose Ricci-null scalar is definitionally the quadratic
contraction of a symmetric matrix-valued Ricci field against a Lorentz-null
probe field.

The structure stores the Raychaudhuri differential law but no stress tensor
and no Ricci-stress equality.
-/
structure MatrixRicciRaychaudhuriData where
  expansion : ℝ → ℝ
  shearSq : ℝ → ℝ
  ricciTensor : ℝ → Matrix (Fin 4) (Fin 4) ℝ
  nullProbe : ℝ → Fin 4 → ℝ
  ricci_symmetric :
    ∀ lambda, Symmetric4 (ricciTensor lambda)
  probe_null :
    ∀ lambda, MinkowskiNull (nullProbe lambda)
  /-- MODEL: twist-free null Raychaudhuri with explicit matrix contraction. -/
  law :
    ∀ lambda : ℝ,
      HasDerivAt expansion
        (raychaudhuriSlope (expansion lambda) (shearSq lambda)
          (quadContr (ricciTensor lambda) (nullProbe lambda)))
        lambda

/-- Forget the matrix presentation and expose the scalar Raychaudhuri data. -/
def MatrixRicciRaychaudhuriData.toLocalRaychaudhuriData
    (D : MatrixRicciRaychaudhuriData) :
    LocalRaychaudhuriData where
  expansion := D.expansion
  shearSq := D.shearSq
  ricciNull := fun lambda =>
    quadContr (D.ricciTensor lambda) (D.nullProbe lambda)
  law := D.law

@[simp] theorem toLocalRaychaudhuriData_ricciNull
    (D : MatrixRicciRaychaudhuriData) (lambda : ℝ) :
    D.toLocalRaychaudhuriData.ricciNull lambda =
      quadContr (D.ricciTensor lambda) (D.nullProbe lambda) :=
  rfl

/--
Matrix form of the equilibrium second-area variation, obtained by definitional
transport of `ricciNull` rather than by storing a separate matching equality.
-/
theorem second_area_deriv_eq_neg_area_mul_quadContr
    (D : MatrixRicciRaychaudhuriData)
    (area : ℝ → ℝ)
    (areaLaw :
      ∀ lambda : ℝ,
        HasDerivAt area (D.expansion lambda * area lambda) lambda)
    (hθ : D.expansion 0 = 0)
    (hσ : D.shearSq 0 = 0) :
    deriv (deriv area) 0 =
      -area 0 * quadContr (D.ricciTensor 0) (D.nullProbe 0) := by
  let A : LocalAreaCongruenceData :=
    { D.toLocalRaychaudhuriData with
      area := area
      areaLaw := areaLaw }
  exact deriv_deriv_area_zero_eq_neg_area_mul_ricciNull A hθ hσ

end LocalAreaRaychaudhuri
end Geometry
end Relativity
end IndisputableMonolith
