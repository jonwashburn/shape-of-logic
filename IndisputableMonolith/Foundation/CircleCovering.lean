import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Covering.Basic
import IndisputableMonolith.Foundation.CircleParam

/-!
# The trigonometric parametrization of `TopCat.sphere 1` is a covering map

This module supplies the covering-space foundation for the by-hand circle-`H₁`
derivation.  Mathlib's singular-homology development (`SingularHomology/Basic`)
proves nothing beyond the totally-disconnected case, so every route to
`H₁(S¹; ℤ) ≅ ℤ` must build its own degree / winding invariant, and the invariant
is defined by lifting singular simplices through a covering map of
`TopCat.sphere 1`.

The headline result is `isCoveringMap_trigCirclePoint`: the concrete map
`t ↦ (cos t, sin t)` already used by `CircleParam` and the fundamental simplex is
an honest covering map.  It is obtained by transporting Mathlib's
`Circle.isCoveringMap_exp` along

* the orthonormal-basis isometry `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`
  (sending `Circle` to the metric unit circle), and
* the `ULift` homeomorphism into the exact `TopCat.sphere 1` carrier.

No axioms, `sorry`, or project-local replacements for `S¹` are used: the result
is about the imported `TopCat.sphere 1` object via real Lean equivalences.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleCovering

open Complex CircleParam

noncomputable section

/-- The orthonormal-basis isometry `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`. -/
def isoE : ℂ ≃ₗᵢ[ℝ] SphereOneAmbient :=
  Complex.orthonormalBasisOneI.repr

/-- The induced homeomorphism from Mathlib's `Circle` onto the exact metric
unit-circle carrier of `TopCat.sphere 1`. -/
def circleHomeoCarrier : Circle ≃ₜ SphereOneCarrier :=
  Homeomorph.subtype isoE.toHomeomorph (fun z => by
    show z ∈ Metric.sphere (0 : ℂ) 1 ↔
        (isoE.toHomeomorph z) ∈ Metric.sphere (0 : SphereOneAmbient) 1
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      LinearIsometryEquiv.norm_map])

/-- The covering map `ℝ → SphereOneCarrier`, transported from `Circle.exp`. -/
def carrierCovering : ℝ → SphereOneCarrier :=
  circleHomeoCarrier ∘ Circle.exp

/-- The transported map is a genuine covering map of the metric circle carrier. -/
theorem isCoveringMap_carrierCovering : IsCoveringMap carrierCovering :=
  Circle.isCoveringMap_exp.homeomorph_comp circleHomeoCarrier

/-- The carrier covering agrees with the ambient trigonometric vector
`(cos t, sin t)`. -/
theorem carrierCovering_val (t : ℝ) :
    (carrierCovering t : SphereOneAmbient) = trigCircleVector t := by
  show isoE (Circle.exp t : ℂ) = trigCircleVector t
  rw [show (Circle.exp t : ℂ) = Complex.exp (t * Complex.I) from Circle.coe_exp t,
      show isoE (Complex.exp (t * Complex.I))
        = Complex.orthonormalBasisOneI.repr (Complex.exp (t * Complex.I)) from rfl]
  ext i
  rw [Complex.orthonormalBasisOneI_repr_apply]
  fin_cases i
  · simp [trigCircleVector, Complex.exp_ofReal_mul_I_re]
  · simp [trigCircleVector, Complex.exp_ofReal_mul_I_im]

/-- The carrier covering, lifted into the exact `TopCat.sphere 1` object, equals
the `CircleParam` trigonometric parametrization pointwise. -/
theorem ulift_carrierCovering_eq_trig :
    (Homeomorph.ulift (X := SphereOneCarrier)).symm ∘ carrierCovering
      = CircleParam.trigCirclePoint := by
  funext t
  apply ULift.ext
  apply Subtype.ext
  exact carrierCovering_val t

/-- **The trigonometric parametrization `t ↦ (cos t, sin t)` of the imported
`TopCat.sphere 1` object is a covering map.**  This is the covering-space
foundation for the winding / degree invariant on singular `1`-chains. -/
theorem isCoveringMap_trigCirclePoint :
    IsCoveringMap CircleParam.trigCirclePoint := by
  rw [← ulift_carrierCovering_eq_trig]
  exact isCoveringMap_carrierCovering.homeomorph_comp
    (Homeomorph.ulift (X := SphereOneCarrier)).symm

end

end CircleCovering
end Foundation
end IndisputableMonolith
