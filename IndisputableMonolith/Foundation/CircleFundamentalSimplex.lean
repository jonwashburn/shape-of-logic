import IndisputableMonolith.Foundation.CircleParam

/-!
# The Fundamental Singular 1-Simplex of the Circle

This module constructs the once-around singular 1-simplex in the actual
singular simplicial set `TopCat.toSSet.obj (TopCat.sphere 1)` and proves its
two faces coincide at the chosen basepoint.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleFundamentalSimplex

open CategoryTheory Opposite
open scoped Real

noncomputable section

open CircleParam

/-- The continuous once-around path from the topological standard 1-simplex to
the exact `TopCat.sphere 1` object.  The parameter is the second barycentric
coordinate, so the endpoints evaluate at angles `0` and `2π`. -/
def fundamentalCirclePathMap :
    C(stdSimplex ℝ (Fin 2), TopCat.sphere 1) where
  toFun x := trigCirclePoint (2 * Real.pi * (x : Fin 2 → ℝ) 1)
  continuous_toFun := by
    apply continuous_trigCirclePoint.comp
    have hcoord : Continuous fun x : stdSimplex ℝ (Fin 2) => (x : Fin 2 → ℝ) 1 :=
      (continuous_apply 1).comp continuous_subtype_val
    exact continuous_const.mul hcoord

/-- The once-around singular 1-simplex in `TopCat.toSSet.obj (TopCat.sphere 1)`.
This is the geometric generator candidate for the later H1 computation. -/
def fundamentalSphereOneSingularOneSimplex :
    (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 1)) :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).symm
    fundamentalCirclePathMap

/-- The `δ 0` face of the fundamental singular 1-simplex is the chosen
basepoint.  In Mathlib's simplex convention this endpoint evaluates the second
barycentric coordinate at `1`, hence the angle `2π`. -/
theorem fundamentalSphereOneSingularOneSimplex_face_zero :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
      fundamentalSphereOneSingularOneSimplex =
        constantSphereOneSingularZeroSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))).injective
  ext x
  dsimp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr,
    fundamentalSphereOneSingularOneSimplex, fundamentalCirclePathMap,
    constantSphereOneSingularZeroSimplex]
  change trigCirclePoint
      (2 * Real.pi *
        ((stdSimplex.map (S := ℝ) ⇑(ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2))) x :
            stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1) =
    sphereOneBasepoint
  rw [show
      ((stdSimplex.map (S := ℝ) ⇑(ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2))) x :
          stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 = 1 by
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    simp [SimplexCategory.δ]
    decide]
  simpa using trigCirclePoint_two_pi

/-- The `δ 1` face of the fundamental singular 1-simplex is the chosen
basepoint.  This endpoint evaluates the second barycentric coordinate at `0`,
hence the angle `0`. -/
theorem fundamentalSphereOneSingularOneSimplex_face_one :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
      fundamentalSphereOneSingularOneSimplex =
        constantSphereOneSingularZeroSimplex := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))).injective
  ext x
  dsimp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr,
    fundamentalSphereOneSingularOneSimplex, fundamentalCirclePathMap,
    constantSphereOneSingularZeroSimplex]
  change trigCirclePoint
      (2 * Real.pi *
        ((stdSimplex.map (S := ℝ) ⇑(ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2))) x :
            stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1) =
    sphereOneBasepoint
  rw [show
      ((stdSimplex.map (S := ℝ) ⇑(ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2))) x :
          stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 = 0 by
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    simp [SimplexCategory.δ]]
  simpa using trigCirclePoint_zero

/-- The fundamental once-around singular 1-simplex is a loop: its two faces are
equal in the actual singular simplicial set of `TopCat.sphere 1`. -/
theorem fundamentalSphereOneSingularOneSimplex_faces_eq :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
      fundamentalSphereOneSingularOneSimplex =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
          fundamentalSphereOneSingularOneSimplex := by
  rw [fundamentalSphereOneSingularOneSimplex_face_zero,
    fundamentalSphereOneSingularOneSimplex_face_one]

end

end CircleFundamentalSimplex
end Foundation
end IndisputableMonolith
