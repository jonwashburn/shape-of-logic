import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Circle Parametrization Primitives

This module starts the by-hand circle-H1 derivation against the actual imported
`TopCat.sphere 1` object.  It establishes the exact carrier, a checked
basepoint, and the constant singular 1-simplex face identities in
`TopCat.toSSet.obj (TopCat.sphere 1)`.

The constant simplex is not the fundamental generator.  It is the first API
anchor: all later once-around simplices should live in this same singular
simplicial set and use the same face maps.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleParam

open CategoryTheory Opposite

noncomputable section

/-- The exact ambient Euclidean space for Mathlib's `TopCat.sphere 1`. -/
abbrev SphereOneAmbient : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- The exact metric-sphere carrier under the `ULift` in `TopCat.sphere 1`. -/
abbrev SphereOneCarrier : Type :=
  Metric.sphere (0 : SphereOneAmbient) 1

/-- The first coordinate unit vector in the ambient Euclidean plane. -/
def sphereOneBaseVector : SphereOneAmbient :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The first coordinate unit vector lies on Mathlib's unit circle. -/
theorem sphereOneBaseVector_mem_sphere :
    sphereOneBaseVector ∈ Metric.sphere (0 : SphereOneAmbient) 1 := by
  change dist (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : SphereOneAmbient) 0 = 1
  simp

/-- Basepoint of the exact `TopCat.sphere 1` object. -/
def sphereOneBasepoint : TopCat.sphere 1 :=
  ULift.up ⟨sphereOneBaseVector, sphereOneBaseVector_mem_sphere⟩

/-- The ambient Euclidean vector `(cos t, sin t)`. -/
def trigCircleVector (t : ℝ) : SphereOneAmbient :=
  !₂[Real.cos t, Real.sin t]

/-- The vector `(cos t, sin t)` lies on the exact metric unit circle used by
`TopCat.sphere 1`. -/
theorem trigCircleVector_mem_sphere (t : ℝ) :
    trigCircleVector t ∈ Metric.sphere (0 : SphereOneAmbient) 1 := by
  change dist (trigCircleVector t) 0 = 1
  rw [dist_zero_right]
  have hsq : ‖trigCircleVector t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [trigCircleVector, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  have hnonneg : 0 ≤ ‖trigCircleVector t‖ := norm_nonneg _
  nlinarith

/-- The ambient trigonometric circle parametrization is continuous. -/
theorem continuous_trigCircleVector :
    Continuous trigCircleVector := by
  change Continuous fun t : ℝ =>
    (WithLp.toLp 2 (fun i : Fin 2 => ![Real.cos t, Real.sin t] i) : SphereOneAmbient)
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp
    (continuous_pi fun i => by
      fin_cases i
      · simpa using Real.continuous_cos
      · simpa using Real.continuous_sin)

/-- The once-around trigonometric parametrization as a point of the exact
`TopCat.sphere 1` object. -/
def trigCirclePoint (t : ℝ) : TopCat.sphere 1 :=
  ULift.up ⟨trigCircleVector t, trigCircleVector_mem_sphere t⟩

/-- The once-around trigonometric parametrization is continuous as a map into
the exact `TopCat.sphere 1` object. -/
theorem continuous_trigCirclePoint :
    Continuous trigCirclePoint := by
  unfold trigCirclePoint
  exact continuous_uliftUp.comp (continuous_trigCircleVector.subtype_mk _)

/-- The trigonometric parametrization starts at the chosen basepoint. -/
theorem trigCirclePoint_zero :
    trigCirclePoint 0 = sphereOneBasepoint := by
  apply ULift.ext
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [trigCirclePoint, trigCircleVector, sphereOneBasepoint, sphereOneBaseVector]

/-- The trigonometric parametrization returns to the basepoint after one full
turn. -/
theorem trigCirclePoint_two_pi :
    trigCirclePoint (2 * Real.pi) = sphereOneBasepoint := by
  apply ULift.ext
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [trigCirclePoint, trigCircleVector, sphereOneBasepoint, sphereOneBaseVector]

/-- The constant singular 1-simplex at `sphereOneBasepoint`, in the actual
singular simplicial set of `TopCat.sphere 1`. -/
def constantSphereOneSingularOneSimplex :
    (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 1)) :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).symm
    (ContinuousMap.const _ sphereOneBasepoint)

/-- The constant singular 0-simplex at `sphereOneBasepoint`. -/
def constantSphereOneSingularZeroSimplex :
    (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 0)) :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))).symm
    (ContinuousMap.const _ sphereOneBasepoint)

/-- The left face of the constant singular 1-simplex is the basepoint
0-simplex. -/
theorem constantSphereOneSingularOneSimplex_face_zero :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
      constantSphereOneSingularOneSimplex =
        constantSphereOneSingularZeroSimplex := by
  rfl

/-- The right face of the constant singular 1-simplex is the basepoint
0-simplex. -/
theorem constantSphereOneSingularOneSimplex_face_one :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
      constantSphereOneSingularOneSimplex =
        constantSphereOneSingularZeroSimplex := by
  rfl

/-- The two faces of the constant singular 1-simplex coincide. -/
theorem constantSphereOneSingularOneSimplex_faces_eq :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
      constantSphereOneSingularOneSimplex =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
          constantSphereOneSingularOneSimplex := by
  rw [constantSphereOneSingularOneSimplex_face_zero,
    constantSphereOneSingularOneSimplex_face_one]

end

end CircleParam
end Foundation
end IndisputableMonolith
