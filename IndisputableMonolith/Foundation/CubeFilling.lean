import Mathlib
import IndisputableMonolith.Foundation.AmbientFromRecognition

/-!
# Filling of the cube 2-skeleton

The solid 3-cube `[0,1]³` is nonempty. Radial contraction onto its
center is the identity at time 1 and the constant map at time 0.
The combinatorial 2-skeleton has Euler characteristic 2.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CubeFilling

open AmbientFromRecognition

/-- The solid 3-cube as a product of intervals. -/
abbrev SolidCube := Fin 3 → Set.Icc (0 : ℝ) 1

theorem solidCube_nonempty : Nonempty SolidCube :=
  ⟨fun _ => ⟨0, by constructor <;> norm_num⟩⟩

noncomputable def cubeCenter : SolidCube :=
  fun _ => ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

lemma combo_mem_Icc {t x : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (1 - t) * (1 / 2) + t * x ∧ (1 - t) * (1 / 2) + t * x ≤ 1 := by
  constructor
  · nlinarith
  · nlinarith

/-- Straight-line contraction of the solid cube onto its center. -/
noncomputable def radialContraction
    (p : Set.Icc (0 : ℝ) 1 × SolidCube) : SolidCube :=
  fun i =>
    let t := (p.1 : ℝ)
    let x := (p.2 i : ℝ)
    ⟨(1 - t) * (1 / 2) + t * x,
      combo_mem_Icc p.1.property.1 p.1.property.2
        (p.2 i).property.1 (p.2 i).property.2⟩

theorem radialContraction_zero (x : SolidCube) :
    radialContraction (⟨0, by constructor <;> norm_num⟩, x) = cubeCenter := by
  funext i
  apply Subtype.ext
  change (1 - (0 : ℝ)) * (1 / 2) + (0 : ℝ) * (x i : ℝ) = (1 / 2)
  ring

theorem radialContraction_one (x : SolidCube) :
    radialContraction (⟨1, by constructor <;> norm_num⟩, x) = x := by
  funext i
  apply Subtype.ext
  change (1 - (1 : ℝ)) * (1 / 2) + (1 : ℝ) * (x i : ℝ) = (x i : ℝ)
  ring

/-- A point of the solid cube lies on a face when some coordinate is 0 or 1. -/
def OnFace (x : SolidCube) : Prop :=
  ∃ i : Fin 3, (x i : ℝ) = 0 ∨ (x i : ℝ) = 1

/-- The combinatorial 2-skeleton still has Euler characteristic 2. -/
theorem two_skeleton_euler :
    (Fintype.card Q3 : ℤ) - GaugeFromCube.cube_edge_count 3 +
      GaugeFromCube.cube_face_count 3 = 2 :=
  cube_2skeleton_euler_from_counts

/-- The solid cube fills the 2-skeleton: it is nonempty and contracts
onto its center, identity at time 1. The combinatorial Euler count is
`two_skeleton_euler`. -/
theorem solid_cube_fills_two_skeleton :
    Nonempty SolidCube ∧
      (∀ x : SolidCube,
        radialContraction (⟨0, by constructor <;> norm_num⟩, x) = cubeCenter) ∧
      (∀ x : SolidCube,
        radialContraction (⟨1, by constructor <;> norm_num⟩, x) = x) :=
  ⟨solidCube_nonempty, radialContraction_zero, radialContraction_one⟩

end CubeFilling
end Foundation
end IndisputableMonolith
