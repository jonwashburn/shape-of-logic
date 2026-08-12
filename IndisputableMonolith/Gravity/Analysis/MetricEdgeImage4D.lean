import Mathlib
import IndisputableMonolith.Foundation.PairKernelDiscreteGauss

/-!
# Finite linearized metric edge image on the Freudenthal patch

Frozen world metric-null of
`holography/plans/OrderSensitive_Gravity_Proposition_20260802.html`.

`MetricEdgeImage F` means `F` is the strain current of some `Mat4`
perturbation on the sixteen-site patch. The strain formula and binary
patch coordinates match `FreudenthalCoverEdgeCurrentAction4D` /
`FreudenthalCoverLedgerGraphPatch4D`, reproduced here so this module
does not import the heavy analysis chain.

## Honesty

* THEOREM: nontriviality, symmetry, properness against antisymmetric posting.
* Scope: linearized flat-patch metric perturbations via `strainCurrent`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace MetricEdgeImage4D

open Foundation.PairKernelDiscreteGauss
open BigOperators

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Binary site coordinates of the unit hypercube (matches `patchSite`). -/
def patchSite (v : Fin 16) (μ : Fin 4) : ℤ :=
  match μ with
  | 0 => ((v.val % 2 : ℕ) : ℤ)
  | 1 => ((v.val / 2 % 2 : ℕ) : ℤ)
  | 2 => ((v.val / 4 % 2 : ℕ) : ℤ)
  | 3 => ((v.val / 8 % 2 : ℕ) : ℤ)

def patchDisp (i j : Fin 16) : Fin 4 → ℤ :=
  fun μ => patchSite j μ - patchSite i μ

/-- Strain formula matching `ReggeExactFlatHessianBlochSymbol4D.edgeStrain`. -/
def edgeStrain (H : Mat4) (D : Fin 4 → ℤ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, H i j * (D i : ℝ) * (D j : ℝ)

/-- Strain current on patch edges. -/
def strainCurrent (H : Mat4) : Fin 16 → Fin 16 → ℝ :=
  fun i j => edgeStrain H (patchDisp i j)

/-- Finite linearized metric edge image on the patch. -/
def MetricEdgeImage (F : Fin 16 → Fin 16 → ℝ) : Prop :=
  ∃ H : Mat4, F = strainCurrent H

theorem edgeStrain_neg (H : Mat4) (D : Fin 4 → ℤ) :
    edgeStrain H (fun μ => -D μ) = edgeStrain H D := by
  unfold edgeStrain
  simp [mul_neg, neg_mul, neg_neg]

theorem patchDisp_symm (i j : Fin 16) (μ : Fin 4) :
    patchDisp j i μ = -patchDisp i j μ := by
  simp [patchDisp, sub_eq_add_neg, add_comm]

theorem strainCurrent_symm (H : Mat4) (i j : Fin 16) :
    strainCurrent H i j = strainCurrent H j i := by
  unfold strainCurrent
  have hD : patchDisp j i = fun μ => -patchDisp i j μ := by
    funext μ; exact patchDisp_symm i j μ
  rw [hD, edgeStrain_neg]

/-- Symmetric off-diagonal witness: H_{23} = H_{32} = 1. -/
def axisTTCross : Mat4 := fun i j =>
  if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then (1 : ℝ) else 0

theorem axisTTCross_in_MetricEdgeImage :
    MetricEdgeImage (strainCurrent axisTTCross) :=
  ⟨axisTTCross, rfl⟩

private theorem patchDisp_zero_twelve :
    patchDisp (0 : Fin 16) 12 = fun μ =>
      (match μ with | 0 => (0 : ℤ) | 1 => 0 | 2 => 1 | 3 => 1) := by
  funext μ
  fin_cases μ <;> rfl

theorem strainCurrent_axisTTCross_zero_twelve :
    strainCurrent axisTTCross (0 : Fin 16) 12 = 2 := by
  unfold strainCurrent
  rw [patchDisp_zero_twelve]
  unfold edgeStrain axisTTCross
  simp [Fin.sum_univ_four]
  norm_num

theorem MetricEdgeImage_nontrivial :
    ∃ F, MetricEdgeImage F ∧ F ≠ fun _ _ => 0 := by
  refine ⟨strainCurrent axisTTCross, axisTTCross_in_MetricEdgeImage, ?_⟩
  intro h
  have := congrFun (congrFun h (0 : Fin 16)) (12 : Fin 16)
  rw [strainCurrent_axisTTCross_zero_twelve] at this
  exact absurd this (by norm_num)

theorem elementaryPosting_zero_four_nonzero :
    elementaryPosting (0 : Fin 16) 4 0 4 = 1 := by
  unfold elementaryPosting
  simp

theorem elementaryPosting_not_in_MetricEdgeImage :
    ¬ MetricEdgeImage (elementaryPosting (0 : Fin 16) 4) := by
  rintro ⟨H, hF⟩
  have hsym := strainCurrent_symm H (0 : Fin 16) 4
  have h0 := congrFun (congrFun hF (0 : Fin 16)) (4 : Fin 16)
  have h1 := congrFun (congrFun hF (4 : Fin 16)) (0 : Fin 16)
  have hanti : elementaryPosting (0 : Fin 16) 4 4 0 =
      -elementaryPosting (0 : Fin 16) 4 0 4 :=
    elementaryPosting_antisym (0 : Fin 16) 4 4 0
  have : elementaryPosting (0 : Fin 16) 4 0 4 =
      elementaryPosting (0 : Fin 16) 4 4 0 := by
    calc
      elementaryPosting (0 : Fin 16) 4 0 4 = strainCurrent H 0 4 := h0
      _ = strainCurrent H 4 0 := hsym
      _ = elementaryPosting (0 : Fin 16) 4 4 0 := h1.symm
  have hnz := elementaryPosting_zero_four_nonzero
  rw [hanti, hnz] at this
  linarith

theorem zero_in_MetricEdgeImage :
    MetricEdgeImage (fun _ _ => 0) := by
  refine ⟨0, ?_⟩
  funext i j
  unfold strainCurrent edgeStrain
  simp

end MetricEdgeImage4D
end Analysis
end Gravity
end IndisputableMonolith
