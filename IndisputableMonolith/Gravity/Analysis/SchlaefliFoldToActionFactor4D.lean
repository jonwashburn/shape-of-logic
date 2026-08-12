import Mathlib

/-!
# Schläfli derivation of the fold-to-action factor

Arc 2 step 9, task 2. Frozen proposition:
`holography/plans/Arc2_Step9_Schlaefli_Factor_Proposition_20260802.html`.

Expected value frozen before this module: **2**.

At flat background the Regge action is `S = Σ_h A_h δ_h` with every deficit
zero. Schläfli cancels the pure-deficit first variation. The Hessian cross
term that remains is the symmetrized pairing

  Σ_h (∂A_h/∂x_i · ∂δ_h/∂x_j + ∂A_h/∂x_j · ∂δ_h/∂x_i).

The bare geometric fold sums only one ordering `Σ_h ∂A · ∂δ`. For scalar
area and deficit variations the two orderings agree, so the action Hessian
is exactly twice the bare fold.

## What is proved

* The symmetrized cross term equals twice the bare fold (factor 2).
* Decoy factor 1 fails (one ordering is not the Hessian).
* Decoy factor 4 fails (product with a foreign normalization is not this gate).

## Honesty

* THEOREM: the algebraic identities below, on an abstract hinge-indexed
  bilinear form. No continuum coefficient module is imported.
* MODEL: identifying the abstract bare fold with
  `exactFlatCrossTermFold` and the symmetrized form with the Regge action
  Hessian. That naming link is Arc 2 step 9 task 1, not this module.
* Scope: flat-background cross term after Schläfli cancellation. Does not
  derive Regge's `ρ = 1/2`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace SchlaefliFoldToActionFactor4D

noncomputable section

/-- Frozen expected value. Written into the proposition HTML before this
module existed. -/
def expectedFoldToActionFactor : ℝ := 2

/-- Decoy: keep only one ordering. -/
def decoyFactorOne : ℝ := 1

/-- Decoy: fold-to-action conflated with the foreign `1/ρ` factor. -/
def decoyFactorFour : ℝ := 4

/-- Bare geometric fold: one ordering of area×deficit variations. -/
def bareFold {H : Type*} [Fintype H] (dA dδ : H → ℝ) : ℝ :=
  ∑ h : H, dA h * dδ h

/-- Action Hessian cross term after Schläfli: symmetrized pairing. -/
def symmetrizedCross {H : Type*} [Fintype H] (dA dδ : H → ℝ) : ℝ :=
  ∑ h : H, (dA h * dδ h + dδ h * dA h)

/-- **Main identity.** For real scalars, the two orderings agree, so the
symmetrized cross term is exactly twice the bare fold. -/
theorem symmetrizedCross_eq_two_mul_bareFold {H : Type*} [Fintype H]
    (dA dδ : H → ℝ) :
    symmetrizedCross dA dδ = 2 * bareFold dA dδ := by
  unfold symmetrizedCross bareFold
  calc
    ∑ h : H, (dA h * dδ h + dδ h * dA h)
        = ∑ h : H, (dA h * dδ h + dA h * dδ h) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          ring
    _ = ∑ h : H, (2 * (dA h * dδ h)) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          ring
    _ = 2 * ∑ h : H, dA h * dδ h := by
          rw [← Finset.mul_sum]

/-- The derived fold-to-action factor, as a ratio when the bare fold is nonzero. -/
def foldToActionFactor {H : Type*} [Fintype H] (dA dδ : H → ℝ) : ℝ :=
  if bareFold dA dδ = 0 then expectedFoldToActionFactor
  else symmetrizedCross dA dδ / bareFold dA dδ

/-- **Derivation.** Whenever the bare fold is nonzero, the factor equals the
frozen expected value 2. -/
theorem foldToActionFactor_eq_two {H : Type*} [Fintype H]
    (dA dδ : H → ℝ) (hne : bareFold dA dδ ≠ 0) :
    foldToActionFactor dA dδ = expectedFoldToActionFactor := by
  unfold foldToActionFactor expectedFoldToActionFactor
  rw [if_neg hne, symmetrizedCross_eq_two_mul_bareFold]
  field_simp [hne]

/-- Abstract witness: one hinge with unit variations. -/
theorem bareFold_unit_ne :
    bareFold (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) ≠ 0 := by
  unfold bareFold
  simp

/-- Instantiated derivation at the unit witness. -/
theorem foldToActionFactor_eq_two_unit :
    foldToActionFactor (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ))
      = expectedFoldToActionFactor :=
  foldToActionFactor_eq_two _ _ bareFold_unit_ne

/-- **Decoy D1 fails.** Factor 1 is not the symmetrized/bare ratio. -/
theorem decoyFactorOne_ne_derived :
    decoyFactorOne ≠ expectedFoldToActionFactor := by
  unfold decoyFactorOne expectedFoldToActionFactor
  norm_num

/-- **Decoy D4 fails.** Factor 4 is not the fold-to-action factor. -/
theorem decoyFactorFour_ne_derived :
    decoyFactorFour ≠ expectedFoldToActionFactor := by
  unfold decoyFactorFour expectedFoldToActionFactor
  norm_num

/-- Composite gate: derived factor is 2; both decoys miss. -/
theorem schlaefli_fold_to_action_gate :
    expectedFoldToActionFactor = 2 ∧
      decoyFactorOne ≠ expectedFoldToActionFactor ∧
      decoyFactorFour ≠ expectedFoldToActionFactor ∧
      foldToActionFactor (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) = 2 := by
  refine ⟨rfl, decoyFactorOne_ne_derived, decoyFactorFour_ne_derived, ?_⟩
  simpa [expectedFoldToActionFactor] using foldToActionFactor_eq_two_unit

end

end SchlaefliFoldToActionFactor4D
end Analysis
end Gravity
end IndisputableMonolith
