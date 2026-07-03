import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Verification

open Constants

/-!
# Verification Bridge Core (certified-surface friendly)

This module contains the **minimal** bridge-invariance infrastructure used by the
certified surface (RS spec / band invariance):

- `UnitsRescaled` (anchor rescaling relation with fixed `c`)
- `Observable` + `BridgeEval` + `anchor_invariance`
- canonical K-gate observables and the bridge-level equality `K_gate_bridge`

It intentionally avoids the larger rendering/manifest scaffolds in `IndisputableMonolith/Verification.lean`
so the certified import-closure stays small and non-smuggled.
-/

/-- Anchor rescaling relation: scale time and length anchors together by s>0, keep c fixed. -/
structure UnitsRescaled (U U' : RSUnits) where
  s    : ℝ
  hs   : 0 < s
  tau0 : U'.tau0 = s * U.tau0
  ell0 : U'.ell0 = s * U.ell0
  cfix : U'.c = U.c

def UnitsRescaled.refl (U : RSUnits) : UnitsRescaled U U :=
{ s := 1
, hs := by norm_num
, tau0 := by simp [one_mul]
, ell0 := by simp [one_mul]
, cfix := rfl }

noncomputable def UnitsRescaled.symm {U U' : RSUnits} (h : UnitsRescaled U U') : UnitsRescaled U' U := by
  refine
    { s := h.s⁻¹
      hs := inv_pos.mpr h.hs
      tau0 := ?_
      ell0 := ?_
      cfix := h.cfix.symm }
  · have hs0 : h.s ≠ 0 := ne_of_gt h.hs
    have hcancel : h.s⁻¹ * (h.s * U.tau0) = U.tau0 := by
      calc
        h.s⁻¹ * (h.s * U.tau0) = (h.s⁻¹ * h.s) * U.tau0 := by
          simpa using (mul_assoc h.s⁻¹ h.s U.tau0).symm
        _ = U.tau0 := by simp [hs0]
    calc
      U.tau0 = h.s⁻¹ * (h.s * U.tau0) := hcancel.symm
      _ = h.s⁻¹ * U'.tau0 := by simp [h.tau0.symm]
  · have hs0 : h.s ≠ 0 := ne_of_gt h.hs
    have hcancel : h.s⁻¹ * (h.s * U.ell0) = U.ell0 := by
      calc
        h.s⁻¹ * (h.s * U.ell0) = (h.s⁻¹ * h.s) * U.ell0 := by
          simpa using (mul_assoc h.s⁻¹ h.s U.ell0).symm
        _ = U.ell0 := by simp [hs0]
    calc
      U.ell0 = h.s⁻¹ * (h.s * U.ell0) := hcancel.symm
      _ = h.s⁻¹ * U'.ell0 := by simp [h.ell0.symm]

def UnitsRescaled.trans {U U' U'' : RSUnits} (h₁ : UnitsRescaled U U') (h₂ : UnitsRescaled U' U'') :
    UnitsRescaled U U'' :=
{ s := h₂.s * h₁.s
, hs := mul_pos h₂.hs h₁.hs
, tau0 := by
    calc
      U''.tau0 = h₂.s * U'.tau0 := h₂.tau0
      _ = h₂.s * (h₁.s * U.tau0) := by simp [h₁.tau0]
      _ = (h₂.s * h₁.s) * U.tau0 := by ring
, ell0 := by
    calc
      U''.ell0 = h₂.s * U'.ell0 := h₂.ell0
      _ = h₂.s * (h₁.s * U.ell0) := by simp [h₁.ell0]
      _ = (h₂.s * h₁.s) * U.ell0 := by ring
, cfix := by
    calc
      U''.c = U'.c := h₂.cfix
      _ = U.c := h₁.cfix }

/-- A numeric display is dimensionless if it is invariant under anchor rescalings. -/
def Dimensionless (f : RSUnits → ℝ) : Prop := ∀ {U U'}, UnitsRescaled U U' → f U = f U'

/-- Observable: a dimensionless display ready for bridge evaluation. -/
structure Observable where
  f       : RSUnits → ℝ
  dimless : Dimensionless f

/-- Bridge evaluation (A ∘ Q): evaluate any observable under anchors; invariant by construction. -/
@[simp] def BridgeEval (O : Observable) (U : RSUnits) : ℝ := O.f U

/-- Anchor-invariance (Q): evaluation does not depend on rescaled anchors. -/
theorem anchor_invariance (O : Observable) {U U'}
  (hUU' : UnitsRescaled U U') : BridgeEval O U = BridgeEval O U' := O.dimless hUU'

/-- K_A observable equals constant K; dimensionless by definition. -/
noncomputable def K_A_obs : Observable :=
{ f := fun _ => Constants.K
, dimless := by intro _U _U' _h; rfl }

/-- K_B observable equals constant K; dimensionless by definition. -/
noncomputable def K_B_obs : Observable :=
{ f := fun _ => Constants.K
, dimless := by intro _U _U' _h; rfl }

/-- The two route displays agree identically as observables (bridge-level K-gate). -/
theorem K_gate_bridge : ∀ U, BridgeEval K_A_obs U = BridgeEval K_B_obs U := by
  intro U; simp [BridgeEval, K_A_obs, K_B_obs]

end Verification
end IndisputableMonolith
