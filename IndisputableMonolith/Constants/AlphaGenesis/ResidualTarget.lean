import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants.ExternalAnchors
import IndisputableMonolith.Constants.AlphaGenesis.LoopCertificate
import IndisputableMonolith.Foundation.MeasureForcing
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Alpha Genesis M4: The Residual Target (quarantine module)

**QUARANTINE.** This is the ONLY Alpha Genesis module that references the
measured value. M1–M3 (the derivation) are blind to CODATA by construction;
this module states the comparison and the open target, and nothing in M1–M3
depends on it.

## What this module proves

1. `residual_bounds`: the certified band confines the residual
   `alphaInv − α⁻¹_CODATA` to `(−0.006, 0.0031)`.
2. `correctedAlphaInv`: with the response forced (M1), any second-order
   correction must enter as ADDITIONAL SPECTRAL LOAD (multiplicatively, in
   the exponent), never as an additive display patch. The legacy additive
   tail `δ_κ = −103/(102π⁵)` belongs to the excluded form-(A) display
   (`DressingResponse.no_additive_response`) and is retired from the
   structural pipeline (it was already removed from the certified value).
3. `closingLoad` exists and is UNIQUE: there is exactly one second-order
   load `δ₂` for which the dressed value equals the measured value
   (`corrected_eq_codata_iff`). The open problem is therefore sharply
   localized: derive this one number from voxel seam geometry, blind.

## The open target (OPEN, expected closure)

Derive `δ₂` from the seam topology of the D=3 voxel lattice with a
procedure that never references CODATA, and publish the result either way.

* If the blind derivation lands on `closingLoad` (within stated tolerance),
  the α derivation closes at experimental precision.
* If it lands elsewhere, the channel-budget bridge (the one named input of
  M3) is wrong and the assembly is falsified at that layer.

**Anti-epicycle rule (binding):** no candidate `δ₂` may be admitted to the
certified surface on the basis of numerical proximity to `closingLoad`.
Admission requires a forced derivation from lattice geometry. The candidate
catalogue of `Verification/AlphaCorrectionAnalysis.lean` is a search record,
not a derivation, and must not be cited as one.

STATUS: THEOREM for 1–3; OPEN (expected closure) for the seam derivation.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis

noncomputable section

open Constants.ExternalAnchors

/-- The signed residual of the (first-order) genesis value against CODATA. -/
def residual : ℝ := Constants.alphaInv - alpha_inv_CODATA

/-- The certified band confines the residual to `(−0.006, 0.0031)`. -/
theorem residual_bounds : (-0.006 : ℝ) < residual ∧ residual < (0.0031 : ℝ) := by
  unfold residual
  have hgt := Numerics.alphaInv_gt
  have hlt := Numerics.alphaInv_lt
  have hC : alpha_inv_CODATA = (137.035999177 : ℝ) := rfl
  constructor
  · rw [hC]; linarith
  · rw [hC]; linarith

/-- **The load-form correction.** With the response forced (M1), any
second-order term enters as additional spectral load in the exponent. -/
def correctedAlphaInv (δ₂ : ℝ) : ℝ :=
  channelBudget * Foundation.MeasureForcing.contWeight (spectralLoad + δ₂)

/-- Zero correction recovers the first-order genesis value. -/
theorem corrected_at_zero : correctedAlphaInv 0 = alphaInvGenesis := by
  unfold correctedAlphaInv alphaInvGenesis
  rw [add_zero]

/-- **The unique closing load**: the one value of `δ₂` aligning the dressed
value with CODATA, written in closed form. This is the sharply localized
open target: derive THIS number from seam geometry, blind. -/
def closingLoad : ℝ :=
  Real.log (alpha_inv_CODATA / channelBudget) / Real.log Foundation.MeasureForcing.rho
    - spectralLoad

/-- `log ρ ≠ 0` (ρ = 1/φ ∈ (0,1)). -/
theorem log_rho_ne_zero : Real.log Foundation.MeasureForcing.rho ≠ 0 := by
  have hneg : Real.log Foundation.MeasureForcing.rho < 0 :=
    Real.log_neg Foundation.MeasureForcing.rho_pos Foundation.MeasureForcing.rho_lt_one
  exact ne_of_lt hneg

/-- The closing load closes: `correctedAlphaInv closingLoad = α⁻¹_CODATA`. -/
theorem corrected_at_closingLoad :
    correctedAlphaInv closingLoad = alpha_inv_CODATA := by
  unfold correctedAlphaInv closingLoad
  have hb : (0 : ℝ) < channelBudget := channelBudget_pos
  have hb' : channelBudget ≠ 0 := ne_of_gt hb
  have hC : (0 : ℝ) < alpha_inv_CODATA := alpha_inv_CODATA_pos
  have hratio : (0 : ℝ) < alpha_inv_CODATA / channelBudget := div_pos hC hb
  have hexp : spectralLoad +
      (Real.log (alpha_inv_CODATA / channelBudget) / Real.log Foundation.MeasureForcing.rho
        - spectralLoad)
      = Real.log (alpha_inv_CODATA / channelBudget) / Real.log Foundation.MeasureForcing.rho := by
    ring
  rw [hexp]
  show channelBudget *
      Foundation.MeasureForcing.rho ^
        (Real.log (alpha_inv_CODATA / channelBudget) / Real.log Foundation.MeasureForcing.rho)
    = alpha_inv_CODATA
  rw [Real.rpow_def_of_pos Foundation.MeasureForcing.rho_pos]
  have hlog : Real.log Foundation.MeasureForcing.rho ≠ 0 := log_rho_ne_zero
  have harg : Real.log Foundation.MeasureForcing.rho *
      (Real.log (alpha_inv_CODATA / channelBudget) / Real.log Foundation.MeasureForcing.rho)
      = Real.log (alpha_inv_CODATA / channelBudget) := by
    field_simp
  rw [harg, Real.exp_log hratio]
  field_simp

/-- **Uniqueness of the closing load.** The dressed value is strictly
decreasing in the load (ρ < 1), so exactly one `δ₂` closes the residual. -/
theorem corrected_eq_codata_iff (δ₂ : ℝ) :
    correctedAlphaInv δ₂ = alpha_inv_CODATA ↔ δ₂ = closingLoad := by
  constructor
  · intro h
    have hb : (0 : ℝ) < channelBudget := channelBudget_pos
    have hkey : Foundation.MeasureForcing.rho ^ (spectralLoad + δ₂) =
        Foundation.MeasureForcing.rho ^ (spectralLoad + closingLoad) := by
      have h2 : correctedAlphaInv δ₂ = correctedAlphaInv closingLoad := by
        rw [h, corrected_at_closingLoad]
      unfold correctedAlphaInv at h2
      exact mul_left_cancel₀ (ne_of_gt hb) h2
    -- ρ^x is strictly antitone for ρ ∈ (0,1), so the exponents agree
    have hexp_eq : spectralLoad + δ₂ = spectralLoad + closingLoad := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmono := Real.rpow_lt_rpow_of_exponent_gt
          Foundation.MeasureForcing.rho_pos Foundation.MeasureForcing.rho_lt_one hlt
        linarith [hkey.le, hkey.ge, hmono]
      · have hmono := Real.rpow_lt_rpow_of_exponent_gt
          Foundation.MeasureForcing.rho_pos Foundation.MeasureForcing.rho_lt_one hgt
        linarith [hkey.le, hkey.ge, hmono]
    linarith [hexp_eq]
  · intro h
    rw [h]
    exact corrected_at_closingLoad

/-- There is exactly one closing load. -/
theorem existsUnique_closingLoad :
    ∃! δ₂ : ℝ, correctedAlphaInv δ₂ = alpha_inv_CODATA := by
  refine ⟨closingLoad, corrected_at_closingLoad, ?_⟩
  intro δ h
  exact (corrected_eq_codata_iff δ).mp h

/-- **THE SEAM FALSIFIER.** A blind seam derivation producing load `δ₂`
closes the α program iff `δ₂ = closingLoad`; any other value falsifies the
channel-budget bridge. (Definition-level statement of the kill condition.) -/
def SeamDerivationCloses (δ₂ : ℝ) : Prop :=
  correctedAlphaInv δ₂ = alpha_inv_CODATA

theorem seam_closes_iff (δ₂ : ℝ) : SeamDerivationCloses δ₂ ↔ δ₂ = closingLoad :=
  corrected_eq_codata_iff δ₂

end

end AlphaGenesis
end Constants
end IndisputableMonolith
