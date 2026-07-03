import Mathlib
import IndisputableMonolith.RecogSpec.RSLedger
import IndisputableMonolith.RecogSpec.ObservablePayloads
import IndisputableMonolith.Constants

/-!
# Mass Law from Ledger Tiers

Derives the canonical mass-ratio payload `LeptonMassRatios` from `RSLedger`
tier structure.

## Canonical semantics

  massRatios = { mu_over_e := φ^{11}, tau_over_e := φ^{17}, tau_over_mu := φ^{6} }

These are inter-generation mass ratios in the lepton sector, derived from the
torsion differences {0, 11, 17} forced by cube geometry.
-/

namespace IndisputableMonolith
namespace RecogSpec

open Constants

noncomputable section

/-- Mass ratios derived from ledger tier structure.

Uses `massRatioFromRungs` to compute φ-powers from rung differences
rather than defining them as literal φ-formulas. -/
def massRatiosFromTiers (L : RSLedger) (φ : ℝ) : LeptonMassRatios :=
  ⟨ massRatioFromRungs L φ .leptons .second .first,
    massRatioFromRungs L φ .leptons .third .first,
    massRatioFromRungs L φ .leptons .third .second ⟩

/-- For any ledger with canonical torsion {0,11,17}, the derived mass-ratio
    payload equals the φ-power triple. -/
theorem massRatiosFromTiers_canonical (L : RSLedger) (φ : ℝ)
    (hL : L.torsion = generationTorsion) :
    massRatiosFromTiers L φ = ⟨φ ^ (11 : ℤ), φ ^ (17 : ℤ), φ ^ (6 : ℤ)⟩ := by
  simp only [massRatiosFromTiers]
  rw [massRatio_21_canonical L φ .leptons hL,
      massRatio_31_canonical L φ .leptons hL,
      massRatio_32_canonical L φ .leptons hL]

/-- The canonical ledger produces the canonical mass-ratio payload. -/
theorem canonical_massRatiosFromTiers (φ : ℝ) :
    massRatiosFromTiers canonicalRSLedger φ =
      ⟨φ ^ (11 : ℤ), φ ^ (17 : ℤ), φ ^ (6 : ℤ)⟩ :=
  massRatiosFromTiers_canonical canonicalRSLedger φ canonicalRSLedger_torsion

/-- All entries in the canonical mass-ratio payload are positive when φ > 0. -/
theorem massRatiosFromTiers_pos (L : RSLedger) (φ : ℝ) (hφ : 0 < φ)
    (hL : L.torsion = generationTorsion) :
    (massRatiosFromTiers L φ).Forall (0 < ·) := by
  rw [massRatiosFromTiers_canonical L φ hL]
  exact ⟨zpow_pos hφ 11, zpow_pos hφ 17, zpow_pos hφ 6⟩

end

end RecogSpec
end IndisputableMonolith
