import Mathlib
import IndisputableMonolith.Physics.MixingDerivation
import IndisputableMonolith.StandardModel.PMNSMatrix

/-!
# Phase 2 (Particle Spectrum) — P2-PMNS: PMNS mixing scorecard

**Row:** full PMNS mixing (sin²θ₁₂, sin²θ₁₃, sin²θ₂₃), PMNS `δ_CP` quadrant band,
re-use **CKM-geometry** Jarlskog construction packaged with PDG-like targets.

**Predicted (RS):** `sin2_theta*_pred` and `PMNSMatrix.deltaCP_pmns_torsion_correction`
from `MixingDerivation` / `PMNSMatrix`.

**Observed (PDG / typical NuFIT center values):** sin²θ₁₂ ≈ 0.307, sin²θ₁₃ ≈ 0.0220,
sin²θ₂₃ ≈ 0.545–0.546, δ_CP ≈ 197° (quadrant check via radians in `(π,2π)`).

**Falsifier (one sentence):** A NuFIT/PDG update that moves any sin²θ center outside
the stated RS absolute-error certificates with no compensating change in the RS inputs
(α, φ-bounds) falsifies the packaged matches.

**Status:** The angle matches and δ_CP band are `PARTIAL_THEOREM` (proved intervals vs
centers); scheme dependence of sin²θ_W and PMNS parameters is a named display residual.

**Lean: 0 sorry, 0 new axiom**
-/

namespace IndisputableMonolith.Physics.PMNSScoreCard

open IndisputableMonolith
open IndisputableMonolith.Physics.MixingDerivation
open IndisputableMonolith.StandardModel.PMNSMatrix

noncomputable section

/-! ## Row aliases re-exporting proved facts -/

theorem row_pmns_theta12 :
    |sin2_theta12_pred - 0.307| < 0.01 := pmns_theta12_match

theorem row_pmns_theta13 :
    |sin2_theta13_pred - 0.022| < 0.002 := pmns_theta13_match

theorem row_pmns_theta23 :
    |sin2_theta23_pred - 0.546| < 0.01 := pmns_theta23_match

theorem row_jarlskog :
    |jarlskog_pred - 3.08e-5| < 0.6e-5 := jarlskog_match

theorem row_jarlskog_pos : 0 < jarlskog_pred := jarlskog_pos

theorem row_deltaCP_pmns_in_open_band :
    Real.pi < deltaCP_pmns_torsion_correction ∧
      deltaCP_pmns_torsion_correction < 2 * Real.pi := deltaCP_pmns_range

structure PMNSScoreCardCert where
  theta12 : |sin2_theta12_pred - 0.307| < 0.01
  theta13 : |sin2_theta13_pred - 0.022| < 0.002
  theta23 : |sin2_theta23_pred - 0.546| < 0.01
  jarlskog : |jarlskog_pred - 3.08e-5| < 0.6e-5
  j_pos : 0 < jarlskog_pred
  deltaCP_band :
    Real.pi < deltaCP_pmns_torsion_correction ∧
      deltaCP_pmns_torsion_correction < 2 * Real.pi

theorem pmnsScoreCardCert_holds : Nonempty PMNSScoreCardCert :=
  ⟨{ theta12 := row_pmns_theta12
     theta13 := row_pmns_theta13
     theta23 := row_pmns_theta23
     jarlskog := row_jarlskog
     j_pos := row_jarlskog_pos
     deltaCP_band := row_deltaCP_pmns_in_open_band }⟩

end

end IndisputableMonolith.Physics.PMNSScoreCard
