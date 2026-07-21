import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D

/-!
# Exact midpoint Bloch m² Rayleigh = algebraic faces (R3)

Inhabits `TypedResidual_m2_rayleigh_eq_algebraic_face`:

* unit-Frobenius TT: `exactMidpointBlochM2 H k / |k|² = -1/8`
* pure gauge: `exactMidpointBlochM2 (pureGaugeFamily m v) m / |m|² = 0`

Certificate lives in `ReggeExactMidpointM2TTIdentity4D` (rational packed
biquadratic table + `native_decide` + closed-form transport).  This module
is the ledger-facing name matching SymbolZero4D / the handoff residual R3.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochM2Rayleigh4D

open Regge4DContinuumPreflight
open ReggeExactFlatHessianSymbol4D
  (exactHessianM2UnitFrobeniusTTCoeff exactHessianM2GaugeCoeff)
open ReggeExactFlatHessianBlochSymbol4D
open EdgeTTDecomposition4D
open ReggeExactMidpointM2TTIdentity4D
  (exactMidpointBlochM2_rayleigh_eq_neg_eighth_of_TT
    exactMidpointBlochM2_gauge_rayleigh_eq_zero)

noncomputable section

/-- Disambiguate shared aliases after multi-module opens. -/
abbrev Mat4 := Regge4DContinuumPreflight.Mat4
abbrev Wave4 := Regge4DContinuumPreflight.Wave4

private theorem frobeniusNormSq_preflight_eq_identity (H : Mat4) :
    Regge4DContinuumPreflight.frobeniusNormSq H =
      ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq H :=
  rfl

private theorem waveNormSq_preflight_eq_identity (k : Wave4) :
    Regge4DContinuumPreflight.waveNormSq k =
      ReggeExactMidpointM2TTIdentity4D.waveNormSq k :=
  rfl

/-- Unit-Frobenius TT Rayleigh equals the algebraic face `-1/8`. -/
theorem exactMidpointBlochM2_rayleigh_eq_unitFrobeniusTTCoeff
    (H : Mat4) (k : Wave4)
    (hTT : IsTT k H)
    (hF : frobeniusNormSq H = 1)
    (hk : waveNormSq k ≠ 0) :
    exactMidpointBlochM2 H k / waveNormSq k =
      exactHessianM2UnitFrobeniusTTCoeff := by
  have hF' : ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq H = 1 := by
    simpa [frobeniusNormSq_preflight_eq_identity] using hF
  have hk' : ReggeExactMidpointM2TTIdentity4D.waveNormSq k ≠ 0 := by
    simpa [waveNormSq_preflight_eq_identity] using hk
  have h :=
    exactMidpointBlochM2_rayleigh_eq_neg_eighth_of_TT H k hTT hF' hk'
  simpa [exactHessianM2UnitFrobeniusTTCoeff, waveNormSq_preflight_eq_identity]
    using h

/-- Pure-gauge Rayleigh equals the algebraic face `0`. -/
theorem exactMidpointBlochM2_rayleigh_eq_gaugeCoeff
    (m v : Wave4) (hm : waveNormSq m ≠ 0) :
    exactMidpointBlochM2 (pureGaugeFamily m v) m / waveNormSq m =
      exactHessianM2GaugeCoeff := by
  have hm' : ReggeExactMidpointM2TTIdentity4D.waveNormSq m ≠ 0 := by
    simpa [waveNormSq_preflight_eq_identity] using hm
  have h := exactMidpointBlochM2_gauge_rayleigh_eq_zero m v hm'
  simpa [pureGaugeFamily, exactHessianM2GaugeCoeff,
    waveNormSq_preflight_eq_identity] using h

/-- Packaged algebraic faces matching residual R3. -/
theorem exactMidpointBlochM2_rayleigh_eq_algebraic_face :
    (∀ (H : Mat4) (k : Wave4),
        IsTT k H →
          frobeniusNormSq H = 1 →
            waveNormSq k ≠ 0 →
              exactMidpointBlochM2 H k / waveNormSq k =
                exactHessianM2UnitFrobeniusTTCoeff) ∧
      (∀ (m : Wave4) (v : Wave4),
        waveNormSq m ≠ 0 →
          exactMidpointBlochM2 (pureGaugeFamily m v) m / waveNormSq m =
            exactHessianM2GaugeCoeff) :=
  ⟨exactMidpointBlochM2_rayleigh_eq_unitFrobeniusTTCoeff,
    exactMidpointBlochM2_rayleigh_eq_gaugeCoeff⟩

/-- Ledger-facing inhabit of R3 (same Prop shape as
`SRSConvergesEH4D.TypedResidual_m2_rayleigh_eq_algebraic_face`). -/
theorem typedResidual_m2_rayleigh_eq_algebraic_face :
    (∀ (H : Mat4) (k : Wave4),
        IsTT k H →
          frobeniusNormSq H = 1 →
            waveNormSq k ≠ 0 →
              exactMidpointBlochM2 H k / waveNormSq k =
                exactHessianM2UnitFrobeniusTTCoeff) ∧
      (∀ (m : Wave4) (v : Wave4),
        waveNormSq m ≠ 0 →
          exactMidpointBlochM2 (pureGaugeFamily m v) m / waveNormSq m =
            exactHessianM2GaugeCoeff) :=
  exactMidpointBlochM2_rayleigh_eq_algebraic_face

end

end ReggeExactFlatHessianBlochM2Rayleigh4D
end Analysis
end Gravity
end IndisputableMonolith
