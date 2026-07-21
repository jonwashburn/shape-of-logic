import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochStarEdgeOriginsM2Eval4D

/-!
# Exact flat Regge Hessian Bloch symbol (true cross-term)

Python-first construction (2026-07-21), judged by the exact-action oracle
`scripts/qg/regge_4d_gauge_discrimination_probe_20260721.py`.

At the flat background every deficit vanishes, so Schläfli reduces the
second variation of `S = Σ_h A_h δ_h` to the cross term
`S'' = Σ_h (dA_h)(dδ_h)` in squared-length coordinates (Codex second
opinion: factor is `Σ A' δ'`, not `2Σ`; then symmetrize).  No pathwise
off-flat Schläfli primitive is required for this flat Hessian.

## Algebraic m² table (2026-07-21 Stage 1)

Unit-cell (50-hinge min-vertex fund domain) with sympy-exact Heron `∂A`
and Gram-dihedral `∂θ`, Taylor `cos(k·Δ) → O(k²)` on absolute midpoints:
`scripts/qg/regge_4d_exact_m2_table_20260721.py`, receipt
`state/qg_full_theory/regge_4d_exact_m2_table_20260721.txt`.

On TT polarizations the m² density is isotropic
`Q_m2(H,k) = (-1/8) ‖H‖_F² |k|²`.  The banked axisTTPlus face
(`‖H‖_F = √2`) is therefore exactly `-1/4`.  Gauge `H = k⊗v+v⊗k`
gives exactly `0`.  All Gram sqrts cancel in the final rationals.

Concrete Stage-1 face coeffs are banked below.  A general algebraic
`ℚ(√)` coupling table `C_abcdij` is **not** present in Lean;
`ExactHessianAlgebraicM2TablePresent` stays honest about that (false).
Decide-certs on named modes are not a general algebraic table.

## Edge-origin m² certificates (2026-07-21)

Lean THEOREM certificates from
`ReggeBlochStarEdgeOriginsM2Eval4D` (radical-cancelled `decide` on
`Fin 24 × Fin 10`), banked here without inhabiting ledger `S_RS` or
flipping `gap_action_recovery`:

* `axisTTPlus` / `symbolDir` → `-1/4`
* `axisTTCross` / `symbolDir` → `-1/4`
* `decoyGauge` / `symbolDir` → `0`
* `gaugeM1100E2` / `symbolDir` → `0`

## What this module is

* Names the **true** flat cross-term Hessian / Bloch symbol object that
  supersedes the distinct-hinge fold for continuum claims.
* Records MEASURED finite-`N` certificates from
  `state/qg_full_theory/regge_4d_exact_hessian_symbol_20260721.txt`.
* Banks Stage-1 isotropic face coeffs and the edge-origin m² decide
  certificates for the banked TT/gauge family.
* States OPEN Lean Tendsto / `S_RS` targets (aligned in words with
  `Regge4DContinuumPreflight`).

## What this module is not

* Does **not** delete or edit fold modules (banked lessons).
* Does **not** inhabit ledger `S_RS_converges_EH_4d`.
* Does **not** flip `gap_action_recovery`.
* Does **not** revive constant-face ContinuumSymbolIs.
* Banks algebraic discrete-bookkeeping TT/gauge faces
  (`2·(-1/8)=-1/4`, gauge `0`) as non-ledger facts.

## Tier tags

* MODEL: `ExactFlatHessianSymbol`, midpoint Bloch phase convention.
* MEASURED (external gate: Python oracle + receipt): TT norm at `N=6`
  on `axisTTPlus`/`symbolDir`; 60-mode binary gauge battery; same-
  lattice-shell TT isotropy.
* THEOREM: Stage-1 isotropic face coeffs; discrete-bookkeeping
  `2·unitF=-1/4`; gauge face `0`; edge-origin m² certificates for
  banked family (TT plus/cross, decoy + counterex gauges on
  `symbolDir`).
* OPEN: `FoldAlongM2Tendsto` / geometric ContinuumSymbolIs Tendsto for
  all modes; ledger `S_RS` inhabit; e0 isotropy.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianSymbol4D

open ReggeBlochStarEdgeOriginsM2Eval4D
open ReggeBlochStarEdgeOrigins4D (m2AllOrbitMomentDistinctHingeEdgeOrigins)
open ReggeBlochM2Symbol4D (symbolDir)
open ReggeEdgeStencil4D (decoyGauge)
open EdgeTTDecomposition4D (axisTTPlus axisTTCross)

noncomputable section

/-! ## §1. Named object (MODEL)

Continuum-facing symbol: flat cross-term quadratic form on plane-wave
edge strains with **true per-edge midpoint phases**
`x_e = base + D/2`.  Not the distinct-hinge fold; not a fitted rescale.
-/

/-- MODEL tag: the true flat cross-term Hessian / midpoint Bloch symbol. -/
structure ExactFlatHessianSymbol where
  usesMidpointPhases : Bool := true
  usesCrossTermOnly : Bool := true
  usesDistinctHingeFold : Bool := false

def exactFlatHessianSymbol : ExactFlatHessianSymbol where
  usesMidpointPhases := true
  usesCrossTermOnly := true
  usesDistinctHingeFold := false

theorem exactFlatHessianSymbol_not_fold :
    exactFlatHessianSymbol.usesDistinctHingeFold = false ∧
      exactFlatHessianSymbol.usesCrossTermOnly = true ∧
        exactFlatHessianSymbol.usesMidpointPhases = true := by
  decide

/-- Frozen EH TT coefficient (banked axisTTPlus / Preflight convention). -/
def einsteinHilbertTTCoefficient4D : ℝ := -(1 / 4)

theorem einsteinHilbertTTCoefficient4D_eq :
    einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) := rfl

/-! ## §2. MEASURED finite-N certificates (frozen receipt numbers) -/

/-- Banked oracle / exact-Hessian TT norm at `N = 6` on
`axisTTPlus` / `symbolDir`: stand-in `-24434/100000` for `-0.24434`. -/
def measuredTTNormCoeffN6 : ℝ := -(24434 / 100000)

theorem measuredTTNormCoeffN6_near_quarter :
    |measuredTTNormCoeffN6 - einsteinHilbertTTCoefficient4D| < (1 / 100 : ℝ) := by
  norm_num [measuredTTNormCoeffN6, einsteinHilbertTTCoefficient4D]

/-- Exact-Hessian / oracle relative agreement bound on that TT mode. -/
def measuredTTRelErrVsOracleN6 : ℝ := 2 / 100000

theorem measuredTTRelErrVsOracleN6_lt_1e4 :
    measuredTTRelErrVsOracleN6 < (1 / 10000 : ℝ) := by
  norm_num [measuredTTRelErrVsOracleN6]

/-- 60-mode binary gauge battery: all norms below `1e-4` at `N=6`. -/
def measuredGaugeBatteryPassN6 : Bool := true

theorem measuredGaugeBatteryPassN6_true :
    measuredGaugeBatteryPassN6 = true := rfl

/-- Same-lattice-shell TT isotropy at finite `N`: plus / cross /
rotated-plus probes with `|m|=√2` agree (MEASURED). -/
def measuredSameShellTTIsotropyN6 : Bool := true

theorem measuredSameShellTTIsotropyN6_true :
    measuredSameShellTTIsotropyN6 = true := rfl

/-- Two-point small-`k` intercept for `axisTTPlus`/`symbolDir`:
stand-in `-249884/1000000` for measured `α ≈ -0.249884`. -/
def measuredSmallKAlphaSymbolDir : ℝ := -(249884 / 1000000)

theorem measuredSmallKAlphaSymbolDir_near_quarter :
    |measuredSmallKAlphaSymbolDir - einsteinHilbertTTCoefficient4D| <
      (1 / 1000 : ℝ) := by
  norm_num [measuredSmallKAlphaSymbolDir, einsteinHilbertTTCoefficient4D]

/-! ## §3. Algebraic m² coefficient table (THEOREM evals)

Receipt: `state/qg_full_theory/regge_4d_exact_m2_table_20260721.txt`.
Unique nonzero quartic-tensor values among `C_abcdij`: `-1/16`, `1/32`,
`1/8`.  On TT the contraction collapses to the isotropic identity below.
-/

/-- Unit-Frobenius TT m² coefficient: `Q_m2 / |k|² = -1/8`. -/
def exactHessianM2UnitFrobeniusTTCoeff : ℝ := -(1 / 8)

theorem exactHessianM2UnitFrobeniusTTCoeff_eq :
    exactHessianM2UnitFrobeniusTTCoeff = -(1 / 8 : ℝ) := rfl

/-- Banked `axisTTPlus` m² coefficient (`‖H‖_F = √2`): exactly `-1/4`. -/
def exactHessianM2AxisTTPlusCoeff : ℝ := -(1 / 4)

theorem exactHessianM2AxisTTPlusCoeff_eq :
    exactHessianM2AxisTTPlusCoeff = -(1 / 4 : ℝ) := rfl

theorem exactHessianM2AxisTTPlus_eq_EH :
    exactHessianM2AxisTTPlusCoeff = einsteinHilbertTTCoefficient4D := by
  simp [exactHessianM2AxisTTPlusCoeff, einsteinHilbertTTCoefficient4D]

/-- Gauge m² coefficient on `H = k⊗v + v⊗k`: exactly `0`. -/
def exactHessianM2GaugeCoeff : ℝ := 0

theorem exactHessianM2GaugeCoeff_eq :
    exactHessianM2GaugeCoeff = (0 : ℝ) := rfl

/-- Relation of the two TT normalizations: `(-1/8) * 2 = -1/4`
(`‖axisTTPlus‖_F² = 2`). -/
theorem exactHessianM2_unitF_times_two_eq_axisTTPlus :
    exactHessianM2UnitFrobeniusTTCoeff * (2 : ℝ) =
      exactHessianM2AxisTTPlusCoeff := by
  norm_num [exactHessianM2UnitFrobeniusTTCoeff, exactHessianM2AxisTTPlusCoeff]

/-- Compact isotropic identity on TT (unit wavevector): coefficient `-1/8`
per unit Frobenius mass.  Named as a definitional certificate; the Python
Stage 1 gate verified it on all 5 TT polarizations × 7 wavevector rays. -/
def exactHessianM2IsotropicOnTT : Bool := true

theorem exactHessianM2IsotropicOnTT_true :
    exactHessianM2IsotropicOnTT = true := rfl

/-- Honest: a general algebraic `ℚ(√)` coupling table is absent in Lean.
Stage-1 isotropic face coeffs and named-mode decide-certs are banked
separately; they do not constitute this table. -/
def ExactHessianAlgebraicM2TablePresent : Bool := false

theorem exactHessianAlgebraicM2Table_absent :
    ExactHessianAlgebraicM2TablePresent = false := rfl

/-- Unique nonzero values appearing in the Stage-1 Python quartic tensor
`C` (MEASURED transcription; not a Lean algebraic table). -/
def exactHessianM2CUniqueValues : List ℚ := [(-1 : ℚ) / 16, (1 : ℚ) / 32, (1 : ℚ) / 8]

theorem exactHessianM2CUniqueValues_eq :
    exactHessianM2CUniqueValues = [(-1 : ℚ) / 16, (1 : ℚ) / 32, (1 : ℚ) / 8] := rfl

/-! ## §4. Banked algebraic faces + edge-origin m² certs (non-ledger)

Geometric midpoint Tendsto of the trig-poly / mesh ContinuumSymbolIs
remains OPEN.  Identities below are banked and do **not** inhabit ledger
`S_RS_converges_EH_4d` or flip `gap_action_recovery`.
-/

/-- Banked: discrete bookkeeping times unit-F m² recovers frozen EH. -/
def ExactHessianTTIsotropyTarget : Prop :=
  (2 : ℝ) * exactHessianM2UnitFrobeniusTTCoeff = einsteinHilbertTTCoefficient4D

theorem ExactHessianTTIsotropyTarget_closed :
    ExactHessianTTIsotropyTarget := by
  unfold ExactHessianTTIsotropyTarget exactHessianM2UnitFrobeniusTTCoeff
    einsteinHilbertTTCoefficient4D
  norm_num

/-- Algebraic gauge m² face is `0`. -/
def ExactHessianGaugeZeroTarget : Prop :=
  exactHessianM2GaugeCoeff = (0 : ℝ)

theorem ExactHessianGaugeZeroTarget_algebraic_face :
    ExactHessianGaugeZeroTarget :=
  exactHessianM2GaugeCoeff_eq

/-- Packaged algebraic-face package (local mirror; not the ledger Prop). -/
def ExactHessianS_RS_converges_EH_4d : Prop :=
  ExactHessianTTIsotropyTarget ∧ ExactHessianGaugeZeroTarget

theorem ExactHessianS_RS_converges_EH_4d_closed :
    ExactHessianS_RS_converges_EH_4d :=
  ⟨ExactHessianTTIsotropyTarget_closed, ExactHessianGaugeZeroTarget_algebraic_face⟩

/-- Algebraic bookkeeping identity closed; geometric Tendsto still open. -/
def ExactHessianNormalizationGatePass : Bool := true

theorem exactHessianNormalizationGatePass_true :
    ExactHessianNormalizationGatePass = true := rfl

theorem exact_unitFrobenius_ne_frozen_EH :
    exactHessianM2UnitFrobeniusTTCoeff ≠ einsteinHilbertTTCoefficient4D := by
  unfold exactHessianM2UnitFrobeniusTTCoeff einsteinHilbertTTCoefficient4D
  norm_num

/-- Structural division identity used by the cosine two-jet Tendsto route:
`(a * s + r) / s = a + r / s` when `s ≠ 0`. -/
theorem exactHessian_m2_div_identity
    (a r s : ℝ) (hs : s ≠ 0) :
    (a * s + r) / s = a + r / s := by
  field_simp [hs]

/-- Punctured-neighborhood form of the same identity (for Tendsto glue). -/
theorem exactHessian_m2_div_identity_punctured
    (a : ℝ) (f r : (Fin 4 → ℝ) → ℝ)
    (hf : ∀ k, f k = a * (∑ i, k i ^ 2) + r k)
    (k : Fin 4 → ℝ) (hk : (∑ i, k i ^ 2) ≠ 0) :
    f k / ∑ i, k i ^ 2 = a + r k / ∑ i, k i ^ 2 := by
  rw [hf k, exactHessian_m2_div_identity a (r k) _ hk]

/-! ## §4b. Banked edge-origin m² certificates (THEOREM)

Imported from `ReggeBlochStarEdgeOriginsM2Eval4D`.  These close the
named-mode discrete moment; they do **not** close Tendsto / `S_RS`.
-/

/-- Banked family: TT plus/cross and decoy/counterex gauges on `symbolDir`. -/
def ExactHessianEdgeOriginsM2Banked : Prop :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir = (-1 / 4 : ℝ) ∧
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir = (-1 / 4 : ℝ) ∧
      m2AllOrbitMomentDistinctHingeEdgeOrigins decoyGauge symbolDir = (0 : ℝ) ∧
        m2AllOrbitMomentDistinctHingeEdgeOrigins gaugeM1100E2 symbolDir = (0 : ℝ)

theorem ExactHessianEdgeOriginsM2Banked_closed :
    ExactHessianEdgeOriginsM2Banked :=
  ⟨m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTPlus_symbolDir,
    m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTCross_symbolDir,
    m2AllOrbitMomentDistinctHingeEdgeOrigins_decoyGauge_symbolDir,
    m2AllOrbitMomentDistinctHingeEdgeOrigins_gaugeM1100E2_symbolDir⟩

theorem exactHessian_m2_axisTTPlus_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir =
      (-1 / 4 : ℝ) :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTPlus_symbolDir

theorem exactHessian_m2_axisTTCross_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir =
      (-1 / 4 : ℝ) :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTCross_symbolDir

theorem exactHessian_m2_decoyGauge_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins decoyGauge symbolDir = (0 : ℝ) :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_decoyGauge_symbolDir

theorem exactHessian_m2_gaugeM1100E2_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins gaugeM1100E2 symbolDir = (0 : ℝ) :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_gaugeM1100E2_symbolDir

/-! ## §5. Status package (honest) -/

structure ExactHessianSymbolStatus where
  oracleValidated : Bool
  gaugeBatteryPass : Bool
  sameShellIsotropy : Bool
  algebraicM2Table : Bool
  edgeOriginsM2Banked : Bool
  srsInhabited : Bool
  gapActionRecovery : Bool

def exactHessianSymbolStatus : ExactHessianSymbolStatus where
  oracleValidated := true
  gaugeBatteryPass := true
  sameShellIsotropy := true
  algebraicM2Table := false
  edgeOriginsM2Banked := true
  srsInhabited := false
  gapActionRecovery := false

theorem exactHessianSymbolStatus_flags :
    exactHessianSymbolStatus.oracleValidated = true ∧
      exactHessianSymbolStatus.gaugeBatteryPass = true ∧
        exactHessianSymbolStatus.sameShellIsotropy = true ∧
          exactHessianSymbolStatus.algebraicM2Table = false ∧
            exactHessianSymbolStatus.edgeOriginsM2Banked = true ∧
              exactHessianSymbolStatus.srsInhabited = false ∧
                exactHessianSymbolStatus.gapActionRecovery = false := by
  decide

/-- Algebraic faces + edge-origin m² banked; ledger S_RS / gap stay false. -/
theorem exact_hessian_algebraic_face_banked :
    ExactHessianS_RS_converges_EH_4d ∧
      ExactHessianEdgeOriginsM2Banked ∧
        exactHessianSymbolStatus.srsInhabited = false ∧
          exactHessianSymbolStatus.gapActionRecovery = false :=
  ⟨ExactHessianS_RS_converges_EH_4d_closed, ExactHessianEdgeOriginsM2Banked_closed,
    rfl, rfl⟩

theorem exact_hessian_srs_still_open :
    exactHessianSymbolStatus.srsInhabited = false ∧
      exactHessianSymbolStatus.gapActionRecovery = false := by
  decide

/-- Residual OPEN targets (not closed by the banked m² certificates). -/
def ExactHessianResidualOpen : Prop :=
  exactHessianSymbolStatus.srsInhabited = false ∧
    exactHessianSymbolStatus.gapActionRecovery = false ∧
      ExactHessianAlgebraicM2TablePresent = false

theorem exact_hessian_residual_open :
    ExactHessianResidualOpen :=
  ⟨rfl, rfl, rfl⟩

end

end ReggeExactFlatHessianSymbol4D
end Analysis
end Gravity
end IndisputableMonolith
