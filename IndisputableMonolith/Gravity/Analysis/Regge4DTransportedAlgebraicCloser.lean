import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Tendsto4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification

/-!
# Transported 4D algebraic closer: concrete continuum sequence + banked ids

Binds the preflight continuum Prop to the transported multi-orbit fold and
banks every algebraic identity available without claiming EH Tendsto
`-(1/4)` or inhabiting `S_RS_converges_EH_4d`.

## THEOREM (banked here)

* Continuum symbol sequence is definitionally
  `blochFoldAllDistinctHinge` (weight `1/r_τ`) on the torus family
  (`finiteTransportedSymbol`).
* Limit uniqueness for that concrete sequence.
* Quadratic homogeneity of `blochFoldAllDistinctHinge` /
  `finiteTransportedSymbol`.
* Distinct-hinge orbit-sum decomposition of the finite transported symbol.
* `(1,1)`-orbit `FoldAlongM2Tendsto` for axis TT (`-3`) and decoy gauge
  (`0`), via `ReggeBlochM2Tendsto4D`.
* One-orbit ray normalized coefficient `m2Symbol / |symbolDir|²` is not
  the frozen EH coefficient (decoy strengthening).
* Area-convention match: `blochFoldOrbit .t11 = blochFold11` and
  `AreaPushforwardMatchOpen` (via `slotOrbitAreaCov_t11`).

## OPEN (named; status `false`; no fake inhabit)

* `Regge4DContinuumEHTarget`: Tendsto of normalized transported fold to
  `-(1/4)` on Frobenius TT.
* `Regge4DContinuumGaugeZeroTarget`: Tendsto to `0` on pure gauge.

## Disclosures

* Factorized `ReggeBlochAllOrbitSymbol4D` is not the continuum object
  (`L-p1-factorized-vs-transported-fold`).
* Does **not** flip `gap_action_recovery`.
* No `sorry` / `admit` / new axioms / `native_decide` / `: True` headlines.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DTransportedAlgebraicCloser

open BigOperators Filter Topology
open Regge4DContinuumPreflight
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochM2Symbol4D
open ReggeBlochM2Tendsto4D
open ReggeBlochFold4D
open ReggeHinge4DOrbitClassification
open ReggeEdgeStencil4D
open EdgeTTDecomposition4D

abbrev Mat4 := Regge4DContinuumPreflight.Mat4

noncomputable section

/-! ## §1. Concrete continuum sequence binding -/

theorem finiteTransportedSymbol_eq_blochFoldAllDistinctHinge
    (j : ℕ) (m : IntMode4) (E : Mat4) :
    finiteTransportedSymbol j m E =
      blochFoldAllDistinctHinge E (realMode (torusSide j) m) :=
  finiteTransportedSymbol_eq j m E

/-- Compatibility alias: continuum sequence is the distinct-hinge fold. -/
theorem finiteTransportedSymbol_eq_blochFoldAll (j : ℕ) (m : IntMode4)
    (E : Mat4) :
    finiteTransportedSymbol j m E =
      blochFoldAllDistinctHinge E (realMode (torusSide j) m) :=
  finiteTransportedSymbol_eq_blochFoldAllDistinctHinge j m E

theorem continuumSymbolIs_unique_limit {m : IntMode4} {E : Mat4}
    {Λ₁ Λ₂ : ℝ} (h1 : Regge4DContinuumSymbolIs m E Λ₁)
    (h2 : Regge4DContinuumSymbolIs m E Λ₂) : Λ₁ = Λ₂ :=
  continuumSymbolIs_unique h1 h2

theorem finiteTransportedSymbol_eq_orbit_sum (j : ℕ) (m : IntMode4)
    (E : Mat4) :
    finiteTransportedSymbol j m E =
      ∑ ty : HingeOrbitType,
        (orbitStarSize ty)⁻¹ *
          blochFoldOrbit ty E (realMode (torusSide j) m) := by
  rw [finiteTransportedSymbol_eq_blochFoldAllDistinctHinge]
  rfl

/-- `(1,1)` orbit slice of the concrete continuum sequence (unweighted). -/
def finiteTransportedT11Symbol (j : ℕ) (m : IntMode4) (E : Mat4) : ℝ :=
  blochFoldOrbit .t11 E (realMode (torusSide j) m)

theorem finiteTransportedT11Symbol_eq (j : ℕ) (m : IntMode4) (E : Mat4) :
    finiteTransportedT11Symbol j m E =
      blochFoldOrbit .t11 E (realMode (torusSide j) m) :=
  rfl

/-! ## §2. Quadratic homogeneity -/

theorem finiteTransportedSymbol_smul (c : ℝ) (j : ℕ) (m : IntMode4)
    (E : Mat4) :
    finiteTransportedSymbol j m (c • E) =
      c ^ 2 * finiteTransportedSymbol j m E := by
  simp_rw [finiteTransportedSymbol_eq_blochFoldAllDistinctHinge,
    blochFoldAllDistinctHinge_smul]

theorem finiteTransportedSymbol_zero (j : ℕ) (m : IntMode4) :
    finiteTransportedSymbol j m 0 = 0 := by
  simpa using finiteTransportedSymbol_smul (0 : ℝ) j m (1 : Mat4)

/-! ## §3. Banked (1,1) m² Tendsto witnesses (not continuum EH) -/

/-- Axis TT: `(1,1)` foldAlong / μ² → `m2Symbol = -3`. -/
theorem t11_foldAlong_m2_tendsto_axisTTPlus :
    FoldAlongM2Tendsto axisTTPlus :=
  FoldAlongM2Tendsto_of_axisTTPlus

/-- Pure gauge decoy: `(1,1)` foldAlong / μ² → `0`. -/
theorem t11_foldAlong_m2_tendsto_decoyGauge :
    FoldAlongM2Tendsto decoyGauge :=
  FoldAlongM2Tendsto_of_decoyGauge

theorem t11_m2Symbol_axisTTPlus :
    m2Symbol axisTTPlus = -3 :=
  m2Symbol_axisTTPlus

theorem t11_m2Symbol_decoyGauge :
    m2Symbol decoyGauge = 0 :=
  m2Symbol_decoyGauge

/-- Integer mode along the closed `(1,1)` symbol ray `(1,1,0,0)`. -/
def symbolDirIntMode : IntMode4 :=
  fun i => if i.val < 2 then (1 : ℤ) else 0

theorem symbolDir_normSq :
    (∑ i : Fin 4, symbolDir i * symbolDir i) = (2 : ℝ) := by
  simp [symbolDir, Fin.sum_univ_four]
  norm_num

theorem realMode_symbolDirIntMode (N : ℕ) (_hN : N ≠ 0) :
    realMode N symbolDirIntMode =
      fun i => ((2 * Real.pi) / (N : ℝ)) * symbolDir i := by
  funext i
  unfold realMode symbolDirIntMode symbolDir
  fin_cases i <;> simp

/-- One-orbit ray coefficient after `/|k|²` normalization on `symbolDir`:
`m2Symbol / |symbolDir|²`.  For axis TT this is `-3/2`, not EH `-1/4`. -/
def oneOrbitRayNormalizedCoeff (H : Mat4) : ℝ :=
  m2Symbol H / (∑ i : Fin 4, symbolDir i * symbolDir i)

theorem oneOrbitRayNormalizedCoeff_axisTTPlus :
    oneOrbitRayNormalizedCoeff axisTTPlus = (-3 : ℝ) / 2 := by
  unfold oneOrbitRayNormalizedCoeff
  rw [m2Symbol_axisTTPlus, symbolDir_normSq]

theorem oneOrbit_ray_normalized_ne_eh_coefficient :
    oneOrbitRayNormalizedCoeff axisTTPlus ≠
      einsteinHilbertTTCoefficient4D := by
  rw [oneOrbitRayNormalizedCoeff_axisTTPlus, einsteinHilbertTTCoefficient4D_eq]
  norm_num

theorem oneOrbit_m2_ne_eh_coefficient :
    m2Symbol axisTTPlus ≠ einsteinHilbertTTCoefficient4D := by
  rw [m2Symbol_axisTTPlus, einsteinHilbertTTCoefficient4D_eq]
  norm_num

/-! ## §4. OPEN continuum value targets (transported; honest) -/

/-- **OPEN**: Frobenius-normalized TT transported continuum symbol equals
`einsteinHilbertTTCoefficient4D = -1/4`. -/
def Regge4DTransportedTTIsotropyOpen : Prop :=
  Regge4DContinuumEHTarget

/-- **OPEN**: pure-gauge transported continuum symbol vanishes. -/
def Regge4DTransportedGaugeZeroOpen : Prop :=
  Regge4DContinuumGaugeZeroTarget

/-- Formerly OPEN area-covector convention match; now THEOREM. -/
def Regge4DTransportedAreaMatchOpen : Prop :=
  AreaPushforwardMatchOpen

theorem Regge4DTransportedAreaMatchOpen_holds :
    Regge4DTransportedAreaMatchOpen :=
  AreaPushforwardMatchOpen_holds

/-- `(1,1)` orbit fold recovers the classical `blochFold11`. -/
theorem blochFoldOrbit_t11_eq_blochFold11 (H : Mat4) (m : Fin 4 → ℝ) :
    blochFoldOrbit .t11 H m = blochFold11 H m :=
  blochFoldOrbit_t11 H m

/-- Packaged OPEN algebraic closer (area match removed; now proved). -/
def Regge4DTransportedAlgebraicCloserTarget : Prop :=
  Regge4DTransportedTTIsotropyOpen ∧ Regge4DTransportedGaugeZeroOpen

theorem transported_targets_eq_preflight :
    Regge4DTransportedTTIsotropyOpen = Regge4DContinuumEHTarget ∧
      Regge4DTransportedGaugeZeroOpen = Regge4DContinuumGaugeZeroTarget :=
  ⟨rfl, rfl⟩

/-! ## §5. Status flags -/

structure Regge4DTransportedAlgebraicCloserStatus where
  continuumSymbolBoundClosed : Bool
  quadraticHomogeneityClosed : Bool
  t11M2TendstoClosed : Bool
  oneOrbitDecoyClosed : Bool
  /-- Full TT isotropy at EH `-1/4`: still OPEN. -/
  transportedTTIsotropyClosed : Bool
  /-- Pure-gauge continuum vanishing: still OPEN. -/
  transportedGaugeZeroClosed : Bool
  /-- Area convention match t11: closed via `slotOrbitAreaCov_t11`. -/
  areaConventionMatchClosed : Bool
  srsConvergesEH4d : Bool
  gapActionRecovery : Bool

def regge4DTransportedAlgebraicCloserStatus :
    Regge4DTransportedAlgebraicCloserStatus where
  continuumSymbolBoundClosed := true
  quadraticHomogeneityClosed := true
  t11M2TendstoClosed := true
  oneOrbitDecoyClosed := true
  transportedTTIsotropyClosed := false
  transportedGaugeZeroClosed := false
  areaConventionMatchClosed := true
  srsConvergesEH4d := false
  gapActionRecovery := false

theorem regge4DTransportedAlgebraicCloserStatus_flags :
    regge4DTransportedAlgebraicCloserStatus.continuumSymbolBoundClosed =
        true ∧
      regge4DTransportedAlgebraicCloserStatus.quadraticHomogeneityClosed =
        true ∧
        regge4DTransportedAlgebraicCloserStatus.t11M2TendstoClosed = true ∧
          regge4DTransportedAlgebraicCloserStatus.oneOrbitDecoyClosed =
            true ∧
            regge4DTransportedAlgebraicCloserStatus.transportedTTIsotropyClosed =
              false ∧
              regge4DTransportedAlgebraicCloserStatus.transportedGaugeZeroClosed =
                false ∧
                regge4DTransportedAlgebraicCloserStatus.areaConventionMatchClosed =
                  true ∧
                  regge4DTransportedAlgebraicCloserStatus.srsConvergesEH4d =
                    false ∧
                    regge4DTransportedAlgebraicCloserStatus.gapActionRecovery =
                      false := by
  decide

/-- Honesty: banked (1,1) identities do not inhabit continuum EH Tendsto,
and the ledger flag stays false. -/
theorem banked_does_not_inhabit_eh_or_flip_gap :
    regge4DTransportedAlgebraicCloserStatus.transportedTTIsotropyClosed =
        false ∧
      regge4DTransportedAlgebraicCloserStatus.gapActionRecovery = false ∧
        oneOrbitRayNormalizedCoeff axisTTPlus ≠
          einsteinHilbertTTCoefficient4D :=
  ⟨rfl, rfl, oneOrbit_ray_normalized_ne_eh_coefficient⟩

end

end Regge4DTransportedAlgebraicCloser
end Analysis
end Gravity
end IndisputableMonolith
