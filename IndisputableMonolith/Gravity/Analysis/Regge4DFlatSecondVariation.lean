import Mathlib
import IndisputableMonolith.Geometry.SchlaefliN
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.Regge4DTorusContinuumLimit
import IndisputableMonolith.Gravity.Analysis.Regge4DTensorAlgebraicCloser
import IndisputableMonolith.Gravity.Analysis.Regge4DTransportedAlgebraicCloser
import IndisputableMonolith.Gravity.Analysis.Regge4DSchlaefliPathwise

/-!
# 4D Regge flat second variation (Schläfli elevation status)

Mirrors the 3D `ReggeTTFlatSecondVariation` contract: Gate A2 elevates the
true nonlinear Regge action to a Schläfli-reduced edge Hessian.  In 3D that
elevation is THEOREM (`tetraSchlaefliSixEdgeClosedForm` →
`trueReggeAction_secondVariation_flat_schlaefli`).  In 4D the flat-seed
Freudenthal flat closed form and flat directional Schläfli kill are
THEOREM in `Regge4DSchlaefliPathwise`
(`freudenthal4SimplexFlatSchlaefli`,
`freudenthal4SimplexFlatDirectionalSchlaefli`, seed-angle `HasDerivAt`);
the full off-flat pathwise closed form remains absent, so elevation of
the nonlinear action stays OPEN.

## Tier tags (binding)

* THEOREM: candidate reduced Hessian identified with the assembled /
  distinct-hinge geometry object; Bloch continuum face of that candidate
  on Frobenius-normalized axis TT at `symbolDir` equals `-1/16`; that
  face differs from frozen EH `-1/4`; density dictionary survivor is `1`.
* THEOREM: flat Freudenthal 4-simplex Schläfli summand table with
  vanishing column sums, seed-hinge geometric match, seed-angle
  `HasDerivAt`, and flat directional kill along every affine velocity
  (`Regge4DSchlaefliPathwise`).
* OPEN: full off-flat `Freudenthal4SimplexPathwiseSchlaefli` and therefore
  `Regge4DSchlafliElevationToCandidate` (nonlinear `S''(0)` equals the
  candidate).
* Does **not** flip `gap_action_recovery`.
* Does **not** inhabit `S_RS_converges_EH_4d`.

## Why prior paths do not close this gap

* Distinct-hinge fold: symbolDir isotropic at face `-1/16`; e0 plus `= 0`.
* Full two-jet: equals `A0·K2` (`K0 = 0`); no repair.
* Path B mean-local: equals distinct-hinge (vacuous); position-resolved
  breaks symbolDir isotropy.
* Density dictionary survivor already `1`.

Residual is therefore Schläfli elevation of the nonlinear action, not
another incidence rescale or fitted factor.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DFlatSecondVariation

open ReggeFlat4DHessianAssembly
open ReggeEdgeStencil4D
open EdgeTTDecomposition4D (axisTTPlus axisTTCross)
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochM2Symbol4D (symbolDir)
open Regge4DContinuumPreflight
open Regge4DTorusContinuumLimit
open Regge4DTensorAlgebraicCloser
open Regge4DTransportedAlgebraicCloser (symbolDir_normSq)
open Geometry.SchlaefliN
open ReggeHinge4DDihedralKernel
open Regge4DSchlaefliPathwise

noncomputable section

/-- Local alias: preflight `Mat4`. -/
abbrev Mat4 := Regge4DContinuumPreflight.Mat4

/-! ## §0. Flat-seed Schläfli progress (from Regge4DSchlaefliPathwise) -/

theorem flat_freudenthal_schlaefli_present :
    freudenthal4SimplexFlatSchlaefliPresent = true :=
  freudenthal4SimplexFlatSchlaefliPresent_true

theorem flat_freudenthal_schlaefli_identity (e : Fin 10) :
    (∑ h : Fin 10, flatSchlaefliSummand h e) = 0 :=
  freudenthal4SimplexFlatSchlaefli e

theorem flat_freudenthal_directional_schlaefli_present :
    freudenthal4SimplexFlatDirectionalSchlaefliPresent = true :=
  freudenthal4SimplexFlatDirectionalSchlaefliPresent_true

/-- Gate A2-style flat directional kill, re-exported for elevation wiring. -/
theorem flat_freudenthal_directional_schlaefli (v : Fin 10 → ℝ) :
    (∑ h : Fin 10, hingeAreaFlat h * flatDirectionalAngleDeriv v h) = 0 :=
  freudenthal4SimplexFlatDirectionalSchlaefli v

theorem flat_freudenthal_seed_angle_hasDerivAt (k : Fin 10) :
    HasDerivAt (fun t : ℝ => seedDihedralAngle (coordPath k t))
      (angleKernel k) (seedFlatSqEdges k) :=
  hasDerivAt_seedDihedralAngle_coord k

/-! ## §1. Candidate Schläfli-reduced Hessian (geometry-derived) -/

/-- Zero-momentum candidate: orbit-count × Heron × star-deficit class
quadratic already assembled from committed geometry kernels. -/
def schlaefliCandidateZeroMom (H : Mat4) : ℝ :=
  trueWeightZeroMomQuadratic H

/-- Finite-momentum candidate: distinct-hinge (`1/r_τ`) transported Bloch
fold of the same true-weight kernels.  This is the object that would equal
`(2/N⁴)·S''_nonlinear` under a 3D-style Schläfli elevation + cell-sum
dictionary (cf. `SchlafliElevationToDistinctHingeOpen`). -/
def schlaefliCandidateFold (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  blochFoldAllDistinctHinge H m

theorem schlaefliCandidateZeroMom_eq (H : Mat4) :
    schlaefliCandidateZeroMom H = trueWeightZeroMomQuadratic H :=
  rfl

theorem schlaefliCandidateFold_eq (H : Mat4) (m : Fin 4 → ℝ) :
    schlaefliCandidateFold H m = blochFoldAllDistinctHinge H m :=
  rfl

theorem schlaefliCandidate_vanishes_on_axisTTPlus :
    schlaefliCandidateZeroMom axisTTPlus = 0 :=
  trueWeightZeroMomQuadratic_axisTTPlus

theorem schlaefliCandidate_vanishes_on_decoyGauge :
    schlaefliCandidateZeroMom decoyGauge = 0 :=
  trueWeightZeroMomQuadratic_decoyGauge

/-! ## §2. Missing 4D Schläfli identity (typed OPEN) -/

/-- **Named missing identity** (not a Lean theorem in this library).

Pathwise Schläfli on every Freudenthal / Kuhn 4-simplex, squared-edge
coordinates:

```
  ∀ σ 4-simplex, ∀ e ∈ edges(σ), at every nondegenerate path point,
    Σ_{h ⊂ σ} A_h(σ) · (∂θ_{σ,h} / ∂ℓ²_e) = 0
```

(`nH = nE = 10` instance of `SchlaefliN.SchlaefliIdentityN` with
measures = hinge areas and `dTheta_dL` = squared-edge partials of the
4-simplex dihedrals).

3D analog (THEOREM):
`Geometry.SchlaefliTetrahedronProof.tetraSchlaefliSixEdgeClosedForm`.

Flat-seed algebraic closed form and flat directional kill are THEOREM in
`Regge4DSchlaefliPathwise` (non-vacuous positive-area witness; seed-angle
`HasDerivAt`).  Full off-flat pathwise closed form along a general
nondegenerate path remains absent
(`freudenthal4SimplexPathwiseSchlaefliPresent` stays `false`).  Do not
inhabit a vacuous `Prop` shell. -/
theorem Freudenthal4SimplexPathwiseSchlaefli_absent :
    freudenthal4SimplexPathwiseSchlaefliPresent = false :=
  freudenthal4SimplexPathwiseSchlaefliPresent_false

/-- Interface readiness only: once a concrete `SchlaefliDataN 10 10`
witness with `SchlaefliIdentityN` is supplied, the angle term dies.
This does **not** construct such a witness for Freudenthal 4-simplices. -/
theorem schlaefliN_interface_ready (D : SchlaefliDataN 10 10)
    (hS : SchlaefliIdentityN D) (e : Fin 10) :
    ∑ h : Fin 10, (D.hinge h).measure * D.dTheta_dL h e = 0 :=
  schlaefliN_kills_angle_term D hS e

/-! ## §3. Elevation obligation (OPEN; not a tautology) -/

/-- Independent nonlinear flat second variation type. -/
abbrev NonlinearFlatSecondVariation4D :=
  Regge4DTorusContinuumLimit.NonlinearSecondVariation4D

/-- **OPEN.** Schläfli elevation: there exists an independent nonlinear
`S''` derived from the edge-length Regge action by the 4D pathwise
Schläfli kill (mirroring
`trueReggeAction_secondVariation_flat_schlaefli`) such that for every
non-aliased mode,
`(2/N⁴) · S''(N,m,E) = schlaefliCandidateFold E (realMode N m)`.

Falsifier for a fake inhabit: setting
`S'' := (N⁴/2) · schlaefliCandidateFold` without a derivation from
`Freudenthal4SimplexPathwiseSchlaefli` and the nonlinear action. -/
def Regge4DSchlafliElevationToCandidate : Prop :=
  ∃ S'' : NonlinearFlatSecondVariation4D,
    ∀ (N : ℕ) [NeZero N] (m : IntMode4) (E : Mat4),
      (∃ i : Fin 4, ¬ (N : ℤ) ∣ 2 * m i) →
        ttSecondDifferenceDensityWeight N * S'' N m E =
          schlaefliCandidateFold E (realMode N m)

/-- Alias retained for downstream imports. -/
def Regge4DSchlafliFiniteMomentumOpen : Prop :=
  Regge4DSchlafliElevationToCandidate

def Regge4DSchlafliBridgeOpen : Prop :=
  Regge4DSchlafliElevationToCandidate

/-- Compatibility with the torus-limit elevation Prop. -/
theorem elevation_iff_torus_open :
    Regge4DSchlafliElevationToCandidate ↔
      SchlafliElevationToDistinctHingeOpen := by
  constructor
  · intro ⟨S'', hS⟩
    refine ⟨S'', ?_⟩
    intro N _ m E hna
    have h := hS N m E hna
    simpa [schlaefliCandidateFold, canonicalFiniteH4D] using h
  · intro ⟨S'', hS⟩
    refine ⟨S'', ?_⟩
    intro N _ m E hna
    have h := hS N m E hna
    simpa [schlaefliCandidateFold, canonicalFiniteH4D] using h

/-! ## §4. Bloch evaluation of the candidate (THEOREM) -/

/-- Raw distinct-hinge m² on axis TT plus / `symbolDir` is `-1/4`. -/
theorem candidate_m2_axisTTPlus_symbolDir :
    distinctHingeMomentForm axisTTPlus symbolDir = (-1 / 4 : ℝ) :=
  distinctHingeMomentForm_axisTTPlus_symbolDir

/-- Continuum-facing coefficient after Frobenius pin and `/|symbolDir|²`:
`-1/16`. -/
theorem candidate_continuumFace_normalizedTT_symbolDir :
    distinctHingeMomentForm ((Real.sqrt 2)⁻¹ • axisTTPlus) symbolDir /
        (∑ i : Fin 4, symbolDir i * symbolDir i) =
      (-1 / 16 : ℝ) :=
  continuumFace_normalizedPlus_symbolDir

/-- Frozen EH target. -/
theorem eh_target_neg_quarter :
    einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) :=
  einsteinHilbertTTCoefficient4D_eq

/-- **THEOREM (falsifier arithmetic).** The candidate's continuum face on
normalized TT at `symbolDir` is `-1/16`, which is not the frozen EH
coefficient `-1/4`.  Density dictionary survivor is already `1`. -/
theorem candidate_face_ne_eh :
    (-1 / 16 : ℝ) ≠ einsteinHilbertTTCoefficient4D ∧
      survivingDictionaryFactor4D = 1 :=
  ⟨by rw [einsteinHilbertTTCoefficient4D_eq]; norm_num, rfl⟩

/-- Packaged claim
“Schläfli elevation to the distinct-hinge candidate restores EH `-1/4`”.

Falsifier: if elevation held, the continuum symbol would be the candidate
face `-1/16` (dictionary survivor `1`), contradicting
`einsteinHilbertTTCoefficient4D = -1/4` on the axis TT / `symbolDir`
witness. -/
def SchlaefliElevationToCandidateClosesEH : Prop :=
  Regge4DSchlafliElevationToCandidate ∧
    Regge4DContinuumEHTarget

theorem schlaefli_elevation_to_candidate_misses_eh_face :
    (-1 / 16 : ℝ) ≠ einsteinHilbertTTCoefficient4D :=
  candidate_face_ne_eh.1

/-- Retained name: former tautology `assembled = assembled` is retired.
The live elevation obligation is `Regge4DSchlafliElevationToCandidate`. -/
def Regge4DSchlafliSecondVariation : Prop :=
  Regge4DSchlafliElevationToCandidate

/-! ## §5. Status (honesty flags) -/

structure Regge4DFlatSecondVariationStatus where
  candidateIdentified : Bool
  candidateBlochFaceEvaluated : Bool
  freudenthal4FlatSchlaefliPresent : Bool
  freudenthal4FlatDirectionalPresent : Bool
  freudenthal4PathwiseSchlaefliPresent : Bool
  schlafliElevationOpen : Bool
  gapActionRecovery : Bool

def regge4DFlatSecondVariationStatus : Regge4DFlatSecondVariationStatus where
  candidateIdentified := true
  candidateBlochFaceEvaluated := true
  freudenthal4FlatSchlaefliPresent := true
  freudenthal4FlatDirectionalPresent := true
  freudenthal4PathwiseSchlaefliPresent := false
  schlafliElevationOpen := true
  gapActionRecovery := false

theorem regge4DFlatSecondVariationStatus_flags :
    regge4DFlatSecondVariationStatus.candidateIdentified = true ∧
      regge4DFlatSecondVariationStatus.candidateBlochFaceEvaluated = true ∧
        regge4DFlatSecondVariationStatus.freudenthal4FlatSchlaefliPresent =
          true ∧
          regge4DFlatSecondVariationStatus.freudenthal4FlatDirectionalPresent =
            true ∧
            regge4DFlatSecondVariationStatus.freudenthal4PathwiseSchlaefliPresent =
              false ∧
              regge4DFlatSecondVariationStatus.schlafliElevationOpen = true ∧
                regge4DFlatSecondVariationStatus.gapActionRecovery = false := by
  decide

/-- Honesty: full pathwise absent; elevation OPEN; gap stays false. -/
theorem schlafli_does_not_flip_gap :
    regge4DFlatSecondVariationStatus.freudenthal4PathwiseSchlaefliPresent =
        false ∧
      regge4DFlatSecondVariationStatus.schlafliElevationOpen = true ∧
        regge4DFlatSecondVariationStatus.gapActionRecovery = false :=
  ⟨rfl, rfl, rfl⟩

end

end Regge4DFlatSecondVariation
end Analysis
end Gravity
end IndisputableMonolith
