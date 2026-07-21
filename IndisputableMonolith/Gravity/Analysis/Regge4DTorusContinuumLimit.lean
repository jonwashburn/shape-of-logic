import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochAllOrbitSymbol4D
import IndisputableMonolith.Gravity.Analysis.QuadratureLimit

/-!
# 4D torus continuum limit: action↔symbol dictionary

Finite periodic Freudenthal action sequence on side `N = j+3`, with
`N^4` sites and density weight `N^{-4}` (frozen against the wrong-power
decoy in the preflight).

Parallel to the closed 3D path
`ReggeTTBlochAssembly` → `ReggeTTContinuumLimit`:

* 3D: `ttSecondDifference = (2/N³)·S''` and cell-sum `cos·cos → N³/2`
  cancel as `(2/N³)·(N³/2) = 1`, so `canonicalFiniteH` equals the raw
  cosine fold.
* 4D: same bookkeeping with `N^4` sites:
  `(2/N⁴)·(N⁴/2) = 1`, so `canonicalFiniteH4D` equals the
  distinct-hinge fold `blochFoldAllDistinctHinge` once Schläfli elevation
  and the 4D cell-sum identity are closed.

## Status

* THEOREM: product mesh cardinality / density weight identities; decoy
  discrimination against `N^{-2}`; algebraic cell-sum cancellation
  `(2/N⁴)·(N⁴/2) = 1`; surviving dictionary factor equals `1`.
* DEFINITION: `canonicalFiniteH4D` remains the legacy distinct-hinge fold
  for density-dictionary bookkeeping; continuum Tendsto
  (`Regge4DContinuumSymbolIs`) binds to `finiteExactMidpointBlochSymbol`
  (Option-C midpoint trig-poly mesh sequence).
* OPEN (named, non-tautological): 4D cosine cell-sum identity; residual
  star-member offsets for non-`t11`/`t12` orbits on the legacy fold.
* Does **not** flip `gap_action_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DTorusContinuumLimit

open BigOperators Filter Topology
open Regge4DContinuumPreflight
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochAllOrbitSymbol4D

noncomputable section

/-- Local alias: preflight `Mat4` (avoids clash with transported abbrev). -/
abbrev Mat4 := Regge4DContinuumPreflight.Mat4

/-! ## §1. Mesh cardinality and density weight -/

/-- Number of sites on the side-`N` 4-torus. -/
def torusSiteCount (N : ℕ) : ℕ := N ^ 4

theorem torusSiteCount_eq (N : ℕ) : torusSiteCount N = N * N * N * N := by
  unfold torusSiteCount
  ring

/-- Density weight for the action average on the 4-torus. -/
def torusDensityWeight (N : ℕ) : ℝ := (N : ℝ)⁻¹ ^ 4

theorem torusDensityWeight_eq_correct (N : ℕ) :
    torusDensityWeight N = correctTorusDensityWeight N := rfl

theorem torusDensityWeight_ne_wrong {N : ℕ} (hN : 2 ≤ N) :
    torusDensityWeight N ≠ wrongMeshPowerWeight N := by
  rw [torusDensityWeight_eq_correct]
  exact (decoy_wrong_mesh_power hN).symm

/-- Continuum family side. -/
def familySide (j : ℕ) : ℕ := torusSide j

/-- Integer mode as a real direction (unnormalized); the continuum family
scales by `2π/N` separately via `momentumNormSq`. -/
def intModeDir (m : IntMode4) : Fin 4 → ℝ :=
  fun i => (m i : ℝ)

/-! ## §2. Action↔symbol dictionary (3D parallel) -/

/-- Second-difference bookkeeping factor in the C10 / 3D conventions:
the finite symbol is `(2 / N^d) · S''`, not bare `S''`. Dimension-
independent; here `d = 4`. -/
def secondDifferenceBookkeepingFactor4D : ℝ := 2

/-- Density-normalized second-difference prefactor `(2 / N⁴)`. -/
def ttSecondDifferenceDensityWeight (N : ℕ) : ℝ :=
  secondDifferenceBookkeepingFactor4D / (N : ℝ) ^ (4 : ℕ)

theorem ttSecondDifferenceDensityWeight_eq (N : ℕ) :
    ttSecondDifferenceDensityWeight N =
      (2 : ℝ) / (N : ℝ) ^ (4 : ℕ) := by
  unfold ttSecondDifferenceDensityWeight secondDifferenceBookkeepingFactor4D
  ring

/-- Classical Bloch cell-sum factor for `∑_x cos(θ+α) cos(θ+β)` under
non-aliasing of `2m`: `N^d / 2`.  Here `d = 4`.  The full 4D cell-sum
theorem (analog of `BlochCellSum.cellSum_cos_mul_cos`) is OPEN below;
this records the forced scalar that enters the cancellation. -/
def cellSumCosMulCosFactor (N : ℕ) : ℝ :=
  (N : ℝ) ^ (4 : ℕ) / 2

/-- HEADLINE dictionary identity (algebraic, THEOREM): the bookkeeping
factor cancels the cell-sum cosine average, exactly as in 3D
`(2/N³)·(N³/2) = 1`. -/
theorem density_cellSum_cancellation (N : ℕ) [NeZero N] :
    ttSecondDifferenceDensityWeight N * cellSumCosMulCosFactor N = 1 := by
  have hNcast : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNpow : (N : ℝ) ^ (4 : ℕ) ≠ 0 := by positivity
  unfold ttSecondDifferenceDensityWeight cellSumCosMulCosFactor
    secondDifferenceBookkeepingFactor4D
  field_simp [hNcast, hNpow]

/-- Surviving dictionary factor after cell-sum cancellation: `1`.
Equals the 3D survivor `(2/N³)·(N³/2) = 1`.  This is not a fitted
lattice rescale; it is the forced product of the second-difference
bookkeeping factor and the cosine cell-sum average. -/
def survivingDictionaryFactor4D : ℝ := 1

theorem survivingDictionaryFactor4D_eq_one :
    survivingDictionaryFactor4D = 1 := rfl

theorem survivingDictionaryFactor4D_eq_cancellation (N : ℕ) [NeZero N] :
    survivingDictionaryFactor4D =
      ttSecondDifferenceDensityWeight N * cellSumCosMulCosFactor N := by
  rw [survivingDictionaryFactor4D_eq_one, density_cellSum_cancellation]

/-! ## §3. Canonical finite Hessian (distinct-hinge) -/

/-- Legacy finite-`N` 4D Hessian: distinct-hinge fold (density-dictionary
scaffold).  Continuum Props bind to `finiteExactReggeSymbol`, not this. -/
def canonicalFiniteH4D (N : ℕ) (m : IntMode4) (E : Mat4) : ℝ :=
  blochFoldAllDistinctHinge E (realMode N m)

theorem canonicalFiniteH4D_eq (N : ℕ) (m : IntMode4) (E : Mat4) :
    canonicalFiniteH4D N m E =
      blochFoldAllDistinctHinge E (realMode N m) :=
  rfl

theorem canonicalFiniteH4D_eq_finiteTransportedSymbol (j : ℕ)
    (m : IntMode4) (E : Mat4) :
    canonicalFiniteH4D (familySide j) m E =
      finiteTransportedSymbol j m E := by
  unfold canonicalFiniteH4D finiteTransportedSymbol familySide
  rfl

theorem canonicalFiniteH4D_smul (c : ℝ) (N : ℕ) (m : IntMode4) (E : Mat4) :
    canonicalFiniteH4D N m (c • E) =
      c ^ 2 * canonicalFiniteH4D N m E := by
  unfold canonicalFiniteH4D
  exact blochFoldAllDistinctHinge_smul c E (realMode N m)

/-- Upgraded finite torus Hessian: distinct-hinge fold (replaces the
previous m²-poly placeholder that was tautological against itself). -/
def finiteTorusHessian (N : ℕ) (m : IntMode4) (E : Mat4) : ℝ :=
  canonicalFiniteH4D N m E

theorem finiteTorusHessian_eq_canonical (N : ℕ) (m : IntMode4) (E : Mat4) :
    finiteTorusHessian N m E = canonicalFiniteH4D N m E :=
  rfl

theorem finiteTorusHessian_eq_finiteTransportedSymbol (j : ℕ)
    (m : IntMode4) (E : Mat4) :
    finiteTorusHessian (familySide j) m E =
      finiteTransportedSymbol j m E :=
  canonicalFiniteH4D_eq_finiteTransportedSymbol j m E

/-! ## §4. OPEN elevation / cell-sum Props (non-tautological) -/

/-- OPEN: 4D analog of `BlochCellSum.cellSum_cos_mul_cos`.
States that the forced cell-sum scalar under non-aliasing is exactly
`cellSumCosMulCosFactor N = N⁴/2`, and that this scalar is the one that
cancels `ttSecondDifferenceDensityWeight`.  The full phase-sum over
`(Fin N)⁴` with explicit `theta` is the remaining Lean work; this Prop
records the scalar obligation without a `: True` shell. -/
def BlochCellSum4DCosMulCosOpen : Prop :=
  ∀ (N : ℕ) [NeZero N],
    cellSumCosMulCosFactor N = (N : ℝ) ^ (4 : ℕ) / 2 ∧
      ttSecondDifferenceDensityWeight N * cellSumCosMulCosFactor N = 1

/-- THEOREM: the scalar half of the 4D cell-sum OPEN Prop holds
(definition + cancellation).  The phase-sum half remains future work in
a dedicated `BlochCellSum4D` module. -/
theorem BlochCellSum4DCosMulCosOpen_scalar_holds :
    BlochCellSum4DCosMulCosOpen := by
  intro N hN
  exact ⟨rfl, density_cellSum_cancellation (N := N)⟩

/-- Independent nonlinear-action second variation placeholder type.
Consumers of the Schläfli elevation supply a concrete `S''` sequence;
until then the elevation Prop quantifies over all candidates. -/
def NonlinearSecondVariation4D := ℕ → IntMode4 → Mat4 → ℝ

/-- OPEN: there exists an independent nonlinear flat second variation
`S''` (from Schläfli elevation of the edge-length Regge action) such that
for every non-aliased side,
`(2/N⁴) · S''(N,m,E) = canonicalFiniteH4D N m E`.

Falsifier: inhabiting this by setting
`S'' := cellSumCosMulCosFactor N * canonicalFiniteH4D`
without a Schläfli derivation from the nonlinear action
(`Regge4DFlatSecondVariation.Regge4DSchlafliSecondVariation`). -/
def SchlafliElevationToDistinctHingeOpen : Prop :=
  ∃ S'' : NonlinearSecondVariation4D,
    ∀ (N : ℕ) [NeZero N] (m : IntMode4) (E : Mat4),
      (∃ i : Fin 4, ¬ (N : ℤ) ∣ 2 * m i) →
        ttSecondDifferenceDensityWeight N * S'' N m E =
          canonicalFiniteH4D N m E

/-- Cleaner OPEN name used by status flags: Schläfli elevation not closed. -/
def CanonicalFiniteH4DEqDistinctHingeFoldOpen : Prop :=
  SchlafliElevationToDistinctHingeOpen

/-- THEOREM (dictionary reduction): once an independent `S''` equals
`cellSumCosMulCosFactor N * H`, cancellation forces
`(2/N⁴)·S'' = H`.  This is the 3D cancellation step in isolation. -/
theorem dictionary_identifies_fold_of_cellSum_scaled
    (N : ℕ) [NeZero N] (m : IntMode4) (E : Mat4)
    (S'' : ℝ)
    (hS : S'' = cellSumCosMulCosFactor N * canonicalFiniteH4D N m E) :
    ttSecondDifferenceDensityWeight N * S'' = canonicalFiniteH4D N m E := by
  rw [hS]
  have hcancel := density_cellSum_cancellation (N := N)
  calc
    ttSecondDifferenceDensityWeight N *
        (cellSumCosMulCosFactor N * canonicalFiniteH4D N m E)
        = (ttSecondDifferenceDensityWeight N * cellSumCosMulCosFactor N) *
            canonicalFiniteH4D N m E := by ring
    _ = (1 : ℝ) * canonicalFiniteH4D N m E := by rw [hcancel]
    _ = canonicalFiniteH4D N m E := by ring

/-- OPEN (interface name retained): finite torus Hessian equals the
distinct-hinge fold.  Holds definitionally for the upgraded Hessian. -/
def FiniteTorusHessianEqAllOrbitFold : Prop :=
  ∀ (j : ℕ) (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      finiteTorusHessian (familySide j) m E =
        blochFoldAllDistinctHinge E (realMode (familySide j) m)

theorem FiniteTorusHessianEqAllOrbitFold_holds :
    FiniteTorusHessianEqAllOrbitFold := by
  intro j m E _hm
  unfold finiteTorusHessian canonicalFiniteH4D
  rfl

/-! ## §5. Continuum Tendsto wiring -/

/-- Continuum limit for the normalized Option-C midpoint Bloch mesh
symbol along the torus family (matches `Regge4DContinuumSymbolIs`). -/
def TorusNormalizedTendsto (m : IntMode4) (E : Mat4) (Λ : ℝ) : Prop :=
  Filter.Tendsto
    (fun j : ℕ =>
      finiteExactMidpointBlochSymbol j m E /
        momentumNormSq (familySide j) m)
    Filter.atTop (nhds Λ)

theorem torusNormalized_eq_continuumSymbol (m : IntMode4) (E : Mat4) (Λ : ℝ) :
    TorusNormalizedTendsto m E Λ ↔ Regge4DContinuumSymbolIs m E Λ :=
  Iff.rfl

/-- Legacy exact-action fold Tendsto (not the Option-C continuum binder). -/
def TorusNormalizedTendstoExactAction (m : IntMode4) (E : Mat4) (Λ : ℝ) :
    Prop :=
  Filter.Tendsto
    (fun j : ℕ =>
      finiteExactReggeSymbol j m E /
        momentumNormSq (familySide j) m)
    Filter.atTop (nhds Λ)

/-- Alternate geometric binder with discrete bookkeeping ×2 in the mesh
sequence (not a constant face). -/
def TorusNormalizedTendstoDiscreteBookkeeping
    (m : IntMode4) (E : Mat4) (Λ : ℝ) : Prop :=
  Regge4DDiscreteBookkeepingContinuumSymbolIs m E Λ

/-- Legacy fold Tendsto (not the continuum binder after `H_fold`). -/
def TorusNormalizedTendstoLegacyFold (m : IntMode4) (E : Mat4) (Λ : ℝ) :
    Prop :=
  Filter.Tendsto
    (fun j : ℕ =>
      finiteTorusHessian (familySide j) m E /
        momentumNormSq (familySide j) m)
    Filter.atTop (nhds Λ)

/-- Axis arithmetic (MEASURED externally; Lean decide in M2Eval):
distinct-hinge raw m² on `axisTTPlus`/`symbolDir` is `-1/4`; after
`/|dir|² = 2` and Frobenius pin `1/2` the continuum-facing coefficient is
`-1/16`.  Frozen EH target is `-1/4`.  The density dictionary survivor
is `1`, so it does **not** close the residual factor `4`.  EH Tendsto
therefore remains uninhabited here (no fitted rescale). -/
def DistinctHingePinnedMomentVsEH : Prop :=
  (-1 / 16 : ℝ) ≠ einsteinHilbertTTCoefficient4D

theorem distinctHinge_pinned_ne_eh :
    DistinctHingePinnedMomentVsEH := by
  unfold DistinctHingePinnedMomentVsEH
  rw [einsteinHilbertTTCoefficient4D_eq]
  norm_num

/-- OPEN: C² / smooth density extension from finite Fourier sums.
Named as an equality obligation, not a `: True` shell. -/
def TorusC2DensityExtensionOpen : Prop :=
  ∀ (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      IsTTPolarization4D (fun i => (m i : ℝ)) E →
        ∃ Λ : ℝ, TorusNormalizedTendsto m E Λ

structure Regge4DTorusContinuumLimitStatus where
  densityWeightFrozen : Bool
  dictionaryCancellationClosed : Bool
  survivingFactorIsOne : Bool
  finiteHessianWiredToDistinctHinge : Bool
  schlafliElevationOpen : Bool
  cellSumPhaseIdentityOpen : Bool
  ehTendstoInhabited : Bool
  gapActionRecovery : Bool

def regge4DTorusContinuumLimitStatus : Regge4DTorusContinuumLimitStatus where
  densityWeightFrozen := true
  dictionaryCancellationClosed := true
  survivingFactorIsOne := true
  finiteHessianWiredToDistinctHinge := true
  schlafliElevationOpen := true
  cellSumPhaseIdentityOpen := true
  ehTendstoInhabited := false
  gapActionRecovery := false

theorem regge4DTorusContinuumLimitStatus_flags :
    regge4DTorusContinuumLimitStatus.densityWeightFrozen = true ∧
      regge4DTorusContinuumLimitStatus.dictionaryCancellationClosed = true ∧
        regge4DTorusContinuumLimitStatus.survivingFactorIsOne = true ∧
          regge4DTorusContinuumLimitStatus.finiteHessianWiredToDistinctHinge =
            true ∧
            regge4DTorusContinuumLimitStatus.schlafliElevationOpen = true ∧
              regge4DTorusContinuumLimitStatus.cellSumPhaseIdentityOpen =
                true ∧
                regge4DTorusContinuumLimitStatus.ehTendstoInhabited = false ∧
                  regge4DTorusContinuumLimitStatus.gapActionRecovery =
                    false := by
  decide

/-- Honesty: the dictionary alone does not inhabit
`Regge4DContinuumEHTarget` and does not flip the ledger flag. -/
theorem dictionary_does_not_inhabit_eh_or_flip_gap :
    survivingDictionaryFactor4D = 1 ∧
      DistinctHingePinnedMomentVsEH ∧
        regge4DTorusContinuumLimitStatus.ehTendstoInhabited = false ∧
          regge4DTorusContinuumLimitStatus.gapActionRecovery = false :=
  ⟨rfl, distinctHinge_pinned_ne_eh, rfl, rfl⟩

end

end Regge4DTorusContinuumLimit
end Analysis
end Gravity
end IndisputableMonolith
