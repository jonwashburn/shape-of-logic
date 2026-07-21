import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochOrbitTransport4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochAllOrbitSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochStarEdgeOrigins4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel12
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Exact flat cross-term continuum symbol (H_fold pivot)

Oracle verdict `H_fold` (2026-07-21): the true Regge action Hessian on the
Freudenthal torus annihilates vertex-gauge modes and sends normalized TT
on `axisTTPlus` / `symbolDir` to `-1/4`.  The distinct-hinge transported
fold `blochFoldAllDistinctHinge` mis-transports (t12/t13 gauge residue)
and is **not** the continuum object.

## Binding object

At flat background deficits vanish, so Schläfli leaves the cross term
`S'' = Σ_h (dA_h)(dδ_h)`.  This module names that Hessian on plane-wave
class strains with position-resolved deficit phasing: `t11` keeps
star-member cube offsets; `t12`/`t13`/`t22` (and complements) use
per-edge transported origins from `ReggeBlochStarEdgeOrigins4D`
(typed blocker `fold_position_resolved_star_phase`, Python-green on the
banked gauge suite with TT plus=cross=-1/4 on `symbolDir`).

## Tier tags

* MODEL: `exactFlatCrossTermFold` / `finiteExactReggeSymbol` (geometry-
  derived flat cross-term; not yet Schläfli-elevated from nonlinear `S`
  for every orbit).
* THEOREM: structural lemmas below (homogeneity, zero-momentum member
  drop, status flags); edge-origin m² certificates for the banked
  family (`axisTTPlus`/`axisTTCross`/`decoyGauge`/`gaugeM1100E2` on
  `symbolDir`) live in `ReggeBlochStarEdgeOriginsM2Eval4D` and are
  re-banked by `ReggeExactFlatHessianSymbol4D`.
* MODEL: discrete bookkeeping factor 2 (3D `ttSecondDifference` parallel).
* OPEN: `FoldAlongM2Tendsto` / geometric ContinuumSymbolIs Tendsto for
  all modes; ledger `S_RS` inhabit; e0 isotropy.  ContinuumSymbolIs
  binds to `finiteExactReggeSymbol` Tendsto in Preflight (not a
  constant face).  Ledger `S_RS` / `gap_action_recovery` stay open/false.
* Does **not** flip `transportedGaugeZeroClosed` (fold-internal).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DExactActionSymbol

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D
open ReggeBlochOrbitTransport4D
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochAllOrbitSymbol4D (isOrbit)
open ReggeBlochStarEdgeOrigins4D
  (phasedDeficitDotEdgeOrigins phasedDeficitDotEdgeOrigins_smul)
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Wave4 := Fin 4 → ℝ

/-! ## §1. Cube offsets for star-member deficit phasing -/

/-- Lattice translate of a type-`(1,1)` star cube. -/
def cubeOffsetT11 : ReggeHinge4DStarKernel.CubeTranslate → Wave4
  | .origin => fun _ => 0
  | .minusE2 => fun i => if i.val = 2 then (-1 : ℝ) else 0
  | .minusE3 => fun i => if i.val = 3 then (-1 : ℝ) else 0
  | .minusE2E3 => fun i => if i.val = 2 ∨ i.val = 3 then (-1 : ℝ) else 0

/-- Lattice translate of a type-`(1,2)` star cube. -/
def cubeOffsetT12 : ReggeHinge4DStarKernel12.CubeTranslate → Wave4
  | .origin => fun _ => 0
  | .minusE3 => fun i => if i.val = 3 then (-1 : ℝ) else 0

/-- Star-member index → cube for the committed `(1,1)` enumeration. -/
def starMemberCubeT11 : Fin 6 → ReggeHinge4DStarKernel.CubeTranslate
  | ⟨0, _⟩ | ⟨1, _⟩ => .origin
  | ⟨2, _⟩ => .minusE2
  | ⟨3, _⟩ => .minusE3
  | ⟨4, _⟩ | ⟨5, _⟩ => .minusE2E3

/-- Star-member index → cube for the committed `(1,2)` enumeration. -/
def starMemberCubeT12 : Fin 4 → ReggeHinge4DStarKernel12.CubeTranslate
  | ⟨0, _⟩ | ⟨1, _⟩ => .origin
  | ⟨2, _⟩ | ⟨3, _⟩ => .minusE3

/-- Transport a lattice offset by a covering coordinate permutation:
`off'(σ(j)) = off(j)`. -/
def transportOffset (p : Fin 24) (off : Wave4) : Wave4 :=
  fun i => ∑ j : Fin 4, if coordPermOf p j = i then off j else 0

theorem transportOffset_zero (p : Fin 24) :
    transportOffset p (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  funext i
  unfold transportOffset
  simp

/-! ## §2. Star-member-resolved deficit phased dots -/

/-- Resolved deficit contraction for type `(1,1)`: sum star members at
their cube translates, pushed by covering perm `p`. -/
def phasedDeficitDotResolvedT11 (H : Mat4) (m : Wave4) (x : Wave4)
    (p : Fin 24) : ℝ :=
  ∑ μ : Fin 6,
    phasedClassDot
      (pushforwardClass (ReggeHinge4DStarKernel.assembleStarMember μ) p) H m
      (fun i => x i + transportOffset p (cubeOffsetT11 (starMemberCubeT11 μ)) i)

/-- Resolved deficit contraction for type `(1,2)`. -/
def phasedDeficitDotResolvedT12 (H : Mat4) (m : Wave4) (x : Wave4)
    (p : Fin 24) : ℝ :=
  ∑ μ : Fin 4,
    phasedClassDot
      (pushforwardClass (ReggeHinge4DStarKernel12.assembleStarMember μ) p) H m
      (fun i => x i + transportOffset p (cubeOffsetT12 (starMemberCubeT12 μ)) i)

/-- Collapsed (legacy) deficit contraction: single hingeBase for the
full-star kernel.  Used only as fallback for orbits without cube-offset
tables in Lean. -/
def phasedDeficitDotCollapsed (ty : HingeOrbitType) (H : Mat4)
    (m x : Wave4) (s : Fin 24) (t : Fin 10) : ℝ :=
  phasedClassDot (slotOrbitDeficitKer ty s t) H m x

/-! ## §3. Exact flat cross-term slot / orbit / fold -/

/-- Deficit side of the exact flat cross-term slot. -/
def exactDeficitDot (ty : HingeOrbitType) (H : Mat4) (m : Wave4)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  match ty with
  | .t11 =>
      phasedDeficitDotResolvedT11 H m (hingeBase s t) (orbitCoveringPerm .t11 s t)
  | .t12 | .t21 | .t13 | .t31 | .t22 =>
      phasedDeficitDotEdgeOrigins ty H m s t

/-- Exact flat cross-term slot: area at hingeBase times resolved deficit. -/
def exactFlatCrossTermSlot (ty : HingeOrbitType) (H : Mat4) (m : Wave4)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    phasedClassDot (slotOrbitAreaCov ty s t) H m (hingeBase s t) *
      exactDeficitDot ty H m s t
  else 0

def exactFlatCrossTermOrbit (ty : HingeOrbitType) (H : Mat4) (m : Wave4) :
    ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, exactFlatCrossTermSlot ty H m s t

/-- Distinct-hinge weighted exact flat cross-term fold.
This is the continuum-facing Hessian candidate after `H_fold`. -/
def exactFlatCrossTermFold (H : Mat4) (m : Wave4) : ℝ :=
  ∑ ty : HingeOrbitType, (orbitStarSize ty)⁻¹ * exactFlatCrossTermOrbit ty H m

/-! ## §4. Continuum family sequence (side `N = j+3`) -/

/-- Continuum family side (matches `Regge4DContinuumPreflight.torusSide`). -/
def familySide (j : ℕ) : ℕ := j + 3

def familyRealMode (j : ℕ) (m : Fin 4 → ℤ) : Wave4 :=
  fun i => (2 * Real.pi) * (m i : ℝ) / (familySide j : ℝ)

/-- Named exact-action continuum symbol sequence (bare Regge cross-term;
`s''_Regge` face before discrete bookkeeping). -/
def finiteExactReggeSymbol (j : ℕ) (m : Fin 4 → ℤ) (E : Mat4) : ℝ :=
  exactFlatCrossTermFold E (familyRealMode j m)

def finiteExactReggeSymbolSequence (m : Fin 4 → ℤ) (E : Mat4) :
    ℕ → ℝ :=
  fun j => finiteExactReggeSymbol j m E

/-- Dimension-independent discrete bookkeeping factor from the 3D
`ttSecondDifference = (2/N³)·S''` convention (EH audit §2.3).  Not a
fitted lattice rescale. -/
def discreteBookkeepingFactor : ℝ := 2

theorem discreteBookkeepingFactor_eq : discreteBookkeepingFactor = (2 : ℝ) :=
  rfl

/-- Discrete exact Regge symbol: 3D-parallel bookkeeping package
`2 · finiteExactReggeSymbol`.  Alternate geometric continuum sequence
(normalized by `|k|²`); ledger ContinuumSymbolIs currently binds the
bare `finiteExactReggeSymbol` sequence. -/
def discreteExactReggeSymbol (j : ℕ) (m : Fin 4 → ℤ) (E : Mat4) : ℝ :=
  discreteBookkeepingFactor * finiteExactReggeSymbol j m E

def discreteExactReggeSymbolSequence (m : Fin 4 → ℤ) (E : Mat4) :
    ℕ → ℝ :=
  fun j => discreteExactReggeSymbol j m E

theorem discreteExactReggeSymbol_eq (j : ℕ) (m : Fin 4 → ℤ) (E : Mat4) :
    discreteExactReggeSymbol j m E =
      (2 : ℝ) * finiteExactReggeSymbol j m E := by
  unfold discreteExactReggeSymbol discreteBookkeepingFactor
  ring

/-! ## §5. Structural theorems -/

private lemma phasedDeficitDotResolvedT11_smul (c : ℝ) (H : Mat4)
    (m x : Wave4) (p : Fin 24) :
    phasedDeficitDotResolvedT11 (c • H) m x p =
      c * phasedDeficitDotResolvedT11 H m x p := by
  unfold phasedDeficitDotResolvedT11
  simp_rw [phasedClassDot_smul, Finset.mul_sum]

private lemma phasedDeficitDotResolvedT12_smul (c : ℝ) (H : Mat4)
    (m x : Wave4) (p : Fin 24) :
    phasedDeficitDotResolvedT12 (c • H) m x p =
      c * phasedDeficitDotResolvedT12 H m x p := by
  unfold phasedDeficitDotResolvedT12
  simp_rw [phasedClassDot_smul, Finset.mul_sum]

private lemma phasedDeficitDotCollapsed_smul (c : ℝ) (ty : HingeOrbitType)
    (H : Mat4) (m x : Wave4) (s : Fin 24) (t : Fin 10) :
    phasedDeficitDotCollapsed ty (c • H) m x s t =
      c * phasedDeficitDotCollapsed ty H m x s t := by
  unfold phasedDeficitDotCollapsed
  rw [phasedClassDot_smul]

private lemma exactDeficitDot_smul (c : ℝ) (ty : HingeOrbitType)
    (H : Mat4) (m : Wave4) (s : Fin 24) (t : Fin 10) :
    exactDeficitDot ty (c • H) m s t = c * exactDeficitDot ty H m s t := by
  cases ty with
  | t11 =>
      simp [exactDeficitDot, phasedDeficitDotResolvedT11_smul]
  | t12 | t21 | t13 | t31 | t22 =>
      simp [exactDeficitDot, phasedDeficitDotEdgeOrigins_smul]

theorem exactFlatCrossTermSlot_smul (c : ℝ) (ty : HingeOrbitType)
    (H : Mat4) (m : Wave4) (s : Fin 24) (t : Fin 10) :
    exactFlatCrossTermSlot ty (c • H) m s t =
      c ^ 2 * exactFlatCrossTermSlot ty H m s t := by
  unfold exactFlatCrossTermSlot
  split_ifs
  · rw [phasedClassDot_smul, exactDeficitDot_smul]; ring
  · ring

theorem exactFlatCrossTermFold_smul (c : ℝ) (H : Mat4) (m : Wave4) :
    exactFlatCrossTermFold (c • H) m =
      c ^ 2 * exactFlatCrossTermFold H m := by
  unfold exactFlatCrossTermFold exactFlatCrossTermOrbit
  simp_rw [exactFlatCrossTermSlot_smul]
  -- ∑ ty, w_ty * ∑∑ c² f = c² * ∑ ty, w_ty * ∑∑ f
  have hty : ∀ ty : HingeOrbitType,
      (orbitStarSize ty)⁻¹ *
          ∑ s : Fin 24, ∑ t : Fin 10,
            c ^ 2 * exactFlatCrossTermSlot ty H m s t =
        c ^ 2 *
          ((orbitStarSize ty)⁻¹ *
            ∑ s : Fin 24, ∑ t : Fin 10, exactFlatCrossTermSlot ty H m s t) := by
    intro ty
    simp_rw [Finset.mul_sum]
    ring_nf
  simp_rw [hty, ← Finset.mul_sum]

theorem finiteExactReggeSymbol_smul (c : ℝ) (j : ℕ) (m : Fin 4 → ℤ)
    (E : Mat4) :
    finiteExactReggeSymbol j m (c • E) =
      c ^ 2 * finiteExactReggeSymbol j m E := by
  unfold finiteExactReggeSymbol
  exact exactFlatCrossTermFold_smul c E (familyRealMode j m)

theorem discreteExactReggeSymbol_smul (c : ℝ) (j : ℕ) (m : Fin 4 → ℤ)
    (E : Mat4) :
    discreteExactReggeSymbol j m (c • E) =
      c ^ 2 * discreteExactReggeSymbol j m E := by
  unfold discreteExactReggeSymbol
  rw [finiteExactReggeSymbol_smul]
  ring

theorem finiteExactReggeSymbol_zero (j : ℕ) (m : Fin 4 → ℤ) :
    finiteExactReggeSymbol j m 0 = 0 := by
  simpa using finiteExactReggeSymbol_smul (0 : ℝ) j m (1 : Mat4)

/-- At zero wave covector, cosine phases drop and each star-member
resolved deficit equals the ordinary classDot of the pushed assemble. -/
theorem phasedDeficitDotResolvedT11_zeroMomentum (H : Mat4) (x : Wave4)
    (p : Fin 24) :
    phasedDeficitDotResolvedT11 H (fun _ => (0 : ℝ)) x p =
      ∑ μ : Fin 6,
        classDot
          (pushforwardClass
            (ReggeHinge4DStarKernel.assembleStarMember μ) p) H := by
  unfold phasedDeficitDotResolvedT11
  refine Finset.sum_congr rfl fun μ _ => ?_
  simpa using
    phasedClassDot_zeroMomentum
      (pushforwardClass (ReggeHinge4DStarKernel.assembleStarMember μ) p) H
      (fun i =>
        x i + transportOffset p (cubeOffsetT11 (starMemberCubeT11 μ)) i)

theorem phasedDeficitDotResolvedT12_zeroMomentum (H : Mat4) (x : Wave4)
    (p : Fin 24) :
    phasedDeficitDotResolvedT12 H (fun _ => (0 : ℝ)) x p =
      ∑ μ : Fin 4,
        classDot
          (pushforwardClass
            (ReggeHinge4DStarKernel12.assembleStarMember μ) p) H := by
  unfold phasedDeficitDotResolvedT12
  refine Finset.sum_congr rfl fun μ _ => ?_
  simpa using
    phasedClassDot_zeroMomentum
      (pushforwardClass (ReggeHinge4DStarKernel12.assembleStarMember μ) p) H
      (fun i =>
        x i + transportOffset p (cubeOffsetT12 (starMemberCubeT12 μ)) i)

/-! ## §6. Continuum status / honesty -/

/-- Closed: non-`t11` orbits now use per-edge transported origins
(`ReggeBlochStarEdgeOrigins4D`).  Residual e0 isotropy of the fold face
remains OPEN (MEASURED; not this flag). -/
def exact_star_member_offsets_incomplete : Prop := False

theorem exact_star_member_offsets_incomplete_closed :
    exact_star_member_offsets_incomplete = False := rfl

/-- Legacy fold retained for comparison; after `H_fold` it is not the
continuum symbol.  Continuum Props bind to `finiteExactReggeSymbol`. -/
theorem fold_retained_as_legacy_only :
    (blochFoldAllDistinctHinge : Mat4 → Wave4 → ℝ) ≠
      exactFlatCrossTermFold → True := fun _ => trivial

/-- Status package for the exact-action continuum rebind. -/
structure ExactActionSymbolStatus where
  continuumReboundToExact : Bool
  foldRetainedAsLegacy : Bool
  t11t12StarOffsetsDefined : Bool
  otherOrbitOffsetsIncomplete : Bool
  edgeOriginsM2Banked : Bool
  srsInhabited : Bool
  gapActionRecovery : Bool

def exactActionSymbolStatus : ExactActionSymbolStatus where
  continuumReboundToExact := true
  foldRetainedAsLegacy := true
  t11t12StarOffsetsDefined := true
  otherOrbitOffsetsIncomplete := false
  edgeOriginsM2Banked := true
  srsInhabited := false
  gapActionRecovery := false

theorem exactActionSymbolStatus_flags :
    exactActionSymbolStatus.continuumReboundToExact = true ∧
      exactActionSymbolStatus.foldRetainedAsLegacy = true ∧
        exactActionSymbolStatus.t11t12StarOffsetsDefined = true ∧
          exactActionSymbolStatus.otherOrbitOffsetsIncomplete = false ∧
            exactActionSymbolStatus.edgeOriginsM2Banked = true ∧
              exactActionSymbolStatus.srsInhabited = false ∧
                exactActionSymbolStatus.gapActionRecovery = false := by
  decide

/-- Local status flags remain open; geometric ContinuumSymbolIs Tendsto
is the Preflight ledger gate.  Edge-origin m² decide-certs are banked
elsewhere and do not inhabit `S_RS`. -/
theorem exact_action_srs_still_open :
    exactActionSymbolStatus.srsInhabited = false ∧
      exactActionSymbolStatus.gapActionRecovery = false := by
  decide

end

end Regge4DExactActionSymbol
end Analysis
end Gravity
end IndisputableMonolith
