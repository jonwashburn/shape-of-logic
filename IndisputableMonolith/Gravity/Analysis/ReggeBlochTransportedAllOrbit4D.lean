import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochAllOrbitSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochOrbitTransport4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel12
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel13
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel22
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly

/-!
# Transported all-orbit 4D Bloch fold

Continuum-facing multi-orbit fold: each slot transports its orbit's seed
area covector and star deficit kernel by `orbitCoveringPerm` (first `S₄`
cover of `orbitRep ty → (diffMaskA, diffMaskB)`).

**Do not** use `transportPermOfDiff` for non-`(1,1)` orbits
(lesson `L-p1-factorized-vs-transported-fold`; MEASURED all-orbit m²
along `symbolDir` on `axisTTPlus` is `-5/2` raw, not the factorized `0`).

## Status

* THEOREM: definitions; covering-based transport; `(1,1)` recovery of
  `blochFold11` / `slotAreaCov` / `slotDeficitKer` (uniform covering
  pushforward, proved via `slotOrbitAreaCov_t11`); m² `(1,1)` slice
  equals `ReggeBlochM2Symbol4D.m2Symbol`; pushforward reindex
  identities; quadratic homogeneity (`blochFoldAll_smul`); raw
  all-orbit m² eval `-5/2` on `axisTTPlus`/`symbolDir` (sibling
  M2Eval module); distinct-hinge fold weight `1/r_τ` with
  `orbitStarSize` and axis/gauge m² evaluations (sibling M2Eval).
* OPEN: all-orbit m² Tendsto; continuum EH isotropy (residual 3D-style
  `2/N⁴` cell-sum dictionary still required for EH Tendsto).
* Does **not** flip `gap_action_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochTransportedAllOrbit4D

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D
open ReggeBlochM2Symbol4D
open ReggeBlochAllOrbitSymbol4D (isOrbit isOrbit_t11_iff_isT11 phaseScaleDir)
open ReggeBlochOrbitTransport4D
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-! ## §1. Seed kernels and pushforwards -/

/-- Seed star deficit kernel for each orbit type (assembly commitment). -/
def orbitSeedKernel : HingeOrbitType → (Fin 15 → ℝ)
  | .t11 => ReggeHinge4DStarKernel.fullStarClassKernel
  | .t12 => ReggeHinge4DStarKernel12.fullStarClassKernel
  | .t21 => kernel21
  | .t13 => ReggeHinge4DStarKernel13.fullStarClassKernel
  | .t31 => kernel31
  | .t22 => ReggeHinge4DStarKernel22.fullStarClassKernel

theorem orbitSeedKernel_eq_assembly (ty : HingeOrbitType) :
    orbitSeedKernel ty = orbitDeficitKernel ty := by
  cases ty <;> rfl

/-- Pushforward of a class covector by a covering permutation. -/
def pushforwardClass (v : Fin 15 → ℝ) (p : Fin 24) : Fin 15 → ℝ :=
  fun d => ∑ d0 : Fin 15, if permClass p d0 = d then v d0 else 0

def transportedOrbitDeficit (ty : HingeOrbitType) (p : Fin 24) : Fin 15 → ℝ :=
  pushforwardClass (orbitSeedKernel ty) p

def transportedOrbitArea (ty : HingeOrbitType) (p : Fin 24) : Fin 15 → ℝ :=
  pushforwardClass (orbitAreaCov ty) p

def slotOrbitDeficitKer (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) :
    Fin 15 → ℝ :=
  transportedOrbitDeficit ty (orbitCoveringPerm ty s t)

/-- Uniform covering pushforward of the assembly area covector (all orbits). -/
def slotOrbitAreaCov (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) :
    Fin 15 → ℝ :=
  transportedOrbitArea ty (orbitCoveringPerm ty s t)

def transportedOrbitSlotTerm (ty : HingeOrbitType) (H : Mat4)
    (m : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    phasedClassDot (slotOrbitAreaCov ty s t) H m (hingeBase s t) *
      phasedClassDot (slotOrbitDeficitKer ty s t) H m (hingeBase s t)
  else 0

def blochFoldOrbit (ty : HingeOrbitType) (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, transportedOrbitSlotTerm ty H m s t

/-- Full transported multi-orbit Bloch fold (incidence × full-star). -/
def blochFoldAll (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, blochFoldOrbit ty H m

/-! ## §1b. Distinct-hinge fold (geometric weight `1/r_τ`) -/

/-- Geometric star size `r_τ` per orbit type.  Theorem-level in the star
modules / paper table: `(1,1)→6`, `(1,2)→4`, `(2,1)→4`, `(1,3)→6`,
`(3,1)→6`, `(2,2)→4`. -/
def orbitStarSize : HingeOrbitType → ℝ
  | .t11 => 6
  | .t12 => 4
  | .t21 => 4
  | .t13 => 6
  | .t31 => 6
  | .t22 => 4

theorem orbitStarSize_pos (ty : HingeOrbitType) : 0 < orbitStarSize ty := by
  cases ty <;> norm_num [orbitStarSize]

theorem orbitStarSize_ne_zero (ty : HingeOrbitType) : orbitStarSize ty ≠ 0 :=
  ne_of_gt (orbitStarSize_pos ty)

/-- Distinct-hinge continuum fold: true hinge sum wants distinct hinges
with full-star deficit, i.e. weight `1/r_τ` on each orbit fold.
Not bare `blochFoldAll`, and not fitted `2/r`. -/
def blochFoldAllDistinctHinge (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, (orbitStarSize ty)⁻¹ * blochFoldOrbit ty H m

/-! ## §2. Pushforward reindex -/

theorem classDot_pushforward (v : Fin 15 → ℝ) (p : Fin 24) (H : Mat4) :
    classDot (pushforwardClass v p) H =
      ∑ d0 : Fin 15, v d0 * classCoeff H (permClass p d0) := by
  unfold classDot coeffDot pushforwardClass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d0 _ => ?_
  have h : ∀ d : Fin 15,
      (if permClass p d0 = d then v d0 else 0) * classCoeff H d =
        if permClass p d0 = d then v d0 * classCoeff H d else 0 := by
    intro d; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  simp

theorem phasedClassDot_pushforward (v : Fin 15 → ℝ) (p : Fin 24) (H : Mat4)
    (m x : Fin 4 → ℝ) :
    phasedClassDot (pushforwardClass v p) H m x =
      ∑ d0 : Fin 15, v d0 * planeWaveClassPert H m x (permClass p d0) := by
  unfold phasedClassDot pushforwardClass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d0 _ => ?_
  have h : ∀ d : Fin 15,
      (if permClass p d0 = d then v d0 else 0) * planeWaveClassPert H m x d =
        if permClass p d0 = d then
          v d0 * planeWaveClassPert H m x d else 0 := by
    intro d; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  simp

/-! ## §3. (1,1) recovery of `blochFold11` -/

theorem orbitSeedKernel_t11 :
    orbitSeedKernel .t11 = ReggeHinge4DStarKernel.fullStarClassKernel := rfl

theorem transportedOrbitDeficit_t11 (p : Fin 24) :
    transportedOrbitDeficit .t11 p = transportedDeficit p := by
  funext d
  simp [transportedOrbitDeficit, pushforwardClass, transportedDeficit,
    orbitSeedKernel_t11]

theorem slotOrbitDeficitKer_t11 (s : Fin 24) (t : Fin 10) :
    slotOrbitDeficitKer .t11 s t = slotDeficitKer s t := by
  unfold slotOrbitDeficitKer slotDeficitKer
  rw [transportedOrbitDeficit_t11, orbitCoveringPerm_t11_eq_slotTransportPerm]

/-- Integer 4× pushforward of the `(1,1)` seed area covector. -/
def pushAreaZ4 (p : Fin 24) (d : Fin 15) : ℤ :=
  (if d = permClass p 0 then (1 : ℤ) else 0) +
    (if d = permClass p 1 then 1 else 0)

private lemma pushforward_areaCov11_div4 (p : Fin 24) (d : Fin 15) :
    pushforwardClass (orbitAreaCov .t11) p d = (pushAreaZ4 p d : ℝ) / 4 := by
  unfold pushforwardClass pushAreaZ4
  let f : Fin 15 → ℝ := fun d0 =>
    if permClass p d0 = d then orbitAreaCov .t11 d0 else 0
  have hz : ∀ d0 ∈ (Finset.univ : Finset (Fin 15)),
      d0 ∉ ({(0 : Fin 15), 1} : Finset (Fin 15)) → f d0 = 0 := by
    intro d0 _ hd0
    have hne : d0 ≠ 0 ∧ d0 ≠ 1 := by
      constructor <;> intro hx <;> simp [hx] at hd0
    have ha : orbitAreaCov .t11 d0 = 0 := by
      fin_cases d0 <;> simp_all [orbitAreaCov, areaCov11]
    simp [f, ha]
  have hsum :
      (∑ d0 : Fin 15, f d0) =
        ∑ d0 ∈ ({(0 : Fin 15), 1} : Finset (Fin 15)), f d0 := by
    simpa using (Finset.sum_subset (Finset.subset_univ _) hz).symm
  simp only [f] at hsum ⊢
  rw [hsum, Finset.sum_pair (by decide : (0 : Fin 15) ≠ 1)]
  simp [orbitAreaCov, areaCov11, eq_comm]
  split_ifs <;> norm_num

private lemma slotAreaCov_div4 (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    slotAreaCov s t d = (slotAreaCovZ4 s t d : ℝ) / 4 := by
  unfold slotAreaCov slotAreaCovZ4
  split_ifs <;> norm_num

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
private lemma pushAreaZ4_eq_slotAreaCovZ4 (s : Fin 24) (t : Fin 10)
    (h : isT11 s t) (d : Fin 15) :
    pushAreaZ4 (slotTransportPerm s t) d = slotAreaCovZ4 s t d := by
  fin_cases s <;> fin_cases t <;>
    first
    | exfalso; exact absurd h (by decide)
    | fin_cases d <;> decide

/-- On `(1,1)` slots, transported assembly area recovers `slotAreaCov`. -/
theorem slotOrbitAreaCov_t11 (s : Fin 24) (t : Fin 10) (h : isT11 s t) :
    slotOrbitAreaCov .t11 s t = slotAreaCov s t := by
  funext d
  simp only [slotOrbitAreaCov, transportedOrbitArea,
    orbitCoveringPerm_t11_eq_slotTransportPerm]
  rw [pushforward_areaCov11_div4, slotAreaCov_div4,
    pushAreaZ4_eq_slotAreaCovZ4 s t h d]

/-- Compatibility wrapper (audit / older callers): same as `slotOrbitAreaCov_t11`. -/
theorem slotOrbitAreaCov_t11_eq (s : Fin 24) (t : Fin 10) (h : isT11 s t) :
    slotOrbitAreaCov .t11 s t = slotAreaCov s t :=
  slotOrbitAreaCov_t11 s t h

/-- Formerly OPEN Prop naming the `(1,1)` area pushforward identity.
Now inhabited by `AreaPushforwardMatchOpen_holds`. -/
def AreaPushforwardMatchOpen : Prop :=
  ∀ (s : Fin 24) (t : Fin 10), isT11 s t →
    transportedOrbitArea .t11 (orbitCoveringPerm .t11 s t) = slotAreaCov s t

theorem AreaPushforwardMatchOpen_holds : AreaPushforwardMatchOpen := by
  intro s t h
  simpa [slotOrbitAreaCov] using slotOrbitAreaCov_t11 s t h

theorem transportedOrbitSlotTerm_t11 (H : Mat4) (m : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) :
    transportedOrbitSlotTerm .t11 H m s t = transportedSlotTerm H m s t := by
  unfold transportedOrbitSlotTerm transportedSlotTerm
  by_cases h : isOrbit .t11 s t
  · have ht : isT11 s t := (isOrbit_t11_iff_isT11 s t).mp h
    simp [h, ht, slotOrbitAreaCov_t11 s t ht, slotOrbitDeficitKer_t11]
  · have ht : ¬ isT11 s t := fun ht =>
      h ((isOrbit_t11_iff_isT11 s t).mpr ht)
    simp [h, ht]

theorem blochFoldOrbit_t11 (H : Mat4) (m : Fin 4 → ℝ) :
    blochFoldOrbit .t11 H m = blochFold11 H m := by
  unfold blochFoldOrbit blochFold11
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
    transportedOrbitSlotTerm_t11 H m s t

/-! ## §4. Zero-momentum phase drop -/

theorem transportedOrbitSlotTerm_zeroMomentum (ty : HingeOrbitType)
    (H : Mat4) (s : Fin 24) (t : Fin 10) :
    transportedOrbitSlotTerm ty H (fun _ => (0 : ℝ)) s t =
      if isOrbit ty s t then
        classDot (slotOrbitAreaCov ty s t) H *
          classDot (slotOrbitDeficitKer ty s t) H
      else 0 := by
  unfold transportedOrbitSlotTerm
  by_cases h : isOrbit ty s t <;> simp [h, phasedClassDot_zeroMomentum]

/-- OPEN: transported zero-momentum all-orbit fold equals the committed
true-weight assembly quadratic for general `H`.  Reindex gives
`classDot (push v p) H = ∑ v d0 * classCoeff H (permClass p d0)`, which
equals `classDot v H` only under class-coeff invariance along `p`, not in
general.  Banked separately from the m² continuum symbol. -/
def ZeroMomTrueWeightMatchOpen : Prop :=
  ∀ H : Mat4, blochFoldAll H (fun _ => (0 : ℝ)) = trueWeightZeroMomQuadratic H

/-! ## §4b. Quadratic homogeneity (polarization scaling) -/

theorem transportedOrbitSlotTerm_smul (ty : HingeOrbitType) (c : ℝ)
    (H : Mat4) (m : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    transportedOrbitSlotTerm ty (c • H) m s t =
      c ^ 2 * transportedOrbitSlotTerm ty H m s t := by
  unfold transportedOrbitSlotTerm
  by_cases h : isOrbit ty s t
  · simp only [h, ite_true]
    rw [phasedClassDot_smul, phasedClassDot_smul]
    ring
  · simp [h]

theorem blochFoldOrbit_smul (ty : HingeOrbitType) (c : ℝ) (H : Mat4)
    (m : Fin 4 → ℝ) :
    blochFoldOrbit ty (c • H) m = c ^ 2 * blochFoldOrbit ty H m := by
  unfold blochFoldOrbit
  simp_rw [transportedOrbitSlotTerm_smul, ← Finset.mul_sum]

theorem blochFoldAll_smul (c : ℝ) (H : Mat4) (m : Fin 4 → ℝ) :
    blochFoldAll (c • H) m = c ^ 2 * blochFoldAll H m := by
  unfold blochFoldAll
  simp_rw [blochFoldOrbit_smul, ← Finset.mul_sum]

theorem blochFoldAll_zero (m : Fin 4 → ℝ) : blochFoldAll 0 m = 0 := by
  have h := blochFoldAll_smul (0 : ℝ) (1 : Mat4) m
  simpa using h

theorem blochFoldAllDistinctHinge_smul (c : ℝ) (H : Mat4) (m : Fin 4 → ℝ) :
    blochFoldAllDistinctHinge (c • H) m =
      c ^ 2 * blochFoldAllDistinctHinge H m := by
  unfold blochFoldAllDistinctHinge
  simp_rw [blochFoldOrbit_smul]
  have hterm : ∀ ty : HingeOrbitType,
      (orbitStarSize ty)⁻¹ * (c ^ 2 * blochFoldOrbit ty H m) =
        c ^ 2 * ((orbitStarSize ty)⁻¹ * blochFoldOrbit ty H m) := by
    intro ty; ring
  simp_rw [hterm, ← Finset.mul_sum]

theorem blochFoldAllDistinctHinge_zero (m : Fin 4 → ℝ) :
    blochFoldAllDistinctHinge 0 m = 0 := by
  have h := blochFoldAllDistinctHinge_smul (0 : ℝ) (1 : Mat4) m
  simpa using h

/-! ## §5. Transported m² moment polynomials -/

/-- Zero-momentum (unphased) transported deficit · classCoeff at a slot. -/
def slotOrbitKerDot (ty : HingeOrbitType) (H : Mat4) (s : Fin 24)
    (t : Fin 10) : ℝ :=
  ∑ d : Fin 15, slotOrbitDeficitKer ty s t d * classCoeff H d

/-- Truncated cosine two-jet slot coefficient `A0*K2`, i.e. the historical
form that assumes slotwise `K0 = 0` (deficit annihilation at μ = 0). -/
def m2TransportedOrbitSlotCoeffTrunc (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    (∑ d : Fin 15, slotOrbitAreaCov ty s t d * classCoeff H d) *
      (-(1 / 2 : ℝ) *
        ∑ d : Fin 15,
          slotOrbitDeficitKer ty s t d * classCoeff H d *
            (phaseScaleDir dir (hingeBase s t) d) ^ 2)
  else 0

/-- Full cosine two-jet of the phased product `A(μ)K(μ)`:
`A0*K2 + A2*K0` with `A2 = -½ Aph²` and `K2 = -½ Kph²`.
Equals the truncated form whenever `slotOrbitKerDot = 0`. -/
def m2TransportedOrbitSlotCoeffFull (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    (∑ d : Fin 15, slotOrbitAreaCov ty s t d * classCoeff H d) *
        (-(1 / 2 : ℝ) *
          ∑ d : Fin 15,
            slotOrbitDeficitKer ty s t d * classCoeff H d *
              (phaseScaleDir dir (hingeBase s t) d) ^ 2) +
      (-(1 / 2 : ℝ) *
          ∑ d : Fin 15,
            slotOrbitAreaCov ty s t d * classCoeff H d *
              (phaseScaleDir dir (hingeBase s t) d) ^ 2) *
        slotOrbitKerDot ty H s t
  else 0

theorem m2TransportedOrbitSlotCoeffFull_eq_trunc_of_ker0
    (ty : HingeOrbitType) (H : Mat4) (dir : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) (hK0 : slotOrbitKerDot ty H s t = 0) :
    m2TransportedOrbitSlotCoeffFull ty H dir s t =
      m2TransportedOrbitSlotCoeffTrunc ty H dir s t := by
  unfold m2TransportedOrbitSlotCoeffFull m2TransportedOrbitSlotCoeffTrunc
  by_cases h : isOrbit ty s t
  · rw [if_pos h, if_pos h, hK0]
    ring
  · rw [if_neg h, if_neg h]

/-- Canonical transported m² slot coefficient: truncated `A0*K2` form used by
the integer certificates.  The honest product two-jet is
`m2TransportedOrbitSlotCoeffFull = A0*K2 + A2*K0`; on TT plus/cross the
two agree slotwise (`K0 = 0`, THEOREM
`slotOrbitKerDot_axisTTPlus` / `slotOrbitKerDot_axisTTCross` in
`ReggeBlochTransportedAllOrbitM2Eval4D`; probe
`scripts/probe_m2_full_twojet_e0.py`). -/
abbrev m2TransportedOrbitSlotCoeff := m2TransportedOrbitSlotCoeffTrunc

def m2TransportedOrbitMoment (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, m2TransportedOrbitSlotCoeff ty H dir s t

def m2TransportedAllOrbitMoment (H : Mat4) (dir : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, m2TransportedOrbitMoment ty H dir

/-- Distinct-hinge m² moment: weight `1/r_τ` on each orbit moment. -/
def m2TransportedAllOrbitMomentDistinctHinge (H : Mat4)
    (dir : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType,
    (orbitStarSize ty)⁻¹ * m2TransportedOrbitMoment ty H dir

/-- Full-jet orbit / distinct-hinge aggregates. -/
def m2TransportedOrbitMomentFull (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, m2TransportedOrbitSlotCoeffFull ty H dir s t

def m2TransportedAllOrbitMomentDistinctHingeFull (H : Mat4)
    (dir : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType,
    (orbitStarSize ty)⁻¹ * m2TransportedOrbitMomentFull ty H dir

private lemma sum_mul_classCoeff_smul (c : ℝ) (H : Mat4) (f : Fin 15 → ℝ) :
    (∑ d : Fin 15, f d * classCoeff (c • H) d) =
      c * ∑ d : Fin 15, f d * classCoeff H d := by
  simp_rw [classCoeff_smul]
  have hterm : ∀ d : Fin 15, f d * (c * classCoeff H d) = c * (f d * classCoeff H d) := by
    intro d; ring
  simp_rw [hterm, ← Finset.mul_sum]

private lemma sum_mul_classCoeff_phase_smul (c : ℝ) (H : Mat4)
    (f g : Fin 15 → ℝ) :
    (∑ d : Fin 15, f d * classCoeff (c • H) d * g d) =
      c * ∑ d : Fin 15, f d * classCoeff H d * g d := by
  simp_rw [classCoeff_smul]
  have hterm : ∀ d : Fin 15,
      f d * (c * classCoeff H d) * g d = c * (f d * classCoeff H d * g d) := by
    intro d; ring
  simp_rw [hterm, ← Finset.mul_sum]

theorem m2TransportedOrbitSlotCoeffTrunc_smul (ty : HingeOrbitType) (c : ℝ)
    (H : Mat4) (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeffTrunc ty (c • H) dir s t =
      c ^ 2 * m2TransportedOrbitSlotCoeffTrunc ty H dir s t := by
  unfold m2TransportedOrbitSlotCoeffTrunc
  by_cases h : isOrbit ty s t
  · simp only [h, ite_true]
    rw [sum_mul_classCoeff_smul c H (slotOrbitAreaCov ty s t)]
    rw [sum_mul_classCoeff_phase_smul c H (slotOrbitDeficitKer ty s t)
      (fun d => (phaseScaleDir dir (hingeBase s t) d) ^ 2)]
    ring
  · simp only [h, ↓reduceIte, mul_zero]

theorem m2TransportedOrbitSlotCoeff_smul (ty : HingeOrbitType) (c : ℝ)
    (H : Mat4) (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff ty (c • H) dir s t =
      c ^ 2 * m2TransportedOrbitSlotCoeff ty H dir s t :=
  m2TransportedOrbitSlotCoeffTrunc_smul ty c H dir s t

theorem m2TransportedOrbitSlotCoeffFull_smul (ty : HingeOrbitType) (c : ℝ)
    (H : Mat4) (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeffFull ty (c • H) dir s t =
      c ^ 2 * m2TransportedOrbitSlotCoeffFull ty H dir s t := by
  unfold m2TransportedOrbitSlotCoeffFull slotOrbitKerDot
  by_cases h : isOrbit ty s t
  · simp only [h, ite_true]
    rw [sum_mul_classCoeff_smul c H (slotOrbitAreaCov ty s t)]
    rw [sum_mul_classCoeff_phase_smul c H (slotOrbitDeficitKer ty s t)
      (fun d => (phaseScaleDir dir (hingeBase s t) d) ^ 2)]
    rw [sum_mul_classCoeff_phase_smul c H (slotOrbitAreaCov ty s t)
      (fun d => (phaseScaleDir dir (hingeBase s t) d) ^ 2)]
    rw [sum_mul_classCoeff_smul c H (slotOrbitDeficitKer ty s t)]
    ring
  · simp only [h, ↓reduceIte, mul_zero]

theorem m2TransportedOrbitMoment_smul (ty : HingeOrbitType) (c : ℝ)
    (H : Mat4) (dir : Fin 4 → ℝ) :
    m2TransportedOrbitMoment ty (c • H) dir =
      c ^ 2 * m2TransportedOrbitMoment ty H dir := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_smul, ← Finset.mul_sum]

theorem m2TransportedAllOrbitMomentDistinctHinge_smul (c : ℝ) (H : Mat4)
    (dir : Fin 4 → ℝ) :
    m2TransportedAllOrbitMomentDistinctHinge (c • H) dir =
      c ^ 2 * m2TransportedAllOrbitMomentDistinctHinge H dir := by
  unfold m2TransportedAllOrbitMomentDistinctHinge
  simp_rw [m2TransportedOrbitMoment_smul]
  have hterm : ∀ ty : HingeOrbitType,
      (orbitStarSize ty)⁻¹ * (c ^ 2 * m2TransportedOrbitMoment ty H dir) =
        c ^ 2 * ((orbitStarSize ty)⁻¹ * m2TransportedOrbitMoment ty H dir) := by
    intro ty; ring
  simp_rw [hterm, ← Finset.mul_sum]

theorem m2TransportedOrbitMomentFull_smul (ty : HingeOrbitType) (c : ℝ)
    (H : Mat4) (dir : Fin 4 → ℝ) :
    m2TransportedOrbitMomentFull ty (c • H) dir =
      c ^ 2 * m2TransportedOrbitMomentFull ty H dir := by
  unfold m2TransportedOrbitMomentFull
  simp_rw [m2TransportedOrbitSlotCoeffFull_smul, ← Finset.mul_sum]

theorem m2TransportedAllOrbitMomentDistinctHingeFull_smul (c : ℝ) (H : Mat4)
    (dir : Fin 4 → ℝ) :
    m2TransportedAllOrbitMomentDistinctHingeFull (c • H) dir =
      c ^ 2 * m2TransportedAllOrbitMomentDistinctHingeFull H dir := by
  unfold m2TransportedAllOrbitMomentDistinctHingeFull
  simp_rw [m2TransportedOrbitMomentFull_smul]
  have hterm : ∀ ty : HingeOrbitType,
      (orbitStarSize ty)⁻¹ * (c ^ 2 * m2TransportedOrbitMomentFull ty H dir) =
        c ^ 2 * ((orbitStarSize ty)⁻¹ * m2TransportedOrbitMomentFull ty H dir) := by
    intro ty; ring
  simp_rw [hterm, ← Finset.mul_sum]

theorem phaseScaleDir_symbolDir (x : Fin 4 → ℝ) (d : Fin 15) :
    phaseScaleDir symbolDir x d = phaseScale x d := by
  rfl

theorem m2TransportedOrbitSlotCoeff_t11 (H : Mat4) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t11 H symbolDir s t = m2SlotCoeff H s t := by
  change m2TransportedOrbitSlotCoeffTrunc .t11 H symbolDir s t = m2SlotCoeff H s t
  unfold m2TransportedOrbitSlotCoeffTrunc m2SlotCoeff
  by_cases h : isOrbit .t11 s t
  · have ht : isT11 s t := (isOrbit_t11_iff_isT11 s t).mp h
    rw [if_pos h, if_pos ht, slotOrbitAreaCov_t11 s t ht, slotOrbitDeficitKer_t11]
    simp_rw [phaseScaleDir_symbolDir]
  · have ht : ¬ isT11 s t := fun ht =>
      h ((isOrbit_t11_iff_isT11 s t).mpr ht)
    rw [if_neg h, if_neg ht]

theorem m2TransportedOrbitMoment_t11 (H : Mat4) :
    m2TransportedOrbitMoment .t11 H symbolDir = m2Symbol H := by
  unfold m2TransportedOrbitMoment m2Symbol
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
    m2TransportedOrbitSlotCoeff_t11 H s t

/-- Formerly OPEN: raw all-orbit moment on axisTTPlus / symbolDir equals `-5/2`
(orbit slices t11=-3, t12=+2, t13=-3/2).  After `/|symbolDir|²` this is
`-5/4`.  Closed in `ReggeBlochTransportedAllOrbitM2Eval4D`.
Distinct-hinge weight `1/r_τ` upgrades the raw axis value to `-1/4`
(path A; residual continuum dictionary still needed for EH Tendsto). -/
def M2TransportedAllOrbitAxisSymbolDirEvalOpen : Prop :=
  m2TransportedAllOrbitMoment axisTTPlus symbolDir = (-5 / 2 : ℝ)

/-- Distinct-hinge raw m² on axisTTPlus / symbolDir equals frozen EH `-1/4`
(`-3/6 + 2/4 + (-3/2)/6`).  Closed in M2Eval. -/
def M2DistinctHingeAxisSymbolDirEvalOpen : Prop :=
  m2TransportedAllOrbitMomentDistinctHinge axisTTPlus symbolDir =
    (-1 / 4 : ℝ)

/-! ## §6. Status -/

structure ReggeBlochTransportedAllOrbit4DStatus where
  definitionsClosed : Bool
  t11MatchClosed : Bool
  m2T11SliceClosed : Bool
  m2AllOrbitAxisEvalClosed : Bool
  distinctHingeAxisEvalClosed : Bool
  m2TendstoClosed : Bool
  continuumEHClosed : Bool
  gapActionRecovery : Bool

def reggeBlochTransportedAllOrbit4DStatus :
    ReggeBlochTransportedAllOrbit4DStatus where
  definitionsClosed := true
  t11MatchClosed := true
  m2T11SliceClosed := true
  m2AllOrbitAxisEvalClosed := true
  distinctHingeAxisEvalClosed := true
  m2TendstoClosed := false
  continuumEHClosed := false
  gapActionRecovery := false

theorem reggeBlochTransportedAllOrbit4DStatus_flags :
    reggeBlochTransportedAllOrbit4DStatus.definitionsClosed = true ∧
      reggeBlochTransportedAllOrbit4DStatus.t11MatchClosed = true ∧
        reggeBlochTransportedAllOrbit4DStatus.m2T11SliceClosed = true ∧
          reggeBlochTransportedAllOrbit4DStatus.m2AllOrbitAxisEvalClosed =
            true ∧
            reggeBlochTransportedAllOrbit4DStatus.distinctHingeAxisEvalClosed =
              true ∧
              reggeBlochTransportedAllOrbit4DStatus.m2TendstoClosed = false ∧
                reggeBlochTransportedAllOrbit4DStatus.continuumEHClosed =
                  false ∧
                  reggeBlochTransportedAllOrbit4DStatus.gapActionRecovery =
                    false := by
  decide

end

end ReggeBlochTransportedAllOrbit4D
end Analysis
end Gravity
end IndisputableMonolith
