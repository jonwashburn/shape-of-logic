import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochAllOrbitSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochOrbitTransport4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel

/-!
# Path B: 3D-style local-incidence kernels (4D continuum)

Missing-factor blocker path B.  Two layers:

1. **Mean-local (vacuous).** `K_local = K_star / r_τ` at each slot.
   Equals Path A distinct-hinge by linearity of class-dot / pushforward.
2. **Position-resolved (non-vacuous).** Expand the star as
   `Σ_m assembleStarMember m` evaluated at cube-translate bases
   `hingeBase + perm(offset_m)`, then weight `1/r_τ`.

MEASURED (Python receipt
`state/qg_full_theory/probe_pathB_local_incidence_20260721.json`):
position-resolved t11 agrees with distinct-hinge on tested TT rays;
extending to t12 breaks symbolDir plus/cross agreement and does not hit
EH `-1/4`.  No `gap_action_recovery` flip.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochLocalIncidence4D

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochAllOrbitSymbol4D (isOrbit phaseScaleDir)
open ReggeBlochOrbitTransport4D
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochFold4D
open EdgeTTDecomposition4D
open ReggeHinge4DStarKernel (CubeTranslate)

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-! ## §1. Vacuous mean-local Path B (= distinct-hinge) -/

/-- Mean of the `r_τ` star-member local deficit kernels (= full-star / `r_τ`). -/
def orbitMeanLocalKernel (ty : HingeOrbitType) : Fin 15 → ℝ :=
  fun d => (orbitStarSize ty)⁻¹ * orbitSeedKernel ty d

theorem orbitMeanLocalKernel_t11 (d : Fin 15) :
    orbitMeanLocalKernel .t11 d =
      (6 : ℝ)⁻¹ * ReggeHinge4DStarKernel.fullStarClassKernel d :=
  rfl

theorem orbitMeanLocalKernel_t11_eq_assembled_mean (d : Fin 15) :
    orbitMeanLocalKernel .t11 d =
      (6 : ℝ)⁻¹ * ReggeHinge4DStarKernel.fullStarClassKernelAssembled d := by
  rw [orbitMeanLocalKernel_t11, ReggeHinge4DStarKernel.fullStarClassKernel_eq]

theorem orbitMeanLocalKernel_smul_star (ty : HingeOrbitType) (d : Fin 15) :
    orbitStarSize ty * orbitMeanLocalKernel ty d = orbitSeedKernel ty d := by
  unfold orbitMeanLocalKernel
  field_simp [orbitStarSize_ne_zero ty]

def transportedOrbitMeanLocal (ty : HingeOrbitType) (p : Fin 24) : Fin 15 → ℝ :=
  pushforwardClass (orbitMeanLocalKernel ty) p

def slotOrbitMeanLocalKer (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) :
    Fin 15 → ℝ :=
  transportedOrbitMeanLocal ty (orbitCoveringPerm ty s t)

theorem slotOrbitMeanLocalKer_eq_scaled (ty : HingeOrbitType)
    (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    slotOrbitMeanLocalKer ty s t d =
      (orbitStarSize ty)⁻¹ * slotOrbitDeficitKer ty s t d := by
  unfold slotOrbitMeanLocalKer transportedOrbitMeanLocal
    slotOrbitDeficitKer transportedOrbitDeficit pushforwardClass
    orbitMeanLocalKernel
  have h : ∀ d0 : Fin 15,
      (if permClass (orbitCoveringPerm ty s t) d0 = d then
          (orbitStarSize ty)⁻¹ * orbitSeedKernel ty d0 else 0) =
        (orbitStarSize ty)⁻¹ *
          (if permClass (orbitCoveringPerm ty s t) d0 = d then
            orbitSeedKernel ty d0 else 0) := by
    intro d0; split_ifs <;> ring
  simp_rw [h, ← Finset.mul_sum]

def meanLocalSlotTerm (ty : HingeOrbitType) (H : Mat4) (m : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    phasedClassDot (slotOrbitAreaCov ty s t) H m (hingeBase s t) *
      phasedClassDot (slotOrbitMeanLocalKer ty s t) H m (hingeBase s t)
  else 0

theorem meanLocalSlotTerm_eq_scaled (ty : HingeOrbitType) (H : Mat4)
    (m : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    meanLocalSlotTerm ty H m s t =
      (orbitStarSize ty)⁻¹ * transportedOrbitSlotTerm ty H m s t := by
  unfold meanLocalSlotTerm transportedOrbitSlotTerm
  by_cases h : isOrbit ty s t
  · simp only [h, ite_true]
    have hker :
        phasedClassDot (slotOrbitMeanLocalKer ty s t) H m (hingeBase s t) =
          (orbitStarSize ty)⁻¹ *
            phasedClassDot (slotOrbitDeficitKer ty s t) H m
              (hingeBase s t) := by
      unfold phasedClassDot
      have hpt : ∀ d : Fin 15,
          slotOrbitMeanLocalKer ty s t d *
              planeWaveClassPert H m (hingeBase s t) d =
            (orbitStarSize ty)⁻¹ *
              (slotOrbitDeficitKer ty s t d *
                planeWaveClassPert H m (hingeBase s t) d) := by
        intro d
        rw [slotOrbitMeanLocalKer_eq_scaled]
        ring
      simp_rw [hpt, ← Finset.mul_sum]
    rw [hker]
    ring
  · simp [h]

def blochFoldOrbitMeanLocal (ty : HingeOrbitType) (H : Mat4)
    (m : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, meanLocalSlotTerm ty H m s t

theorem blochFoldOrbitMeanLocal_eq_scaled (ty : HingeOrbitType) (H : Mat4)
    (m : Fin 4 → ℝ) :
    blochFoldOrbitMeanLocal ty H m =
      (orbitStarSize ty)⁻¹ * blochFoldOrbit ty H m := by
  unfold blochFoldOrbitMeanLocal blochFoldOrbit
  simp_rw [meanLocalSlotTerm_eq_scaled, ← Finset.mul_sum]

/-- Vacuous Path B fold (= distinct-hinge). -/
def blochFoldAllMeanLocal (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, blochFoldOrbitMeanLocal ty H m

theorem blochFoldAllMeanLocal_eq_distinctHinge (H : Mat4) (m : Fin 4 → ℝ) :
    blochFoldAllMeanLocal H m = blochFoldAllDistinctHinge H m := by
  unfold blochFoldAllMeanLocal blochFoldAllDistinctHinge
  refine Finset.sum_congr rfl fun ty _ =>
    blochFoldOrbitMeanLocal_eq_scaled ty H m

/-! ## §2. Mean-local m² -/

def m2MeanLocalOrbitSlotCoeff (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    (∑ d : Fin 15, slotOrbitAreaCov ty s t d * classCoeff H d) *
      (-(1 / 2 : ℝ) *
        ∑ d : Fin 15,
          slotOrbitMeanLocalKer ty s t d * classCoeff H d *
            (phaseScaleDir dir (hingeBase s t) d) ^ 2)
  else 0

theorem m2MeanLocalOrbitSlotCoeff_eq_scaled (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    m2MeanLocalOrbitSlotCoeff ty H dir s t =
      (orbitStarSize ty)⁻¹ * m2TransportedOrbitSlotCoeff ty H dir s t := by
  change m2MeanLocalOrbitSlotCoeff ty H dir s t =
    (orbitStarSize ty)⁻¹ * m2TransportedOrbitSlotCoeffTrunc ty H dir s t
  unfold m2MeanLocalOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
  by_cases h : isOrbit ty s t
  · simp only [h, ↓reduceIte]
    have hsum :
        (∑ d : Fin 15,
            slotOrbitMeanLocalKer ty s t d * classCoeff H d *
              (phaseScaleDir dir (hingeBase s t) d) ^ 2) =
          (orbitStarSize ty)⁻¹ *
            ∑ d : Fin 15,
              slotOrbitDeficitKer ty s t d * classCoeff H d *
                (phaseScaleDir dir (hingeBase s t) d) ^ 2 := by
      have hpt : ∀ d : Fin 15,
          slotOrbitMeanLocalKer ty s t d * classCoeff H d *
              (phaseScaleDir dir (hingeBase s t) d) ^ 2 =
            (orbitStarSize ty)⁻¹ *
              (slotOrbitDeficitKer ty s t d * classCoeff H d *
                (phaseScaleDir dir (hingeBase s t) d) ^ 2) := by
        intro d
        rw [slotOrbitMeanLocalKer_eq_scaled]
        ring
      simp_rw [hpt, ← Finset.mul_sum]
    rw [hsum]
    ring
  · simp only [h, ↓reduceIte, mul_zero]

def m2MeanLocalOrbitMoment (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, m2MeanLocalOrbitSlotCoeff ty H dir s t

theorem m2MeanLocalOrbitMoment_eq_scaled (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) :
    m2MeanLocalOrbitMoment ty H dir =
      (orbitStarSize ty)⁻¹ * m2TransportedOrbitMoment ty H dir := by
  unfold m2MeanLocalOrbitMoment m2TransportedOrbitMoment
  simp_rw [m2MeanLocalOrbitSlotCoeff_eq_scaled, ← Finset.mul_sum]

def m2MeanLocalAllOrbitMoment (H : Mat4) (dir : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, m2MeanLocalOrbitMoment ty H dir

theorem m2MeanLocalAllOrbitMoment_eq_distinctHinge (H : Mat4)
    (dir : Fin 4 → ℝ) :
    m2MeanLocalAllOrbitMoment H dir =
      m2TransportedAllOrbitMomentDistinctHinge H dir := by
  unfold m2MeanLocalAllOrbitMoment m2TransportedAllOrbitMomentDistinctHinge
  refine Finset.sum_congr rfl fun ty _ =>
    m2MeanLocalOrbitMoment_eq_scaled ty H dir

theorem m2MeanLocalAllOrbitMoment_smul (c : ℝ) (H : Mat4) (dir : Fin 4 → ℝ) :
    m2MeanLocalAllOrbitMoment (c • H) dir =
      c ^ 2 * m2MeanLocalAllOrbitMoment H dir := by
  rw [m2MeanLocalAllOrbitMoment_eq_distinctHinge,
    m2TransportedAllOrbitMomentDistinctHinge_smul,
    m2MeanLocalAllOrbitMoment_eq_distinctHinge]

/-! ## §3. Position-resolved Path B (t11 seed geometry) -/

/-- Cube translate of a `(1,1)` star member as an ℝ⁴ lattice offset. -/
def cubeTranslateOffset : CubeTranslate → (Fin 4 → ℝ)
  | .origin => fun _ => 0
  | .minusE2 => fun i => if i = 2 then (-1 : ℝ) else 0
  | .minusE3 => fun i => if i = 3 then (-1 : ℝ) else 0
  | .minusE2E3 => fun i =>
      if i = 2 then (-1 : ℝ) else if i = 3 then (-1 : ℝ) else 0

/-- Seed-frame offsets for the six `(1,1)` star members, in
`starMembers` / `assembleStarMember` order. -/
def t11MemberOffset : Fin 6 → (Fin 4 → ℝ)
  | 0 | 1 => cubeTranslateOffset .origin
  | 2 => cubeTranslateOffset .minusE2
  | 3 => cubeTranslateOffset .minusE3
  | 4 | 5 => cubeTranslateOffset .minusE2E3

def addBase (x δ : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => x i + δ i

/-- Pushforward of one `(1,1)` star-member local kernel. -/
def transportedT11Member (m : Fin 6) (p : Fin 24) : Fin 15 → ℝ :=
  pushforwardClass (ReggeHinge4DStarKernel.assembleStarMember m) p

/-- Apply covering perm as an axis permutation of a seed-frame offset.
`coordPermOf p` maps seed axis `i` to world axis `(coordPermOf p) i`. -/
def permOffset (p : Fin 24) (δ : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun j => ∑ i : Fin 4, if coordPermOf p i = j then δ i else 0

/-- Position-resolved deficit phased class-dot for type `(1,1)`:
`Σ_m K_m` at `base + perm(offset_m)`. -/
def phasedT11PositionResolved (H : Mat4) (mvec : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  let p := orbitCoveringPerm .t11 s t
  let base := hingeBase s t
  ∑ mem : Fin 6,
    phasedClassDot (transportedT11Member mem p) H mvec
      (addBase base (permOffset p (t11MemberOffset mem)))

/-- Position-resolved t11 slot term (area at hinge base). -/
def t11PositionResolvedSlotTerm (H : Mat4) (mvec : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit .t11 s t then
    phasedClassDot (slotOrbitAreaCov .t11 s t) H mvec (hingeBase s t) *
      phasedT11PositionResolved H mvec s t
  else 0

/-- Star assembly identity: Σ_m assembleStarMember = fullStar. -/
theorem t11_member_sum_eq_fullStar (d : Fin 15) :
    (∑ mem : Fin 6, ReggeHinge4DStarKernel.assembleStarMember mem d) =
      ReggeHinge4DStarKernel.fullStarClassKernel d := by
  simpa [ReggeHinge4DStarKernel.fullStarClassKernelAssembled] using
    ReggeHinge4DStarKernel.fullStarClassKernel_eq d

/-! ## §4. Status / OPEN obligations -/

/-- **OPEN**: all-orbit position-resolved Path B equals (or repairs) the
distinct-hinge continuum TT symbol.  MEASURED counterexample on t12
cross (receipt): symbolDir plus/cross agreement breaks; EH face not hit. -/
def Regge4DPathBPositionResolvedClosesEH : Prop :=
  False

theorem Regge4DPathBPositionResolvedClosesEH_status_open :
    Regge4DPathBPositionResolvedClosesEH = False :=
  rfl

/-- Vacuous mean-local Path B cannot repair e0 anisotropy / factor 4,
because it equals distinct-hinge. -/
theorem meanLocal_inherits_distinctHinge_on_any (H : Mat4)
    (dir : Fin 4 → ℝ) :
    m2MeanLocalAllOrbitMoment H dir =
      m2TransportedAllOrbitMomentDistinctHinge H dir :=
  m2MeanLocalAllOrbitMoment_eq_distinctHinge H dir

structure ReggeBlochLocalIncidence4DStatus where
  meanLocalEqualsDistinctHinge : Bool
  positionResolvedT11Defined : Bool
  pathBClosesEH : Bool
  gapActionRecovery : Bool

def reggeBlochLocalIncidence4DStatus : ReggeBlochLocalIncidence4DStatus where
  meanLocalEqualsDistinctHinge := true
  positionResolvedT11Defined := true
  pathBClosesEH := false
  gapActionRecovery := false

theorem reggeBlochLocalIncidence4DStatus_flags :
    reggeBlochLocalIncidence4DStatus.meanLocalEqualsDistinctHinge = true ∧
      reggeBlochLocalIncidence4DStatus.positionResolvedT11Defined = true ∧
        reggeBlochLocalIncidence4DStatus.pathBClosesEH = false ∧
          reggeBlochLocalIncidence4DStatus.gapActionRecovery = false := by
  decide

theorem does_not_flip_gap_action_recovery :
    reggeBlochLocalIncidence4DStatus.gapActionRecovery = false :=
  rfl

end

end ReggeBlochLocalIncidence4D
end Analysis
end Gravity
end IndisputableMonolith
