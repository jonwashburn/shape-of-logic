import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel12
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel13
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel22

/-!
# Regge 4D Bloch symbol: all-orbit factorized fold and m² moment

Generic orbit-indexed fold over the six S4 hinge types
`(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)`, `(2,2)` (four orbits under
S4+complement), consuming the committed Heron area covectors and deficit
kernels from `ReggeFlat4DHessianAssembly`.

## Tier tags (binding)

* THEOREM: orbit-count identity, zero-momentum reductions, evenness of
  the ray fold, complement kernel identities, status/decoy flags.
* DEFINITION: finite-momentum all-orbit fold and all-orbit m² moment
  polynomial (cosine two-jet formal coefficient).
* OPEN (named `Prop`, status `false`): arbitrary-direction cosine
  two-jet Tendsto per orbit and for the all-orbit sum.
* Scope: factorized (orbit-constant) kernels. Does **not** replace the
  transported `(1,1)` fold of `ReggeBlochFold4D`.
* Does **not** prove continuum Einstein–Hilbert recovery.
* Does **not** flip `gap_action_recovery`.
* Decoy: one-orbit symbol ≠ continuum target.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochAllOrbitSymbol4D

open BigOperators Filter Topology
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D

noncomputable section

/-! ## §1. Orbit predicate and proved slot counts -/

/-- Slot belongs to lattice orbit type `ty`. -/
def isOrbit (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) : Prop :=
  hingeOrbitType s t = ty

instance (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) :
    Decidable (isOrbit ty s t) :=
  inferInstanceAs (Decidable (hingeOrbitType s t = ty))

theorem isOrbit_iff_pop (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) :
    isOrbit ty s t ↔ hingeTypePop s t = ty.toPop := by
  constructor
  · intro h
    have hpop := hingeOrbitType_toPop s t
    simp only [isOrbit] at h
    rw [h] at hpop
    exact hpop.symm
  · intro h
    simp only [isOrbit, hingeOrbitType]
    rw [h]
    cases ty <;> rfl

theorem isOrbit_t11_iff_isT11 (s : Fin 24) (t : Fin 10) :
    isOrbit .t11 s t ↔ isT11 s t := by
  simp [isOrbit, isT11]

/-- Oriented slot count for each orbit type equals the committed cell count. -/
theorem orbit_slot_count_nat (ty : HingeOrbitType) :
    (∑ s : Fin 24, ∑ t : Fin 10, (if isOrbit ty s t then (1 : ℕ) else 0)) =
      orbitCellCount ty := by
  rw [orbitCellCount_eq_classification]
  unfold cellTriangleCount triangleTypeNat
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases h : isOrbit ty s t
  · have hp : hingeTypePop s t = ty.toPop := (isOrbit_iff_pop ty s t).mp h
    simp [h, hp]
  · have : hingeTypePop s t ≠ ty.toPop := fun happ =>
      h ((isOrbit_iff_pop ty s t).mpr happ)
    simp [h, this]

theorem orbit_slot_count_real (ty : HingeOrbitType) :
    (∑ s : Fin 24, ∑ t : Fin 10, (if isOrbit ty s t then (1 : ℝ) else 0)) =
      (orbitCellCount ty : ℝ) := by
  have := congrArg (fun n : ℕ => (n : ℝ)) (orbit_slot_count_nat ty)
  refine Eq.trans ?_ this
  simp_rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases h : isOrbit ty s t <;> simp [h]

/-- Complement pairs share deficit kernels (S4+complement four-orbit merge). -/
theorem complement_orbit_deficit_kernels :
    (∀ d : Fin 15, orbitDeficitKernel .t21 d = orbitDeficitKernel .t12 d) ∧
      (∀ d : Fin 15, orbitDeficitKernel .t31 d = orbitDeficitKernel .t13 d) := by
  constructor
  · intro d; rfl
  · intro d; rfl

/-- Area covectors are the committed Heron edge gradients on seed supports. -/
theorem orbitAreaCov_uses_heron_grads :
    (areaCov11 0 = areaGradA 1 1 2 ∧
      areaCov11 1 = areaGradB 1 1 2 ∧
        areaCov11 2 = areaGradC 1 1 2) ∧
      (areaCov12 0 = areaGradA 1 2 3 ∧
        areaCov12 5 = areaGradB 1 2 3 ∧
          areaCov12 6 = areaGradC 1 2 3) ∧
        (areaCov22 2 = areaGradA 2 2 4 ∧
          areaCov22 11 = areaGradB 2 2 4 ∧
            areaCov22 14 = areaGradC 2 2 4) :=
  ⟨areaCov11_eq_grads, areaCov12_eq_grads, areaCov22_eq_grads⟩

/-! ## §2. Generic factorized orbit fold -/

/-- Factorized slot term: orbit-constant area covector × deficit kernel,
phased by the midpoint plane-wave convention. -/
def factorizedOrbitSlotTerm (ty : HingeOrbitType) (H : Mat4) (m : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    phasedClassDot (orbitAreaCov ty) H m (hingeBase s t) *
      phasedClassDot (orbitDeficitKernel ty) H m (hingeBase s t)
  else 0

/-- Finite-momentum factorized Bloch fold for one orbit type. -/
def factorizedBlochFoldOrbit (ty : HingeOrbitType) (H : Mat4)
    (m : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, factorizedOrbitSlotTerm ty H m s t

/-- Full finite-momentum all-orbit factorized fold (sum of six S4 types). -/
def factorizedBlochFoldAll (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, factorizedBlochFoldOrbit ty H m

theorem factorizedBlochFoldOrbit_t11_eq (H : Mat4) (m : Fin 4 → ℝ) :
    factorizedBlochFoldOrbit .t11 H m = factorizedBlochFold11 H m := by
  unfold factorizedBlochFoldOrbit factorizedBlochFold11
    factorizedOrbitSlotTerm factorizedSlotTerm
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases h : isOrbit .t11 s t
  · have ht : isT11 s t := (isOrbit_t11_iff_isT11 s t).mp h
    simp [h, ht, orbitAreaCov, orbitDeficitKernel]
  · have ht : ¬ isT11 s t := fun ht => h ((isOrbit_t11_iff_isT11 s t).mpr ht)
    simp [h, ht]

/-- Consistency gate: each orbit fold at zero momentum recovers the
committed `orbitZeroMomQuadratic`. -/
theorem factorizedBlochFoldOrbit_zeroMomentum (ty : HingeOrbitType)
    (H : Mat4) :
    factorizedBlochFoldOrbit ty H (fun _ => (0 : ℝ)) =
      orbitZeroMomQuadratic ty H := by
  unfold factorizedBlochFoldOrbit orbitZeroMomQuadratic
  have hterm : ∀ s t,
      factorizedOrbitSlotTerm ty H (fun _ => (0 : ℝ)) s t =
        (if isOrbit ty s t then (1 : ℝ) else 0) *
          (classDot (orbitAreaCov ty) H *
            classDot (orbitDeficitKernel ty) H) := by
    intro s t
    unfold factorizedOrbitSlotTerm
    by_cases h : isOrbit ty s t <;> simp [h, phasedClassDot_zeroMomentum]
  simp_rw [hterm]
  rw [show
      (∑ s : Fin 24, ∑ t : Fin 10,
          (if isOrbit ty s t then (1 : ℝ) else 0) *
            (classDot (orbitAreaCov ty) H *
              classDot (orbitDeficitKernel ty) H)) =
        (∑ s : Fin 24, ∑ t : Fin 10, (if isOrbit ty s t then (1 : ℝ) else 0)) *
          (classDot (orbitAreaCov ty) H *
            classDot (orbitDeficitKernel ty) H) by
    simp_rw [Finset.sum_mul]]
  rw [orbit_slot_count_real]
  ring

/-- All-orbit fold at zero momentum is the committed true-weight Hessian. -/
theorem factorizedBlochFoldAll_zeroMomentum (H : Mat4) :
    factorizedBlochFoldAll H (fun _ => (0 : ℝ)) =
      trueWeightZeroMomQuadratic H := by
  unfold factorizedBlochFoldAll trueWeightZeroMomQuadratic
  exact Finset.sum_congr rfl fun ty _ =>
    factorizedBlochFoldOrbit_zeroMomentum ty H

theorem factorizedBlochFoldAll_axis_zeroMomentum :
    factorizedBlochFoldAll axisTTPlus (fun _ => (0 : ℝ)) = 0 := by
  rw [factorizedBlochFoldAll_zeroMomentum, trueWeightZeroMomQuadratic_axisTTPlus]

theorem factorizedBlochFoldAll_gauge_zeroMomentum :
    factorizedBlochFoldAll decoyGauge (fun _ => (0 : ℝ)) = 0 := by
  rw [factorizedBlochFoldAll_zeroMomentum, trueWeightZeroMomQuadratic_decoyGauge]

/-! ## §3. Ray folds and evenness -/

/-- Scale a wave direction: `m = μ · dir`. -/
def foldOrbitAlong (ty : HingeOrbitType) (H : Mat4) (dir : Fin 4 → ℝ)
    (μ : ℝ) : ℝ :=
  factorizedBlochFoldOrbit ty H (fun i => μ * dir i)

def foldAllAlong (H : Mat4) (dir : Fin 4 → ℝ) (μ : ℝ) : ℝ :=
  factorizedBlochFoldAll H (fun i => μ * dir i)

/-- Midpoint phase linear in the ray parameter. -/
def phaseScaleDir (dir : Fin 4 → ℝ) (x : Fin 4 → ℝ) (d : Fin 15) : ℝ :=
  (∑ i : Fin 4, dir i * x i) +
    (∑ i : Fin 4, dir i * classDisp d i) / 2

theorem classMidpointPhase_scaleDir (dir : Fin 4 → ℝ) (μ : ℝ)
    (x : Fin 4 → ℝ) (d : Fin 15) :
    classMidpointPhase (fun i => μ * dir i) x d =
      μ * phaseScaleDir dir x d := by
  unfold classMidpointPhase phaseScaleDir
  have hx :
      (∑ i : Fin 4, (μ * dir i) * x i) =
        μ * ∑ i : Fin 4, dir i * x i := by
    simp [mul_assoc, Finset.mul_sum]
  have hd :
      (∑ i : Fin 4, (μ * dir i) * classDisp d i) =
        μ * ∑ i : Fin 4, dir i * classDisp d i := by
    simp [mul_assoc, Finset.mul_sum]
  rw [hx, hd]; ring

theorem phasedClassDot_scaleDir (v : Fin 15 → ℝ) (H : Mat4)
    (dir : Fin 4 → ℝ) (μ : ℝ) (x : Fin 4 → ℝ) :
    phasedClassDot v H (fun i => μ * dir i) x =
      ∑ d : Fin 15, v d * classCoeff H d * Real.cos (μ * phaseScaleDir dir x d) := by
  unfold phasedClassDot planeWaveClassPert
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [classMidpointPhase_scaleDir]; ring

theorem foldOrbitAlong_neg (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) (μ : ℝ) :
    foldOrbitAlong ty H dir (-μ) = foldOrbitAlong ty H dir μ := by
  unfold foldOrbitAlong factorizedBlochFoldOrbit factorizedOrbitSlotTerm
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : isOrbit ty s t
  · simp only [ht, ite_true]
    have hphase (v : Fin 15 → ℝ) :
        phasedClassDot v H (fun i => (-μ) * dir i) (hingeBase s t) =
          phasedClassDot v H (fun i => μ * dir i) (hingeBase s t) := by
      rw [phasedClassDot_scaleDir, phasedClassDot_scaleDir]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [neg_mul, Real.cos_neg]
    rw [hphase (orbitAreaCov ty), hphase (orbitDeficitKernel ty)]
  · simp [ht]

theorem foldOrbitAlong_even (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) : Function.Even (foldOrbitAlong ty H dir) :=
  fun μ => foldOrbitAlong_neg ty H dir μ

theorem foldAllAlong_neg (H : Mat4) (dir : Fin 4 → ℝ) (μ : ℝ) :
    foldAllAlong H dir (-μ) = foldAllAlong H dir μ := by
  unfold foldAllAlong factorizedBlochFoldAll
  refine Finset.sum_congr rfl fun ty _ => foldOrbitAlong_neg ty H dir μ

theorem foldAllAlong_even (H : Mat4) (dir : Fin 4 → ℝ) :
    Function.Even (foldAllAlong H dir) :=
  fun μ => foldAllAlong_neg H dir μ

private lemma zero_smul_dir (dir : Fin 4 → ℝ) :
    (fun i : Fin 4 => (0 : ℝ) * dir i) = fun _ => (0 : ℝ) := by
  funext i; ring

theorem foldAllAlong_zero (H : Mat4) (dir : Fin 4 → ℝ) :
    foldAllAlong H dir 0 = trueWeightZeroMomQuadratic H := by
  unfold foldAllAlong
  simp_rw [zero_smul_dir]
  exact factorizedBlochFoldAll_zeroMomentum H

theorem foldAllAlong_axis_zero (dir : Fin 4 → ℝ) :
    foldAllAlong axisTTPlus dir 0 = 0 := by
  rw [foldAllAlong_zero, trueWeightZeroMomQuadratic_axisTTPlus]

theorem foldAllAlong_gauge_zero (dir : Fin 4 → ℝ) :
    foldAllAlong decoyGauge dir 0 = 0 := by
  rw [foldAllAlong_zero, trueWeightZeroMomQuadratic_decoyGauge]

/-! ## §4. All-orbit m² moment polynomial (definition) -/

/-- Formal cosine two-jet m² coefficient for one orbit at direction `dir`.
This is the algebraic moment polynomial; Tendsto glue is OPEN below. -/
def m2OrbitMomentPoly (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10,
    if isOrbit ty s t then
      classDot (orbitAreaCov ty) H *
        (-(1 / 2 : ℝ) *
          ∑ d : Fin 15,
            orbitDeficitKernel ty d * classCoeff H d *
              (phaseScaleDir dir (hingeBase s t) d) ^ 2)
    else 0

/-- Full all-orbit m² moment polynomial. -/
def m2AllOrbitMomentPoly (H : Mat4) (dir : Fin 4 → ℝ) : ℝ :=
  ∑ ty : HingeOrbitType, m2OrbitMomentPoly ty H dir

/-- At vanishing area·H the moment polynomial is identically zero. -/
theorem m2OrbitMomentPoly_of_area_zero (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) (hA : classDot (orbitAreaCov ty) H = 0) :
    m2OrbitMomentPoly ty H dir = 0 := by
  unfold m2OrbitMomentPoly
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : isOrbit ty s t <;> simp [ht, hA]

/-- Ray fold at μ = 0 recovers the committed zero-momentum orbit quadratic. -/
theorem foldOrbitAlong_zero (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) :
    foldOrbitAlong ty H dir 0 = orbitZeroMomQuadratic ty H := by
  unfold foldOrbitAlong
  simp_rw [zero_smul_dir]
  exact factorizedBlochFoldOrbit_zeroMomentum ty H

theorem foldOrbitAlong_axis_zero (ty : HingeOrbitType) (dir : Fin 4 → ℝ) :
    foldOrbitAlong ty axisTTPlus dir 0 = 0 := by
  rw [foldOrbitAlong_zero]
  unfold orbitZeroMomQuadratic
  rw [orbitDeficit_dot_axisTTPlus ty, mul_zero]

theorem foldOrbitAlong_gauge_zero (ty : HingeOrbitType) (dir : Fin 4 → ℝ) :
    foldOrbitAlong ty decoyGauge dir 0 = 0 := by
  rw [foldOrbitAlong_zero]
  unfold orbitZeroMomQuadratic
  rw [orbitDeficit_dot_decoyGauge ty, mul_zero]
/-! ## §5. OPEN Props: arbitrary-direction cosine two-jets / Tendsto -/

/-- OPEN: punctured Tendsto of one-orbit ray fold / μ² to the moment poly. -/
def OrbitFoldAlongM2Tendsto (ty : HingeOrbitType) (H : Mat4)
    (dir : Fin 4 → ℝ) : Prop :=
  Tendsto (fun μ : ℝ => foldOrbitAlong ty H dir μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
    (𝓝 (m2OrbitMomentPoly ty H dir))

/-- OPEN: punctured Tendsto of the all-orbit ray fold / μ². -/
def AllOrbitFoldAlongM2Tendsto (H : Mat4) (dir : Fin 4 → ℝ) : Prop :=
  Tendsto (fun μ : ℝ => foldAllAlong H dir μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
    (𝓝 (m2AllOrbitMomentPoly H dir))

/-- OPEN: cosine two-jet / Tendsto holds for every nonzero direction. -/
def ArbitraryDirectionCosineTwoJet (ty : HingeOrbitType) (H : Mat4) : Prop :=
  ∀ dir : Fin 4 → ℝ, dir ≠ 0 → OrbitFoldAlongM2Tendsto ty H dir

/-- OPEN: all-orbit arbitrary-direction cosine two-jet. -/
def AllOrbitArbitraryDirectionCosineTwoJet (H : Mat4) : Prop :=
  ∀ dir : Fin 4 → ℝ, dir ≠ 0 → AllOrbitFoldAlongM2Tendsto H dir

/-! ## §6. Status flags and decoys -/

structure BlochAllOrbitSymbol4DStatus where
  orbitCountsClosed : Bool
  zeroMomentumReductionClosed : Bool
  rayEvennessClosed : Bool
  heronAreaGradientsWired : Bool
  complementKernelsClosed : Bool
  m2MomentPolyDefined : Bool
  /-- Arbitrary-direction Tendsto per orbit: still OPEN. -/
  orbitM2TendstoClosed : Bool
  /-- All-orbit arbitrary-direction Tendsto: still OPEN. -/
  allOrbitM2TendstoClosed : Bool
  /-- Continuum EH / full Hessian symbol: not claimed here. -/
  continuumEHClosed : Bool
  /-- Ledger flag must stay false. -/
  gapActionRecovery : Bool
  /-- Honesty: one-orbit symbol is not the continuum target. -/
  oneOrbitIsNotContinuumTarget : Bool

def blochAllOrbitSymbol4DStatus : BlochAllOrbitSymbol4DStatus where
  orbitCountsClosed := true
  zeroMomentumReductionClosed := true
  rayEvennessClosed := true
  heronAreaGradientsWired := true
  complementKernelsClosed := true
  m2MomentPolyDefined := true
  orbitM2TendstoClosed := false
  allOrbitM2TendstoClosed := false
  continuumEHClosed := false
  gapActionRecovery := false
  oneOrbitIsNotContinuumTarget := true

theorem blochAllOrbitSymbol4DStatus_flags :
    blochAllOrbitSymbol4DStatus.orbitCountsClosed = true ∧
      blochAllOrbitSymbol4DStatus.zeroMomentumReductionClosed = true ∧
        blochAllOrbitSymbol4DStatus.rayEvennessClosed = true ∧
          blochAllOrbitSymbol4DStatus.heronAreaGradientsWired = true ∧
            blochAllOrbitSymbol4DStatus.complementKernelsClosed = true ∧
              blochAllOrbitSymbol4DStatus.m2MomentPolyDefined = true ∧
                blochAllOrbitSymbol4DStatus.orbitM2TendstoClosed = false ∧
                  blochAllOrbitSymbol4DStatus.allOrbitM2TendstoClosed = false ∧
                    blochAllOrbitSymbol4DStatus.continuumEHClosed = false ∧
                      blochAllOrbitSymbol4DStatus.gapActionRecovery = false ∧
                        blochAllOrbitSymbol4DStatus.oneOrbitIsNotContinuumTarget =
                          true := by
  decide

/-- DECOY: the closed one-orbit `(1,1)` m² coefficient `-3` is not the
continuum EH target; continuum recovery requires the full all-orbit symbol. -/
theorem decoy_one_orbit_m2_is_not_continuum_target :
    ReggeBlochM2Symbol4D.m2Symbol axisTTPlus = -3 ∧
      blochAllOrbitSymbol4DStatus.continuumEHClosed = false ∧
        blochAllOrbitSymbol4DStatus.oneOrbitIsNotContinuumTarget = true ∧
          blochAllOrbitSymbol4DStatus.gapActionRecovery = false := by
  refine ⟨ReggeBlochM2Symbol4D.m2Symbol_axisTTPlus, rfl, rfl, rfl⟩

/-- Named OPEN props remain uninhabited status markers (not theorems). -/
theorem open_props_are_status_false :
    blochAllOrbitSymbol4DStatus.orbitM2TendstoClosed = false ∧
      blochAllOrbitSymbol4DStatus.allOrbitM2TendstoClosed = false := by
  decide

end

end ReggeBlochAllOrbitSymbol4D
end Analysis
end Gravity
end IndisputableMonolith
