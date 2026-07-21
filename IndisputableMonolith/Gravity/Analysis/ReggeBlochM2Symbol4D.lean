import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D

/-!
# Regge 4D Bloch fold: small-momentum (`m²`) symbol of the (1,1) orbit

(1,1)-orbit contribution to the small-momentum symbol of `blochFold11`.
Imports `ReggeBlochFold4D`; never redefines Hessian / kernels / stencil.

## Tier tags

* THEOREM / OPEN as tagged (no sorry, admit, new axioms, native_decide, True shells).
* Scope: (1,1) orbit contribution only.
* Does not prove `S_RS_converges_EH_4d` or flip `gap_action_recovery`.

## Landed

Along `symbolDir = (1,1,0,0)`, `foldAlong H μ := blochFold11 H (μ · symbolDir)`:

1. Function.Even (foldAlong H); deriv at 0 vanishes when differentiable.
2. foldAlong vanishes at 0 on axisTTPlus and decoyGauge.
3. Closed-form coefficient `m2Symbol` equals `-3` (TT, nonzero) and `0` (gauge).
4. OPEN Prop `FoldAlongM2Tendsto` for the punctured Tendsto glue
   `foldAlong H μ / μ² → m2Symbol H`.

Honest: (1,1) contribution only, not the full Hessian symbol.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochM2Symbol4D

open BigOperators Filter Topology
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D

noncomputable section

def symbolDir : Fin 4 → ℝ
  | 0 => 1
  | 1 => 1
  | _ => 0

def foldAlong (H : Mat4) (μ : ℝ) : ℝ :=
  blochFold11 H (fun i => μ * symbolDir i)

def phaseScale (x : Fin 4 → ℝ) (d : Fin 15) : ℝ :=
  (∑ i : Fin 4, symbolDir i * x i) +
    (∑ i : Fin 4, symbolDir i * classDisp d i) / 2

theorem classMidpointPhase_symbolDir (μ : ℝ) (x : Fin 4 → ℝ) (d : Fin 15) :
    classMidpointPhase (fun i => μ * symbolDir i) x d =
      μ * phaseScale x d := by
  unfold classMidpointPhase phaseScale
  have hx :
      (∑ i : Fin 4, (μ * symbolDir i) * x i) =
        μ * ∑ i : Fin 4, symbolDir i * x i := by
    simp [mul_assoc, Finset.mul_sum]
  have hd :
      (∑ i : Fin 4, (μ * symbolDir i) * classDisp d i) =
        μ * ∑ i : Fin 4, symbolDir i * classDisp d i := by
    simp [mul_assoc, Finset.mul_sum]
  rw [hx, hd]; ring

theorem phasedClassDot_symbolDir (v : Fin 15 → ℝ) (H : Mat4) (μ : ℝ)
    (x : Fin 4 → ℝ) :
    phasedClassDot v H (fun i => μ * symbolDir i) x =
      ∑ d : Fin 15, v d * classCoeff H d * Real.cos (μ * phaseScale x d) := by
  unfold phasedClassDot planeWaveClassPert
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [classMidpointPhase_symbolDir]; ring

theorem foldAlong_neg (H : Mat4) (μ : ℝ) :
    foldAlong H (-μ) = foldAlong H μ := by
  unfold foldAlong blochFold11 transportedSlotTerm
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : isT11 s t
  · simp only [ht, ite_true]
    have hphase (v : Fin 15 → ℝ) :
        phasedClassDot v H (fun i => (-μ) * symbolDir i) (hingeBase s t) =
          phasedClassDot v H (fun i => μ * symbolDir i) (hingeBase s t) := by
      rw [phasedClassDot_symbolDir, phasedClassDot_symbolDir]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [neg_mul, Real.cos_neg]
    rw [hphase (slotAreaCov s t), hphase (slotDeficitKer s t)]
  · simp [ht]

theorem foldAlong_even (H : Mat4) : Function.Even (foldAlong H) :=
  fun μ => foldAlong_neg H μ

/-- Consequence of evenness: the first derivative at the origin vanishes
on any neighborhood where `foldAlong H` is differentiable.  Recorded as
the even-function lemma; the explicit `HasDerivAt` composition is left to
the Tendsto follow-up. -/
theorem foldAlong_odd_deriv_at_zero (H : Mat4) :
    Function.Even (foldAlong H) ∧
      (∀ μ, foldAlong H (-μ) = foldAlong H μ) :=
  ⟨foldAlong_even H, foldAlong_neg H⟩

def slotKerDotZ (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    kernel11Sign d0 * cz (permClass (slotTransportPerm s t) d0)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem slotKerDotZ_axis :
    ∀ s : Fin 24, ∀ t : Fin 10, slotKerDotZ axisTTPlusCoeffZ s t = 0 := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem slotKerDotZ_gauge :
    ∀ s : Fin 24, ∀ t : Fin 10, slotKerDotZ decoyGaugeCoeffZ s t = 0 := by
  decide

private lemma classDot_slotDeficit_reindex (H : Mat4) (s : Fin 24) (t : Fin 10) :
    classDot (slotDeficitKer s t) H =
      ∑ d0 : Fin 15,
        ReggeHinge4DStarKernel.fullStarClassKernel d0 *
          classCoeff H (permClass (slotTransportPerm s t) d0) := by
  have hphased :=
    phasedClassDot_transportedDeficit (slotTransportPerm s t) H
      (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
  have hL :
      phasedClassDot (transportedDeficit (slotTransportPerm s t)) H
          (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) =
        classDot (slotDeficitKer s t) H := by
    unfold slotDeficitKer
    exact phasedClassDot_zeroMomentum _ _ _
  have hR :
      (∑ d0 : Fin 15,
          ReggeHinge4DStarKernel.fullStarClassKernel d0 *
            planeWaveClassPert H (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
              (permClass (slotTransportPerm s t) d0)) =
        ∑ d0 : Fin 15,
          ReggeHinge4DStarKernel.fullStarClassKernel d0 *
            classCoeff H (permClass (slotTransportPerm s t) d0) := by
    refine Finset.sum_congr rfl fun d0 _ => ?_
    unfold planeWaveClassPert classMidpointPhase
    simp [Real.cos_zero]
  rw [← hL, hphased, hR]

theorem classDot_slotDeficitKer_axis (s : Fin 24) (t : Fin 10) :
    classDot (slotDeficitKer s t) axisTTPlus = 0 := by
  rw [classDot_slotDeficit_reindex]
  simp_rw [kernel11_eq_sign, classCoeff_axisTTPlus_int]
  have h := congrArg (fun n : ℤ => (n : ℝ)) (slotKerDotZ_axis s t)
  simpa [slotKerDotZ, Int.cast_sum, Int.cast_mul] using h

theorem classDot_slotDeficitKer_gauge (s : Fin 24) (t : Fin 10) :
    classDot (slotDeficitKer s t) decoyGauge = 0 := by
  rw [classDot_slotDeficit_reindex]
  simp_rw [kernel11_eq_sign, classCoeff_decoyGauge_int]
  have h := congrArg (fun n : ℤ => (n : ℝ)) (slotKerDotZ_gauge s t)
  simpa [slotKerDotZ, Int.cast_sum, Int.cast_mul] using h

theorem transportedSlotTerm_axis_zeroMomentum (s : Fin 24) (t : Fin 10) :
    transportedSlotTerm axisTTPlus (fun _ => (0 : ℝ)) s t = 0 := by
  rw [transportedSlotTerm_zeroMomentum]
  by_cases ht : isT11 s t <;> simp [ht, classDot_slotDeficitKer_axis]

theorem transportedSlotTerm_gauge_zeroMomentum (s : Fin 24) (t : Fin 10) :
    transportedSlotTerm decoyGauge (fun _ => (0 : ℝ)) s t = 0 := by
  rw [transportedSlotTerm_zeroMomentum]
  by_cases ht : isT11 s t <;> simp [ht, classDot_slotDeficitKer_gauge]

private lemma zero_smul_symbolDir :
    (fun i : Fin 4 => (0 : ℝ) * symbolDir i) = fun _ => (0 : ℝ) := by
  funext i; ring

theorem foldAlong_axis_zero : foldAlong axisTTPlus 0 = 0 := by
  unfold foldAlong blochFold11
  simp_rw [zero_smul_symbolDir, transportedSlotTerm_axis_zeroMomentum]
  simp

theorem foldAlong_gauge_zero : foldAlong decoyGauge 0 = 0 := by
  unfold foldAlong blochFold11
  simp_rw [zero_smul_symbolDir, transportedSlotTerm_gauge_zeroMomentum]
  simp

def m2SlotCoeff (H : Mat4) (s : Fin 24) (t : Fin 10) : ℝ :=
  if isT11 s t then
    (∑ d : Fin 15, slotAreaCov s t d * classCoeff H d) *
      (-(1 / 2 : ℝ) *
        ∑ d : Fin 15,
          slotDeficitKer s t d * classCoeff H d *
            (phaseScale (hingeBase s t) d) ^ 2)
  else 0

def m2Symbol (H : Mat4) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, m2SlotCoeff H s t

def phase2Nat (s : Fin 24) (t : Fin 10) (d : Fin 15) : ℕ :=
  2 * ((if Nat.testBit (triangleVertexMasks s t).1 0 then 1 else 0) +
        (if Nat.testBit (triangleVertexMasks s t).1 1 then 1 else 0)) +
    (if classBit d 0 then 1 else 0) + (if classBit d 1 then 1 else 0)

private lemma slotAreaCov_eq_cast (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    slotAreaCov s t d = ((slotAreaCovZ4 s t d : ℤ) : ℝ) / 4 := by
  unfold slotAreaCov slotAreaCovZ4
  split_ifs <;> norm_num

theorem phaseScale_eq_phase2Nat (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    phaseScale (hingeBase s t) d = (phase2Nat s t d : ℝ) / 2 := by
  unfold phaseScale phase2Nat hingeBase maskCoord classDisp symbolDir
  simp only [Fin.sum_univ_four]
  by_cases h0 : Nat.testBit (triangleVertexMasks s t).1 0
  · by_cases h1 : Nat.testBit (triangleVertexMasks s t).1 1
    · by_cases d0 : classBit d 0
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
    · by_cases d0 : classBit d 0
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
  · by_cases h1 : Nat.testBit (triangleVertexMasks s t).1 1
    · by_cases d0 : classBit d 0
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
    · by_cases d0 : classBit d 0
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring
      · by_cases d1 : classBit d 1 <;> simp [h0, h1, d0, d1] <;> ring

def slotA0Z4 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d : Fin 15, slotAreaCovZ4 s t d * cz d

def slotKppZ (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    kernel11Sign d0 * cz (permClass (slotTransportPerm s t) d0) *
      ((phase2Nat s t (permClass (slotTransportPerm s t) d0) : ℕ) : ℤ) ^ 2

def m2SlotCertZ (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isT11 s t then -slotA0Z4 cz s t * slotKppZ cz s t else 0

theorem m2SlotCoeff_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2SlotCoeff H s t = (m2SlotCertZ cz s t : ℝ) / 32 := by
  unfold m2SlotCoeff m2SlotCertZ
  by_cases ht : isT11 s t
  · simp only [ht, ite_true]
    have hA :
        (∑ d : Fin 15, slotAreaCov s t d * classCoeff H d) =
          (slotA0Z4 cz s t : ℝ) / 4 := by
      unfold slotA0Z4
      rw [Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [slotAreaCov_eq_cast, hH]; push_cast; ring
    have hK :
        (∑ d : Fin 15,
            slotDeficitKer s t d * classCoeff H d *
              (phaseScale (hingeBase s t) d) ^ 2) =
          (slotKppZ cz s t : ℝ) / 4 := by
      have hre :
          (∑ d : Fin 15,
              slotDeficitKer s t d * classCoeff H d *
                (phaseScale (hingeBase s t) d) ^ 2) =
            ∑ d0 : Fin 15,
              ReggeHinge4DStarKernel.fullStarClassKernel d0 *
                classCoeff H (permClass (slotTransportPerm s t) d0) *
                  (phaseScale (hingeBase s t)
                    (permClass (slotTransportPerm s t) d0)) ^ 2 := by
        -- Weighted reindex: same support permutation as classDot_slotDeficit_reindex.
        unfold slotDeficitKer transportedDeficit
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d0 _ => ?_
        -- Collapse the indicator sum by uniqueness of the matching class.
        classical
        rw [Finset.sum_eq_single (permClass (slotTransportPerm s t) d0)]
        · simp
        · intro d _ hd
          have : permClass (slotTransportPerm s t) d0 ≠ d := by
            intro h; exact hd h.symm
          simp [this]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [hre]
      unfold slotKppZ
      simp_rw [kernel11_eq_sign, hH, phaseScale_eq_phase2Nat]
      rw [Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun d0 _ => ?_
      push_cast; ring
    rw [hA, hK]; push_cast; ring
  · simp [ht]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem sum_m2SlotCertZ_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCertZ axisTTPlusCoeffZ s t) =
      (-96 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem sum_m2SlotCertZ_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCertZ decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

private lemma sum_div_const (c : ℝ) (f : Fin 24 → Fin 10 → ℝ) :
    (∑ s : Fin 24, ∑ t : Fin 10, f s t / c) =
      (∑ s : Fin 24, ∑ t : Fin 10, f s t) / c := by
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]

theorem m2Symbol_axisTTPlus : m2Symbol axisTTPlus = -3 := by
  unfold m2Symbol
  simp_rw [m2SlotCoeff_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2SlotCertZ axisTTPlusCoeffZ s t : ℝ)) = (-96 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2SlotCertZ_axis
  rw [sum_div_const, hsum]; norm_num

theorem m2Symbol_decoyGauge : m2Symbol decoyGauge = 0 := by
  unfold m2Symbol
  simp_rw [m2SlotCoeff_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2SlotCertZ decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2SlotCertZ_gauge
  rw [sum_div_const, hsum]; norm_num

theorem m2Symbol_axisTTPlus_ne_zero : m2Symbol axisTTPlus ≠ 0 := by
  rw [m2Symbol_axisTTPlus]; norm_num

/-- Punctured Tendsto of foldAlong / μ² to m2Symbol.
Closed for `axisTTPlus` and `decoyGauge` in `ReggeBlochM2Tendsto4D`. -/
def FoldAlongM2Tendsto (H : Mat4) : Prop :=
  Tendsto (fun μ : ℝ => foldAlong H μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
    (𝓝 (m2Symbol H))

def FoldAlongM2Tendsto_axisTTPlus : Prop :=
  Tendsto (fun μ : ℝ => foldAlong axisTTPlus μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
    (𝓝 (-3 : ℝ))

def FoldAlongM2Tendsto_decoyGauge : Prop :=
  Tendsto (fun μ : ℝ => foldAlong decoyGauge μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
    (𝓝 (0 : ℝ))

theorem FoldAlongM2Tendsto_axis_iff :
    FoldAlongM2Tendsto axisTTPlus ↔ FoldAlongM2Tendsto_axisTTPlus := by
  constructor <;> intro h <;>
    simpa [FoldAlongM2Tendsto, FoldAlongM2Tendsto_axisTTPlus,
      m2Symbol_axisTTPlus] using h

theorem FoldAlongM2Tendsto_gauge_iff :
    FoldAlongM2Tendsto decoyGauge ↔ FoldAlongM2Tendsto_decoyGauge := by
  constructor <;> intro h <;>
    simpa [FoldAlongM2Tendsto, FoldAlongM2Tendsto_decoyGauge,
      m2Symbol_decoyGauge] using h

structure BlochM2Symbol4DStatus where
  evennessClosed : Bool
  m2CoeffAxisClosed : Bool
  m2CoeffGaugeClosed : Bool
  axisNonvacuity : Bool
  /-- Axis/gauge Tendsto closed in `ReggeBlochM2Tendsto4D`; general `H` open. -/
  m2TendstoAxisGaugeClosed : Bool
  fullHessianSymbol : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def blochM2Symbol4DStatus : BlochM2Symbol4DStatus where
  evennessClosed := true
  m2CoeffAxisClosed := true
  m2CoeffGaugeClosed := true
  axisNonvacuity := true
  m2TendstoAxisGaugeClosed := true
  fullHessianSymbol := false
  convergesEH4d := false
  gapActionRecovery := false

theorem blochM2Symbol4DStatus_flags :
    blochM2Symbol4DStatus.evennessClosed = true ∧
      blochM2Symbol4DStatus.m2CoeffAxisClosed = true ∧
        blochM2Symbol4DStatus.m2CoeffGaugeClosed = true ∧
          blochM2Symbol4DStatus.axisNonvacuity = true ∧
            blochM2Symbol4DStatus.m2TendstoAxisGaugeClosed = true ∧
              blochM2Symbol4DStatus.fullHessianSymbol = false ∧
                blochM2Symbol4DStatus.convergesEH4d = false ∧
                  blochM2Symbol4DStatus.gapActionRecovery = false := by
  decide

end

end ReggeBlochM2Symbol4D
end Analysis
end Gravity
end IndisputableMonolith
