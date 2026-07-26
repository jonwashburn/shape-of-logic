/-
  PrimitiveRecognitionCalculus/PRCNativeCostUniqueness.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Immediate target after pass 24: attack `PRCNativeCostUniquenessTarget`
    or isolate the smallest exact blocker.

  The current PRC cost hypotheses are too weak to prove uniqueness directly:
  after setting `g = F + 1`, the RCL has the d'Alembert form
  `g(xy) + g(x/y) = 2 g(x) g(y)`. On a rational multiplicative group,
  one-point calibration at `2` does not by itself control all prime directions.
  This file names the exact missing character-factorization and calibrated
  character-rigidity targets and proves that together they imply native
  cost uniqueness.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Kernel
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.TraceClosure
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCMonotoneDAlembert

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

/-- A ratio-character candidate for the d'Alembert factorization of a PRC cost.
It is stated at the ratio-orbit level and uses cross-equivalence rather than
definitional equality, so it remains quotient-native. -/
structure PRCRatioCharacter (χ : RatioOrbit → RatioOrbit) : Prop where
  unit :
    RatioOrbit.crossEq (χ RatioOrbit.one) RatioOrbit.one
  multiplicative :
    ∀ x y : RatioOrbit,
      RatioOrbit.crossEq (χ (RatioOrbit.mul x y))
        (RatioOrbit.mul (χ x) (χ y))
  reciprocal :
    ∀ x : RatioOrbit,
      RatioOrbit.crossEq (χ (RatioOrbit.recip x))
        (RatioOrbit.recip (χ x))
  normalized_invariant :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq (χ q) (χ (DistinctionNat.normalizeRatio q))
  nonzero_preserving :
    ∀ {q : RatioOrbit}, q.toRat ≠ 0 → (χ q).toRat ≠ 0

/-- Cost generated from a rational character. The canonical PRC cost is the
identity-character case. -/
def costFromCharacter (χ : RatioOrbit → RatioOrbit) (q : RatioOrbit) :
    RatioOrbit :=
  onRatioOrbit (χ q)

theorem costFromCharacter_toRat
    (χ : RatioOrbit → RatioOrbit) (q : RatioOrbit) :
    (costFromCharacter χ q).toRat =
      ((χ q).toRat + (χ q).toRat⁻¹) / 2 - 1 := by
  exact onRatioOrbit_toRat (χ q)

/-- The doubled trace value `2(a+1)` attached to a cost value `a`. -/
def doubledTraceValue (a : RatioOrbit) : RatioOrbit :=
  RatioOrbit.mul two (RatioOrbit.add a RatioOrbit.one)

/-- The doubled d'Alembert trace carried by a native cost: `T_F(q)=2(F(q)+1)`.
For a generated cost this is exactly `χ(q)+χ(q)⁻¹`. -/
def nativeCostDoubledTrace
    (F : RatioOrbit → RatioOrbit) (q : RatioOrbit) : RatioOrbit :=
  doubledTraceValue (F q)

theorem doubledTraceValue_congr {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (doubledTraceValue a) (doubledTraceValue b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  simp [doubledTraceValue, RatioOrbit.mul_toRat, RatioOrbit.add_toRat,
    two_toRat, RatioOrbit.one_toRat]
  linarith

/-- Native d'Alembert trace equation. This is the RCL equation after setting
`T_F = 2(F+1)`. -/
def PRCDoubledTraceDAlembert (T : RatioOrbit → RatioOrbit) : Prop :=
  ∀ {x y : RatioOrbit}, x.toRat ≠ 0 → y.toRat ≠ 0 →
    RatioOrbit.crossEq
      (RatioOrbit.add (T (RatioOrbit.mul x y)) (T (div x y)))
      (RatioOrbit.mul (T x) (T y))

theorem nativeCostDoubledTrace_dAlembert_of_native_hypotheses
    {F : RatioOrbit → RatioOrbit}
    (hF : PRCNativeCostHypotheses F) :
    PRCDoubledTraceDAlembert (nativeCostDoubledTrace F) := by
  intro x y hx hy
  have hrcl := hF.canonical_rcl hx hy
  rw [RatioOrbit.crossEq_iff_toRat_eq] at hrcl ⊢
  simp [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.add_toRat,
    RatioOrbit.mul_toRat, two_toRat, RatioOrbit.one_toRat] at hrcl ⊢
  ring_nf at hrcl ⊢
  linarith

/-- Hypotheses carried by the doubled trace of a native PRC cost. -/
structure PRCDoubledTraceHypotheses (T : RatioOrbit → RatioOrbit) : Prop where
  reciprocal :
    ∀ q, RatioOrbit.crossEq (T q) (T (RatioOrbit.recip q))
  normalized_invariant :
    ∀ q, RatioOrbit.crossEq (T q) (T (DistinctionNat.normalizeRatio q))
  dAlembert :
    PRCDoubledTraceDAlembert T
  unit_trace :
    RatioOrbit.crossEq (T RatioOrbit.one) two
  two_trace :
    RatioOrbit.crossEq (T two) (nativeCostDoubledTrace onRatioOrbit two)

theorem nativeCostDoubledTrace_hypotheses_of_native_cost_hypotheses
    {F : RatioOrbit → RatioOrbit}
    (hF : PRCNativeCostHypotheses F) :
    PRCDoubledTraceHypotheses (nativeCostDoubledTrace F) := by
  refine
    { reciprocal := ?_,
      normalized_invariant := ?_,
      dAlembert := nativeCostDoubledTrace_dAlembert_of_native_hypotheses hF,
      unit_trace := ?_,
      two_trace := ?_ }
  · intro q
    exact doubledTraceValue_congr (hF.reciprocal q)
  · intro q
    exact doubledTraceValue_congr (hF.normalized_invariant q)
  · rw [RatioOrbit.crossEq_iff_toRat_eq]
    rw [nativeCostDoubledTrace, doubledTraceValue, hF.unit_zero,
      RatioOrbit.mul_toRat, RatioOrbit.add_toRat, RatioOrbit.zero_toRat,
      RatioOrbit.one_toRat, two_toRat]
    norm_num
  · exact doubledTraceValue_congr hF.two_calibrated

/-- Trace form of character factorization. This is the d'Alembert lift hidden
inside `F = J ∘ χ`: the generated trace of `χ q` must be `2(F q + 1)`. -/
def PRCCharacterTraceMatchesCost
    (F : RatioOrbit → RatioOrbit) (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q : RatioOrbit,
    RatioOrbit.crossEq
      (RatioOrbit.add (χ q) (RatioOrbit.recip (χ q)))
      (nativeCostDoubledTrace F q)

theorem PRCCharacterTraceMatchesCost_of_cost_crossEq
    {F χ : RatioOrbit → RatioOrbit}
    (hcost : ∀ q : RatioOrbit,
      RatioOrbit.crossEq (F q) (costFromCharacter χ q)) :
    PRCCharacterTraceMatchesCost F χ := by
  intro q
  have h := hcost q
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [costFromCharacter_toRat] at h
  rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.add_toRat,
    RatioOrbit.recip_toRat, RatioOrbit.mul_toRat, two_toRat,
    RatioOrbit.add_toRat, RatioOrbit.one_toRat]
  linarith

theorem cost_crossEq_of_PRCCharacterTraceMatchesCost
    {F χ : RatioOrbit → RatioOrbit}
    (htrace : PRCCharacterTraceMatchesCost F χ) :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq (F q) (costFromCharacter χ q) := by
  intro q
  have h := htrace q
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.add_toRat,
    RatioOrbit.recip_toRat, RatioOrbit.mul_toRat, two_toRat, RatioOrbit.add_toRat,
    RatioOrbit.one_toRat] at h
  rw [costFromCharacter_toRat]
  linarith

/-- Exact d'Alembert trace-lift version of character factorization. -/
def PRCNativeCostCharacterTraceLiftTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
          PRCCharacterTraceMatchesCost F χ

/-- Coherent-root version of the remaining d'Alembert blocker. It asks for a
multiplicative ratio character whose trace realizes any native doubled trace. -/
def PRCDoubledTraceCoherentRootTarget : Prop :=
  ∀ T : RatioOrbit → RatioOrbit,
    PRCDoubledTraceHypotheses T →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq
              (RatioOrbit.add (χ q) (RatioOrbit.recip (χ q)))
              (T q)

theorem RatioOrbit.recip_zero_eq :
    RatioOrbit.recip RatioOrbit.zero = RatioOrbit.zero := by
  unfold RatioOrbit.recip
  simp [RatioOrbit.zero, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.zero_toInt]

/-- A doubled trace that is canonical away from zero but deliberately spikes the
zero orbit to trace `1`. The current doubled-trace hypotheses do not see this
because their d'Alembert law is restricted to nonzero inputs. -/
def zeroSpikeDoubledTrace (q : RatioOrbit) : RatioOrbit :=
  if q.toRat = 0 then RatioOrbit.one else nativeCostDoubledTrace onRatioOrbit q

theorem zeroSpikeDoubledTrace_zero :
    zeroSpikeDoubledTrace RatioOrbit.zero = RatioOrbit.one := by
  rw [zeroSpikeDoubledTrace, if_pos RatioOrbit.zero_toRat]

theorem zeroSpikeDoubledTrace_nonzero {q : RatioOrbit}
    (hq : q.toRat ≠ 0) :
    zeroSpikeDoubledTrace q = nativeCostDoubledTrace onRatioOrbit q := by
  rw [zeroSpikeDoubledTrace, if_neg hq]

theorem zeroSpikeDoubledTrace_hypotheses :
    PRCDoubledTraceHypotheses zeroSpikeDoubledTrace := by
  refine
    { reciprocal := ?_,
      normalized_invariant := ?_,
      dAlembert := ?_,
      unit_trace := ?_,
      two_trace := ?_ }
  · intro q
    by_cases hq : q.toRat = 0
    · have hrec : (RatioOrbit.recip q).toRat = 0 := by
        rw [RatioOrbit.recip_toRat, hq]
        norm_num
      rw [RatioOrbit.crossEq_iff_toRat_eq]
      rw [zeroSpikeDoubledTrace, if_pos hq]
      rw [zeroSpikeDoubledTrace, if_pos hrec]
    · have hrec : (RatioOrbit.recip q).toRat ≠ 0 := by
        rw [RatioOrbit.recip_toRat]
        exact inv_ne_zero hq
      rw [zeroSpikeDoubledTrace_nonzero hq,
        zeroSpikeDoubledTrace_nonzero hrec]
      exact doubledTraceValue_congr (reciprocal_symmetric q)
  · intro q
    by_cases hq : q.toRat = 0
    · have hnorm : (DistinctionNat.normalizeRatio q).toRat = 0 := by
        rw [DistinctionNat.normalizeRatio_toRat, hq]
      rw [RatioOrbit.crossEq_iff_toRat_eq]
      rw [zeroSpikeDoubledTrace, if_pos hq]
      rw [zeroSpikeDoubledTrace, if_pos hnorm]
    · have hnorm : (DistinctionNat.normalizeRatio q).toRat ≠ 0 := by
        rw [DistinctionNat.normalizeRatio_toRat]
        exact hq
      rw [zeroSpikeDoubledTrace_nonzero hq,
        zeroSpikeDoubledTrace_nonzero hnorm]
      exact doubledTraceValue_congr (normalized_invariant q)
  · intro x y hx hy
    have hxy : (RatioOrbit.mul x y).toRat ≠ 0 := by
      rw [RatioOrbit.mul_toRat]
      exact mul_ne_zero hx hy
    have hdiv : (div x y).toRat ≠ 0 := by
      rw [div_toRat]
      exact div_ne_zero hx hy
    rw [zeroSpikeDoubledTrace_nonzero hxy,
      zeroSpikeDoubledTrace_nonzero hdiv,
      zeroSpikeDoubledTrace_nonzero hx,
      zeroSpikeDoubledTrace_nonzero hy]
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    rw [RatioOrbit.add_toRat, RatioOrbit.mul_toRat,
      nativeCostDoubledTrace, nativeCostDoubledTrace, nativeCostDoubledTrace,
      nativeCostDoubledTrace, doubledTraceValue, doubledTraceValue,
      doubledTraceValue, doubledTraceValue,
      RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
      RatioOrbit.mul_toRat, RatioOrbit.add_toRat, RatioOrbit.add_toRat,
      RatioOrbit.add_toRat, RatioOrbit.add_toRat, two_toRat,
      RatioOrbit.one_toRat, onRatioOrbit_toRat, onRatioOrbit_toRat,
      onRatioOrbit_toRat, onRatioOrbit_toRat, RatioOrbit.mul_toRat, div_toRat]
    field_simp [hx, hy, mul_ne_zero hx hy]
    ring
  · rw [RatioOrbit.crossEq_iff_toRat_eq]
    rw [zeroSpikeDoubledTrace_nonzero (by
      rw [RatioOrbit.one_toRat]
      norm_num : RatioOrbit.one.toRat ≠ 0)]
    rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
      onRatioOrbit_toRat, RatioOrbit.one_toRat]
    norm_num
  · rw [zeroSpikeDoubledTrace_nonzero (by
      rw [two_toRat]
      norm_num : two.toRat ≠ 0)]
    exact RatioOrbit.crossEq_refl _

theorem zeroSpikeDoubledTrace_no_ratio_character_trace :
    ¬ ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq
              (RatioOrbit.add (χ q) (RatioOrbit.recip (χ q)))
              (zeroSpikeDoubledTrace q) := by
  intro h
  rcases h with ⟨χ, hχ, htrace⟩
  let a : ℚ := (χ RatioOrbit.zero).toRat
  have hrec := hχ.reciprocal RatioOrbit.zero
  have hrecRat : a = a⁻¹ := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_zero_eq,
      RatioOrbit.recip_toRat] at hrec
    exact hrec
  have htraceZero := htrace RatioOrbit.zero
  have htraceRat : a + a⁻¹ = 1 := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.recip_toRat, zeroSpikeDoubledTrace_zero,
      RatioOrbit.one_toRat] at htraceZero
    exact htraceZero
  have haHalf : a = (1 / 2 : ℚ) := by
    linarith
  rw [haHalf] at hrecRat
  norm_num at hrecRat

theorem PRCDoubledTraceCoherentRootTarget_refuted :
    ¬ PRCDoubledTraceCoherentRootTarget := by
  intro hroot
  exact zeroSpikeDoubledTrace_no_ratio_character_trace
    (hroot zeroSpikeDoubledTrace zeroSpikeDoubledTrace_hypotheses)

/-- Missing zero-orbit compatibility for doubled traces. The nonzero
d'Alembert law cannot constrain `T(0)`, but character traces with the intended
zero image have doubled trace `0` at the zero orbit. -/
def PRCDoubledTraceZeroCalibrated (T : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (T RatioOrbit.zero) RatioOrbit.zero

theorem zeroSpikeDoubledTrace_not_zero_calibrated :
    ¬ PRCDoubledTraceZeroCalibrated zeroSpikeDoubledTrace := by
  intro h
  rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
    zeroSpikeDoubledTrace_zero, RatioOrbit.one_toRat,
    RatioOrbit.zero_toRat] at h
  norm_num at h

/-- Repaired coherent-root target after the zero-spike no-go. -/
def PRCDoubledTraceZeroCalibratedCoherentRootTarget : Prop :=
  ∀ T : RatioOrbit → RatioOrbit,
    PRCDoubledTraceHypotheses T →
      PRCDoubledTraceZeroCalibrated T →
        ∃ χ : RatioOrbit → RatioOrbit,
          PRCRatioCharacter χ ∧
            ∀ q : RatioOrbit,
              RatioOrbit.crossEq
                (RatioOrbit.add (χ q) (RatioOrbit.recip (χ q)))
                (T q)

/-- The denominator `3` appearing in the linear root extraction
`χ(q) = (2*T(2q)-T(q))/3`. -/
def traceRootDenominator : RatioOrbit :=
  RatioOrbit.add two RatioOrbit.one

@[simp] theorem traceRootDenominator_toRat :
    traceRootDenominator.toRat = 3 := by
  rw [traceRootDenominator, RatioOrbit.add_toRat, two_toRat,
    RatioOrbit.one_toRat]
  norm_num

/-- Linear root candidate forced by the split trace at the distinguished
axis `2`: if `T(q)=χ(q)+χ(q)⁻¹` and `χ(2)=2`, then
`χ(q) = (2*T(2q)-T(q))/3`. The zero case is supplied by the repaired
zero-calibration field. -/
def traceRootCandidate (T : RatioOrbit → RatioOrbit) (q : RatioOrbit) :
    RatioOrbit :=
  if q.toRat = 0 then
    RatioOrbit.zero
  else
    RatioOrbit.mul
      (RatioOrbit.sub
        (RatioOrbit.mul two (T (RatioOrbit.mul two q)))
        (T q))
      (RatioOrbit.recip traceRootDenominator)

theorem traceRootCandidate_zero (T : RatioOrbit → RatioOrbit) :
    traceRootCandidate T RatioOrbit.zero = RatioOrbit.zero := by
  rw [traceRootCandidate, if_pos RatioOrbit.zero_toRat]

theorem traceRootCandidate_toRat_of_nonzero
    (T : RatioOrbit → RatioOrbit) {q : RatioOrbit} (hq : q.toRat ≠ 0) :
    (traceRootCandidate T q).toRat =
      (2 * (T (RatioOrbit.mul two q)).toRat - (T q).toRat) / 3 := by
  rw [traceRootCandidate, if_neg hq]
  rw [RatioOrbit.mul_toRat, RatioOrbit.sub_toRat, RatioOrbit.mul_toRat,
    two_toRat, RatioOrbit.recip_toRat, traceRootDenominator_toRat]
  norm_num
  ring

/-- Exact linear-root version of the repaired doubled-trace root problem. -/
def PRCDoubledTraceLinearRootCandidateWorks
    (T : RatioOrbit → RatioOrbit) : Prop :=
  PRCRatioCharacter (traceRootCandidate T) ∧
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.add
          (traceRootCandidate T q)
          (RatioOrbit.recip (traceRootCandidate T q)))
        (T q)

def PRCDoubledTraceZeroCalibratedLinearRootTarget : Prop :=
  ∀ T : RatioOrbit → RatioOrbit,
    PRCDoubledTraceHypotheses T →
      PRCDoubledTraceZeroCalibrated T →
        PRCDoubledTraceLinearRootCandidateWorks T

theorem PRCDoubledTraceZeroCalibratedCoherentRootTarget_of_linear_root
    (hlinear : PRCDoubledTraceZeroCalibratedLinearRootTarget) :
    PRCDoubledTraceZeroCalibratedCoherentRootTarget := by
  intro T hT hzero
  rcases hlinear T hT hzero with ⟨hχ, htrace⟩
  exact ⟨traceRootCandidate T, hχ, htrace⟩

theorem PRCNativeCostCharacterTraceLiftTarget_of_doubled_trace_coherent_root
    (hroot : PRCDoubledTraceCoherentRootTarget) :
    PRCNativeCostCharacterTraceLiftTarget := by
  intro F hF
  rcases hroot (nativeCostDoubledTrace F)
      (nativeCostDoubledTrace_hypotheses_of_native_cost_hypotheses hF) with
    ⟨χ, hχ, hχtrace⟩
  exact ⟨χ, hχ, hχtrace⟩

/-- First exact blocker: every admissible PRC-native RCL cost should factor
through a ratio character. This is the discrete d'Alembert factorization step. -/
def PRCNativeCostCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

theorem PRCNativeCostCharacterTraceLiftTarget_of_factorization
    (hfactor : PRCNativeCostCharacterFactorizationTarget) :
    PRCNativeCostCharacterTraceLiftTarget := by
  intro F hF
  rcases hfactor F hF with ⟨χ, hχ, hcost⟩
  exact ⟨χ, hχ, PRCCharacterTraceMatchesCost_of_cost_crossEq hcost⟩

theorem PRCNativeCostCharacterFactorizationTarget_of_trace_lift
    (htrace : PRCNativeCostCharacterTraceLiftTarget) :
    PRCNativeCostCharacterFactorizationTarget := by
  intro F hF
  rcases htrace F hF with ⟨χ, hχ, hχtrace⟩
  exact ⟨χ, hχ, cost_crossEq_of_PRCCharacterTraceMatchesCost hχtrace⟩

theorem PRCNativeCostCharacterFactorizationTarget_of_doubled_trace_coherent_root
    (hroot : PRCDoubledTraceCoherentRootTarget) :
    PRCNativeCostCharacterFactorizationTarget :=
  PRCNativeCostCharacterFactorizationTarget_of_trace_lift
    (PRCNativeCostCharacterTraceLiftTarget_of_doubled_trace_coherent_root hroot)

theorem PRCNativeCostCharacterFactorizationTarget_iff_trace_lift :
    PRCNativeCostCharacterFactorizationTarget ↔
      PRCNativeCostCharacterTraceLiftTarget := by
  constructor
  · exact PRCNativeCostCharacterTraceLiftTarget_of_factorization
  · exact PRCNativeCostCharacterFactorizationTarget_of_trace_lift

/-- Second exact blocker: a calibrated rational character cost must be the
canonical identity-character cost. This is where prime-direction freedom has
to be eliminated. -/
def PRCNativeCostCharacterRigidityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) →
        ∀ q : RatioOrbit,
          RatioOrbit.crossEq (costFromCharacter χ q) (onRatioOrbit q)

/-- The ratio direction associated to a nonzero orbit position. -/
def orbitDirection (p : DistinctionNat) (_hp : p ≠ DistinctionNat.zero) :
    RatioOrbit where
  num := SignedOrbit.ofOrbit p
  den := DistinctionNat.one
  den_ne_zero := DistinctionNat.one_ne_zero

/-- The ratio direction associated to a native prime orbit. -/
def primeDirection (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    RatioOrbit :=
  orbitDirection p hp.1

/-- A ratio character is calibrated on every native prime direction when its
generated cost agrees with canonical J-cost on each prime orbit. -/
def PRCCharacterPrimeDirectionCalibrated
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq
      (costFromCharacter χ (primeDirection p hp))
      (onRatioOrbit (primeDirection p hp))

/-- Sharper target A: the two-point calibration at orbit `2` must force
calibration on every prime direction. This is the exact place where the present
surface lacks control of independent prime axes. -/
def PRCTwoCalibrationForcesPrimeCalibrationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) →
        PRCCharacterPrimeDirectionCalibrated χ

/-- Sharper target B: once every prime direction is calibrated, the character
cost propagates to every rational direction. This is the unique-factorization
side of the rigidity problem. -/
def PRCPrimeCalibrationPropagationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        ∀ q : RatioOrbit,
          RatioOrbit.crossEq (costFromCharacter χ q) (onRatioOrbit q)

theorem onRatioOrbit_congr {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (onRatioOrbit a) (onRatioOrbit b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [onRatioOrbit_toRat, onRatioOrbit_toRat, h]

theorem jcost_eq_forces_same_or_reciprocal {a b : RatioOrbit}
    (ha : a.toRat ≠ 0) (hb : b.toRat ≠ 0)
    (h : RatioOrbit.crossEq (onRatioOrbit a) (onRatioOrbit b)) :
    RatioOrbit.crossEq a b ∨
      RatioOrbit.crossEq a (RatioOrbit.recip b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  rw [onRatioOrbit_toRat, onRatioOrbit_toRat] at h
  rw [RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat]
  have hsum : a.toRat + a.toRat⁻¹ = b.toRat + b.toRat⁻¹ := by
    linarith
  have hprod :
      (a.toRat - b.toRat) * (a.toRat * b.toRat - 1) = 0 := by
    have hmul :=
      congrArg (fun t : ℚ => t * (a.toRat * b.toRat)) hsum
    field_simp [ha, hb] at hmul
    ring_nf at hmul ⊢
    linarith
  rcases mul_eq_zero.mp hprod with hsame | hrec
  · left
    linarith
  · right
    have hmul : a.toRat * b.toRat = 1 := by
      linarith
    have hb_inv : b.toRat * b.toRat⁻¹ = 1 := by
      field_simp [hb]
    calc
      a.toRat = a.toRat * (b.toRat * b.toRat⁻¹) := by
        rw [hb_inv, mul_one]
      _ = (a.toRat * b.toRat) * b.toRat⁻¹ := by
        ring
      _ = b.toRat⁻¹ := by
        rw [hmul, one_mul]

theorem primeDirection_toRat_ne_zero
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    (primeDirection p hp).toRat ≠ 0 := by
  have hpNat : p.toNat ≠ 0 := by
    intro hzero
    apply hp.1
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  unfold primeDirection orbitDirection RatioOrbit.toRat
  simp [SignedOrbit.ofOrbit_toInt, DistinctionNat.one_toNat, hpNat]

theorem primeDirection_toRat
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    (primeDirection p hp).toRat = (p.toNat : ℚ) := by
  unfold primeDirection orbitDirection RatioOrbit.toRat
  simp [SignedOrbit.ofOrbit_toInt, DistinctionNat.one_toNat]

theorem twoOrbit_primeOrbit :
    DistinctionNat.primeOrbit twoOrbit := by
  rw [DistinctionNat.primeOrbit_iff_toNat_no_nontrivial_factor]
  constructor
  · rw [twoOrbit_toNat]
    norm_num
  · constructor
    · rw [twoOrbit_toNat]
      norm_num
    · intro hfac
      rcases hfac with ⟨a, b, _ha0, _hb0, ha1, hb1, hmul⟩
      have hprime : Nat.Prime 2 := by decide
      have hmul2 : a * b = 2 := by
        simpa [twoOrbit_toNat] using hmul
      have hadvd : a ∣ 2 := ⟨b, hmul2.symm⟩
      rcases hprime.eq_one_or_self_of_dvd a hadvd with ha | ha
      · exact ha1 ha
      · have hb : b = 1 := by
          rw [ha] at hmul2
          omega
        exact hb1 hb

/-- The three-step orbit position, used as the canonical non-`2` prime witness. -/
def threeOrbit : DistinctionNat :=
  DistinctionNat.succ twoOrbit

@[simp] theorem threeOrbit_toNat :
    threeOrbit.toNat = 3 := by
  unfold threeOrbit
  rw [DistinctionNat.toNat_succ, twoOrbit_toNat]

theorem threeOrbit_primeOrbit :
    DistinctionNat.primeOrbit threeOrbit := by
  rw [DistinctionNat.primeOrbit_iff_toNat_no_nontrivial_factor]
  constructor
  · rw [threeOrbit_toNat]
    norm_num
  · constructor
    · rw [threeOrbit_toNat]
      norm_num
    · intro hfac
      rcases hfac with ⟨a, b, _ha0, _hb0, ha1, hb1, hmul⟩
      have hprime : Nat.Prime 3 := by decide
      have hmul3 : a * b = 3 := by
        simpa [threeOrbit_toNat] using hmul
      have hadvd : a ∣ 3 := ⟨b, hmul3.symm⟩
      rcases hprime.eq_one_or_self_of_dvd a hadvd with ha | ha
      · exact ha1 ha
      · have hb : b = 1 := by
          rw [ha] at hmul3
          omega
        exact hb1 hb

theorem threeOrbit_ne_twoOrbit :
    threeOrbit ≠ twoOrbit := by
  intro h
  have hnat := congrArg DistinctionNat.toNat h
  rw [threeOrbit_toNat, twoOrbit_toNat] at hnat
  norm_num at hnat

theorem orbitDirection_toRat
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero) :
    (orbitDirection p hp).toRat = (p.toNat : ℚ) := by
  unfold orbitDirection RatioOrbit.toRat
  simp [SignedOrbit.ofOrbit_toInt, DistinctionNat.one_toNat]

theorem primeDirection_not_crossEq_recip
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    ¬ RatioOrbit.crossEq
      (primeDirection p hp)
      (RatioOrbit.recip (primeDirection p hp)) := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    primeDirection_toRat] at h
  have hpNat0 : p.toNat ≠ 0 := by
    intro hzero
    apply hp.1
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hpNatQ0 : (p.toNat : ℚ) ≠ 0 := by
    exact_mod_cast hpNat0
  have hsqQ : (p.toNat : ℚ) * (p.toNat : ℚ) = 1 := by
    have hmul := congrArg (fun t : ℚ => t * (p.toNat : ℚ)) h
    field_simp [hpNatQ0] at hmul
    ring_nf at hmul ⊢
    exact hmul
  have hsqNat : p.toNat * p.toNat = 1 := by
    exact_mod_cast hsqQ
  have hle : p.toNat ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ p.toNat := by omega
    have hprodge : 2 ≤ p.toNat * p.toNat := by
      calc
        2 ≤ 2 * 2 := by norm_num
        _ ≤ p.toNat * p.toNat := Nat.mul_le_mul hge hge
    omega
  have hpOne : p.toNat = 1 := by omega
  exact hp.2.1 ((DistinctionNat.unit_iff_toNat_eq_one p).mpr hpOne)

theorem orbitDirection_nonunit_not_crossEq_recip
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero)
    (hunit : ¬ DistinctionNat.unit p) :
    ¬ RatioOrbit.crossEq
      (orbitDirection p hp)
      (RatioOrbit.recip (orbitDirection p hp)) := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    orbitDirection_toRat] at h
  have hpNat0 : p.toNat ≠ 0 := by
    intro hzero
    apply hp
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hpNatQ0 : (p.toNat : ℚ) ≠ 0 := by
    exact_mod_cast hpNat0
  have hsqQ : (p.toNat : ℚ) * (p.toNat : ℚ) = 1 := by
    have hmul := congrArg (fun t : ℚ => t * (p.toNat : ℚ)) h
    field_simp [hpNatQ0] at hmul
    ring_nf at hmul ⊢
    exact hmul
  have hsqNat : p.toNat * p.toNat = 1 := by
    exact_mod_cast hsqQ
  have hle : p.toNat ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ p.toNat := by omega
    have hprodge : 2 ≤ p.toNat * p.toNat := by
      calc
        2 ≤ 2 * 2 := by norm_num
        _ ≤ p.toNat * p.toNat := Nat.mul_le_mul hge hge
    omega
  have hpOne : p.toNat = 1 := by omega
  exact hunit ((DistinctionNat.unit_iff_toNat_eq_one p).mpr hpOne)

theorem orbit_succ_ne_zero (p : DistinctionNat) :
    DistinctionNat.succ p ≠ DistinctionNat.zero := by
  intro h
  exact DistinctionNat.zero_ne_succ p h.symm

theorem orbitDirection_succ_crossEq_add_one
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero) :
    RatioOrbit.crossEq
      (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))
      (RatioOrbit.add (orbitDirection p hp) RatioOrbit.one) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq]
  rw [RatioOrbit.add_toRat, RatioOrbit.one_toRat,
    orbitDirection_toRat, orbitDirection_toRat, DistinctionNat.toNat_succ]
  norm_num

theorem RatioOrbit.add_right_one_cancel {a b : RatioOrbit}
    (h : RatioOrbit.crossEq
      (RatioOrbit.add a RatioOrbit.one)
      (RatioOrbit.add b RatioOrbit.one)) :
    RatioOrbit.crossEq a b := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [RatioOrbit.add_toRat, RatioOrbit.add_toRat, RatioOrbit.one_toRat] at h
  linarith

/-- Native trace carried by an orbit position, defined by recursion on the
δ-orbit rather than by importing verifier `Nat` as object theory. -/
def orbitPositionTrace : DistinctionNat → Trace
  | DistinctionNat.zero => Trace.empty
  | DistinctionNat.succ n => Trace.step (orbitPositionTrace n)

theorem orbitPositionTrace_add_extends_left
    (p r : DistinctionNat) :
    Trace.Extends (orbitPositionTrace p) (orbitPositionTrace (p + r)) := by
  induction r with
  | zero =>
      rw [DistinctionNat.add_zero_eq]
      exact Trace.extends_refl (orbitPositionTrace p)
  | succ r ih =>
      rw [DistinctionNat.add_succ_eq]
      rcases ih with ⟨suffix, hsuffix⟩
      refine ⟨Trace.step suffix, ?_⟩
      simp [Trace.step, orbitPositionTrace, hsuffix]

theorem orbitPositionTrace_add_extends_right
    (p r : DistinctionNat) :
    Trace.Extends (orbitPositionTrace r) (orbitPositionTrace (p + r)) := by
  rw [DistinctionNat.add_comm p r]
  exact orbitPositionTrace_add_extends_left r p

theorem orbitPositionTrace_extends_of_toNat_le
    {p r : DistinctionNat} (hpr : p.toNat ≤ r.toNat) :
    Trace.Extends (orbitPositionTrace p) (orbitPositionTrace r) := by
  let k : DistinctionNat := DistinctionNat.ofNat (r.toNat - p.toNat)
  have hsum : p + k = r := by
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_add, DistinctionNat.toNat_ofNat]
    omega
  rw [← hsum]
  exact orbitPositionTrace_add_extends_left p k

theorem orbitPositionTrace_comparable
    (p r : DistinctionNat) :
    Trace.Extends (orbitPositionTrace p) (orbitPositionTrace r) ∨
      Trace.Extends (orbitPositionTrace r) (orbitPositionTrace p) := by
  by_cases hpr : p.toNat ≤ r.toNat
  · exact Or.inl (orbitPositionTrace_extends_of_toNat_le hpr)
  · have hrp : r.toNat ≤ p.toNat := by omega
    exact Or.inr (orbitPositionTrace_extends_of_toNat_le hrp)

/-- Two prime axes are trace-connected when their native orbit traces admit a
common finite δ-extension. -/
def PRCPrimeAxisTraceConnected
    (p : DistinctionNat) (_hp : DistinctionNat.primeOrbit p)
    (r : DistinctionNat) (_hr : DistinctionNat.primeOrbit r) : Prop :=
  ∃ T : Trace,
    Trace.Extends (orbitPositionTrace p) T ∧
      Trace.Extends (orbitPositionTrace r) T

theorem PRCPrimeAxisTraceConnected_proved
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p)
    (r : DistinctionNat) (hr : DistinctionNat.primeOrbit r) :
    PRCPrimeAxisTraceConnected p hp r hr := by
  exact ⟨orbitPositionTrace (p + r),
    orbitPositionTrace_add_extends_left p r,
    orbitPositionTrace_add_extends_right p r⟩

/-- A character has global cost orientation when every rational direction is
sent either to itself or to its reciprocal. Since J-cost is reciprocal-symmetric,
this is exactly the orientation information needed for cost propagation. -/
def PRCCharacterGlobalCostOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q : RatioOrbit,
    RatioOrbit.crossEq (χ q) q ∨
      RatioOrbit.crossEq (χ q) (RatioOrbit.recip q)

/-- Sharper propagation blocker: prime calibration must force a coherent global
orientation. Without this, independent prime inversions can preserve prime
costs while breaking composite costs. -/
def PRCPrimeCalibrationForcesGlobalOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterGlobalCostOrientation χ

/-- Prime-axis orientation is coherent when the character chooses the same
orientation on every native prime direction: all identity or all reciprocal. -/
def PRCCharacterPrimeOrientationCoherent
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) ∨
  (∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp))
      (RatioOrbit.recip (primeDirection p hp)))

def twoPrimeDirection : RatioOrbit :=
  primeDirection twoOrbit twoOrbit_primeOrbit

@[simp] theorem twoPrimeDirection_toRat :
    twoPrimeDirection.toRat = 2 := by
  unfold twoPrimeDirection
  rw [primeDirection_toRat, twoOrbit_toNat]
  norm_num

/-- Distinguished-prime branch control: once the branch at orbit `2` is known,
the same branch holds on every native prime axis. This is the one-axis version
of coherent prime orientation. -/
def PRCCharacterTwoPrimeBranchControlsPrimes
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection →
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) ∧
  (RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) →
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)))

/-- Identity-iff-two normal form: identity orientation on a native prime axis is
equivalent to identity orientation on the distinguished orbit-`2` prime axis. -/
def PRCCharacterPrimeIdentityIffTwoPrimeIdentity
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ↔
      RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection

/-- One-sided normal form: identity at any calibrated prime axis forces
identity at the distinguished orbit-`2` prime axis. The reverse implication is
recovered at target level by applying the same statement to the reciprocal twist
of the character. -/
def PRCCharacterPrimeIdentityForcesTwoPrimeIdentity
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
      RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection

/-- Contrapositive branch normal form: if the distinguished orbit-`2` prime axis
is reciprocal-oriented, no native prime axis may be identity-oriented. -/
def PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) →
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      ¬ RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)

/-- Witness form of the orbit-`2` branch obstruction: reciprocal orientation at
the distinguished prime axis cannot coexist with even one identity-oriented
native prime witness. This is the atomic two-specific mixed-witness blocker. -/
def PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) →
    (∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) →
      False

/-- The exact mixed branch configuration that would refute the orbit-`2`
witness exclusion: the distinguished prime axis is reciprocal-oriented while
some native prime axis remains identity-oriented. -/
def PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) ∧
    ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)

/-- Sharpened mixed branch configuration: the identity-oriented native prime
witness is explicitly not the distinguished orbit-`2` axis. -/
def PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) ∧
    ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      p ≠ twoOrbit ∧
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)

/-- Concrete two-adic axis-twist form: orbit `2` is reciprocal-oriented while
every native prime axis other than `2` is identity-oriented. This is the obvious
countermodel one would construct from a native two-adic valuation. -/
def PRCCharacterTwoAdicAxisTwist
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) ∧
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      p ≠ twoOrbit →
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)

/-- Uncalibrated construction target for the two-adic axis twist. Pass 115 proves
the prime-calibration field is automatic once this branch behavior is carried by
a ratio character. -/
def PRCTwoAdicAxisTwistRatioCharacter : Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterTwoAdicAxisTwist χ

/-- Verifier-backed section from rationals to ratio orbits. This is deliberately
not a new PRC primitive; it is used to test whether the current character
interface already admits a classical rational countermodel. -/
def ratioOrbitOfRat (x : ℚ) : RatioOrbit where
  num := ⟨DistinctionNat.ofNat x.num.toNat,
    DistinctionNat.ofNat (-x.num).toNat⟩
  den := DistinctionNat.ofNat x.den
  den_ne_zero := by
    intro h
    have hnat := congrArg DistinctionNat.toNat h
    rw [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_zero] at hnat
    exact x.den_nz hnat

theorem ratioOrbitOfRat_toRat (x : ℚ) :
    (ratioOrbitOfRat x).toRat = x := by
  unfold ratioOrbitOfRat RatioOrbit.toRat SignedOrbit.toInt
  rw [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_ofNat,
    DistinctionNat.toNat_ofNat]
  have hnum :
      ((x.num.toNat : ℕ) : ℤ) - (((-x.num).toNat : ℕ) : ℤ) =
        x.num := by
    omega
  rw [hnum]
  exact Rat.num_div_den x

/-- The ratio-orbit display of `-1`, used to expose the missing signed-unit
calibration in prime-to-global orientation propagation. -/
noncomputable def negativeOneRatio : RatioOrbit :=
  ratioOrbitOfRat (-1)

@[simp] theorem negativeOneRatio_toRat :
    negativeOneRatio.toRat = -1 := by
  rw [negativeOneRatio, ratioOrbitOfRat_toRat]

/-- A character is calibrated on the signed unit when it fixes the ratio orbit
`-1`. Prime-direction data alone cannot force this. -/
def PRCCharacterSignedUnitCalibrated
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ negativeOneRatio) negativeOneRatio

/-- Exact signed-ratio decomposition needed after pass 279: every nonzero raw
ratio is either a positive orbit numerator times the reciprocal denominator, or
the signed unit times such a positive ratio. -/
def PRCSignedRatioDecompositionTarget : Prop :=
  ∀ q : RatioOrbit,
    q.toRat ≠ 0 →
      (∃ n d : DistinctionNat,
        ∃ hn : n ≠ DistinctionNat.zero,
        ∃ hd : d ≠ DistinctionNat.zero,
          RatioOrbit.crossEq q
            (RatioOrbit.mul (orbitDirection n hn)
              (RatioOrbit.recip (orbitDirection d hd)))) ∨
      (∃ n d : DistinctionNat,
        ∃ hn : n ≠ DistinctionNat.zero,
        ∃ hd : d ≠ DistinctionNat.zero,
          RatioOrbit.crossEq q
            (RatioOrbit.mul negativeOneRatio
              (RatioOrbit.mul (orbitDirection n hn)
                (RatioOrbit.recip (orbitDirection d hd)))))

theorem PRCSignedRatioDecompositionTarget_proved :
    PRCSignedRatioDecompositionTarget := by
  intro q hq
  have hnumInt : q.num.toInt ≠ 0 := by
    intro hzero
    apply hq
    unfold RatioOrbit.toRat
    rw [hzero]
    norm_num
  have hn : q.num.abs ≠ DistinctionNat.zero :=
    SignedOrbit.abs_ne_zero_of_toInt_ne_zero hnumInt
  by_cases hnonneg : q.num.nonnegFlag = true
  · left
    refine ⟨q.num.abs, q.den, hn, q.den_ne_zero, ?_⟩
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      RatioOrbit.recip_toRat, orbitDirection_toRat, orbitDirection_toRat]
    unfold RatioOrbit.toRat
    have habs : (q.num.abs.toNat : ℤ) = q.num.toInt := by
      rw [SignedOrbit.abs_toNat]
      exact Int.ofNat_natAbs_of_nonneg
        ((SignedOrbit.nonnegFlag_eq_true_iff q.num).mp hnonneg)
    have hden : (q.den.toNat : ℚ) ≠ 0 := q.den_cast_ne_zero
    rw [show ((q.num.abs.toNat : ℚ) : ℚ) =
        ((q.num.toInt : ℤ) : ℚ) by exact_mod_cast habs]
    field_simp [hden]
  · right
    have hflagFalse : q.num.nonnegFlag = false := by
      cases hflag : q.num.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hnonneg hflag
    refine ⟨q.num.abs, q.den, hn, q.den_ne_zero, ?_⟩
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      negativeOneRatio_toRat, RatioOrbit.mul_toRat, RatioOrbit.recip_toRat,
      orbitDirection_toRat, orbitDirection_toRat]
    unfold RatioOrbit.toRat
    have hneg : q.num.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff q.num).mp hflagFalse
    have habs : (q.num.abs.toNat : ℤ) = -q.num.toInt := by
      rw [SignedOrbit.abs_toNat]
      exact Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
    have hden : (q.den.toNat : ℚ) ≠ 0 := q.den_cast_ne_zero
    rw [show ((q.num.abs.toNat : ℚ) : ℚ) =
        (-q.num.toInt : ℤ) by exact_mod_cast habs]
    field_simp [hden]
    norm_num

/-- Absolute-value character on verifier rational displays. It is a quotient
respecting ratio character, but it erases the sign of `-1`. -/
noncomputable def absValueCharacter (q : RatioOrbit) : RatioOrbit :=
  ratioOrbitOfRat |q.toRat|

@[simp] theorem absValueCharacter_toRat (q : RatioOrbit) :
    (absValueCharacter q).toRat = |q.toRat| := by
  rw [absValueCharacter, ratioOrbitOfRat_toRat]

theorem absValueCharacter_ratio_character :
    PRCRatioCharacter absValueCharacter where
  unit := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, absValueCharacter_toRat,
      RatioOrbit.one_toRat]
    norm_num
  multiplicative := by
    intro x y
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    simp [absValueCharacter_toRat, RatioOrbit.mul_toRat, abs_mul]
  reciprocal := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    simp [absValueCharacter_toRat, RatioOrbit.recip_toRat, abs_inv]
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, absValueCharacter_toRat,
      absValueCharacter_toRat, DistinctionNat.normalizeRatio_toRat]
  nonzero_preserving := by
    intro q hq
    rw [absValueCharacter_toRat]
    exact abs_ne_zero.mpr hq

theorem absValueCharacter_prime_identity :
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (absValueCharacter (primeDirection p hp))
        (primeDirection p hp) := by
  intro p hp
  rw [RatioOrbit.crossEq_iff_toRat_eq, absValueCharacter_toRat,
    primeDirection_toRat]
  exact abs_of_nonneg (by exact_mod_cast Nat.zero_le p.toNat)

theorem absValueCharacter_prime_orientation_coherent :
    PRCCharacterPrimeOrientationCoherent absValueCharacter :=
  Or.inl absValueCharacter_prime_identity

theorem absValueCharacter_prime_calibrated :
    PRCCharacterPrimeDirectionCalibrated absValueCharacter := by
  intro p hp
  exact onRatioOrbit_congr (absValueCharacter_prime_identity p hp)

theorem absValueCharacter_two_cost_calibrated :
    RatioOrbit.crossEq (costFromCharacter absValueCharacter two)
      (onRatioOrbit two) := by
  have hcost := absValueCharacter_prime_calibrated twoOrbit twoOrbit_primeOrbit
  simpa [twoPrimeDirection, primeDirection] using hcost

theorem absValueCharacter_negative_one_cost_not_canonical :
    ¬ RatioOrbit.crossEq (costFromCharacter absValueCharacter negativeOneRatio)
      (onRatioOrbit negativeOneRatio) := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat,
    absValueCharacter_toRat, onRatioOrbit_toRat, negativeOneRatio_toRat] at h
  norm_num at h

theorem PRCNativeCostCharacterRigidityTarget_refuted :
    ¬ PRCNativeCostCharacterRigidityTarget := by
  intro hrigid
  exact absValueCharacter_negative_one_cost_not_canonical
    (hrigid absValueCharacter absValueCharacter_ratio_character
      absValueCharacter_two_cost_calibrated negativeOneRatio)

theorem absValueCharacter_not_signed_unit_calibrated :
    ¬ PRCCharacterSignedUnitCalibrated absValueCharacter := by
  intro hsign
  rw [PRCCharacterSignedUnitCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
    absValueCharacter_toRat, negativeOneRatio_toRat] at hsign
  norm_num at hsign

/-- Classical verifier two-adic branch twist on rational displays. It fixes the
odd-prime axes and inverts the orbit-`2` exponent. -/
noncomputable def twoAdicTwistRat (x : ℚ) : ℚ :=
  x * (2 : ℚ) ^ (-2 * padicValRat 2 x)

theorem twoAdicTwistRat_one :
    twoAdicTwistRat 1 = 1 := by
  unfold twoAdicTwistRat
  have h : padicValRat 2 (1 : ℚ) = 0 := by
    norm_num [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  rw [h]
  norm_num

theorem twoAdicTwistRat_mul (x y : ℚ) :
    twoAdicTwistRat (x * y) =
      twoAdicTwistRat x * twoAdicTwistRat y := by
  unfold twoAdicTwistRat
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · rw [padicValRat.mul hx hy]
      have hbase : (2 : ℚ) ≠ 0 := by norm_num
      have hexp :
          -2 * (padicValRat 2 x + padicValRat 2 y) =
            (-2 * padicValRat 2 x) + (-2 * padicValRat 2 y) := by
        ring
      rw [hexp]
      rw [zpow_add₀ hbase]
      ring

theorem twoAdicTwistRat_inv (x : ℚ) :
    twoAdicTwistRat x⁻¹ = (twoAdicTwistRat x)⁻¹ := by
  unfold twoAdicTwistRat
  by_cases hx : x = 0
  · simp [hx]
  · rw [padicValRat.inv]
    have hbase : (2 : ℚ) ≠ 0 := by norm_num
    have hxpow : (2 : ℚ) ^ (-2 * padicValRat 2 x) ≠ 0 :=
      zpow_ne_zero _ hbase
    have hexp :
        -2 * (-padicValRat 2 x) = -(-2 * padicValRat 2 x) := by
      ring
    rw [hexp, zpow_neg]
    field_simp [hx, hxpow]

theorem twoAdicTwistRat_ne_zero {x : ℚ}
    (hx : x ≠ 0) :
    twoAdicTwistRat x ≠ 0 := by
  unfold twoAdicTwistRat
  have hbase : (2 : ℚ) ≠ 0 := by norm_num
  exact mul_ne_zero hx (zpow_ne_zero _ hbase)

theorem twoAdicTwistRat_two :
    twoAdicTwistRat 2 = (2 : ℚ)⁻¹ := by
  unfold twoAdicTwistRat
  have h : padicValRat 2 (2 : ℚ) = 1 :=
    padicValRat.self (by norm_num : 1 < 2)
  rw [h]
  norm_num

theorem padicValRat_two_primeDirection_eq_zero_of_ne_two
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p)
    (hpne : p ≠ twoOrbit) :
    padicValRat 2 (primeDirection p hp).toRat = 0 := by
  rw [primeDirection_toRat]
  rw [show (p.toNat : ℚ) = ((p.toNat : ℤ) : ℚ) by norm_num]
  rw [padicValRat.of_int]
  have hInt : padicValInt 2 (p.toNat : ℤ) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdivZ
    have hdivNat : 2 ∣ p.toNat := by
      exact_mod_cast hdivZ
    have hdivNat' : twoOrbit.toNat ∣ p.toNat := by
      rw [twoOrbit_toNat]
      exact hdivNat
    have hdiv : DistinctionNat.divides twoOrbit p :=
      (DistinctionNat.divides_iff_toNat_dvd twoOrbit p).mpr hdivNat'
    rcases DistinctionNat.unit_or_eq_of_divides_prime hp hdiv with hunit | heq
    · rw [DistinctionNat.unit_iff_toNat_eq_one, twoOrbit_toNat] at hunit
      norm_num at hunit
    · exact hpne heq.symm
  exact_mod_cast hInt

theorem twoAdicTwistRat_primeDirection_of_ne_two
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p)
    (hpne : p ≠ twoOrbit) :
    twoAdicTwistRat (primeDirection p hp).toRat =
      (primeDirection p hp).toRat := by
  unfold twoAdicTwistRat
  rw [padicValRat_two_primeDirection_eq_zero_of_ne_two hp hpne]
  norm_num

/-- Ratio-orbit realization of the verifier two-adic branch twist. -/
noncomputable def twoAdicAxisTwistCharacter (q : RatioOrbit) : RatioOrbit :=
  ratioOrbitOfRat (twoAdicTwistRat q.toRat)

theorem twoAdicAxisTwistCharacter_toRat (q : RatioOrbit) :
    (twoAdicAxisTwistCharacter q).toRat =
      twoAdicTwistRat q.toRat := by
  unfold twoAdicAxisTwistCharacter
  exact ratioOrbitOfRat_toRat _

theorem twoAdicAxisTwistCharacter_ratio_character :
    PRCRatioCharacter twoAdicAxisTwistCharacter where
  unit := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat,
      RatioOrbit.one_toRat]
    exact twoAdicTwistRat_one
  multiplicative := by
    intro x y
    rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat,
      RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
      twoAdicAxisTwistCharacter_toRat, twoAdicAxisTwistCharacter_toRat]
    exact twoAdicTwistRat_mul x.toRat y.toRat
  reciprocal := by
    intro x
    rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat,
      RatioOrbit.recip_toRat, RatioOrbit.recip_toRat,
      twoAdicAxisTwistCharacter_toRat]
    exact twoAdicTwistRat_inv x.toRat
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat,
      twoAdicAxisTwistCharacter_toRat, DistinctionNat.normalizeRatio_toRat]
  nonzero_preserving := by
    intro q hq
    rw [twoAdicAxisTwistCharacter_toRat]
    exact twoAdicTwistRat_ne_zero hq

theorem twoAdicAxisTwistCharacter_branch :
    PRCCharacterTwoAdicAxisTwist twoAdicAxisTwistCharacter := by
  constructor
  · rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat,
      RatioOrbit.recip_toRat, twoPrimeDirection_toRat]
    exact twoAdicTwistRat_two
  · intro p hp hpne
    rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat]
    exact twoAdicTwistRat_primeDirection_of_ne_two hp hpne

theorem PRCTwoAdicAxisTwistRatioCharacter_constructed :
    PRCTwoAdicAxisTwistRatioCharacter :=
  ⟨twoAdicAxisTwistCharacter,
    twoAdicAxisTwistCharacter_ratio_character,
    twoAdicAxisTwistCharacter_branch⟩

/-- δ-native cost non-forcing (headline blocker, stated exactly).

There is a PRC ratio character `χ` that fixes the orientation of every prime
axis except orbit `2`, yet inverts the orbit-`2` axis. Concretely `χ` is the
two-adic axis twist `x ↦ x · 2^(-2·v₂(x))`, which is reciprocal-symmetric,
multiplicative, normalized, and nonzero-preserving (a full `PRCRatioCharacter`),
identity-oriented on every odd prime, and reciprocal-oriented on `2`.

Consequence: the δ-native reciprocal-character axioms together with identity
orientation on *every other prime* do not force identity orientation at `2`.
The multiplicative group of the rational carrier is free abelian on the prime
axes, so each axis carries an independent orientation choice. The canonical
reciprocal cost `J` is therefore underdetermined on the rational (`RatioOrbit`)
carrier: it is the all-identity orientation, but the all-identity choice is not
forced by the discrete arithmetic.

This is the exact reason J-forcing requires the continuous completion. On
`(0,∞)` the calibration condition (a second derivative at the unit) plus
continuity propagate one curvature value along the connected line
(`IndisputableMonolith.Cost.FunctionalEquation.law_of_logic_forces_jcost`). The
discrete carrier has neither a derivative nor connectivity, so the per-prime
orientation freedom witnessed here survives. The forward repair is to derive the
unit calibration from the cost of a single δ act on the completion, not to pin
each prime axis by hypothesis. -/
theorem prc_native_cost_orientation_underdetermined :
    ∃ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ ∧
      (∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
        p ≠ twoOrbit →
          RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) ∧
      ¬ RatioOrbit.crossEq (twoAdicAxisTwistCharacter twoPrimeDirection)
          twoPrimeDirection := by
  refine ⟨twoAdicAxisTwistCharacter, twoAdicAxisTwistCharacter_ratio_character,
    twoAdicAxisTwistCharacter_branch.2, ?_⟩
  intro hId
  have hself :
      RatioOrbit.crossEq twoPrimeDirection
        (RatioOrbit.recip twoPrimeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hId)
      twoAdicAxisTwistCharacter_branch.1
  exact primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself

/-- The canonical non-two prime direction used for the first concrete
two-adic mixed-composite test. -/
def threePrimeDirection : RatioOrbit :=
  primeDirection threeOrbit threeOrbit_primeOrbit

@[simp] theorem threePrimeDirection_toRat :
    threePrimeDirection.toRat = 3 := by
  unfold threePrimeDirection
  rw [primeDirection_toRat, threeOrbit_toNat]
  norm_num

/-- Classical verifier three-adic branch twist on rational displays. It fixes
the non-`3` prime axes and inverts the orbit-`3` exponent. This is the base-`3`
analogue of `twoAdicTwistRat`; it exists to show that calibrating the native
cost at one prime (here, agreement with J at `2`) does not propagate to the
other prime axes (here, `3`). -/
noncomputable def threeAdicTwistRat (x : ℚ) : ℚ :=
  x * (3 : ℚ) ^ (-2 * padicValRat 3 x)

theorem threeAdicTwistRat_one :
    threeAdicTwistRat 1 = 1 := by
  unfold threeAdicTwistRat
  have h : padicValRat 3 (1 : ℚ) = 0 := by
    norm_num [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  rw [h]
  norm_num

theorem threeAdicTwistRat_mul (x y : ℚ) :
    threeAdicTwistRat (x * y) =
      threeAdicTwistRat x * threeAdicTwistRat y := by
  unfold threeAdicTwistRat
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · rw [padicValRat.mul hx hy]
      have hbase : (3 : ℚ) ≠ 0 := by norm_num
      have hexp :
          -2 * (padicValRat 3 x + padicValRat 3 y) =
            (-2 * padicValRat 3 x) + (-2 * padicValRat 3 y) := by
        ring
      rw [hexp]
      rw [zpow_add₀ hbase]
      ring

theorem threeAdicTwistRat_inv (x : ℚ) :
    threeAdicTwistRat x⁻¹ = (threeAdicTwistRat x)⁻¹ := by
  unfold threeAdicTwistRat
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · simp [hx]
  · rw [padicValRat.inv]
    have hbase : (3 : ℚ) ≠ 0 := by norm_num
    have hxpow : (3 : ℚ) ^ (-2 * padicValRat 3 x) ≠ 0 :=
      zpow_ne_zero _ hbase
    have hexp :
        -2 * (-padicValRat 3 x) = -(-2 * padicValRat 3 x) := by
      ring
    rw [hexp, zpow_neg]
    field_simp [hx, hxpow]

theorem threeAdicTwistRat_ne_zero {x : ℚ}
    (hx : x ≠ 0) :
    threeAdicTwistRat x ≠ 0 := by
  unfold threeAdicTwistRat
  have hbase : (3 : ℚ) ≠ 0 := by norm_num
  exact mul_ne_zero hx (zpow_ne_zero _ hbase)

theorem threeAdicTwistRat_three :
    threeAdicTwistRat 3 = (3 : ℚ)⁻¹ := by
  unfold threeAdicTwistRat
  have h : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (by norm_num : 1 < 3)
  rw [h]
  norm_num

theorem padicValRat_three_primeDirection_eq_zero_of_ne_three
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p)
    (hpne : p ≠ threeOrbit) :
    padicValRat 3 (primeDirection p hp).toRat = 0 := by
  rw [primeDirection_toRat]
  rw [show (p.toNat : ℚ) = ((p.toNat : ℤ) : ℚ) by norm_num]
  rw [padicValRat.of_int]
  have hInt : padicValInt 3 (p.toNat : ℤ) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdivZ
    have hdivNat : 3 ∣ p.toNat := by
      exact_mod_cast hdivZ
    have hdivNat' : threeOrbit.toNat ∣ p.toNat := by
      rw [threeOrbit_toNat]
      exact hdivNat
    have hdiv : DistinctionNat.divides threeOrbit p :=
      (DistinctionNat.divides_iff_toNat_dvd threeOrbit p).mpr hdivNat'
    rcases DistinctionNat.unit_or_eq_of_divides_prime hp hdiv with hunit | heq
    · rw [DistinctionNat.unit_iff_toNat_eq_one, threeOrbit_toNat] at hunit
      norm_num at hunit
    · exact hpne heq.symm
  exact_mod_cast hInt

theorem threeAdicTwistRat_primeDirection_of_ne_three
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p)
    (hpne : p ≠ threeOrbit) :
    threeAdicTwistRat (primeDirection p hp).toRat =
      (primeDirection p hp).toRat := by
  unfold threeAdicTwistRat
  rw [padicValRat_three_primeDirection_eq_zero_of_ne_three hp hpne]
  norm_num

/-- Ratio-orbit realization of the verifier three-adic branch twist. -/
noncomputable def threeAdicAxisTwistCharacter (q : RatioOrbit) : RatioOrbit :=
  ratioOrbitOfRat (threeAdicTwistRat q.toRat)

theorem threeAdicAxisTwistCharacter_toRat (q : RatioOrbit) :
    (threeAdicAxisTwistCharacter q).toRat =
      threeAdicTwistRat q.toRat := by
  unfold threeAdicAxisTwistCharacter
  exact ratioOrbitOfRat_toRat _

theorem threeAdicAxisTwistCharacter_ratio_character :
    PRCRatioCharacter threeAdicAxisTwistCharacter where
  unit := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeAdicAxisTwistCharacter_toRat,
      RatioOrbit.one_toRat]
    exact threeAdicTwistRat_one
  multiplicative := by
    intro x y
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeAdicAxisTwistCharacter_toRat,
      RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
      threeAdicAxisTwistCharacter_toRat, threeAdicAxisTwistCharacter_toRat]
    exact threeAdicTwistRat_mul x.toRat y.toRat
  reciprocal := by
    intro x
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeAdicAxisTwistCharacter_toRat,
      RatioOrbit.recip_toRat, RatioOrbit.recip_toRat,
      threeAdicAxisTwistCharacter_toRat]
    exact threeAdicTwistRat_inv x.toRat
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeAdicAxisTwistCharacter_toRat,
      threeAdicAxisTwistCharacter_toRat, DistinctionNat.normalizeRatio_toRat]
  nonzero_preserving := by
    intro q hq
    rw [threeAdicAxisTwistCharacter_toRat]
    exact threeAdicTwistRat_ne_zero hq

theorem threeAdicAxisTwistCharacter_two_identity :
    RatioOrbit.crossEq (threeAdicAxisTwistCharacter twoPrimeDirection)
      twoPrimeDirection := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, threeAdicAxisTwistCharacter_toRat]
  simpa [twoPrimeDirection] using
    threeAdicTwistRat_primeDirection_of_ne_three twoOrbit_primeOrbit
      (threeOrbit_ne_twoOrbit).symm

theorem threeAdicAxisTwistCharacter_three_reciprocal :
    RatioOrbit.crossEq (threeAdicAxisTwistCharacter threePrimeDirection)
      (RatioOrbit.recip threePrimeDirection) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, threeAdicAxisTwistCharacter_toRat,
    RatioOrbit.recip_toRat, threePrimeDirection_toRat]
  exact threeAdicTwistRat_three

/-- δ-native cost non-forcing, complementary axis (headline blocker, stated
exactly).

There is a PRC ratio character `χ` (the three-adic axis twist
`x ↦ x · 3^(-2·v₃(x))`) that agrees with the canonical cost J at the prime `2`
(identity orientation there) yet inverts the orbit-`3` axis. Together with
`prc_native_cost_orientation_underdetermined` (which fixes every odd prime and
flips `2`), this proves the orientation freedom is genuinely per-prime: pinning
the native cost at one prime does not pin it at another.

Consequence for the calibration repair: no finite set of prime calibrations can
force J on the rational carrier, because each remaining prime axis is still a
free orientation choice. The continuous `law_of_logic_forces_jcost` escapes this
only because its calibration hypothesis is a second-derivative condition at the
unit, which constrains the cost on a full neighborhood (uncountably many points)
at once. This is the exact sense in which J-forcing requires the completion and
not the discrete carrier, and it pins the forward repair to deriving that
single neighborhood-level calibration from the cost of one δ act. -/
theorem prc_single_prime_calibration_insufficient :
    ∃ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ ∧
      RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection ∧
      ¬ RatioOrbit.crossEq (χ threePrimeDirection) threePrimeDirection := by
  refine ⟨threeAdicAxisTwistCharacter,
    threeAdicAxisTwistCharacter_ratio_character,
    threeAdicAxisTwistCharacter_two_identity, ?_⟩
  intro hId
  have hself :
      RatioOrbit.crossEq threePrimeDirection
        (RatioOrbit.recip threePrimeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hId)
      threeAdicAxisTwistCharacter_three_reciprocal
  exact primeDirection_not_crossEq_recip threeOrbit threeOrbit_primeOrbit hself

/-! ### Classification: every prime axis is an independent orientation freedom

Passes 329 and 330 each exhibit one ratio character that flips a single prime
axis (`2`, resp. `3`) while fixing the others. They are two witnesses of one
structural fact: the multiplicative group of the rational carrier is free
abelian on the prime orbits, so each prime axis carries an independent
orientation choice. The following collapses both witnesses into a single theorem
parameterized by an arbitrary prime orbit. It supersedes the per-prime
`_refuted` treadmill: there is one base-parameterized twist character per prime,
not a separate construction per case. -/

/-- A prime orbit displays as a `Nat` prime. Bridge from the δ-native primality
predicate to `Nat.Prime`, with no import of Nat prime theory into the predicate
itself. -/
theorem natPrime_toNat_of_primeOrbit {p : DistinctionNat}
    (hp : DistinctionNat.primeOrbit p) : Nat.Prime p.toNat := by
  rw [DistinctionNat.primeOrbit_iff_toNat_no_nontrivial_factor] at hp
  obtain ⟨h0, h1, hfac⟩ := hp
  rw [Nat.prime_def]
  refine ⟨by omega, ?_⟩
  intro m hm
  obtain ⟨k, hk⟩ := hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  · refine Or.inr ?_
    by_cases hk1 : k = 1
    · rw [hk, hk1, mul_one]
    · exfalso
      apply hfac
      have hm0 : m ≠ 0 := by
        rintro rfl; rw [zero_mul] at hk; exact h0 hk
      have hk0 : k ≠ 0 := by
        rintro rfl; rw [mul_zero] at hk; exact h0 hk
      exact ⟨m, k, hm0, hk0, hm1, hk1, hk.symm⟩

/-- Base-parameterized axis twist on rational displays: invert the exponent on
the prime axis `b`, fix every other prime axis. For `b = 2` this is
`twoAdicTwistRat`; for `b = 3` it is `threeAdicTwistRat`. -/
noncomputable def axisTwistRat (b : ℕ) (x : ℚ) : ℚ :=
  x * (b : ℚ) ^ (-2 * padicValRat b x)

theorem axisTwistRat_base_ne_zero (b : ℕ) [Fact (Nat.Prime b)] :
    (b : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime b).pos.ne'

theorem axisTwistRat_one (b : ℕ) [Fact (Nat.Prime b)] :
    axisTwistRat b 1 = 1 := by
  unfold axisTwistRat
  rw [padicValRat.one]
  norm_num

theorem axisTwistRat_mul (b : ℕ) [Fact (Nat.Prime b)] (x y : ℚ) :
    axisTwistRat b (x * y) = axisTwistRat b x * axisTwistRat b y := by
  unfold axisTwistRat
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · rw [padicValRat.mul hx hy]
      have hbase : (b : ℚ) ≠ 0 := axisTwistRat_base_ne_zero b
      have hexp :
          -2 * (padicValRat b x + padicValRat b y) =
            (-2 * padicValRat b x) + (-2 * padicValRat b y) := by ring
      rw [hexp, zpow_add₀ hbase]
      ring

theorem axisTwistRat_inv (b : ℕ) [Fact (Nat.Prime b)] (x : ℚ) :
    axisTwistRat b x⁻¹ = (axisTwistRat b x)⁻¹ := by
  unfold axisTwistRat
  by_cases hx : x = 0
  · simp [hx]
  · rw [padicValRat.inv]
    have hbase : (b : ℚ) ≠ 0 := axisTwistRat_base_ne_zero b
    have hxpow : (b : ℚ) ^ (-2 * padicValRat b x) ≠ 0 := zpow_ne_zero _ hbase
    have hexp : -2 * (-padicValRat b x) = -(-2 * padicValRat b x) := by ring
    rw [hexp, zpow_neg]
    field_simp [hx, hxpow]

theorem axisTwistRat_ne_zero (b : ℕ) [Fact (Nat.Prime b)] {x : ℚ}
    (hx : x ≠ 0) : axisTwistRat b x ≠ 0 := by
  unfold axisTwistRat
  exact mul_ne_zero hx (zpow_ne_zero _ (axisTwistRat_base_ne_zero b))

theorem axisTwistRat_self (b : ℕ) [Fact (Nat.Prime b)] :
    axisTwistRat b (b : ℚ) = (b : ℚ)⁻¹ := by
  unfold axisTwistRat
  have hb : 1 < b := (Fact.out : Nat.Prime b).one_lt
  have hbase : (b : ℚ) ≠ 0 := axisTwistRat_base_ne_zero b
  rw [padicValRat.self hb, show (-2 * (1 : ℤ)) = (-2 : ℤ) by ring]
  nth_rewrite 1 [show (b : ℚ) = (b : ℚ) ^ (1 : ℤ) by rw [zpow_one]]
  rw [← zpow_add₀ hbase, show (1 : ℤ) + (-2 : ℤ) = -1 by ring, zpow_neg_one]

/-- Off-axis primes are fixed by the `b`-axis twist: if the evaluated prime orbit
`r` differs from the axis orbit `p`, the `p.toNat`-adic valuation of `r`'s
display vanishes. -/
theorem padicValRat_axis_primeDirection_eq_zero_of_ne
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p)
    {r : DistinctionNat} (hr : DistinctionNat.primeOrbit r)
    (hne : r ≠ p) :
    padicValRat p.toNat (primeDirection r hr).toRat = 0 := by
  haveI : Fact (Nat.Prime p.toNat) := ⟨natPrime_toNat_of_primeOrbit hp⟩
  rw [primeDirection_toRat, padicValRat.of_nat]
  norm_cast
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have hdiv : DistinctionNat.divides p r :=
    (DistinctionNat.divides_iff_toNat_dvd p r).mpr hdvd
  rcases DistinctionNat.unit_or_eq_of_divides_prime hr hdiv with hunit | heq
  · rw [DistinctionNat.unit_iff_toNat_eq_one] at hunit
    exact (natPrime_toNat_of_primeOrbit hp).ne_one hunit
  · exact hne heq.symm

/-- The ratio-orbit realization of the `b`-axis twist, `b = p.toNat`. -/
noncomputable def axisTwistCharacter (p : DistinctionNat) (q : RatioOrbit) :
    RatioOrbit :=
  ratioOrbitOfRat (axisTwistRat p.toNat q.toRat)

theorem axisTwistCharacter_toRat (p : DistinctionNat) (q : RatioOrbit) :
    (axisTwistCharacter p q).toRat = axisTwistRat p.toNat q.toRat := by
  unfold axisTwistCharacter
  exact ratioOrbitOfRat_toRat _

theorem axisTwistCharacter_ratio_character
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p) :
    PRCRatioCharacter (axisTwistCharacter p) := by
  haveI : Fact (Nat.Prime p.toNat) := ⟨natPrime_toNat_of_primeOrbit hp⟩
  exact {
    unit := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, axisTwistCharacter_toRat,
        RatioOrbit.one_toRat]
      exact axisTwistRat_one p.toNat
    multiplicative := by
      intro x y
      rw [RatioOrbit.crossEq_iff_toRat_eq, axisTwistCharacter_toRat,
        RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
        axisTwistCharacter_toRat, axisTwistCharacter_toRat]
      exact axisTwistRat_mul p.toNat x.toRat y.toRat
    reciprocal := by
      intro x
      rw [RatioOrbit.crossEq_iff_toRat_eq, axisTwistCharacter_toRat,
        RatioOrbit.recip_toRat, RatioOrbit.recip_toRat,
        axisTwistCharacter_toRat]
      exact axisTwistRat_inv p.toNat x.toRat
    normalized_invariant := by
      intro q
      rw [RatioOrbit.crossEq_iff_toRat_eq, axisTwistCharacter_toRat,
        axisTwistCharacter_toRat, DistinctionNat.normalizeRatio_toRat]
    nonzero_preserving := by
      intro q hq
      rw [axisTwistCharacter_toRat]
      exact axisTwistRat_ne_zero p.toNat hq }

theorem axisTwistCharacter_off_axis_identity
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p)
    {r : DistinctionNat} (hr : DistinctionNat.primeOrbit r)
    (hne : r ≠ p) :
    RatioOrbit.crossEq (axisTwistCharacter p (primeDirection r hr))
      (primeDirection r hr) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, axisTwistCharacter_toRat]
  unfold axisTwistRat
  rw [padicValRat_axis_primeDirection_eq_zero_of_ne hp hr hne]
  norm_num

theorem axisTwistCharacter_on_axis_reciprocal
    {p : DistinctionNat} (hp : DistinctionNat.primeOrbit p) :
    RatioOrbit.crossEq (axisTwistCharacter p (primeDirection p hp))
      (RatioOrbit.recip (primeDirection p hp)) := by
  haveI : Fact (Nat.Prime p.toNat) := ⟨natPrime_toNat_of_primeOrbit hp⟩
  rw [RatioOrbit.crossEq_iff_toRat_eq, axisTwistCharacter_toRat,
    RatioOrbit.recip_toRat, primeDirection_toRat]
  exact axisTwistRat_self p.toNat

/-- **δ-native cost non-forcing, classified (headline).**

For *every* prime orbit `p` there is a PRC ratio character that fixes the
orientation of every other prime axis yet inverts the orbit-`p` axis. This is one
theorem in place of the per-prime witnesses `prc_native_cost_orientation_under-
determined` (the `p = 2` case) and `prc_single_prime_calibration_insufficient`
(the `p = 3` case): the orientation freedom is genuinely per-prime, on every
axis at once.

Consequence: no finite (indeed, no proper) set of prime calibrations forces `J`
on the rational carrier, because every axis outside the set remains a free
orientation. The canonical reciprocal cost `J` is the all-identity orientation,
and the all-identity choice is not forced by the discrete arithmetic. J-forcing
therefore requires the continuous completion, where the calibration hypothesis of
`law_of_logic_forces_jcost` constrains a full neighborhood of the unit at once
rather than one axis at a time. -/
theorem prc_every_prime_axis_orientation_free
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    ∃ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ ∧
      (∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
        r ≠ p →
          RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)) ∧
      ¬ RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) := by
  refine ⟨axisTwistCharacter p, axisTwistCharacter_ratio_character hp,
    fun r hr hne => axisTwistCharacter_off_axis_identity hp hr hne, ?_⟩
  intro hId
  have hself :
      RatioOrbit.crossEq (primeDirection p hp)
        (RatioOrbit.recip (primeDirection p hp)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hId)
      (axisTwistCharacter_on_axis_reciprocal hp)
  exact primeDirection_not_crossEq_recip p hp hself

/-! ### Completion-side companion: calibration is the binding constraint

The two blockers above act on the discrete rational carrier. The following
companion isolates the same constraint on the continuous completion, where
`law_of_logic_forces_jcost` lives. The point is to identify, as an exact Lean
witness, which hypothesis of that theorem actually does the forcing.

The composition law (the RCL) is, after the substitution `g = F + 1`, the
d'Alembert identity `g(xy) + g(x/y) = 2 g(x) g(y)`. Its continuous solutions
are `g(x) = cosh(λ · log x)`, i.e. `F(x) = (x^λ + x^{-λ})/2 - 1` for any real
`λ ≥ 0`. Reciprocal symmetry, normalization, and continuity hold for the whole
family; only the calibration `G''(0) = λ² = 1` selects `λ = 1`. So on the
completion the algebraic laws fix the *form* of the cost but not its *scale*. -/

/-- A second member of the cost family: `F₂(x) = (x² + x⁻²)/2 - 1`, the
`λ = 2` cost. Its log-coordinate curvature at the unit is `4`, not `1`. -/
noncomputable def costLambdaTwo (x : ℝ) : ℝ := (x ^ 2 + (x ^ 2)⁻¹) / 2 - 1

/-- **Completion-side non-forcing (headline blocker, stated exactly).**

There is a function `F : ℝ → ℝ` (the `λ = 2` cost `(x² + x⁻²)/2 - 1`) that
satisfies every hypothesis of `law_of_logic_forces_jcost` *except* calibration
(reciprocal symmetry, normalization, the composition law (RCL), and continuity on
the positive reals) yet is not the canonical cost `Cost.Jcost`. Therefore the
calibration hypothesis `IsCalibrated` is load-bearing and cannot be dropped: the
composition law and the other algebraic laws do not, by themselves, force J even
on the continuous completion.

This is the continuum analogue of `prc_native_cost_orientation_underdetermined`
and `prc_single_prime_calibration_insufficient`. Read together: on the rational
carrier orientation is free per prime; on the completion the scale (the curvature
`λ²` at the unit) is free. In both regimes the binding constraint is a
calibration, not the algebra. Consequently "δ forces J" can only mean "δ forces
the cost family `(x^λ + x^{-λ})/2 - 1`, and a separately supplied unit
calibration selects `λ = 1`." Whether δ supplies that unit calibration is the
open joint (live track T1); this theorem proves it is genuinely needed, i.e. it
is not already implied by the composition law. -/
theorem composition_law_without_calibration_does_not_force_jcost :
    ∃ F : ℝ → ℝ,
      Cost.FunctionalEquation.IsReciprocalCost F ∧
      Cost.FunctionalEquation.IsNormalized F ∧
      Cost.FunctionalEquation.SatisfiesCompositionLaw F ∧
      ContinuousOn F (Set.Ioi 0) ∧
      F ≠ Cost.Jcost := by
  refine ⟨costLambdaTwo, ?_, ?_, ?_, ?_, ?_⟩
  · -- reciprocal symmetry
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    unfold costLambdaTwo
    field_simp
    ring
  · -- normalization F 1 = 0
    show ((1 : ℝ) ^ 2 + ((1 : ℝ) ^ 2)⁻¹) / 2 - 1 = 0
    norm_num
  · -- composition law (RCL)
    intro x y hx hy
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hy0 : y ≠ 0 := ne_of_gt hy
    unfold costLambdaTwo
    field_simp
    ring
  · -- continuity on the positive reals
    unfold costLambdaTwo
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.div_const
    refine ContinuousOn.add ((continuous_pow 2).continuousOn) ?_
    refine ContinuousOn.inv₀ ((continuous_pow 2).continuousOn) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hx))
  · -- F ≠ Jcost, witnessed at x = 2
    intro h
    have h2 := congrFun h 2
    unfold costLambdaTwo Cost.Jcost at h2
    norm_num at h2

/-- The full one-parameter cost family `F_λ(x) = (x^λ + x^(-λ))/2 - 1`, using
real powers. `λ = 1` is `Cost.Jcost`; `λ = 2` is `costLambdaTwo`. -/
noncomputable def costLambda (l x : ℝ) : ℝ := (x ^ l + x ^ (-l)) / 2 - 1

/-- **Calibration is an irreducible scale choice (headline blocker, stated
exactly).**

For every exponent `λ > 0`, the cost `F_λ(x) = (x^λ + x^(-λ))/2 - 1` satisfies
reciprocal symmetry, normalization, the composition law (RCL), and continuity on
the positive reals. These are exactly the hypotheses of
`law_of_logic_forces_jcost` other than calibration. So the composition law's
continuous solution set is the entire one-parameter family `{F_λ : λ > 0}`, not a
single function. The calibration `G''(0) = λ² = 1` is the lone datum that
collapses the family to J (the `λ = 1` member). Combined with
`composition_law_without_calibration_does_not_force_jcost` (the `λ = 2` instance,
which is distinct from J), this shows the scale is a genuine continuum of choices
that the algebra cannot prefer between. The forward program (T1) is therefore
exactly: supply `λ = 1` from a δ-native curvature, or accept "δ forces J up to a
choice of cost scale." -/
theorem composition_law_admits_full_scale_family (l : ℝ) (hl : 0 < l) :
    Cost.FunctionalEquation.IsReciprocalCost (costLambda l) ∧
    Cost.FunctionalEquation.IsNormalized (costLambda l) ∧
    Cost.FunctionalEquation.SatisfiesCompositionLaw (costLambda l) ∧
    ContinuousOn (costLambda l) (Set.Ioi 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- reciprocal symmetry
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    unfold costLambda
    rw [Real.inv_rpow hx0, Real.inv_rpow hx0, ← Real.rpow_neg hx0,
      ← Real.rpow_neg hx0, neg_neg]
    ring
  · -- normalization F 1 = 0
    show ((1 : ℝ) ^ l + (1 : ℝ) ^ (-l)) / 2 - 1 = 0
    rw [Real.one_rpow, Real.one_rpow]
    norm_num
  · -- composition law (RCL)
    intro x y hx hy
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
    set a : ℝ := x ^ l with ha_def
    set b : ℝ := y ^ l with hb_def
    have ha : (0 : ℝ) < a := Real.rpow_pos_of_pos hx l
    have hb : (0 : ℝ) < b := Real.rpow_pos_of_pos hy l
    unfold costLambda
    rw [Real.mul_rpow hx0 hy0, Real.div_rpow hx0 hy0,
      Real.rpow_neg (le_of_lt (mul_pos hx hy)),
      Real.rpow_neg (le_of_lt (div_pos hx hy)),
      Real.rpow_neg hx0, Real.rpow_neg hy0,
      Real.mul_rpow hx0 hy0, Real.div_rpow hx0 hy0]
    rw [← ha_def, ← hb_def]
    field_simp
    ring
  · -- continuity on the positive reals
    unfold costLambda
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.div_const
    apply ContinuousOn.add
    · intro x hx
      exact (Real.continuousAt_rpow_const x l
        (Or.inl (ne_of_gt (Set.mem_Ioi.mp hx)))).continuousWithinAt
    · intro x hx
      exact (Real.continuousAt_rpow_const x (-l)
        (Or.inl (ne_of_gt (Set.mem_Ioi.mp hx)))).continuousWithinAt

/-- **Calibration is a multiplicative-automorphism gauge (headline blocker,
stated exactly).**

The whole cost family collapses to a single function pulled back along the
automorphism group of the positive reals under multiplication:

* `costLambda l x = Cost.Jcost (x ^ l)` for `x > 0`: every family member is J
  precomposed with the power map `φ_λ(x) = x^λ`;
* `φ_λ` is a multiplicative homomorphism (`(x·y)^λ = x^λ · y^λ`) fixing the unit
  (`1^λ = 1`), hence (for `λ ≠ 0`) an automorphism of `(ℝ_{>0}, ×)`.

Therefore the family `{F_λ}` is exactly the orbit of `Cost.Jcost` under the
automorphism group `Aut(ℝ_{>0}, ×) ≅ ℝˣ` (scalings `t ↦ λt` in log
coordinates). The δ-native structure determines the multiplicative group but no
preferred automorphism scale, and the composition law is preserved by every such
pullback (`composition_law_admits_full_scale_family`). The calibration
`λ² = 1` is the choice of unit speed for this gauge group.

This is the exact, structural reason branch (a) of T1 cannot succeed on the
δ-native data alone: a single δ successor act delivers a secant value
`F_λ(2) = (2^λ + 2^{-λ})/2 - 1`, not the curvature limit, and that secant is
λ-dependent (distinctness of `λ = 1` from `λ = 2` is witnessed by
`composition_law_without_calibration_does_not_force_jcost`, the `λ = 2` member
that differs from J). The curvature, being the unit speed of an automorphism
gauge, is a normalization rather than a consequence of the group structure. The
honest terminal claim is: δ forces J up to a multiplicative-automorphism gauge,
and a unit calibration fixes the gauge. -/
theorem calibration_is_mul_automorphism_gauge :
    (∀ l x : ℝ, 0 < x → costLambda l x = Cost.Jcost (x ^ l)) ∧
    (∀ l x y : ℝ, 0 < x → 0 < y → (x * y) ^ l = x ^ l * y ^ l) ∧
    (∀ l : ℝ, (1 : ℝ) ^ l = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l x hx
    unfold costLambda Cost.Jcost
    rw [Real.rpow_neg (le_of_lt hx)]
  · intro l x y hx hy
    exact Real.mul_rpow (le_of_lt hx) (le_of_lt hy)
  · intro l
    exact Real.one_rpow l

/-- In log coordinates the family member `costLambda l` is `cosh(l·t) - 1`:
`G (costLambda l) t = Real.cosh (l * t) - 1`. -/
theorem G_costLambda (l : ℝ) :
    Cost.FunctionalEquation.G (costLambda l) = fun t => Real.cosh (l * t) - 1 := by
  funext t
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  simp only [Cost.FunctionalEquation.G, costLambda]
  rw [Real.rpow_def_of_pos hpos l, Real.rpow_def_of_pos hpos (-l), Real.log_exp,
    Real.cosh_eq, mul_comm t l, show t * (-l) = -(l * t) by ring]

/-- **The calibration value of `costLambda l` is exactly `l²`.**

The log-coordinate curvature at the unit (the quantity `IsCalibrated` fixes to
`1`) is `deriv (deriv (G (costLambda l))) 0 = l²`. This is the exact content of
"calibration selects `λ = 1`": the calibration condition is `l² = 1`. -/
theorem calibration_value_costLambda (l : ℝ) :
    deriv (deriv (Cost.FunctionalEquation.G (costLambda l))) 0 = l ^ 2 := by
  have hlin : ∀ t : ℝ, HasDerivAt (fun t => l * t) l t := by
    intro t; simpa using (hasDerivAt_id t).const_mul l
  have hd1 : ∀ t : ℝ,
      HasDerivAt (fun t => Real.cosh (l * t) - 1) (Real.sinh (l * t) * l) t := by
    intro t; exact ((hlin t).cosh).sub_const 1
  have hderiv1 : deriv (fun t => Real.cosh (l * t) - 1)
      = fun t => Real.sinh (l * t) * l := by
    funext t; exact (hd1 t).deriv
  have hd2 : HasDerivAt (fun t => Real.sinh (l * t) * l)
      (Real.cosh (l * 0) * l * l) 0 := ((hlin 0).sinh).mul_const l
  rw [G_costLambda l, hderiv1, hd2.deriv]
  simp [Real.cosh_zero]
  ring

/-- **J is the unique calibrated member of the cost family (exact).**

`costLambda l` satisfies the calibration condition of `law_of_logic_forces_jcost`
iff `l² = 1`. So among the gauge family `{F_λ}`, calibration is precisely the
equation that selects `λ = ±1`; with `λ > 0` it selects `λ = 1`, the member
equal to `Cost.Jcost` (`costLambda 1 x = Cost.Jcost x` for `x > 0`). This is the
within-family selection that, combined with
`calibration_is_mul_automorphism_gauge`, makes the stratification exact:
δ + algebra force the family; calibration `l² = 1` selects J; and the value of
the calibration constant (the gauge) is not itself fixed by δ. -/
theorem isCalibrated_costLambda_iff (l : ℝ) :
    Cost.FunctionalEquation.IsCalibrated (costLambda l) ↔ l ^ 2 = 1 := by
  unfold Cost.FunctionalEquation.IsCalibrated
  rw [calibration_value_costLambda l]

/-- For positive exponents, the calibrated member is exactly `λ = 1`. -/
theorem isCalibrated_costLambda_pos_iff {l : ℝ} (hl : 0 < l) :
    Cost.FunctionalEquation.IsCalibrated (costLambda l) ↔ l = 1 := by
  rw [isCalibrated_costLambda_iff l]
  constructor
  · intro h
    nlinarith [sq_nonneg (l - 1), sq_nonneg (l + 1)]
  · intro h; rw [h]; norm_num

/-- The `λ = 1` member is `Cost.Jcost` on the positive reals, and it is
calibrated. -/
theorem costLambda_one_eq_jcost (x : ℝ) (hx : 0 < x) :
    costLambda 1 x = Cost.Jcost x := by
  unfold costLambda Cost.Jcost
  rw [Real.rpow_one, Real.rpow_neg (le_of_lt hx), Real.rpow_one]

/-- **The cost family is a single gauge orbit: the automorphism action is
transitive (exact).**

For any two positive exponents `λ, μ` and any `x > 0`,
`costLambda l x = costLambda m (x ^ (l / m))`. That is, the multiplicative
automorphism `x ↦ x^(l/m)` of `(ℝ_{>0}, ×)` carries the family member `F_μ` onto
`F_λ`. Since the action is transitive (any member reaches any other), the family
`{F_λ : λ > 0}` is a single homogeneous orbit under
`Aut(ℝ_{>0}, ×)`, with no member distinguished by the algebra. This is the
precise mathematical content of "the calibration is a gauge": J is singled out
only by the external unit calibration `λ = 1`, never by the composition law,
which is invariant along the whole orbit. It strengthens
`calibration_is_mul_automorphism_gauge` (each member is `J ∘ (·^λ)`) to the orbit
being homogeneous (any member is any other, post-automorphism), so there is no
algebraically preferred basepoint to call canonical without importing the unit. -/
theorem costLambda_gauge_transitive (l m x : ℝ) (hm : 0 < m) (hx : 0 < x) :
    costLambda l x = costLambda m (x ^ (l / m)) := by
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
  have e1 : (l / m) * m = l := div_mul_cancel₀ l (ne_of_gt hm)
  have e2 : (l / m) * (-m) = -l := by rw [mul_neg, e1]
  unfold costLambda
  rw [← Real.rpow_mul hx0, ← Real.rpow_mul hx0, e1, e2]

/-- **The gauge parameterization is faithful: the automorphism action is free
(exact).**

Distinct positive exponents give distinct costs: if `costLambda l = costLambda m`
as functions and `l, m > 0`, then `l = m`. (Proof: the log-coordinate curvature
at the unit is `λ²` by `calibration_value_costLambda`; equal functions have equal
curvature, so `l² = m²`, and positivity gives `l = m`.)

Together with `costLambda_gauge_transitive` (transitivity) this says the family
`{F_λ : λ > 0}` is a **torsor** (principal homogeneous space) under the gauge
group: the action is both free (here) and transitive (there). That is the exact,
gold-standard sense in which the calibration is a gauge: the admissible costs,
modulo the calibration datum, form a faithful continuum of choices isomorphic to
the gauge group itself, with no algebraically preferred member. Calibration
`λ = 1` removes exactly this one real degree of freedom to single out `J`. -/
theorem costLambda_injective {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (h : ∀ x : ℝ, costLambda l x = costLambda m x) : l = m := by
  have hG : Cost.FunctionalEquation.G (costLambda l)
      = Cost.FunctionalEquation.G (costLambda m) := by
    funext t; simp only [Cost.FunctionalEquation.G]; rw [h]
  have hsq : l ^ 2 = m ^ 2 := by
    have e := calibration_value_costLambda l
    rw [hG, calibration_value_costLambda m] at e
    exact e.symm
  have h1 : (l - m) * (l + m) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h1 with h0 | h0
  · linarith
  · linarith

/-- **A single point-evaluation fixes the gauge: one real datum suffices.**

This is strictly sharper than `costLambda_injective`. That theorem needs the
two costs to agree *everywhere* (equivalently, equal log-coordinate curvature)
to conclude `l = m`. Here we need agreement at a **single** point `x₀ > 1`:
if `F_l(x₀) = F_m(x₀)` and `l, m > 0`, then `l = m`.

Operationally this is the load-bearing statement of the gauge story. The
family `{F_λ : λ > 0}` is a torsor under the multiplicative-automorphism group
(`costLambda_gauge_transitive` + `costLambda_injective`), so fixing the gauge
costs exactly one real degree of freedom. This theorem says that degree of
freedom is pinned by one measurement: the value of the cost at any single
distinction ratio `x₀ ≠ 1`. The recognition quantum, viewed through δ, is
precisely this one datum; no further structure is needed to single out `J`
once it is supplied.

Proof: write `a = x₀^l`, `b = x₀^m`; both exceed `1` (base `> 1`, exponent
`> 0`). Equality of `F` gives `a + a⁻¹ = b + b⁻¹`, i.e. `(a-b)(ab-1) = 0`.
Since `ab > 1`, the second factor is nonzero, so `a = b`, and strict
monotonicity of `t ↦ x₀^t` (base `> 1`) gives `l = m`. -/
theorem costLambda_single_point_calibration {x₀ l m : ℝ}
    (hx₀ : 1 < x₀) (hl : 0 < l) (hm : 0 < m)
    (h : costLambda l x₀ = costLambda m x₀) : l = m := by
  have hx0pos : (0 : ℝ) < x₀ := lt_trans one_pos hx₀
  have hapos : 0 < x₀ ^ l := Real.rpow_pos_of_pos hx0pos l
  have hbpos : 0 < x₀ ^ m := Real.rpow_pos_of_pos hx0pos m
  have ha1 : 1 < x₀ ^ l := (Real.one_lt_rpow_iff_of_pos hx0pos).mpr (Or.inl ⟨hx₀, hl⟩)
  have hb1 : 1 < x₀ ^ m := (Real.one_lt_rpow_iff_of_pos hx0pos).mpr (Or.inl ⟨hx₀, hm⟩)
  unfold costLambda at h
  rw [Real.rpow_neg (le_of_lt hx0pos) l, Real.rpow_neg (le_of_lt hx0pos) m] at h
  have h2 : x₀ ^ l + (x₀ ^ l)⁻¹ = x₀ ^ m + (x₀ ^ m)⁻¹ := by linarith
  have hane : x₀ ^ l ≠ 0 := ne_of_gt hapos
  have hbne : x₀ ^ m ≠ 0 := ne_of_gt hbpos
  -- Clear denominators: a + a⁻¹ = b + b⁻¹ becomes the factored cubic identity.
  have hexpand : (x₀ ^ l) ^ 2 * x₀ ^ m + x₀ ^ m
      = x₀ ^ l * (x₀ ^ m) ^ 2 + x₀ ^ l := by
    have lhs : (x₀ ^ l + (x₀ ^ l)⁻¹) * (x₀ ^ l * x₀ ^ m)
        = (x₀ ^ l) ^ 2 * x₀ ^ m + x₀ ^ m := by field_simp
    have rhs : (x₀ ^ m + (x₀ ^ m)⁻¹) * (x₀ ^ l * x₀ ^ m)
        = x₀ ^ l * (x₀ ^ m) ^ 2 + x₀ ^ l := by field_simp
    rw [← lhs, ← rhs, h2]
  have key : (x₀ ^ l - x₀ ^ m) * (x₀ ^ l * x₀ ^ m - 1) = 0 := by
    linear_combination hexpand
  have hab : x₀ ^ l = x₀ ^ m := by
    rcases mul_eq_zero.mp key with hd | hd
    · linarith
    · exfalso; nlinarith [ha1, hb1, hapos, hbpos]
  have hle : l ≤ m := (Real.rpow_le_rpow_left_iff hx₀).mp (le_of_eq hab)
  have hge : m ≤ l := (Real.rpow_le_rpow_left_iff hx₀).mp (le_of_eq hab.symm)
  linarith

/-- **Honest stratification of the load-bearing cost joint (single exact
object).**

This structure states, as one Lean object, exactly what is forced and what is a
gauge at the joint where the δ-program forces (or fails to force) the cost
function J. Each field is discharged by a named theorem; nothing here is prose.

* `form_forced`: the algebraic laws (reciprocal symmetry, normalization, the
  composition law/RCL, continuity) hold for the entire one-parameter family
  `F_λ = costLambda λ`, `λ > 0`. So the algebra forces the cost *form*, not a
  single function. (`composition_law_admits_full_scale_family`.)
* `gauge_orbit`: that family is the orbit of `Cost.Jcost` under the automorphism
  group of `(ℝ_{>0}, ×)`: `F_λ(x) = J(x^λ)` with `x ↦ x^λ` multiplicative.
  (`calibration_is_mul_automorphism_gauge`.)
* `calibration_selects_jcost`: within the family, the calibration condition of
  `law_of_logic_forces_jcost` holds iff `λ = 1` (for `λ > 0`), and that member is
  `Cost.Jcost` on the positives. So calibration is exactly the within-form
  selector of J. (`isCalibrated_costLambda_pos_iff`, `costLambda_one_eq_jcost`.)
* `gauge_not_forced`: there is a member of the family (`λ = 2`) clearing every
  algebraic law yet differing from J, so the algebra alone does not fix the gauge
  (the calibration constant). (`composition_law_without_calibration_does_not_force_jcost`.)

Read together: δ and the algebraic laws force the cost form; calibration
`λ² = 1` selects J within it; and the value of the calibration constant is a
multiplicative-automorphism gauge that the δ structure does not pin. This is the
honest terminal statement of the joint. -/
structure PRCCostJointStratification : Prop where
  form_forced :
    ∀ l : ℝ, 0 < l →
      Cost.FunctionalEquation.IsReciprocalCost (costLambda l) ∧
      Cost.FunctionalEquation.IsNormalized (costLambda l) ∧
      Cost.FunctionalEquation.SatisfiesCompositionLaw (costLambda l) ∧
      ContinuousOn (costLambda l) (Set.Ioi 0)
  gauge_orbit :
    (∀ l x : ℝ, 0 < x → costLambda l x = Cost.Jcost (x ^ l)) ∧
    (∀ l x y : ℝ, 0 < x → 0 < y → (x * y) ^ l = x ^ l * y ^ l)
  calibration_selects_jcost :
    (∀ l : ℝ, 0 < l →
      (Cost.FunctionalEquation.IsCalibrated (costLambda l) ↔ l = 1)) ∧
    (∀ x : ℝ, 0 < x → costLambda 1 x = Cost.Jcost x)
  gauge_not_forced :
    ∃ F : ℝ → ℝ,
      Cost.FunctionalEquation.IsReciprocalCost F ∧
      Cost.FunctionalEquation.IsNormalized F ∧
      Cost.FunctionalEquation.SatisfiesCompositionLaw F ∧
      ContinuousOn F (Set.Ioi 0) ∧
      F ≠ Cost.Jcost

/-- The honest stratification of the cost joint holds, assembled from the
pass 331/331b/332/333 theorems. -/
theorem prc_cost_joint_stratification : PRCCostJointStratification where
  form_forced := composition_law_admits_full_scale_family
  gauge_orbit :=
    ⟨calibration_is_mul_automorphism_gauge.1,
      calibration_is_mul_automorphism_gauge.2.1⟩
  calibration_selects_jcost :=
    ⟨fun _ hl => isCalibrated_costLambda_pos_iff hl, costLambda_one_eq_jcost⟩
  gauge_not_forced := composition_law_without_calibration_does_not_force_jcost

/-- **Strength separation for J-forcing (single exact object).**

The program's central claim, stated as a checked proposition rather than a
docstring: J is *not* forced at δ-only carrier strength, but *is* selected at
completion (trace-closure) strength, and trace-closure is a strictly stronger
commitment than δ-only in the K1 ledger order. This is the type-level form of
"J is forced only on the continuous completion": the same forcing question
gets opposite answers at two strengths, with a genuine strengthening between
them.

* `delta_only_does_not_force`: on the δ-native rational carrier, for every
  prime orbit there is a PRC ratio character fixing every other prime axis and
  inverting that one, an orientation distinct from J's. So no δ-only datum
  forces J. (`prc_every_prime_axis_orientation_free`.)
* `completion_selects_jcost`: on the completion, within the forced cost form,
  the calibration condition holds iff `λ = 1`, selecting J.
  (`isCalibrated_costLambda_pos_iff`.)
* `strength_strictly_increases`: `deltaOnly < traceClosure` in the commitment
  order, so the strength that forces J strictly exceeds the strength at which it
  provably fails. (`StrengthTag.deltaOnly_lt_traceClosure`.)

Without the third field this would be two unrelated facts; with it the object
asserts that the gap between the failing strength and the forcing strength is
real and ordered, which is exactly the non-bookkeeping content. -/
structure PRCJCostStrengthSeparation : Prop where
  delta_only_does_not_force :
    ∀ (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p),
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
        (∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
          r ≠ p →
            RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)) ∧
        ¬ RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)
  completion_selects_jcost :
    ∀ l : ℝ, 0 < l →
      (Cost.FunctionalEquation.IsCalibrated (costLambda l) ↔ l = 1)
  strength_strictly_increases :
    StrengthTag.deltaOnly < StrengthTag.traceClosure

/-- The strength separation holds: δ-only fails to force J, the completion
selects it, and the completion strength is strictly stronger. No project-local
axioms. -/
theorem prc_jcost_strength_separation : PRCJCostStrengthSeparation where
  delta_only_does_not_force := prc_every_prime_axis_orientation_free
  completion_selects_jcost := fun _ hl => isCalibrated_costLambda_pos_iff hl
  strength_strictly_increases := StrengthTag.deltaOnly_lt_traceClosure

/-- **The gauge group acts on the entire cost-solution set (exact).**

The cost-joint stratification proves the `costLambda` family *is* a set of
solutions (`form_forced`: family ⊆ solutions) and exhibits one non-`J` solution
(`gauge_not_forced`). What it does not prove is that the gauge action stays
inside the solution set at all. This theorem supplies that: for every `a > 0`,
the gauge substitution `x ↦ x^a` carries any solution of the four algebraic
laws (reciprocal symmetry, normalization, the composition law/RCL, continuity
on the positives) to another solution of the same four laws.

This is the structural half of completeness. The full completeness claim is
`{four-law solutions} = {costLambda λ : λ > 0}` (the gauge orbit is the *entire*
residual freedom, not merely *some* of it). The family ⊆ solutions direction is
`form_forced`; the reverse needs (i) the gauge acting on all solutions (proved
here) and (ii) every solution being gauge-equivalent to a calibrated one, which
is the curvature-normalization fact isolated in
`PRCFourLawCompletenessTarget` below. With this theorem the solution set is
*gauge-stable*: it is a union of `Aut(ℝ_{>0}, ×)`-orbits, so the calibration
freedom is the only freedom that can possibly distinguish members. -/
theorem cost_laws_gauge_invariant {F : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hCont : ContinuousOn F (Set.Ioi 0)) :
    Cost.FunctionalEquation.IsReciprocalCost (fun x => F (x ^ a)) ∧
    Cost.FunctionalEquation.IsNormalized (fun x => F (x ^ a)) ∧
    Cost.FunctionalEquation.SatisfiesCompositionLaw (fun x => F (x ^ a)) ∧
    ContinuousOn (fun x => F (x ^ a)) (Set.Ioi 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxa : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
    show F (x ^ a) = F (x⁻¹ ^ a)
    rw [Real.inv_rpow (le_of_lt hx) a]
    exact hRecip _ hxa
  · show F ((1 : ℝ) ^ a) = 0
    rw [Real.one_rpow]; exact hNorm
  · intro x y hx hy
    have hxa : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
    have hya : (0 : ℝ) < y ^ a := Real.rpow_pos_of_pos hy a
    show F ((x * y) ^ a) + F ((x / y) ^ a)
        = 2 * F (x ^ a) * F (y ^ a) + 2 * F (x ^ a) + 2 * F (y ^ a)
    rw [Real.mul_rpow (le_of_lt hx) (le_of_lt hy),
        Real.div_rpow (le_of_lt hx) (le_of_lt hy) a]
    exact hComp _ _ hxa hya
  · have hf : ContinuousOn (fun x : ℝ => x ^ a) (Set.Ioi 0) :=
      (Real.continuous_rpow_const (le_of_lt ha)).continuousOn
    have hmaps : Set.MapsTo (fun x : ℝ => x ^ a) (Set.Ioi 0) (Set.Ioi 0) :=
      fun x hx => Real.rpow_pos_of_pos hx a
    exact hCont.comp hf hmaps

/-- **The isolated analytic blocker for four-law completeness (exact Prop).**

This is the one fact that, together with `cost_laws_gauge_invariant` and
`law_of_logic_forces_jcost`, would close completeness
(`{four-law solutions} ⊆ {costLambda λ}`). It says: every non-trivial solution
of the four algebraic laws is gauge-equivalent to a *calibrated* solution: that
is, there is a positive gauge exponent `c` that rescales `F` to unit log-curvature.

It is stated, not proved, because the proof requires the uncalibrated
d'Alembert classification (continuous solutions are `cosh(c·)` for a *free*
frequency `c`), whereas the existing `FunctionalEquation` pipeline bakes in the
calibration `c = 1` from the start (`dAlembert_cosh_solution` assumes
`deriv (deriv H) 0 = 1`). Generalizing that to a free frequency, and excluding
the oscillatory `cos(c·)` branch via the cost positivity, is a genuine piece of
analysis. Isolating it here as an exact statement, rather than asserting
completeness, is the honest terminal form of this track. -/
def PRCFourLawCompletenessTarget : Prop :=
  ∀ F : ℝ → ℝ,
    Cost.FunctionalEquation.IsReciprocalCost F →
    Cost.FunctionalEquation.IsNormalized F →
    Cost.FunctionalEquation.SatisfiesCompositionLaw F →
    ContinuousOn F (Set.Ioi 0) →
    (0 < deriv (deriv (Cost.FunctionalEquation.G F)) 0) →
    ∃ c : ℝ, 0 < c ∧
      Cost.FunctionalEquation.IsCalibrated (fun x => F (x ^ c⁻¹))

/-- **Four-law completeness, conditional on the isolated blocker (exact).**

Given the calibratability fact `PRCFourLawCompletenessTarget`, every non-trivial
solution of the four algebraic laws *is* a member of the `costLambda` family.
Combined with `composition_law_admits_full_scale_family` (family ⊆ solutions),
this is the biconditional: the four-law solution set with positive log-curvature
is *exactly* the gauge orbit `{costLambda c : c > 0}`. So the calibration unit
is provably the *only* residual freedom: nothing outside the gauge orbit
satisfies the laws. The hypothesis is the sole analytic input; the rest is the
rescaling reduction discharged through `law_of_logic_forces_jcost` and the
gauge-orbit identity `costLambda c x = J(x^c)`. -/
theorem cost_laws_complete_of_calibratable
    [Cost.FunctionalEquation.AczelSmoothnessPackage]
    (hTarget : PRCFourLawCompletenessTarget)
    {F : ℝ → ℝ}
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hκ : 0 < deriv (deriv (Cost.FunctionalEquation.G F)) 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → F x = costLambda c x := by
  obtain ⟨c, hc, hCalib⟩ := hTarget F hRecip hNorm hComp hCont hκ
  -- The rescaled solution `F̃(y) = F(y^(1/c))` satisfies all four laws (gauge
  -- invariance with exponent `c⁻¹`) and is calibrated (the hypothesis), so it
  -- equals `J` by `law_of_logic_forces_jcost`.
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  obtain ⟨hR, hN, hC, hCo⟩ := cost_laws_gauge_invariant hcinv hRecip hNorm hComp hCont
  have hJ : ∀ x : ℝ, 0 < x → F (x ^ c⁻¹) = Cost.Jcost x :=
    Cost.FunctionalEquation.law_of_logic_forces_jcost
      (fun x => F (x ^ c⁻¹)) hR hN hC hCalib hCo
  refine ⟨c, hc, ?_⟩
  intro x hx
  -- `F x = F((x^c)^(1/c)) = J(x^c) = costLambda c x`.
  have hxc : (0 : ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
  have hpow : (x ^ c) ^ c⁻¹ = x := by
    rw [← Real.rpow_mul (le_of_lt hx), mul_inv_cancel₀ (ne_of_gt hc), Real.rpow_one]
  calc F x = F ((x ^ c) ^ c⁻¹) := by rw [hpow]
    _ = Cost.Jcost (x ^ c) := hJ (x ^ c) hxc
    _ = costLambda c x := (calibration_is_mul_automorphism_gauge.1 c x hx).symm

/-- Second derivative of a left-scaled function at the origin: for `g`
with `deriv g` differentiable, `(t ↦ g(m·t))'' (0) = m² · g''(0)`. Pure
calculus; the scaling factor squares because it is pulled out once per
differentiation. Used to transport the calibration (log-curvature) of a cost
under the gauge substitution `x ↦ x^a`. -/
theorem deriv2_comp_mul_left_at_zero (g : ℝ → ℝ) (m : ℝ)
    (hg2 : Differentiable ℝ (deriv g)) :
    deriv (deriv (fun s => g (m * s))) 0 = m ^ 2 * deriv (deriv g) 0 := by
  have h1 : deriv (fun s => g (m * s)) = fun s => m * deriv g (m * s) := by
    funext s
    simpa [smul_eq_mul] using deriv_comp_mul_left m g s
  rw [h1]
  have hd : DifferentiableAt ℝ (fun s => deriv g (m * s)) 0 :=
    (hg2 (m * 0)).comp 0 (by fun_prop)
  rw [deriv_const_mul m hd]
  have h3 : deriv (fun s => deriv g (m * s)) 0 = m * deriv (deriv g) (m * 0) := by
    simpa [smul_eq_mul] using deriv_comp_mul_left m (deriv g) 0
  rw [h3]; simp only [mul_zero]; ring

/-- **The isolated analytic blocker is a theorem (T1′ discharged).**

Every positive-log-curvature solution of the four algebraic laws is
gauge-equivalent to a calibrated one. This proves `PRCFourLawCompletenessTarget`
outright, so the conditional `cost_laws_complete_of_calibratable` becomes
unconditional (`prc_four_law_completeness` below).

Proof: a four-law `F` has `G F = F ∘ exp` smooth, because `H F = G F + 1` is a
continuous d'Alembert solution and `AczelSmoothnessPackage` makes such solutions
`C^∞`. Let `κ = G F''(0) > 0` and `c = √κ`. The gauge substitution
`x ↦ x^{1/c}` sends `G F` to `t ↦ G F(t/c)`, whose second derivative at the
origin is `c⁻² · κ = 1` (`deriv2_comp_mul_left_at_zero`). So the rescaled cost
is calibrated. -/
theorem prc_four_law_completeness_target
    [Cost.FunctionalEquation.AczelSmoothnessPackage] :
    PRCFourLawCompletenessTarget := by
  intro F hRecip hNorm hComp hCont hκ
  set Gf := Cost.FunctionalEquation.G F with hGf_def
  set Hf := Cost.FunctionalEquation.H F with hHf_def
  -- H F is a continuous d'Alembert solution with H F 0 = 1.
  have h_H0 : Hf 0 = 1 := by
    show Cost.FunctionalEquation.H F 0 = 1
    simp only [Cost.FunctionalEquation.H, Cost.FunctionalEquation.G, Real.exp_zero]
    rw [hNorm]; ring
  have h_G_cont : Continuous Gf := by
    have h := ContinuousOn.comp_continuous hCont Real.continuous_exp
    have h' : Continuous (fun t => F (Real.exp t)) :=
      h (by intro t; exact Set.mem_Ioi.mpr (Real.exp_pos t))
    simpa [hGf_def, Cost.FunctionalEquation.G] using h'
  have h_H_cont : Continuous Hf := by
    simpa [hHf_def, Cost.FunctionalEquation.H] using h_G_cont.add continuous_const
  have hCoshAdd : Cost.FunctionalEquation.CoshAddIdentity F :=
    Cost.FunctionalEquation.composition_law_equiv_coshAdd F |>.mp hComp
  have h_direct : Cost.FunctionalEquation.DirectCoshAdd Gf :=
    Cost.FunctionalEquation.CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    have h_goal : (Gf (t + u) + 1) + (Gf (t - u) + 1)
        = 2 * (Gf t + 1) * (Gf u + 1) := by
      calc (Gf (t + u) + 1) + (Gf (t - u) + 1)
          = (Gf (t + u) + Gf (t - u)) + 2 := by ring
        _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by rw [hG]
        _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
    simpa [hHf_def, Cost.FunctionalEquation.H, hGf_def] using h_goal
  -- Smoothness, hence twice-differentiability of G F.
  have hHsmooth : ContDiff ℝ ⊤ Hf :=
    Cost.FunctionalEquation.aczel_dAlembert_smooth Hf h_H0 h_H_cont h_dAlembert
  have hGf_smooth : ContDiff ℝ ⊤ Gf := by
    have he : Gf = fun t => Hf t - 1 := by
      funext t; simp [hGf_def, hHf_def, Cost.FunctionalEquation.H]
    rw [he]; exact hHsmooth.sub contDiff_const
  have hGf_diff2 : Differentiable ℝ (deriv Gf) :=
    (contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp (hGf_smooth.of_le le_top)).2).1
  -- Curvature and the calibrating exponent.
  set c := Real.sqrt (deriv (deriv Gf) 0) with hc_def
  have hcpos : 0 < c := Real.sqrt_pos.mpr hκ
  have hc2 : c ^ 2 = deriv (deriv Gf) 0 := Real.sq_sqrt (le_of_lt hκ)
  refine ⟨c, hcpos, ?_⟩
  show deriv (deriv (Cost.FunctionalEquation.G (fun x => F (x ^ c⁻¹)))) 0 = 1
  have hGtilde :
      Cost.FunctionalEquation.G (fun x => F (x ^ c⁻¹)) = fun t => Gf (c⁻¹ * t) := by
    funext t
    show F ((Real.exp t) ^ c⁻¹) = Gf (c⁻¹ * t)
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, mul_comm t c⁻¹]
    simp [hGf_def, Cost.FunctionalEquation.G]
  rw [hGtilde, deriv2_comp_mul_left_at_zero Gf c⁻¹ hGf_diff2,
      inv_pow, ← hc2, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hcpos))]

/-- **Four-law completeness, unconditional (T1′ closed).**

Every positive-log-curvature solution of the four algebraic laws equals
`costLambda c` for some `c > 0`. With `composition_law_admits_full_scale_family`
(family ⊆ solutions) this is the biconditional: the positive-curvature four-law
solution set is *exactly* the gauge orbit `{costLambda c : c > 0}`. The
calibration unit is therefore provably the only residual freedom: nothing
outside the gauge orbit satisfies the laws. -/
theorem prc_four_law_completeness
    [Cost.FunctionalEquation.AczelSmoothnessPackage]
    {F : ℝ → ℝ}
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hκ : 0 < deriv (deriv (Cost.FunctionalEquation.G F)) 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → F x = costLambda c x :=
  cost_laws_complete_of_calibratable prc_four_law_completeness_target
    hRecip hNorm hComp hCont hκ

/-- **The residual cost freedom is exactly one positive real (gauge is a torsor).**

`prc_four_law_completeness` gives *existence* of a calibrating exponent
(`∃ c > 0`). This upgrades it to *unique* existence (`∃!`): every
positive-curvature four-law solution `F` equals `costLambda c` for one and only
one `c > 0`. So the gauge orbit is a torsor under the multiplicative-automorphism
group with no redundancy: the freedom δ leaves in the cost is precisely one
positive real, and that real is pinned by `F` itself. This is the exact
quantification of the program's "what is forced versus assumed": the cost *form*
is forced (the four laws plus positive curvature), and exactly one positive-real
*unit* is assumed, uniquely.

The uniqueness half is `costLambda_single_point_calibration`: two calibrating
exponents both reproduce `F`, hence agree at the single distinction ratio
`x₀ = 2 > 1`, which already forces them equal. No new analysis; this packages
free action (`costLambda_injective`), transitive action
(`costLambda_gauge_transitive`), and surjectivity (`prc_four_law_completeness`)
into the one torsor statement those docstrings only asserted in prose. -/
theorem prc_cost_freedom_is_one_real
    [Cost.FunctionalEquation.AczelSmoothnessPackage]
    {F : ℝ → ℝ}
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hκ : 0 < deriv (deriv (Cost.FunctionalEquation.G F)) 0) :
    ∃! c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → F x = costLambda c x := by
  obtain ⟨c, hcpos, hc⟩ := prc_four_law_completeness hRecip hNorm hComp hCont hκ
  refine ⟨c, ⟨hcpos, hc⟩, ?_⟩
  rintro d ⟨hdpos, hd⟩
  have h2 : costLambda d 2 = costLambda c 2 := by
    rw [← hd 2 (by norm_num), ← hc 2 (by norm_num)]
  exact costLambda_single_point_calibration (by norm_num : (1 : ℝ) < 2) hdpos hcpos h2

/-- **The completion strictly extends the δ-native carrier (cost-independent).**

The strength separation `prc_jcost_strength_separation` witnesses the
carrier/completion gap *through the cost*: J-forcing fails on the δ-native
carrier and holds on the completion. This theorem gives the same gap at the most
primitive level, with no reference to cost at all: the completion `ℝ` contains a
square root of `2`, while no element of the δ-native rational carrier
`RatioOrbit` has a value squaring to `2` (its verifier image lies in `ℚ`, and
`√2` is irrational). So the move from the carrier to the completion is a genuine
extension: the carrier cannot even express the limits the completion supplies,
quite apart from whether any cost is forced. This is the algebraic root of the
program's "J is forced only on the continuous completion": the completion is a
strictly larger object, tagged `traceClosure` and provably above the δ-only
floor (`StrengthTag.deltaOnly_lt_traceClosure`). -/
theorem prc_completion_strictly_extends_carrier :
    (∃ x : ℝ, x ^ 2 = 2) ∧
    ¬ ∃ q : RatioOrbit, ((RatioOrbit.toRat q : ℝ)) ^ 2 = 2 := by
  refine ⟨⟨Real.sqrt 2, Real.sq_sqrt (by norm_num)⟩, ?_⟩
  rintro ⟨q, hq⟩
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hsqrt : Real.sqrt 2 = |(RatioOrbit.toRat q : ℝ)| := by
    have h := Real.sqrt_sq_eq_abs (RatioOrbit.toRat q : ℝ)
    rw [hq] at h; exact h
  rw [hsqrt] at hirr
  exact hirr ⟨|RatioOrbit.toRat q|, by rw [Rat.cast_abs]⟩

/-- The δ-native rational field (standard model `ℚ`) has no square root of `2`:
the carrier is not even real-closed, let alone complete. -/
theorem rat_no_sqrt_two : ¬ ∃ q : ℚ, q ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have hcast : ((q : ℝ)) ^ 2 = 2 := by exact_mod_cast hq
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have h := Real.sqrt_sq_eq_abs (q : ℝ)
  rw [hcast] at h
  rw [h] at hirr
  exact hirr ⟨|q|, by rw [Rat.cast_abs]⟩

/-- The continuum `ℝ` is not countable (type-level). -/
theorem real_not_countable : ¬ Countable ℝ := by
  intro h
  haveI := h
  exact Cardinal.not_countable_real Set.countable_univ

/-- `√2` is algebraic over `ℚ`: it is a root of `X^2 - 2`, the cleanest
δ-posable polynomial comparison that the bare rational field cannot answer
(`forced_field_has_gap`). -/
theorem sqrt_two_isAlgebraic : IsAlgebraic ℚ (Real.sqrt 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) 2
  · have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [show (algebraMap ℚ ℝ) 2 = (2 : ℝ) by norm_num, h2, sub_self]

/-- **§5.1 / §9 backing: closing δ's algebraic questions never escapes
countability.**

The `prc_continuum_not_forced` docstring asserts in prose that even the *real
closure* of the δ-forced field — the real algebraic numbers, the carrier in
which every δ-posable *polynomial* comparison resolves, including the `√2` gap
that the bare rational field `ℚ` misses — stays countable, so closing δ's
algebraic questions never escapes countability. That claim is here a checked
theorem rather than a label:

* the set of reals algebraic over `ℚ` is countable (`Algebraic.countable`);
* it does contain `√2`, the specific gap `ℚ` lacks (`sqrt_two_isAlgebraic`);
* `ℝ` is uncountable (`real_not_countable`).

So the most generous algebraic closure of the δ-forced field is still strictly
below the continuum. This pins the precise arena for the §9 target
(now CLOSED, positive — see `dAlembert_cosh_of_monotone` and
`composition_law_monotone_forces_costLambda` below): a countable field in which
all polynomial δ-questions resolve is exactly where one asks whether `J` can be
forced *without* completeness, and the answer is yes. The cardinality gap
survives the algebraic closure; only the completeness posit crosses it. -/
theorem delta_algebraic_closure_stays_countable :
    Set.Countable { x : ℝ | IsAlgebraic ℚ x }
      ∧ IsAlgebraic ℚ (Real.sqrt 2)
      ∧ ¬ Countable ℝ :=
  ⟨Algebraic.countable ℚ ℝ, sqrt_two_isAlgebraic, real_not_countable⟩

/-- **§9 payoff, family form: monotonicity forces `F` into the `costLambda` family.**

Sharpens `composition_law_monotone_forces_cosh_family` to the statement directly
comparable to the `ContinuousOn` family theorem `composition_law_admits_full_scale_family`:
a reciprocal-symmetric, normalized, composition-law cost that is monotone (via
`H_F` on `[0,∞)`) equals `costLambda c` on `(0,∞)` for a single real `c`. The
residual `c` is exactly the one unit-of-scale posit; with the calibration
`c = 1` this is `Cost.Jcost`. No completeness is used anywhere. -/
theorem composition_law_monotone_forces_costLambda (F : ℝ → ℝ)
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hMono : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ))) :
    ∃ c : ℝ, ∀ x : ℝ, 0 < x → F x = costLambda c x := by
  obtain ⟨c, hc⟩ :=
    composition_law_monotone_forces_cosh_family F hRecip hNorm hComp hMono
  refine ⟨c, ?_⟩
  intro x hx
  have htx : x = Real.exp (Real.log x) := (Real.exp_log hx).symm
  have h1 : Cost.FunctionalEquation.H F (Real.log x) = Real.cosh (c * Real.log x) := hc _
  have h2 : Cost.FunctionalEquation.H F (Real.log x) = F x + 1 := by
    simp only [Cost.FunctionalEquation.H, Cost.FunctionalEquation.G]
    rw [← htx]
  have h3 : costLambda c x = Real.cosh (c * Real.log x) - 1 := by
    have hg := congrFun (G_costLambda c) (Real.log x)
    simp only [Cost.FunctionalEquation.G] at hg
    rw [← htx] at hg
    exact hg
  have hsum : F x + 1 = Real.cosh (c * Real.log x) := by rw [← h2, h1]
  rw [h3]; linarith

/-- **§9 capstone: the residual freedom is EXACTLY one positive real.**

The scale family `costLambda` is injective in its positive exponent: if
`costLambda l` and `costLambda l'` agree on all of `(0,∞)` with `l, l' > 0`, then
`l = l'`. Evaluating at `x = 2` turns the equality into
`cosh (log 2 · l) = cosh (log 2 · l')`, and `cosh` is injective on `[0,∞)`
(`Real.cosh_strictMonoOn`), so `log 2 · l = log 2 · l'`, hence `l = l'`. No
completeness is used. Combined with `composition_law_monotone_forces_costLambda`
(every monotone solution IS some `costLambda c`), this is the complete
completeness-free classification: the monotone, reciprocal, normalized,
composition-law costs are faithfully parameterized by exactly one positive real.
The residual unit of scale is therefore genuine and irreducible, not an artifact
of a loose argument: no order-only datum can collapse it further. -/
theorem costLambda_injOn_pos {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l')
    (h : ∀ x : ℝ, 0 < x → costLambda l x = costLambda l' x) : l = l' := by
  have e : ∀ a : ℝ, (2 : ℝ) ^ a = Real.exp (Real.log 2 * a) := fun a =>
    Real.rpow_def_of_pos (by norm_num) a
  have hcosh : ∀ a : ℝ,
      ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) / 2 = Real.cosh (Real.log 2 * a) := by
    intro a
    rw [Real.cosh_eq, e a, e (-a), show Real.log 2 * (-a) = -(Real.log 2 * a) by ring]
  have h2 := h 2 (by norm_num)
  unfold costLambda at h2
  have h3 : ((2 : ℝ) ^ l + (2 : ℝ) ^ (-l)) / 2
      = ((2 : ℝ) ^ l' + (2 : ℝ) ^ (-l')) / 2 := by linarith [h2]
  rw [hcosh l, hcosh l'] at h3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : Real.log 2 * l ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
  have hb : Real.log 2 * l' ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
  have hmul : Real.log 2 * l = Real.log 2 * l' := Real.cosh_strictMonoOn.injOn ha hb h3
  exact mul_left_cancel₀ (ne_of_gt hlog2) hmul

/-! ### The countability premise, formalized (paper §"Finitary generative systems")

The δ non-forcing result rests on one standing premise: distinction is a
*finitary generative system*, so its reach is countable. The paper states this as
Theorem "Generative systems reach only countable collections" (`thm:countgen`).
Here that theorem is upgraded from prose to a machine-checked statement, together
with its contrapositive (escaping countability requires a genuinely infinitary
input) and the `ℝ` corollary (no finitary system exhausts the real line). This is
the formal backing for the premise the paper names, not a closure of the
interpretive question of whether distinction *is* such a system. -/

/-- Stage `k` of a finitary generative system: seed `S0`, rule set `R` (each rule
a finite-arity map `List α → α`). `G₀ = S0`; `G_{k+1}` adjoins every rule applied
to a finite tuple of already-reached objects. -/
def genStage {α : Type*} (S0 : Set α) (R : Set (List α → α)) : ℕ → Set α
  | 0 => S0
  | (k + 1) =>
      genStage S0 R k ∪
        {x | ∃ ρ ∈ R, ∃ l : List α, (∀ y ∈ l, y ∈ genStage S0 R k) ∧ ρ l = x}

/-- The generated collection: everything reached in finitely many stages. -/
def generated {α : Type*} (S0 : Set α) (R : Set (List α → α)) : Set α :=
  ⋃ k, genStage S0 R k

/-- The set of lists all of whose entries lie in a countable set is countable. -/
theorem countable_setOf_lists_mem {α : Type*} {s : Set α} (hs : s.Countable) :
    {l : List α | ∀ y ∈ l, y ∈ s}.Countable := by
  have hc : Countable s := hs.to_subtype
  rw [← Set.countable_coe_iff]
  have key : ∀ (L : {l : List α // ∀ y ∈ l, y ∈ s}),
      (L.1.attach.map (fun x => (⟨x.1, L.2 x.1 x.2⟩ : s))).map Subtype.val = L.1 := by
    intro L; simp
  have hinj : Function.Injective
      (fun (L : {l : List α // ∀ y ∈ l, y ∈ s}) =>
        L.1.attach.map (fun x => (⟨x.1, L.2 x.1 x.2⟩ : s))) := by
    intro L1 L2 hL
    apply Subtype.ext
    have hL' := congrArg (List.map Subtype.val) hL
    rw [key L1, key L2] at hL'
    exact hL'
  exact hinj.countable

/-- **`thm:countgen`: each stage of a finitary generative system is countable.** -/
theorem genStage_countable {α : Type*} {S0 : Set α} {R : Set (List α → α)}
    (hS0 : S0.Countable) (hR : R.Countable) : ∀ k, (genStage S0 R k).Countable := by
  intro k
  induction k with
  | zero => simpa only [genStage] using hS0
  | succ k ih =>
    simp only [genStage]
    refine Set.Countable.union ih ?_
    have hlists : {l : List α | ∀ y ∈ l, y ∈ genStage S0 R k}.Countable :=
      countable_setOf_lists_mem ih
    have hsub :
        {x | ∃ ρ ∈ R, ∃ l : List α,
              (∀ y ∈ l, y ∈ genStage S0 R k) ∧ ρ l = x}
          = ⋃ ρ ∈ R, ρ '' {l : List α | ∀ y ∈ l, y ∈ genStage S0 R k} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨ρ, hρ, l, hl, rfl⟩; exact ⟨ρ, hρ, l, hl, rfl⟩
      · rintro ⟨ρ, hρ, l, hl, rfl⟩; exact ⟨ρ, hρ, l, hl, rfl⟩
    rw [hsub]
    exact hR.biUnion (fun ρ _ => hlists.image ρ)

/-- **`thm:countgen`: the generated collection of a finitary generative system is
countable.** Seed countable + countably many finite-arity rules ⇒ reach countable.
Completeness-free; the only inputs are countable unions, countable products of
countable sets, and images. -/
theorem generated_countable {α : Type*} {S0 : Set α} {R : Set (List α → α)}
    (hS0 : S0.Countable) (hR : R.Countable) : (generated S0 R).Countable := by
  unfold generated
  exact Set.countable_iUnion (genStage_countable hS0 hR)

/-- **Contrapositive: escaping countability requires a genuinely infinitary input.**
If a generative system's reach is uncountable, then either its seed is uncountable
or it has uncountably many rules. So the only way distinction could reach the
continuum is by an uncountable seed or uncountably many simultaneous rules, i.e. by
positing an infinitary act, which is the completeness principle smuggled in. This
is the exact "the escape is circular" point of the paper, made precise. -/
theorem uncountable_generated_needs_infinitary {α : Type*}
    {S0 : Set α} {R : Set (List α → α)}
    (h : ¬ (generated S0 R).Countable) : ¬ S0.Countable ∨ ¬ R.Countable := by
  by_contra hc
  push_neg at hc
  exact h (generated_countable hc.1 hc.2)

/-- **`ℝ` corollary: no finitary generative system exhausts the real line.**
A countable seed closed under countably many finite-arity rules can never reach
all of `ℝ`. This is the formal statement that distinction, read as a finitary
generative system, does not force the continuum. -/
theorem generated_ne_univ_real {S0 : Set ℝ} {R : Set (List ℝ → ℝ)}
    (hS0 : S0.Countable) (hR : R.Countable) : generated S0 R ≠ Set.univ := by
  intro huniv
  have huniv_c : (Set.univ : Set ℝ).Countable := huniv ▸ generated_countable hS0 hR
  exact real_not_countable (Set.countable_univ_iff.mp huniv_c)

/-- **`cor:measure`: the reach of a finitary generative system on `ℝ` has Lebesgue
measure zero.** Countable sets are null for any atomless measure, and Lebesgue
volume on `ℝ` is atomless. This is the measure-theoretic form of non-forcing: the
reachable reals occupy none of the line. -/
theorem generated_volume_zero {S0 : Set ℝ} {R : Set (List ℝ → ℝ)}
    (hS0 : S0.Countable) (hR : R.Countable) :
    MeasureTheory.volume (generated S0 R) = 0 :=
  Set.Countable.measure_zero (generated_countable hS0 hR) MeasureTheory.volume

/-- **Almost every real is unreachable.** A real drawn at random (Lebesgue-a.e.)
lies outside the reach of any finitary generative system: the reachable reals are
a null set, so their complement is conull. This is the sharpest "size" statement of
the four non-forcing arguments. -/
theorem generated_ae_unreachable {S0 : Set ℝ} {R : Set (List ℝ → ℝ)}
    (hS0 : S0.Countable) (hR : R.Countable) :
    ∀ᵐ x : ℝ, x ∉ generated S0 R := by
  rw [MeasureTheory.ae_iff]
  simpa using generated_volume_zero hS0 hR

/-! ### Non-vacuity: the completeness-free forcing applies to the actual cost

The monotone forcing theorems above are not abstract possibilities; their
hypotheses are satisfied by the canonical recognition cost `Cost.Jcost`. The
log-coordinate transform of `J` is exactly `cosh`, which is monotone on `[0,∞)`, so
`composition_law_monotone_forces_costLambda` fires on `J` itself and places it in
the forced one-parameter family with no completeness assumption anywhere. -/

/-- The log-coordinate transform of the recognition cost is `cosh`:
`H J t = G J t + 1 = (cosh t - 1) + 1 = cosh t`. -/
theorem H_Jcost_eq_cosh (t : ℝ) :
    Cost.FunctionalEquation.H Cost.Jcost t = Real.cosh t := by
  simp only [Cost.FunctionalEquation.H]
  rw [Cost.FunctionalEquation.Jcost_G_eq_cosh_sub_one]; ring

/-- `H J` is monotone on `[0,∞)` (it is `cosh`), so `J` satisfies the
completeness-free regularity hypothesis of the monotone forcing theorems. -/
theorem H_Jcost_monotoneOn :
    MonotoneOn (Cost.FunctionalEquation.H Cost.Jcost) (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  rw [H_Jcost_eq_cosh, H_Jcost_eq_cosh]
  exact Real.cosh_strictMonoOn.monotoneOn ha hb hab

/-- **Non-vacuity capstone: the recognition cost `J` is forced by monotonicity.**
`Cost.Jcost` satisfies reciprocal symmetry, normalization, the composition law, and
the monotonicity of its log-transform, so the completeness-free
`composition_law_monotone_forces_costLambda` applies and places `J` in the forced
scale family `costLambda c` for some `c > 0`. With the scale calibration `c = 1`
(`costLambda 1 = J`) this recovers `J` exactly. The order-only forcing route is
therefore not merely abstract: it forces the actual recognition cost. -/
theorem Jcost_forced_by_monotonicity :
    ∃ c : ℝ, ∀ x : ℝ, 0 < x → Cost.Jcost x = costLambda c x :=
  composition_law_monotone_forces_costLambda Cost.Jcost
    (fun x _ => by simp only [Cost.Jcost, inv_inv]; ring)
    (by show Cost.Jcost 1 = 0; norm_num [Cost.Jcost])
    ((Cost.FunctionalEquation.composition_law_equiv_coshAdd Cost.Jcost).mpr
      Cost.FunctionalEquation.Jcost_cosh_add_identity)
    H_Jcost_monotoneOn

/-- **Headline capstone: the recognition cost `J` is forced by ORDER alone
(completeness-free analogue of `law_of_logic_forces_jcost`).**

`Cost.FunctionalEquation.law_of_logic_forces_jcost` pins `F = J` using a
`ContinuousOn` hypothesis. This theorem replaces continuity by *monotonicity* of
the log-transform `H F` on `[0,∞)`: any reciprocal-symmetric, normalized,
composition-law cost whose log-transform is monotone and which satisfies the unit
calibration `G''(0) = 1` equals `Cost.Jcost` on the positive reals. No
completeness, no continuity, and no derivative-of-a-limit on the real line is
used.

Proof skeleton: `composition_law_monotone_forces_costLambda` places `F` in the
scale family `costLambda c` on `(0,∞)`. Because the log-coordinate transform
`G F t = F (exp t)` only ever evaluates `F` at the positive point `exp t`, the
positive-domain equality `F = costLambda c` lifts to `G F = G (costLambda c)`
*everywhere*, so the calibration `deriv (deriv (G F)) 0 = 1` transfers verbatim to
`costLambda c`. The within-family calibration identity `isCalibrated_costLambda_iff`
then forces `c² = 1`, i.e. `c = ±1`, and both members collapse to `J` by the
reciprocal symmetry of the family (`costLambda (-1) x = costLambda 1 x`). The
load-bearing cost joint is therefore pinned to `J` using order in place of the
continuum. -/
theorem law_of_logic_forces_jcost_monotone (F : ℝ → ℝ)
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hMono : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ)))
    (hCalib : Cost.FunctionalEquation.IsCalibrated F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  obtain ⟨c, hc⟩ :=
    composition_law_monotone_forces_costLambda F hRecip hNorm hComp hMono
  -- The log-coordinate transform sees only positive arguments (`exp t > 0`),
  -- so positive-domain equality lifts to equality of `G F` everywhere.
  have hG : Cost.FunctionalEquation.G F = Cost.FunctionalEquation.G (costLambda c) := by
    funext t
    simp only [Cost.FunctionalEquation.G]
    exact hc (Real.exp t) (Real.exp_pos t)
  have hCalibC : Cost.FunctionalEquation.IsCalibrated (costLambda c) := by
    unfold Cost.FunctionalEquation.IsCalibrated at hCalib ⊢
    rw [← hG]; exact hCalib
  have hc2 : c ^ 2 = 1 := (isCalibrated_costLambda_iff c).mp hCalibC
  have hcpm : c = 1 ∨ c = -1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [hc2]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  intro x hx
  rw [hc x hx]
  rcases hcpm with h1 | hm1
  · subst h1; exact costLambda_one_eq_jcost x hx
  · subst hm1
    have hsymm : costLambda (-1) x = costLambda 1 x := by
      unfold costLambda
      rw [show -(-1 : ℝ) = 1 by norm_num]
      ring
    rw [hsymm]; exact costLambda_one_eq_jcost x hx

/-- **The δ-act cost is an exact closed form: distinguishing successor orbits
`n` and `n+1` costs `1/(2n(n+1))`.**

The most primitive δ-act along the integer ladder is the step from orbit `n` to
orbit `n+1`, carried by the ratio `(n+1)/n`. Its recognition cost is *exactly*
`1/(2n(n+1))` — a closed rational identity, with no limit, no Taylor expansion,
and no calibration posit. This is the literal "cost of one δ-act" object named as
Move 1 in the δ publication program. Two facts fall out of it:

* `1/(2n(n+1)) = ½(1/n − 1/(n+1))`, so the costs along the ladder *telescope*:
  the total recognition cost of building the entire integer ladder from the unit
  orbit is `∑_{n≥1} 1/(2n(n+1)) = 1/2`, exactly.
* The leading per-step coefficient is `n² · J((n+1)/n) → 1/2`
  (`jcost_successor_increment_tendsto`).

Honest reading (this does *not* force `J`): a scale-family member `costLambda c`
is `cosh (c·t) - 1` in log coordinates, so its discrete per-step act cost has
leading coefficient `c²/2`. The δ-act ladder therefore sees exactly the
calibration invariant `c²` — the same invariant the continuous condition
`G''(0) = c²` sees — and not the absolute scale; the closed form here is the
canonical `c = 1` instance. What the result establishes is that the calibration
is *not analytic in nature*: it is the leading coefficient of an exact rational
ladder of δ-act costs, a discrete object. The residual freedom is one positive
number (which `c²` counts as the unit), recorded as the faithfulness of the
family (`costLambda_injOn_pos`). -/
theorem jcost_successor_increment (n : ℝ) (hn : 0 < n) :
    Cost.Jcost ((n + 1) / n) = 1 / (2 * n * (n + 1)) := by
  have hn' : n ≠ 0 := ne_of_gt hn
  have hn1 : n + 1 ≠ 0 := by positivity
  unfold Cost.Jcost
  field_simp
  ring

/-- **The δ-act cost carried to the completion recovers the calibration coefficient
`1/2`.**

The leading coefficient of the per-step δ-act cost along the integer ladder is
`n² · J((n+1)/n) → 1/2`. This is the canonical `c = 1` instance of the family
pattern `n² · costLambda c ((n+1)/n) → c²/2`: the discrete act-cost ladder
exhibits the calibration invariant as a leading coefficient, a discrete datum
rather than an analytic one. It does not pin the absolute scale (see
`jcost_successor_increment`). The proof is elementary: on `n ≥ 1` the term equals
`n/(2(n+1)) = 1/2 − 1/(2(n+1))`, and `1/(2(n+1)) → 0`. -/
theorem jcost_successor_increment_tendsto :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 2 * Cost.Jcost (((n : ℝ) + 1) / (n : ℝ)))
      Filter.atTop (nhds (1 / 2)) := by
  have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have := h0.const_mul (1 / 2 : ℝ)
    simpa [mul_comm, mul_div_assoc, div_div, one_div] using this
  have hbase : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / 2 - (1 : ℝ) / (2 * ((n : ℝ) + 1)))
      Filter.atTop (nhds (1 / 2)) := by
    have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h1
    simpa using this
  apply hbase.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) ≤ n := hn
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [jcost_successor_increment (n : ℝ) hnpos]
  field_simp
  ring

/-- **The δ-act ladder sees exactly the calibration invariant `c²`, for the whole
scale family.**

Generalizing `jcost_successor_increment_tendsto` (the `c = 1` instance) to every
member of the forced scale family: the leading per-step coefficient of the
δ-act cost is `n² · costLambda c ((n+1)/n) → c²/2`. This is the precise statement
of "the discrete δ-act cost determines the calibration invariant `c²` and nothing
more" (Move 1, adjudicated to the second falsifier branch): the act-cost ladder
sees the same `c²` the continuous calibration `G''(0) = c²` sees, so it does *not*
pin the absolute scale; the canonical `c = 1` gives `1/2`.

Proof: write `p = ((n+1)/n)^c`; then `costLambda c ((n+1)/n) = (p + p⁻¹)/2 - 1 =
(p-1)²/(2p)`, so `n² · costLambda c = (n(p-1))²/(2p)`. The base `(n+1)/n → 1`, so
`p → 1`; and `n(p-1) = n((1+1/n)^c - 1) → c` is the slope of `x ↦ x^c` at `1`
(its derivative there is `c`). Hence the quotient tends to `c²/2`. -/
theorem costLambda_successor_increment_tendsto (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 2 * costLambda c (((n : ℝ) + 1) / (n : ℝ)))
      Filter.atTop (nhds (c ^ 2 / 2)) := by
  -- `n · ((1+1/n)^c - 1) → c` is the slope of `x ↦ x^c` at `1`.
  have hderiv : HasDerivAt (fun y : ℝ => y ^ c) c 1 := by
    have h := Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero)
    simpa using h
  have hslope : Filter.Tendsto (slope (fun y : ℝ => y ^ c) 1) (nhdsWithin 1 {1}ᶜ)
      (nhds c) := hasDerivAt_iff_tendsto_slope.mp hderiv
  -- `1 + 1/n → 1`, staying away from `1`.
  have hy : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ))
      Filter.atTop (nhdsWithin 1 {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
          Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
      have := (tendsto_const_nhds (x := (1 : ℝ))).add h0
      simpa using this
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hdpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc; nlinarith [hdpos]
  have hcomp : Filter.Tendsto
      (fun n : ℕ => slope (fun y : ℝ => y ^ c) 1 ((1 : ℝ) + 1 / (n : ℝ)))
      Filter.atTop (nhds c) := hslope.comp hy
  have hslope_n : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * (((1 : ℝ) + 1 / (n : ℝ)) ^ c - 1))
      Filter.atTop (nhds c) := by
    apply hcomp.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnz : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    rw [slope_def_field, Real.one_rpow]
    rw [show ((1 : ℝ) + 1 / (n : ℝ)) - 1 = 1 / (n : ℝ) by ring]
    rw [div_eq_mul_inv, inv_div, div_one]
    ring
  -- `p = (1+1/n)^c → 1`.
  have hp1 : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) + 1 / (n : ℝ)) ^ c)
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ))
        Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
          Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
      have := (tendsto_const_nhds (x := (1 : ℝ))).add h0
      simpa using this
    have hcont : ContinuousAt (fun y : ℝ => y ^ c) 1 :=
      Real.continuousAt_rpow_const 1 c (Or.inl one_ne_zero)
    have := hcont.tendsto.comp hbase
    simpa [Real.one_rpow] using this
  -- Assemble the quotient `(n(p-1))²/(2p) → c²/2`.
  have hnum : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) * (((1 : ℝ) + 1 / (n : ℝ)) ^ c - 1)) ^ 2)
      Filter.atTop (nhds (c ^ 2)) := hslope_n.pow 2
  have hden : Filter.Tendsto (fun n : ℕ => 2 * ((1 : ℝ) + 1 / (n : ℝ)) ^ c)
      Filter.atTop (nhds 2) := by
    have := hp1.const_mul (2 : ℝ)
    simpa using this
  have hquot : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) * (((1 : ℝ) + 1 / (n : ℝ)) ^ c - 1)) ^ 2
        / (2 * ((1 : ℝ) + 1 / (n : ℝ)) ^ c))
      Filter.atTop (nhds (c ^ 2 / 2)) := hnum.div hden (by norm_num)
  apply hquot.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hxe : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by field_simp
  have hxpos : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have hp : (0 : ℝ) < ((1 : ℝ) + 1 / (n : ℝ)) ^ c := Real.rpow_pos_of_pos hxpos c
  have hpne : ((1 : ℝ) + 1 / (n : ℝ)) ^ c ≠ 0 := ne_of_gt hp
  have hxneg : ((1 : ℝ) + 1 / (n : ℝ)) ^ (-c) = (((1 : ℝ) + 1 / (n : ℝ)) ^ c)⁻¹ :=
    Real.rpow_neg (le_of_lt hxpos) c
  unfold costLambda
  rw [hxe, hxneg]
  field_simp
  ring

/-
================================================================================
PROGRAM-GOAL PAPER TRAIL (recorded 2026-05-28, pass 349). READ THIS.

This block exists so that no future session re-opens a question that is closed,
and so the GOAL of the whole δ effort is not forgotten or quietly inflated.

WHAT WAS THE GOAL.
  The δ / PRC program asks: how much of mathematics and physics is FORCED by the
  single primitive act of distinction (δ), and where exactly does forcing stop
  and posit begin? The load-bearing joint is the forcing of the cost function J.
  J is pinned down only on a CONTINUOUS domain (the argument uses limits and
  derivatives). So the real final target was always: is that continuous
  completion (the real line) FORCED by δ, or merely ASSUMED?

  That boundary question, "where does necessity end," was the correct target all
  along. A program claiming "everything is forced, nothing arbitrary" has no
  successful outcome: taken literally it is false (see below), softened it is an
  unfalsifiable slogan. The result with content is the LOCATION OF THE SEAM.

WHAT WAS PROVEN (theorem `prc_continuum_not_forced`, this file).
  Distinction does NOT force the continuum. The answer is the NEGATIVE direction
  and it is a real theorem, not a missing lemma. Two independent classical
  pillars force it:
    (1) Cantor. δ proceeds one act at a time; its native index is ℕ
        (DistinctionNat ≃ ℕ); so everything δ generates is countable, including
        the rational field and even its algebraic closure. ℝ is uncountable.
        A countable generator cannot produce an uncountable object.
    (2) Löwenheim–Skolem. Any first-order theory with an infinite model has a
        countable model; no first-order theory forces uncountability.
        Completeness (the axiom singling out ℝ) is irreducibly second-order; the
        only way to "force ℝ from logic" is to admit full second-order logic,
        which smuggles in the power set = the continuum under another name.

WHY THE NEGATIVE IS STRONGER THAN "ℝ IS FORCED" WOULD HAVE BEEN.
  (a) True and unassailable; a forcing claim would have been circular (the J
      argument imports the very ℝ it would claim to force).
  (b) More information: a forced countable core, ℝ not in it, gap measured
      exactly as ℵ₀ < 𝔠.
  (c) Minimal posits: the entire arbitrary content of the framework is now
      exactly TWO nested posits, one continuum and one unit of scale within it
      (the unit is `prc_cost_freedom_is_one_real`). Everything else (counting,
      ratios, the cost FORM) is proven forced.
  (d) The seam lands on the fault line of mathematics itself: the countable /
      uncountable jump is exactly where CH, Gödel–Cohen independence, and
      constructive-vs-classical analysis live. δ must posit at precisely the
      point set theory itself must choose.

THE HONEST TERMINAL CLAIM OF THE PROGRAM (do not inflate past this):
  δ FORCES the discrete number tower and the rational field (arithmetic, derived).
  The continuous completion is the FIRST genuine posit beyond δ (analysis,
  assumed; size = ℵ₀ < 𝔠). On the completion the cost FORM is forced, and the
  residual freedom is exactly ONE positive real. Every link, including this
  boundary where forcing stops, is an exact theorem.

ONE PREMISE, STATED PLAINLY: the countability argument reads δ as a generative
  act proceeding one step at a time (grounded in DistinctionNat ≃ ℕ). That
  reading is high-confidence but is a premise about what a δ-act is, not itself a
  theorem. Escaping it requires letting δ pose uncountably many comparisons at
  once, which IS completeness, so that route is circular.

THE ONE SHARPER TARGET THAT REMAINS (not closed by this theorem): we proved δ
  does not force ℝ. We did NOT prove the continuum is NECESSARY to force J. Open
  question worth future sessions: can J be forced on a countable real-closed
  field with no completeness at all? If yes, the continuum posit dissolves and
  the framework's arbitrary content drops from two posits to one. If no, a
  theorem explaining WHY completeness is required would promote the continuum
  from assumption to proven necessity.

  PASS 350 (2026-05-28): the ARENA of that target is now a checked theorem, not
  prose. `delta_algebraic_closure_stays_countable` proves the set of reals
  algebraic over ℚ is countable (Mathlib `Algebraic.countable`), contains √2
  (`sqrt_two_isAlgebraic`, the gap ℚ lacks), while ℝ is uncountable. So the
  countable field in which every δ-posable POLYNOMIAL comparison resolves is
  pinned: it stays strictly below the continuum, and that is exactly where the
  §9 question lives. This UPGRADES the §5.1 prose remark to a theorem; it does
  NOT close the §9 target (whether J is forceable on that arena without
  completeness is still open). Honest tag: prose→theorem on the sub-claim,
  open on the main question.

  PASS 351 (2026-05-28): the regularity-substitute brick is now a theorem.
  `monotone_additive_isLinear` proves a Monotone solution of Cauchy's additive
  equation is linear (`f x = f 1 · x`), using ONLY Archimedean density of ℚ
  (`exists_rat_btwn`), never completeness. This is the exact lemma a
  completeness-free re-proof of J-uniqueness would consume: the RCL's d'Alembert
  reduction lands on an additive exponent, and monotonicity (an order property
  present on any ordered field) forces that exponent linear, hence `J`. It does
  NOT yet re-prove `law_of_logic_forces_jcost` with `MonotoneOn` in place of
  `ContinuousOn`; it supplies the missing analytic-free regularity step. Next:
  thread it through the d'Alembert layer (`Cost.FunctionalEquation.G`) to a
  `MonotoneOn (Set.Ioi 0)` variant of the uniqueness theorem; if a Hamel-basis
  pathology survives monotonicity that obstruction is the "why completeness is
  required" theorem, otherwise the continuum dependence of the cost dissolves.

  PASS 352 (2026-05-28): two order-only, completeness-free constraints on the
  d'Alembert solution landed. `dAlembert_duplication`: H(2t)=2(H t)²−1 (cosh
  duplication, pure algebra). `dAlembert_ge_one_of_monotone`: a d'Alembert
  solution monotone on [0,∞) with H(0)=1 stays ≥1, so the bounded cosine branch
  H=cos(c·) is excluded BY ORDER ALONE — no analytic input. This is exactly the
  job continuity used to do (rule out the oscillatory branch). The remaining
  CRUX, now precisely located: from d'Alembert one gets
  H(s+t)−H(s−t) = ±2√((H(s)²−1)(H(t)²−1)) (the "sinh product"); proving the
  associated φ(t)=H(t)+√(H(t)²−1) is multiplicative (φ(s+t)=φ(s)φ(t)) requires
  matching that sign consistently. Sign-matching is the suspected exact point
  where the present argument uses continuity. The §9 question reduces to: can
  monotonicity alone fix the sign? If yes, log∘φ is additive+monotone, hence
  linear by `monotone_additive_isLinear`, hence H=cosh(linear), and completeness
  is NOT required for J. If the sign genuinely needs a limit, that is the
  "why completeness is required" theorem. Next target: the sign-matching lemma.

  PASS 353 (2026-05-28): THE SIGN CRUX IS RESOLVED — monotonicity fixes the sign.
  Key algebra: `dAlembert_prod` (apply d'Alembert to (s+t),(s−t):
  H(2s)+H(2t)=2H(s+t)H(s−t)) and `dAlembert_diff_sq`
  ((H(s+t)−H(s−t))²=4(H(s)²−1)(H(t)²−1)). Then `dAlembert_diff_eq_of_monotone`:
  for 0≤t≤s both s±t are in [0,∞) where H is monotone, so H(s+t)≥H(s−t), and the
  difference is the NONNEGATIVE root: H(s+t)−H(s−t)=2√(H(s)²−1)√(H(t)²−1). The
  sign — the single place the analytic proof used continuity — is pinned by ORDER
  ALONE. `dAlembert_add_of_monotone` gives the cosh addition formula
  H(s+t)=H s·H t+√√. So the §9 answer is now in view and POSITIVE: the cost form
  does NOT require completeness, only the order structure. Remaining tail (pure
  follow-through, no new obstruction expected): S-addition
  √(H(s+t)²−1)=H s·S t+S s·H t ⇒ φ=H+√(H²−1) multiplicative on [0,∞) ⇒ log∘φ
  additive+monotone ⇒ linear (`monotone_additive_isLinear`) ⇒ H=cosh(c·) ⇒ swap
  MonotoneOn for ContinuousOn in `law_of_logic_forces_jcost`. Next: that assembly.

  PASS 354 (2026-05-28): the multiplicative structure is now a theorem.
  `dAlembert_S_add_of_monotone`: the sinh-addition identity
  √(H(s+t)²−1)=H s·√(H t²−1)+√(H s²−1)·H t (squared, nonnegative root, via the
  H-addition formula; linear_combination over the sqrt-square facts). Packaged in
  `phi_mul_of_monotone`: φ(s+t)=φ(s)·φ(t) for 0≤t≤s with φ x=H x+√(H x²−1). So φ
  is multiplicative on [0,∞) with NO completeness used — only order + field +
  sqrt. Remaining tail to close §9 positively: φ>0 ⇒ log∘φ additive on [0,∞);
  monotone (H,√(H²−1) both increase) ⇒ extend odd to ℝ ⇒ linear by
  `monotone_additive_isLinear` ⇒ H=cosh(c·) ⇒ a MonotoneOn variant of
  `law_of_logic_forces_jcost`. The mathematical content is finished; the tail is
  the odd-extension bookkeeping and the cosh identification. Next: that assembly.

  PASS 355 (2026-05-28): §9 IS CLOSED, POSITIVE. The assembly is a theorem:
  `dAlembert_cosh_of_monotone`. An even, normalized (H 0=1), monotone-on-[0,∞)
  d'Alembert solution IS H t=cosh(c·t) for a single real c. Built from
  `monotone_additive_nonneg_isLinear` (odd-extension of an additive-on-[0,∞)
  monotone function to all of ℝ, then `monotone_additive_isLinear`, completeness-
  free) + log∘φ additive (from `phi_mul_of_monotone`) + monotone (φ increasing)
  ⇒ log φ(t)=c·t ⇒ φ(t)=exp(c·t) ⇒ H t=(φ+φ⁻¹)/2=cosh(c·t); evenness extends to
  t<0 via `Real.cosh_neg`. NO continuity, NO smoothness, NO Aczél package, NO
  least-upper-bound. Only field ops, sqrt, order, and Archimedean density. So the
  proof transfers verbatim to ANY Archimedean real-closed field — including the
  countable arena pinned in pass 350. CONCLUSION FOR THE δ PROGRAM: the continuum
  is NOT required to force the cost form. Monotonicity (an order property of any
  ordered field) does everything continuity did. The framework's arbitrary
  content drops from TWO nested posits (continuum + unit) to ONE (unit of scale,
  the residual c = `prc_cost_freedom_is_one_real`). The continuum posit for the
  cost DISSOLVES. The sharper §9 target — open since pass 350 — is resolved in the
  positive direction. Honest tag: THEOREM (0 sorry, 0 new axiom; depends only on
  Mathlib + the in-file monotone/d'Alembert chain). What remains is purely a
  downstream convenience: re-skinning `Cost.FunctionalEquation.law_of_logic_forces_jcost`
  to consume `MonotoneOn` instead of `ContinuousOn`+Aczél — the math is done; that
  is an API edit, not an open question. The δ frontier as posed in the paper's §9
  is now answered.

  PASS 356 (2026-05-28): the API edit is DONE too. `composition_law_monotone_forces_cosh_family`
  takes the actual cost hypotheses (`Cost.FunctionalEquation.IsReciprocalCost` +
  `IsNormalized` + `SatisfiesCompositionLaw`) plus `MonotoneOn (H F) [0,∞)` and
  returns `∃ c, H F t = cosh(c·t)` — composition law ⇒ d'Alembert on H F (via
  `composition_law_equiv_coshAdd`), reciprocal symmetry ⇒ evenness, normalization
  ⇒ H F 0 = 1, then `dAlembert_cosh_of_monotone`. `composition_law_monotone_forces_costLambda`
  sharpens this to `∃ c, ∀ x>0, F x = costLambda c x` — the exact completeness-free
  counterpart of `composition_law_admits_full_scale_family` (which used `ContinuousOn`).
  So the swap "MonotoneOn for ContinuousOn+Aczél" is now a checked theorem in the
  cost layer, not a promise. Nothing about §9 remains open: the continuum is not
  needed to force the cost, monotonicity suffices, and the residual is one real c.

  PASS 357 (2026-05-28): the classification is now COMPLETE in both directions.
  `costLambda_injOn_pos`: the scale family is injective in its positive exponent
  (agreement on (0,∞) for l,l'>0 ⇒ l=l'), proved by evaluating at x=2, reducing to
  cosh(log2·l)=cosh(log2·l'), and `Real.cosh_strictMonoOn.injOn` on [0,∞). No
  completeness. Together with `composition_law_monotone_forces_costLambda` (every
  monotone solution IS some costLambda c) this is the full completeness-free
  classification: the monotone, reciprocal, normalized, composition-law costs are
  faithfully parameterized by exactly one positive real. So "the residual is one
  unit of scale" is now a THEOREM on BOTH sides — the family covers all solutions
  AND no two distinct positive scales coincide. No order-only datum collapses the
  scale further; the one posit is genuine and irreducible, not an artifact of a
  loose argument. The δ §9 architecture is closed end to end: forcing reaches the
  cost FORM with monotonicity alone, and the freedom that remains is exactly ℝ_{>0}.

  PASS 358 (2026-05-28): the OTHER δ load-bearer, the countability premise, is now
  Lean-backed too. The paper's central premise-theorem `thm:countgen` ("a finitary
  generative system reaches only a countable collection") is formalized:
  `genStage`/`generated` define the seed-plus-finite-arity-rule closure;
  `generated_countable` proves the reach is countable from `S0.Countable` +
  `R.Countable` (via `countable_setOf_lists_mem`: lists over a countable set are
  countable, by injection into `List ↥s`); `uncountable_generated_needs_infinitary`
  is the contrapositive (escaping countability forces an uncountable seed or
  uncountably many rules, i.e. an infinitary act, which is the completeness
  principle smuggled in, the paper's "circular" point made exact); and
  `generated_ne_univ_real` is the ℝ corollary (no finitary system exhausts the real
  line). HONEST SCOPE: this formalizes the MATH under the premise (IF distinction is
  a finitary generative system THEN its reach is countable, and cannot be ℝ). It
  does NOT close the interpretive question of whether distinction IS such a system;
  that remains a reading of the primitive, exactly as the paper says. So both δ
  load-bearers now have Lean backing: the cost FORM is forced by order alone
  (passes 355-357), and the countability boundary is a theorem given the finitary
  reading (pass 358). The sole genuinely-open item is the interpretive premise, and
  it is open by nature, not for lack of formalization.

  PASS 359 (2026-05-28): the measure-theoretic non-forcing argument is now Lean-
  backed too, as a direct corollary of pass 358. `generated_volume_zero`: the reach
  of a finitary generative system on ℝ has Lebesgue measure zero (countable ⇒ null
  for the atomless volume measure). `generated_ae_unreachable`: almost every real is
  outside the reach (the reachable set is null, its complement conull). This is the
  paper's `cor:measure`. So THREE of the paper's four non-forcing arguments are now
  machine-checked: cardinality (pass 350, `real_not_countable` + algebraic-closure
  countability), generative-system countability (pass 358, `thm:countgen`), and
  measure zero (pass 359). The fourth, definability in a countable language /
  Löwenheim-Skolem model theory, was at this pass still prose-only (superseded by
  pass 361, which formalizes it after all). The δ architecture is fully load-bearing in Lean: cost FORM
  forced by order alone, residual freedom exactly ℝ_{>0}, countability boundary a
  theorem under the finitary reading, and the reachable reals null in ℝ.

  PASS 360 (2026-05-28): non-vacuity. The monotone forcing route is shown to apply
  to the ACTUAL recognition cost, not just abstractly. `H_Jcost_eq_cosh`: the
  log-transform of J is exactly cosh (H J t = G J t + 1 = cosh t).
  `H_Jcost_monotoneOn`: hence H J is monotone on [0,∞). `Jcost_forced_by_monotonicity`:
  feeding J's reciprocal symmetry, normalization, composition law, and that
  monotonicity into `composition_law_monotone_forces_costLambda` yields
  ∃ c, ∀ x>0, J x = costLambda c x — so the completeness-free order-only route forces
  the real J into the scale family (c=1 recovers J exactly). The forcing theorem is
  therefore non-vacuous: its hypotheses are satisfied by the canonical cost, and the
  conclusion recovers J with no continuity, no smoothness, no completeness. This
  closes the loop between the abstract §9 result and the concrete recognition cost.

  PASS 361 (2026-05-28): the FOURTH non-forcing argument is now Lean-backed, so all
  four of the paper's independent routes are machine-checked. New sibling module
  `PRCModelTheoryNonForcing` (heavy `Mathlib.ModelTheory` import isolated there).
  `real_has_countable_ee_model`: for any countable first-order language L carrying a
  structure on ℝ (card L ≤ ℵ₀), there is a structure N with ℝ ≅[L] N (elementarily
  equivalent: same first-order sentences) and #N = ℵ₀ — a direct instantiation of
  Mathlib's downward Löwenheim-Skolem `exists_elementarilyEquivalent_card_eq` at the
  cardinal ℵ₀. `real_not_first_order_categorical`: that companion has #ℝ ≠ #N (from
  `mk_real` : #ℝ = 𝔠 and `aleph0_lt_continuum`), so it is not equinumerous with ℝ,
  hence not isomorphic by any structure map. `real_first_order_underdetermined`
  bundles all three. CONTENT: no first-order description in a countable language pins
  ℝ up to isomorphism — whatever complete first-order theory distinction writes about
  its number line, a countable model of that very theory exists. The continuum is not
  forced by any amount of first-order distinction, independently of cardinality,
  generative countability, and measure. Reversal of the pass-359 stance: the fourth
  argument was called "not worth formalizing"; on reflection it is one Mathlib
  theorem away and completes the paper's stated "four independent proofs" in Lean, so
  it was worth the small cost. ALL FOUR non-forcing arguments now have machine-checked
  Lean witnesses. The δ §9 frontier is closed on every front the paper claims.

Long-form prose version (no Lean references), saved as the canonical record:
  δ/Delta_Continuum_Is_Not_Forced.tex  (compiled: .pdf).
================================================================================
-/

/-- **T0 resolved, NEGATIVE: distinction does not force the continuum.**

This is the answer to the program's last load-bearing question, and it is a
*non-forcing* result. The whole J-forcing argument lives on the continuous
completion. The question was whether δ *forces* that completion or merely
*assumes* it. The answer is: δ does not force it, and the obstruction is exact
and quantitative, a cardinality gap.

The argument, from first principles:

1. δ's native counting is exactly `ℕ` (`DistinctionNat ≃ ℕ`,
   `delta_index_countable`). Distinction proceeds one act at a time, so every
   object it generates by iteration is indexed by `ℕ` and is therefore
   *countable*.
2. The δ-forced rational field is `ℚ` (`forced_field_countable`), countable.
   Even its real closure (the real algebraic numbers, where every δ-posable
   *polynomial* comparison resolves) is countable; closing δ's algebraic
   questions never escapes countability. The carrier is not even real-closed:
   it has no `√2` (`forced_field_has_gap`).
3. The continuum `ℝ` is *uncountable* (`completion_uncountable`). Concretely,
   every enumeration `f : ℕ → ℝ`, i.e. everything a countable δ-process can ever
   name, misses some real (`completion_unnamable`). Almost every real number is
   never named by any sequence of distinction acts.
4. `ℚ` embeds in `ℝ` as an ordered field (`shared_rational_field`), and `ℝ`
   fills the `√2` gap (`completion_fills_gap`), so the two share exactly the
   δ-forced rational structure and differ precisely on completeness.

Therefore the completeness principle, "every gap a δ-comparison points at is
filled," is **not** a consequence of distinction. It posits uncountably many
points that no δ-act names. Distinction cannot force the existence of objects it
can never name. The completion is a genuine added axiom, strictly stronger than
δ (this is exactly the `traceClosure` tag, now justified by a theorem rather
than a label), and the cardinality gap `#ℚ = ℵ₀ < 𝔠 = #ℝ` is the exact measure
of what it adds.

Honest consequence for the unification: δ forces the discrete tower and the
rational field; the continuous completion is the first genuine posit beyond
distinction, and J-forcing is conditional on it. The maximal "δ forces
everything including ℝ" reading is false. The true terminal claim is the
stratified one. -/
structure PRCContinuumNotForced : Prop where
  delta_index_countable : Nonempty (DistinctionNat ≃ ℕ)
  forced_field_countable : Countable ℚ
  forced_field_has_gap : ¬ ∃ q : ℚ, q ^ 2 = 2
  shared_rational_field : ∃ φ : ℚ →+* ℝ, Function.Injective φ ∧ StrictMono φ
  completion_fills_gap : ∃ r : ℝ, r ^ 2 = 2
  completion_uncountable : ¬ Countable ℝ
  completion_unnamable : ∀ f : ℕ → ℝ, ∃ r : ℝ, ∀ n : ℕ, f n ≠ r

/-- The continuum is not δ-forced: proven, each field discharged from δ-native
facts (`DistinctionNat ≃ ℕ`) and Mathlib cardinality. No project-local axioms. -/
theorem prc_continuum_not_forced : PRCContinuumNotForced where
  delta_index_countable := ⟨DistinctionNat.equivNat⟩
  forced_field_countable := inferInstance
  forced_field_has_gap := rat_no_sqrt_two
  shared_rational_field := by
    refine ⟨Rat.castHom ℝ, (Rat.castHom ℝ).injective, ?_⟩
    have hco : (⇑(Rat.castHom ℝ) : ℚ → ℝ) = ((↑) : ℚ → ℝ) := by ext q; simp
    rw [hco]; exact Rat.cast_strictMono
  completion_fills_gap := ⟨Real.sqrt 2, Real.sq_sqrt (by norm_num)⟩
  completion_uncountable := real_not_countable
  completion_unnamable := by
    intro f
    by_contra h
    push_neg at h
    have hsurj : Function.Surjective f := h
    have hrange : (Set.range f).Countable := Set.countable_range f
    rw [hsurj.range_eq] at hrange
    exact Cardinal.not_countable_real hrange

/-- **The full honest stratification, as one checked proposition (reconstructed).**

This is the top-level "what is forced versus assumed" object the program
objective asks for, assembled entirely from proven theorems with no
project-local axioms. It supersedes the per-stratum prose and re-establishes the
`prc_full_stratification` object (lost when an earlier `UniversalFoundation.lean`
edit was reverted) in a stable location, scoped to the load-bearing joint rather
than the bookkeeping certificate.

The seven fields are the complete honest accounting, bottom to top:

* `delta_only_floor` (`KernelFirstPassCertificate`, tag `deltaOnly`): δ alone
  forces the number tower (`DistinctionNat ≃ Nat`), the integer surface, and the
  rational field. This is what is genuinely **forced** from distinction.
* `completion_boundary` (`TraceClosureCertificate`, tag `traceClosure`): the move
  to the continuous completion is a trace-closure commitment, strictly stronger
  than `deltaOnly`. This is the first thing **assumed** beyond δ.
* `carrier_strictly_below_completion` (pass 346): a cost-independent witness that
  the assumption is non-vacuous: the completion contains `√2` while the δ-native
  carrier provably does not. The completion genuinely adds elements.
* `completion_not_forced` (pass 349, the T0 resolution): the completion is not
  merely stronger, it is *not δ-forced at all*. δ's native index is `ℕ`, so every
  object it generates is countable; `ℝ` is uncountable; the completeness axiom
  posits uncountably many points no δ-act names. The cardinality gap
  `ℵ₀ < 𝔠` is the exact measure of the assumption. This is the negative answer
  to the program's last load-bearing question.
* `jcost_strength_separation` (pass 343): on the carrier J is not forced (every
  prime axis is orientation-free); on the completion the calibration selects J;
  and `deltaOnly < traceClosure`. The forcing of J lives strictly above the
  carrier.
* `cost_form_forced` (pass 331/332/333/334): on the completion the four algebraic
  laws force the cost *form*, the gauge orbit `{costLambda l : l > 0}`.
* `residual_freedom_is_one_real` (pass 347): the only thing left **assumed** on
  top of the forced form is exactly one positive real, uniquely pinned by the
  solution. Not zero (the unit is a gauge δ does not fix), not more than one.
* `jcost_forced_order_only` (pass 362): the continuum is removed even from the
  *selection* of the canonical cost. A reciprocal-symmetric, normalized,
  composition-law, unit-calibrated cost whose log-transform is monotone on
  `[0,∞)` **equals** `Cost.Jcost` on the positives, with `ContinuousOn` nowhere
  invoked. So the only continuous-analysis input the cost-forcing story ever used
  (continuity) is replaced by an order property present on any ordered field; the
  residual assumption collapses to the single calibration unit and nothing of the
  continuum survives in the cost joint.

Read end to end: δ forces {number tower, rational field}; the completion and a
single cost unit are assumed; on the completion the cost form is forced, the
residual freedom is exactly one real, and the canonical cost itself is forced by
order alone. This is the terminal honest claim of the δ program's load-bearing
joint. -/
structure PRCFullStratification : Prop where
  delta_only_floor : KernelFirstPassCertificate
  completion_boundary : TraceClosureCertificate
  carrier_strictly_below_completion :
    (∃ x : ℝ, x ^ 2 = 2) ∧
    ¬ ∃ q : RatioOrbit, ((RatioOrbit.toRat q : ℝ)) ^ 2 = 2
  completion_not_forced : PRCContinuumNotForced
  jcost_strength_separation : PRCJCostStrengthSeparation
  cost_form_forced : PRCCostJointStratification
  residual_freedom_is_one_real :
    ∀ F : ℝ → ℝ,
      Cost.FunctionalEquation.IsReciprocalCost F →
      Cost.FunctionalEquation.IsNormalized F →
      Cost.FunctionalEquation.SatisfiesCompositionLaw F →
      ContinuousOn F (Set.Ioi 0) →
      0 < deriv (deriv (Cost.FunctionalEquation.G F)) 0 →
      ∃! c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → F x = costLambda c x
  jcost_forced_order_only :
    ∀ F : ℝ → ℝ,
      Cost.FunctionalEquation.IsReciprocalCost F →
      Cost.FunctionalEquation.IsNormalized F →
      Cost.FunctionalEquation.SatisfiesCompositionLaw F →
      MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ)) →
      Cost.FunctionalEquation.IsCalibrated F →
      ∀ x : ℝ, 0 < x → F x = Cost.Jcost x

/-- The full stratification holds, discharged field-by-field from proven
theorems. No project-local axioms; the `AczelSmoothnessPackage` instance is a
proved instance, not an axiom. -/
theorem prc_full_stratification
    [Cost.FunctionalEquation.AczelSmoothnessPackage] :
    PRCFullStratification where
  delta_only_floor := kernel_first_pass_certificate
  completion_boundary := trace_closure_certificate
  carrier_strictly_below_completion := prc_completion_strictly_extends_carrier
  completion_not_forced := prc_continuum_not_forced
  jcost_strength_separation := prc_jcost_strength_separation
  cost_form_forced := prc_cost_joint_stratification
  residual_freedom_is_one_real := fun _ h1 h2 h3 h4 h5 =>
    prc_cost_freedom_is_one_real h1 h2 h3 h4 h5
  jcost_forced_order_only := fun F h1 h2 h3 h4 h5 =>
    law_of_logic_forces_jcost_monotone F h1 h2 h3 h4 h5

/-- Verifier rational character that rebases the native `3` prime axis to `5`
while fixing the `2` axis. This is the narrow countermodel to two-calibration
forcing all prime calibrations. -/
noncomputable def threeToFiveRebaseRat (x : ℚ) : ℚ :=
  x * ((5 : ℚ) / 3) ^ (padicValRat 3 x)

theorem threeToFiveRebaseRat_one :
    threeToFiveRebaseRat 1 = 1 := by
  unfold threeToFiveRebaseRat
  have h : padicValRat 3 (1 : ℚ) = 0 := by
    norm_num [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  rw [h]
  norm_num

theorem threeToFiveRebaseRat_mul (x y : ℚ) :
    threeToFiveRebaseRat (x * y) =
      threeToFiveRebaseRat x * threeToFiveRebaseRat y := by
  unfold threeToFiveRebaseRat
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · rw [padicValRat.mul hx hy]
      have hbase : ((5 : ℚ) / 3) ≠ 0 := by norm_num
      rw [zpow_add₀ hbase]
      ring

theorem threeToFiveRebaseRat_inv (x : ℚ) :
    threeToFiveRebaseRat x⁻¹ = (threeToFiveRebaseRat x)⁻¹ := by
  unfold threeToFiveRebaseRat
  by_cases hx : x = 0
  · simp [hx]
  · rw [padicValRat.inv]
    have hbase : ((5 : ℚ) / 3) ≠ 0 := by norm_num
    have hxpow : ((5 : ℚ) / 3) ^ (padicValRat 3 x) ≠ 0 :=
      zpow_ne_zero _ hbase
    rw [zpow_neg]
    field_simp [hx, hxpow]

theorem threeToFiveRebaseRat_ne_zero {x : ℚ}
    (hx : x ≠ 0) :
    threeToFiveRebaseRat x ≠ 0 := by
  unfold threeToFiveRebaseRat
  have hbase : ((5 : ℚ) / 3) ≠ 0 := by norm_num
  exact mul_ne_zero hx (zpow_ne_zero _ hbase)

theorem padicValRat_three_two_eq_zero :
    padicValRat 3 (2 : ℚ) = 0 := by
  rw [show (2 : ℚ) = ((2 : ℤ) : ℚ) by norm_num]
  rw [padicValRat.of_int]
  have hInt : padicValInt 3 (2 : ℤ) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdiv
    norm_num at hdiv
  exact_mod_cast hInt

theorem threeToFiveRebaseRat_two :
    threeToFiveRebaseRat 2 = (2 : ℚ) := by
  unfold threeToFiveRebaseRat
  rw [padicValRat_three_two_eq_zero]
  norm_num

theorem threeToFiveRebaseRat_three :
    threeToFiveRebaseRat 3 = (5 : ℚ) := by
  unfold threeToFiveRebaseRat
  have h : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (by norm_num : 1 < 3)
  rw [h]
  norm_num

noncomputable def threeToFiveRebaseCharacter (q : RatioOrbit) : RatioOrbit :=
  ratioOrbitOfRat (threeToFiveRebaseRat q.toRat)

theorem threeToFiveRebaseCharacter_toRat (q : RatioOrbit) :
    (threeToFiveRebaseCharacter q).toRat =
      threeToFiveRebaseRat q.toRat := by
  unfold threeToFiveRebaseCharacter
  exact ratioOrbitOfRat_toRat _

theorem threeToFiveRebaseCharacter_ratio_character :
    PRCRatioCharacter threeToFiveRebaseCharacter where
  unit := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeToFiveRebaseCharacter_toRat,
      RatioOrbit.one_toRat]
    exact threeToFiveRebaseRat_one
  multiplicative := by
    intro x y
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeToFiveRebaseCharacter_toRat,
      RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
      threeToFiveRebaseCharacter_toRat, threeToFiveRebaseCharacter_toRat]
    exact threeToFiveRebaseRat_mul x.toRat y.toRat
  reciprocal := by
    intro x
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeToFiveRebaseCharacter_toRat,
      RatioOrbit.recip_toRat, RatioOrbit.recip_toRat,
      threeToFiveRebaseCharacter_toRat]
    exact threeToFiveRebaseRat_inv x.toRat
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, threeToFiveRebaseCharacter_toRat,
      threeToFiveRebaseCharacter_toRat, DistinctionNat.normalizeRatio_toRat]
  nonzero_preserving := by
    intro q hq
    rw [threeToFiveRebaseCharacter_toRat]
    exact threeToFiveRebaseRat_ne_zero hq

theorem threeToFiveRebaseCharacter_two_identity :
    RatioOrbit.crossEq (threeToFiveRebaseCharacter two) two := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, threeToFiveRebaseCharacter_toRat,
    two_toRat]
  exact threeToFiveRebaseRat_two

theorem threeToFiveRebaseCharacter_three_to_five :
    (threeToFiveRebaseCharacter threePrimeDirection).toRat = 5 := by
  rw [threeToFiveRebaseCharacter_toRat, threePrimeDirection_toRat]
  exact threeToFiveRebaseRat_three

theorem threeToFiveRebaseCharacter_two_calibrated :
    RatioOrbit.crossEq (costFromCharacter threeToFiveRebaseCharacter two)
      (onRatioOrbit two) := by
  unfold costFromCharacter
  exact onRatioOrbit_congr threeToFiveRebaseCharacter_two_identity

theorem threeToFiveRebaseCharacter_not_three_prime_calibrated :
    ¬ RatioOrbit.crossEq
      (costFromCharacter threeToFiveRebaseCharacter threePrimeDirection)
      (onRatioOrbit threePrimeDirection) := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat,
    onRatioOrbit_toRat, threeToFiveRebaseCharacter_three_to_five,
    threePrimeDirection_toRat] at h
  norm_num at h

theorem PRCTwoCalibrationForcesPrimeCalibrationTarget_refuted :
    ¬ PRCTwoCalibrationForcesPrimeCalibrationTarget := by
  intro htarget
  exact threeToFiveRebaseCharacter_not_three_prime_calibrated
    (htarget threeToFiveRebaseCharacter
      threeToFiveRebaseCharacter_ratio_character
      threeToFiveRebaseCharacter_two_calibrated
      threeOrbit threeOrbit_primeOrbit)

/-- The first mixed composite direction in the two-adic obstruction: `2 * 3`. -/
def twoThreePrimeCompositeDirection : RatioOrbit :=
  RatioOrbit.mul twoPrimeDirection threePrimeDirection

@[simp] theorem twoThreePrimeCompositeDirection_toRat :
    twoThreePrimeCompositeDirection.toRat = 6 := by
  unfold twoThreePrimeCompositeDirection
  rw [RatioOrbit.mul_toRat, twoPrimeDirection_toRat, threePrimeDirection_toRat]
  norm_num

/-- The mixed image forced by a two-adic axis twist at the composite `2 * 3`:
the `2` branch is reciprocal and the `3` branch is identity, giving `3/2`. -/
def twoThreePrimeMixedDirection : RatioOrbit :=
  RatioOrbit.mul (RatioOrbit.recip twoPrimeDirection) threePrimeDirection

@[simp] theorem twoThreePrimeMixedDirection_toRat :
    twoThreePrimeMixedDirection.toRat = (3 / 2 : ℚ) := by
  unfold twoThreePrimeMixedDirection
  rw [RatioOrbit.mul_toRat, RatioOrbit.recip_toRat, twoPrimeDirection_toRat,
    threePrimeDirection_toRat]
  norm_num

/-- Local orientation at the first mixed composite would require the character
image of `2*3` to be either the composite itself or its reciprocal. -/
def PRCCharacterTwoThreeCompositeLocalOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoThreePrimeCompositeDirection)
      twoThreePrimeCompositeDirection ∨
    RatioOrbit.crossEq (χ twoThreePrimeCompositeDirection)
      (RatioOrbit.recip twoThreePrimeCompositeDirection)

/-- Positive `2*3` composite-local form of the current two-adic branch blocker:
every ratio character carrying the two-adic axis branch must still choose one
of the two canonical local orientations at the first mixed composite. -/
def PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterTwoAdicAxisTwist χ →
        PRCCharacterTwoThreeCompositeLocalOrientation χ

/-- Witness form of the `2*3` composite-local failure. This is the constructive
countermodel surface equivalent to the reduced two-adic ratio-character target. -/
def PRCTwoThreeCompositeLocalOrientationFailureCharacter :
    Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterTwoAdicAxisTwist χ ∧
        ¬ PRCCharacterTwoThreeCompositeLocalOrientation χ

/-- Composite-defect form of the non-two mixed branch obstruction. A character
that sends orbit `2` to the reciprocal branch and a distinct native prime `p`
to identity must send the composite direction `2*p` to the mixed value `p/2`. -/
def PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) ∧
    ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      p ≠ twoOrbit ∧
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ∧
          RatioOrbit.crossEq
            (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
            (RatioOrbit.mul
              (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp))

/-- Cost-visible composite defect: the mixed composite image is not J-cost
calibrated at the composite direction `2*p`. -/
def PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) ∧
    ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      p ≠ twoOrbit ∧
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ∧
          RatioOrbit.crossEq
            (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
            (RatioOrbit.mul
              (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)) ∧
            ¬ RatioOrbit.crossEq
              (costFromCharacter χ
                (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
              (onRatioOrbit
                (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))

/-- Universal target form of the cost-visible blocker: prime calibration must
calibrate the composite direction `2*p` even under the mixed orientation data
that sends orbit `2` reciprocal and a distinct native prime `p` identity. -/
def PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        RatioOrbit.crossEq (χ twoPrimeDirection)
            (RatioOrbit.recip twoPrimeDirection) →
          ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
            p ≠ twoOrbit →
              RatioOrbit.crossEq (χ (primeDirection p hp))
                (primeDirection p hp) →
                RatioOrbit.crossEq
                  (costFromCharacter χ
                    (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
                  (onRatioOrbit
                    (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))

/-- Product-calibration target: prime calibration must propagate to the product
of any two native prime directions. This is the natural composite surface whose
`2*p` mixed-orientation instance is the current branch-rigidity blocker. -/
def PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
          ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
            RatioOrbit.crossEq
              (costFromCharacter χ
                (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))
              (onRatioOrbit
                (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))

/-- Character-local form of prime-pair product cost consistency. Unlike
`PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget`, this is a
field that can be required of one character as part of admissibility. -/
def PRCCharacterPrimePairProductCostConsistent
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq
        (costFromCharacter χ
          (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))
        (onRatioOrbit
          (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))

/-- Repaired admissible-character interface after the two-adic countermodel:
a character must satisfy the ratio-character laws, prime calibration, and
prime-pair product cost consistency. This field preserves the two global
orientations but excludes valuation twists. -/
structure PRCAdmissibleRatioCharacter
    (χ : RatioOrbit → RatioOrbit) : Prop where
  ratio_character : PRCRatioCharacter χ
  prime_calibrated : PRCCharacterPrimeDirectionCalibrated χ
  prime_pair_product_cost :
    PRCCharacterPrimePairProductCostConsistent χ

/-- Signed repaired admissible-character interface: prime and prime-pair
admissibility plus explicit preservation of the signed unit. Pass 279 proves
the unsigned interface cannot imply this field. -/
structure PRCSignedAdmissibleRatioCharacter
    (χ : RatioOrbit → RatioOrbit) : Prop where
  admissible : PRCAdmissibleRatioCharacter χ
  signed_unit : PRCCharacterSignedUnitCalibrated χ

theorem absValueCharacter_prime_pair_product_cost :
    PRCCharacterPrimePairProductCostConsistent absValueCharacter := by
  intro p hp r hr
  have hprod :
      RatioOrbit.crossEq
        (absValueCharacter
          (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))
        (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)) :=
    by
      rw [RatioOrbit.crossEq_iff_toRat_eq, absValueCharacter_toRat,
        RatioOrbit.mul_toRat, primeDirection_toRat, primeDirection_toRat]
      exact abs_of_nonneg
        (mul_nonneg
          (by exact_mod_cast Nat.zero_le p.toNat)
          (by exact_mod_cast Nat.zero_le r.toNat))
  exact onRatioOrbit_congr hprod

theorem absValueCharacter_admissible :
    PRCAdmissibleRatioCharacter absValueCharacter where
  ratio_character := absValueCharacter_ratio_character
  prime_calibrated := absValueCharacter_prime_calibrated
  prime_pair_product_cost := absValueCharacter_prime_pair_product_cost

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_all_prime_calibrated_admissible :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ∀ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ →
          PRCCharacterPrimeDirectionCalibrated χ →
            PRCAdmissibleRatioCharacter χ := by
  constructor
  · intro htarget χ hχ hprime
    exact
      ⟨hχ, hprime, htarget χ hχ hprime⟩
  · intro hadm χ hχ hprime
    exact (hadm χ hχ hprime).prime_pair_product_cost

/-- Admissible replacement for the character-factorization blocker: every
native cost must factor through a character satisfying the repaired interface,
not merely through an arbitrary ratio character. -/
def PRCNativeCostAdmissibleCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCAdmissibleRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

/-- Exact upgrade lemma still missing on the factorization side: an arbitrary
ratio-character factor for a native cost must be replaceable by an admissible
factor with the same generated cost. This is weaker than demanding that the
original factor itself be admissible, and it is the right target because
`J(χ q)` cannot distinguish a direction from its reciprocal. -/
def PRCNativeCostFactorizationAdmissibilityUpgradeTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      ∀ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ →
          (∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)) →
            ∃ ψ : RatioOrbit → RatioOrbit,
              PRCAdmissibleRatioCharacter ψ ∧
                ∀ q : RatioOrbit,
                  RatioOrbit.crossEq (F q) (costFromCharacter ψ q)

/-- Admissible replacement for character rigidity. The cost, rather than the
character orientation itself, must collapse to canonical J-cost on all ratio
orbits. -/
def PRCNativeCostAdmissibleCharacterRigidityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCAdmissibleRatioCharacter χ →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (costFromCharacter χ q) (onRatioOrbit q)

/-- Admissible-character rigidity reduced to orientation: under the repaired
interface, every admissible character should be globally identity-oriented or
reciprocal-oriented pointwise. -/
def PRCAdmissibleCharacterGlobalOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCAdmissibleRatioCharacter χ →
      PRCCharacterGlobalCostOrientation χ

/-- Prime-orientation subtarget under admissibility: the repaired prime-pair
field should force all prime axes to choose one branch coherently. -/
def PRCAdmissibleCharacterPrimeOrientationCoherentTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCAdmissibleRatioCharacter χ →
      PRCCharacterPrimeOrientationCoherent χ

theorem PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_global_orientation
    (horient : PRCAdmissibleCharacterGlobalOrientationTarget) :
    PRCNativeCostAdmissibleCharacterRigidityTarget := by
  intro χ hadm q
  rcases horient χ hadm q with hsame | hinv
  · exact onRatioOrbit_congr hsame
  · exact RatioOrbit.crossEq_trans
      (onRatioOrbit_congr hinv)
      (RatioOrbit.crossEq_symm (reciprocal_symmetric q))

theorem PRCNativeCostCharacterFactorizationTarget_of_admissible_character_factorization
    (hfactor : PRCNativeCostAdmissibleCharacterFactorizationTarget) :
    PRCNativeCostCharacterFactorizationTarget := by
  intro F hF
  rcases hfactor F hF with ⟨χ, hadm, hFχ⟩
  exact ⟨χ, hadm.ratio_character, hFχ⟩

theorem PRCNativeCostAdmissibleCharacterFactorizationTarget_of_character_factorization_and_admissibility_upgrade
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (hupgrade : PRCNativeCostFactorizationAdmissibilityUpgradeTarget) :
    PRCNativeCostAdmissibleCharacterFactorizationTarget := by
  intro F hF
  rcases hfactor F hF with ⟨χ, hχ, hFχ⟩
  exact hupgrade F hF χ hχ hFχ

theorem PRCNativeCostAdmissibleCharacterRigidityTarget_of_prime_calibration_propagation
    (hprop : PRCPrimeCalibrationPropagationTarget) :
    PRCNativeCostAdmissibleCharacterRigidityTarget := by
  intro χ hadm q
  exact hprop χ hadm.ratio_character hadm.prime_calibrated q

theorem PRCNativeCostUniquenessTarget_of_admissible_character_targets
    (hfactor : PRCNativeCostAdmissibleCharacterFactorizationTarget)
    (hrigid : PRCNativeCostAdmissibleCharacterRigidityTarget) :
    PRCNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q) (hrigid χ hadm q)

theorem PRCNativeCostUniquenessTarget_of_character_factorization_upgrade_and_prime_propagation
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (hupgrade : PRCNativeCostFactorizationAdmissibilityUpgradeTarget)
    (hprop : PRCPrimeCalibrationPropagationTarget) :
    PRCNativeCostUniquenessTarget :=
  PRCNativeCostUniquenessTarget_of_admissible_character_targets
    (PRCNativeCostAdmissibleCharacterFactorizationTarget_of_character_factorization_and_admissibility_upgrade
      hfactor hupgrade)
    (PRCNativeCostAdmissibleCharacterRigidityTarget_of_prime_calibration_propagation
      hprop)

/-- Positive reciprocal-branch transport normal form: if the distinguished
orbit-`2` prime axis is reciprocal-oriented, every native prime axis is
reciprocal-oriented. -/
def PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ twoPrimeDirection)
      (RatioOrbit.recip twoPrimeDirection) →
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp))

/-- Converse distinguished-axis reciprocal normal form: reciprocal orientation at
any calibrated prime axis forces reciprocal orientation at the orbit-`2` prime
axis. Together with the two-to-all reciprocal rule, this is exactly
reciprocal-witness globalization. -/
def PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)) →
      RatioOrbit.crossEq (χ twoPrimeDirection)
        (RatioOrbit.recip twoPrimeDirection)

/-- Split distinguished-axis form of reciprocal-witness globalization. -/
def PRCCharacterPrimeReciprocalWitnessGlobalizesSplit
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ ∧
    PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ

/-- Trace-connected form of the same positive reciprocal branch transport: the
reciprocal branch at orbit `2` transports along a finite δ-trace connection from
the orbit-`2` prime axis to the target native prime axis. -/
def PRCCharacterTwoPrimeReciprocalRespectsTraceConnected
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    PRCPrimeAxisTraceConnected twoOrbit twoOrbit_primeOrbit p hp →
      RatioOrbit.crossEq (χ twoPrimeDirection)
          (RatioOrbit.recip twoPrimeDirection) →
        RatioOrbit.crossEq (χ (primeDirection p hp))
          (RatioOrbit.recip (primeDirection p hp))

/-- Identity analogue of two-prime trace-connected branch transport: identity at
orbit `2` transports along a finite δ-trace connection from the orbit-`2` prime
axis to the target native prime axis. -/
def PRCCharacterTwoPrimeIdentityRespectsTraceConnected
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    PRCPrimeAxisTraceConnected twoOrbit twoOrbit_primeOrbit p hp →
      RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection →
        RatioOrbit.crossEq (χ (primeDirection p hp))
          (primeDirection p hp)

/-- Local prime orientation says each prime axis is individually sent to itself
or to its reciprocal. This is the algebraic content of equality of J-costs on a
single prime direction. -/
def PRCCharacterPrimeLocalOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ∨
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp))

/-- No mixed prime orientation says a character cannot choose identity on one
prime axis and reciprocal on another. This is the trace-coherence condition that
rules out independent prime-axis inversions. -/
def PRCCharacterNoMixedPrimeOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
        RatioOrbit.crossEq (χ (primeDirection r hr))
          (RatioOrbit.recip (primeDirection r hr)) →
          False

/-- Existential form of prime-axis no-mixing: no identity-oriented prime witness
can coexist with a reciprocal-oriented prime witness. -/
def PRCCharacterNoMixedPrimeWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ¬ ((∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) ∧
      (∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
        RatioOrbit.crossEq (χ (primeDirection r hr))
          (RatioOrbit.recip (primeDirection r hr))))

/-- Positive mixed-prime witness form: one native prime axis is identity-oriented
while one (possibly different) native prime axis is reciprocal-oriented. -/
def PRCCharacterMixedPrimeWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) ∧
  (∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
    RatioOrbit.crossEq (χ (primeDirection r hr))
      (RatioOrbit.recip (primeDirection r hr)))

/-- Pair-packaged mixed-prime witness form: the two branch witnesses are named
in one existential package. This removes the last propositional wrapper around
the current mixed-prime obstruction. -/
def PRCCharacterMixedPrimePairWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
    ∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ∧
        RatioOrbit.crossEq (χ (primeDirection r hr))
          (RatioOrbit.recip (primeDirection r hr))

/-- Same-axis mixed-prime pair witness: the identity-oriented and
reciprocal-oriented prime witnesses are carried by the same native prime
orbit. This is the self-reciprocal branch-conflict case. -/
def PRCCharacterSamePrimeMixedPairWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
    ∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
      p = r ∧
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ∧
          RatioOrbit.crossEq (χ (primeDirection r hr))
            (RatioOrbit.recip (primeDirection r hr))

/-- Distinct-axis mixed-prime pair witness: the identity-oriented and
reciprocal-oriented prime witnesses live on different native prime orbits. -/
def PRCCharacterDistinctPrimeMixedPairWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
    ∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
      p ≠ r ∧
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) ∧
          RatioOrbit.crossEq (χ (primeDirection r hr))
            (RatioOrbit.recip (primeDirection r hr))

/-- One-sided witness exclusion for prime axes: once an identity-oriented native
prime witness exists, no reciprocal-oriented native prime witness can coexist
with it. This is the atomic witness form of prime no-mixing. -/
def PRCCharacterPrimeIdentityWitnessExcludesReciprocal
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) →
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection r hr))
        (RatioOrbit.recip (primeDirection r hr)) →
        False

/-- Positive reciprocal-witness globalization for prime axes: if any native
prime witness is reciprocal-oriented, every native prime axis is
reciprocal-oriented. This is the reciprocal branch form of prime no-mixing. -/
def PRCCharacterPrimeReciprocalWitnessGlobalizes
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp))) →
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection r hr))
        (RatioOrbit.recip (primeDirection r hr))

/-- Prime identity orientation is trace-coherent when identity orientation at
one calibrated prime forces identity orientation at every calibrated prime. This
is the missing cross-prime relation; the current ratio-character laws are local
to multiplication and reciprocal and do not by themselves connect the orientation
choices of different prime axes. -/
def PRCCharacterPrimeIdentityTraceCoherent
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
        RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)

/-- The trace-free content of the prime identity transport blocker: if any native
prime axis is identity-oriented, then every native prime axis is
identity-oriented. This is definitionally the same proposition as prime
identity trace coherence, but the name records that the remaining obstruction is
branch uniformity, not trace construction. -/
def PRCCharacterPrimeIdentityBranchUniform
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
        RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)

/-- A character respects prime-axis trace connection when identity orientation
transports along the finite δ-trace component relating two prime axes. -/
def PRCCharacterPrimeIdentityRespectsTraceConnected
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      PRCPrimeAxisTraceConnected p hp r hr →
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
          RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)

/-- A more explicit form of the trace-transport rule: identity orientation
transports when two prime-axis traces are witnessed inside the same finite
δ-trace extension. -/
def PRCCharacterPrimeIdentityRespectsCommonTraceExtension
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      ∀ T : Trace,
        Trace.Extends (orbitPositionTrace p) T →
          Trace.Extends (orbitPositionTrace r) T →
            RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
              RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)

/-- Canonical-add-trace form: identity orientation transports through the
specific finite common extension `orbitPositionTrace (p + r)`. This removes the
arbitrary witness from common-trace transport; the only remaining content is that
the character respects the canonical finite δ-trace merger of two prime axes. -/
def PRCCharacterPrimeIdentityRespectsCanonicalAddTrace
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      Trace.Extends (orbitPositionTrace p) (orbitPositionTrace (p + r)) →
        Trace.Extends (orbitPositionTrace r) (orbitPositionTrace (p + r)) →
          RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
            RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)

/-- The exact trace-order law: identity orientation transports between prime axes
whose finite δ-orbit traces are comparable by extension. The structural
comparability of any two orbit traces is proved above, so this is the part that
must come from the ratio character respecting trace order. -/
def PRCCharacterPrimeIdentityRespectsComparableTrace
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      (Trace.Extends (orbitPositionTrace p) (orbitPositionTrace r) ∨
        Trace.Extends (orbitPositionTrace r) (orbitPositionTrace p)) →
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
          RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr)

/-- Identity orientation for an arbitrary nonzero orbit direction, not only for
prime axes. This lets trace transport pass through composite orbit positions. -/
def PRCCharacterOrbitDirectionIdentity
    (χ : RatioOrbit → RatioOrbit)
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero) : Prop :=
  RatioOrbit.crossEq (χ (orbitDirection p hp)) (orbitDirection p hp)

/-- Reciprocal orientation for an arbitrary nonzero orbit direction. -/
def PRCCharacterOrbitDirectionReciprocal
    (χ : RatioOrbit → RatioOrbit)
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero) : Prop :=
  RatioOrbit.crossEq
    (χ (orbitDirection p hp)) (RatioOrbit.recip (orbitDirection p hp))

/-- Prime identity witness globalization says that once any calibrated prime axis
chooses the identity branch, identity propagates to every nonunit orbit
direction. The no-prime-identity case is handled separately by the prime-witness
reflection lemma. -/
def PRCCharacterPrimeIdentityWitnessGlobalizesNonunit
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) →
      ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
        ¬ DistinctionNat.unit r →
          PRCCharacterOrbitDirectionIdentity χ r hr

/-- The one-step trace-order law: identity orientation is invariant under one
successor step of the nonzero δ-orbit. This is smaller than prime-to-prime
transport, because it acts before primality is imposed. -/
def PRCCharacterOrbitIdentityRespectsSuccessorStep
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    PRCCharacterOrbitDirectionIdentity χ p hp ↔
      PRCCharacterOrbitDirectionIdentity χ
        (DistinctionNat.succ p) (orbit_succ_ne_zero p)

/-- Forward one-step successor law for identity orientation on nonzero orbit
directions. -/
def PRCCharacterOrbitIdentityExtendsSuccessorStep
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    PRCCharacterOrbitDirectionIdentity χ p hp →
      PRCCharacterOrbitDirectionIdentity χ
        (DistinctionNat.succ p) (orbit_succ_ne_zero p)

/-- Backward one-step successor law for identity orientation on nonzero orbit
directions. -/
def PRCCharacterOrbitIdentityContractsSuccessorStep
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    PRCCharacterOrbitDirectionIdentity χ
      (DistinctionNat.succ p) (orbit_succ_ne_zero p) →
        PRCCharacterOrbitDirectionIdentity χ p hp

/-- The successor-step transport needed for trace coherence is exactly the
forward and backward one-step laws bundled together. -/
def PRCCharacterOrbitIdentitySuccessorTransport
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  PRCCharacterOrbitIdentityExtendsSuccessorStep χ ∧
    PRCCharacterOrbitIdentityContractsSuccessorStep χ

/-- Additive compatibility with the δ-successor operation on nonzero orbit
directions. This is the missing bridge between multiplicative ratio characters
and the trace/additive structure of the orbit. -/
def PRCCharacterOrbitSuccessorAdditiveCompatible
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    RatioOrbit.crossEq
      (χ (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p)))
      (RatioOrbit.add (χ (orbitDirection p hp)) RatioOrbit.one)

theorem PRCCharacterOrbitIdentityExtendsSuccessorStep_of_additive_compat
    {χ : RatioOrbit → RatioOrbit}
    (hadd : PRCCharacterOrbitSuccessorAdditiveCompatible χ) :
    PRCCharacterOrbitIdentityExtendsSuccessorStep χ := by
  intro p hp hpId
  have hχsucc := hadd p hp
  rw [PRCCharacterOrbitDirectionIdentity] at hpId ⊢
  rw [RatioOrbit.crossEq_iff_toRat_eq] at hχsucc hpId ⊢
  rw [RatioOrbit.add_toRat, RatioOrbit.one_toRat] at hχsucc
  rw [hχsucc, hpId]
  rw [orbitDirection_toRat, orbitDirection_toRat, DistinctionNat.toNat_succ]
  norm_num

theorem PRCCharacterOrbitIdentityContractsSuccessorStep_of_additive_compat
    {χ : RatioOrbit → RatioOrbit}
    (hadd : PRCCharacterOrbitSuccessorAdditiveCompatible χ) :
    PRCCharacterOrbitIdentityContractsSuccessorStep χ := by
  intro p hp hsuccId
  have hχsucc := hadd p hp
  rw [PRCCharacterOrbitDirectionIdentity] at hsuccId ⊢
  rw [RatioOrbit.crossEq_iff_toRat_eq] at hχsucc hsuccId ⊢
  rw [RatioOrbit.add_toRat, RatioOrbit.one_toRat] at hχsucc
  rw [hχsucc] at hsuccId
  rw [orbitDirection_toRat, DistinctionNat.toNat_succ] at hsuccId
  rw [orbitDirection_toRat]
  have hsuccCast :
      ((Nat.succ p.toNat : Nat) : ℚ) = (p.toNat : ℚ) + 1 := by
    norm_num
  rw [hsuccCast] at hsuccId
  linarith

theorem PRCCharacterOrbitIdentitySuccessorTransport_of_additive_compat
    {χ : RatioOrbit → RatioOrbit}
    (hadd : PRCCharacterOrbitSuccessorAdditiveCompatible χ) :
    PRCCharacterOrbitIdentitySuccessorTransport χ :=
  ⟨PRCCharacterOrbitIdentityExtendsSuccessorStep_of_additive_compat hadd,
    PRCCharacterOrbitIdentityContractsSuccessorStep_of_additive_compat hadd⟩

theorem orbit_succ_not_unit_of_nonzero_not_unit
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero)
    (hunit : ¬ DistinctionNat.unit p) :
    ¬ DistinctionNat.unit (DistinctionNat.succ p) := by
  intro hsuccUnit
  have hpNat0 : p.toNat ≠ 0 := by
    intro hz
    apply hp
    apply DistinctionNat.toNat_inj
    rw [hz, DistinctionNat.toNat_zero]
  have hpNat1 : p.toNat ≠ 1 := by
    intro hone
    exact hunit ((DistinctionNat.unit_iff_toNat_eq_one p).mpr hone)
  have hsuccNat1 : (DistinctionNat.succ p).toNat = 1 :=
    (DistinctionNat.unit_iff_toNat_eq_one (DistinctionNat.succ p)).mp hsuccUnit
  rw [DistinctionNat.toNat_succ] at hsuccNat1
  omega

/-- Every nonunit orbit direction is locally oriented: identity or reciprocal.
This is the nonprime analogue of the already proved local-prime orientation
alternative. -/
def PRCCharacterNonunitOrbitLocalOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionIdentity χ p hp ∨
        PRCCharacterOrbitDirectionReciprocal χ p hp

/-- Product-factor propagation for local orientation. If two nonunit factors are
locally identity-or-reciprocal oriented, their product is locally oriented too.
This is the exact multiplicative step needed to move from prime-axis
orientation to composite orbit directions. -/
def PRCCharacterOrbitProductLocalOrientationPropagates
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ a b p : DistinctionNat,
    ∀ ha : a ≠ DistinctionNat.zero, ∀ hb : b ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit a →
        ¬ DistinctionNat.unit b →
          ∀ hp : p ≠ DistinctionNat.zero,
            ¬ DistinctionNat.unit p →
              a * b = p →
                (PRCCharacterOrbitDirectionIdentity χ a ha ∨
                  PRCCharacterOrbitDirectionReciprocal χ a ha) →
                (PRCCharacterOrbitDirectionIdentity χ b hb ∨
                  PRCCharacterOrbitDirectionReciprocal χ b hb) →
                  PRCCharacterOrbitDirectionIdentity χ p hp ∨
                    PRCCharacterOrbitDirectionReciprocal χ p hp

theorem ratioOrbit_mul_congr {a₁ a₂ b₁ b₂ : RatioOrbit}
    (ha : RatioOrbit.crossEq a₁ a₂) (hb : RatioOrbit.crossEq b₁ b₂) :
    RatioOrbit.crossEq (RatioOrbit.mul a₁ b₁) (RatioOrbit.mul a₂ b₂) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at ha hb ⊢
  rw [RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, ha, hb]

theorem ratioOrbit_add_congr {a₁ a₂ b₁ b₂ : RatioOrbit}
    (ha : RatioOrbit.crossEq a₁ a₂) (hb : RatioOrbit.crossEq b₁ b₂) :
    RatioOrbit.crossEq (RatioOrbit.add a₁ b₁) (RatioOrbit.add a₂ b₂) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at ha hb ⊢
  rw [RatioOrbit.add_toRat, RatioOrbit.add_toRat, ha, hb]

theorem ratioOrbit_recip_congr {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [RatioOrbit.recip_toRat, RatioOrbit.recip_toRat, h]

theorem ratioOrbit_recip_left_crossEq_iff (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip a) b ↔
      RatioOrbit.crossEq a (RatioOrbit.recip b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.recip_toRat, RatioOrbit.recip_toRat]
  constructor
  · intro h
    rw [← h]
    exact (inv_inv a.toRat).symm
  · intro h
    rw [h]
    exact inv_inv b.toRat

theorem ratioOrbit_recip_recip_crossEq_self (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip (RatioOrbit.recip a)) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.recip_toRat]
  exact inv_inv a.toRat

theorem ratioOrbit_mul_recip_recip_crossEq_recip_mul
    (a b : RatioOrbit) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
      (RatioOrbit.recip (RatioOrbit.mul a b)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.recip_toRat, RatioOrbit.recip_toRat, RatioOrbit.recip_toRat,
    RatioOrbit.mul_toRat]
  by_cases ha : a.toRat = 0
  · simp [ha]
  · by_cases hb : b.toRat = 0
    · simp [hb]
    · field_simp [ha, hb]

def PRCCharacterReciprocalTwist (χ : RatioOrbit → RatioOrbit)
    (q : RatioOrbit) : RatioOrbit :=
  RatioOrbit.recip (χ q)

theorem PRCRatioCharacter.reciprocalTwist
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) :
    PRCRatioCharacter (PRCCharacterReciprocalTwist χ) where
  unit := by
    have hone := ratioOrbit_recip_congr hχ.unit
    have hrecOne : RatioOrbit.crossEq (RatioOrbit.recip RatioOrbit.one)
        RatioOrbit.one := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
        RatioOrbit.one_toRat]
      norm_num
    exact RatioOrbit.crossEq_trans hone hrecOne
  multiplicative := by
    intro x y
    exact RatioOrbit.crossEq_trans
      (ratioOrbit_recip_congr (hχ.multiplicative x y))
      (RatioOrbit.crossEq_symm
        (ratioOrbit_mul_recip_recip_crossEq_recip_mul (χ x) (χ y)))
  reciprocal := by
    intro x
    exact ratioOrbit_recip_congr (hχ.reciprocal x)
  normalized_invariant := by
    intro q
    exact ratioOrbit_recip_congr (hχ.normalized_invariant q)
  nonzero_preserving := by
    intro q hq
    rw [PRCCharacterReciprocalTwist, RatioOrbit.recip_toRat]
    exact inv_ne_zero (hχ.nonzero_preserving hq)

theorem PRCCharacterPrimeDirectionCalibrated.reciprocalTwist
    {χ : RatioOrbit → RatioOrbit}
    (hprime : PRCCharacterPrimeDirectionCalibrated χ) :
    PRCCharacterPrimeDirectionCalibrated (PRCCharacterReciprocalTwist χ) := by
  intro p hp
  exact RatioOrbit.crossEq_trans
    (RatioOrbit.crossEq_symm (reciprocal_symmetric (χ (primeDirection p hp))))
    (hprime p hp)

theorem PRCCharacterPrimePairProductCostConsistent.reciprocalTwist
    {χ : RatioOrbit → RatioOrbit}
    (hpair : PRCCharacterPrimePairProductCostConsistent χ) :
    PRCCharacterPrimePairProductCostConsistent
      (PRCCharacterReciprocalTwist χ) := by
  intro p hp r hr
  exact RatioOrbit.crossEq_trans
    (RatioOrbit.crossEq_symm
      (reciprocal_symmetric
        (χ (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))))
    (hpair p hp r hr)

theorem PRCAdmissibleRatioCharacter.reciprocalTwist
    {χ : RatioOrbit → RatioOrbit}
    (hadm : PRCAdmissibleRatioCharacter χ) :
    PRCAdmissibleRatioCharacter (PRCCharacterReciprocalTwist χ) where
  ratio_character := hadm.ratio_character.reciprocalTwist
  prime_calibrated := hadm.prime_calibrated.reciprocalTwist
  prime_pair_product_cost :=
    hadm.prime_pair_product_cost.reciprocalTwist

theorem PRCCharacterReciprocalTwist_prime_identity_iff_reciprocal
    (χ : RatioOrbit → RatioOrbit)
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    RatioOrbit.crossEq
        (PRCCharacterReciprocalTwist χ (primeDirection p hp))
        (primeDirection p hp) ↔
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)) := by
  exact ratioOrbit_recip_left_crossEq_iff
    (χ (primeDirection p hp)) (primeDirection p hp)

theorem PRCCharacterReciprocalTwist_two_identity_iff_reciprocal
    (χ : RatioOrbit → RatioOrbit) :
    RatioOrbit.crossEq
        (PRCCharacterReciprocalTwist χ twoPrimeDirection)
        twoPrimeDirection ↔
      RatioOrbit.crossEq (χ twoPrimeDirection)
        (RatioOrbit.recip twoPrimeDirection) := by
  exact ratioOrbit_recip_left_crossEq_iff (χ twoPrimeDirection) twoPrimeDirection

theorem PRCCharacterReciprocalTwist_prime_reciprocal_iff_identity
    (χ : RatioOrbit → RatioOrbit)
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    RatioOrbit.crossEq
        (PRCCharacterReciprocalTwist χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)) ↔
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) := by
  constructor
  · intro h
    have htoDoubleRecip :
        RatioOrbit.crossEq (χ (primeDirection p hp))
          (RatioOrbit.recip (RatioOrbit.recip (primeDirection p hp))) :=
      (ratioOrbit_recip_left_crossEq_iff
        (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp))).mp
        (by simpa [PRCCharacterReciprocalTwist] using h)
    exact RatioOrbit.crossEq_trans htoDoubleRecip
      (ratioOrbit_recip_recip_crossEq_self (primeDirection p hp))
  · intro h
    simpa [PRCCharacterReciprocalTwist] using ratioOrbit_recip_congr h

theorem PRCCharacterReciprocalTwist_two_reciprocal_iff_identity
    (χ : RatioOrbit → RatioOrbit) :
    RatioOrbit.crossEq
        (PRCCharacterReciprocalTwist χ twoPrimeDirection)
        (RatioOrbit.recip twoPrimeDirection) ↔
      RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection := by
  constructor
  · intro h
    have htoDoubleRecip :
        RatioOrbit.crossEq (χ twoPrimeDirection)
          (RatioOrbit.recip (RatioOrbit.recip twoPrimeDirection)) :=
      (ratioOrbit_recip_left_crossEq_iff
        (χ twoPrimeDirection)
        (RatioOrbit.recip twoPrimeDirection)).mp
        (by simpa [PRCCharacterReciprocalTwist] using h)
    exact RatioOrbit.crossEq_trans htoDoubleRecip
      (ratioOrbit_recip_recip_crossEq_self twoPrimeDirection)
  · intro h
    simpa [PRCCharacterReciprocalTwist] using ratioOrbit_recip_congr h

theorem orbitDirection_mul_crossEq
    (a b p : DistinctionNat)
    (ha : a ≠ DistinctionNat.zero) (hb : b ≠ DistinctionNat.zero)
    (hp : p ≠ DistinctionNat.zero)
    (hmul : a * b = p) :
    RatioOrbit.crossEq (orbitDirection p hp)
      (RatioOrbit.mul (orbitDirection a ha) (orbitDirection b hb)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, orbitDirection_toRat,
    RatioOrbit.mul_toRat, orbitDirection_toRat, orbitDirection_toRat]
  have hnat := congrArg DistinctionNat.toNat hmul
  rw [DistinctionNat.toNat_mul] at hnat
  exact_mod_cast hnat.symm

/-- A character is compatible with the native display of an orbit product when
the character value on the product orbit agrees with the character value on the
ratio product of the factor orbits. This is not automatic from
cross-equivalence; it is the quotient-respect step missing from the bare
character interface. -/
def PRCCharacterOrbitProductDisplayCompatible
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ a b p : DistinctionNat,
    ∀ ha : a ≠ DistinctionNat.zero, ∀ hb : b ≠ DistinctionNat.zero,
      ∀ hp : p ≠ DistinctionNat.zero,
        a * b = p →
          RatioOrbit.crossEq (χ (orbitDirection p hp))
            (χ (RatioOrbit.mul (orbitDirection a ha) (orbitDirection b hb)))

/-- Quotient-respect for a ratio character: equivalent ratio-orbit displays
must receive equivalent character values. This is the missing map-respects-setoid
condition for using a raw `RatioOrbit → RatioOrbit` function as a quotient-native
PRC character. -/
def PRCCharacterRespectsCrossEq (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q r : RatioOrbit,
    RatioOrbit.crossEq q r → RatioOrbit.crossEq (χ q) (χ r)

/-- Quotient-respect for doubled traces: equivalent ratio-orbit displays must
carry equivalent trace values. -/
def PRCDoubledTraceRespectsCrossEq (T : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q r : RatioOrbit,
    RatioOrbit.crossEq q r → RatioOrbit.crossEq (T q) (T r)

/-- Canonical-normalization target for ratio orbits. If two raw ratio displays
are cross-equivalent, native GCD normalization should return the same raw
representative. This is the exact quotient-normalization uniqueness statement
needed to turn `normalized_invariant` into general quotient respect. -/
def PRCNormalizeRatioCanonicalTarget : Prop :=
  ∀ q r : RatioOrbit,
    RatioOrbit.crossEq q r →
      DistinctionNat.normalizeRatio q = DistinctionNat.normalizeRatio r

/-- A signed-orbit display is sign-canonical when it is literally the
nonnegative orbit display of its absolute value, or literally the negated
nonnegative display of its absolute value. This records the raw representative
condition supplied by `signedQuotient`, not just balanced integer equality. -/
def PRCSignedOrbitSignCanonical (z : SignedOrbit) : Prop :=
  (0 ≤ z.toInt ∧ z = SignedOrbit.ofOrbit z.abs) ∨
    (z.toInt < 0 ∧ z = SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))

/-- A raw ratio display is reduced and sign-canonical when its numerator
absolute value is coprime to the positive denominator and the signed numerator
itself is in the canonical raw signed-orbit form. -/
def PRCRatioReducedSignCanonical (q : RatioOrbit) : Prop :=
  DistinctionNat.coprime q.num.abs q.den ∧
    PRCSignedOrbitSignCanonical q.num

theorem signedOrbit_ofOrbit_abs_self (n : DistinctionNat) :
    (SignedOrbit.ofOrbit n).abs = n := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.ofOrbit_toInt]
  simp

theorem signedOrbit_neg_ofOrbit_abs_self (n : DistinctionNat) :
    (SignedOrbit.negate (SignedOrbit.ofOrbit n)).abs = n := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.negate_toInt,
    SignedOrbit.ofOrbit_toInt]
  simp

theorem signedQuotient_signCanonical_of_divides
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero)
    (hdiv : DistinctionNat.divides d z.abs) :
    PRCSignedOrbitSignCanonical (DistinctionNat.signedQuotient z d hd) := by
  unfold DistinctionNat.signedQuotient
  by_cases hflag : z.nonnegFlag = true
  · left
    constructor
    · simp [hflag, SignedOrbit.ofOrbit_toInt]
    · rw [if_pos hflag]
      rw [signedOrbit_ofOrbit_abs_self]
  · have hflagFalse : z.nonnegFlag = false := by
      cases h : z.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hflag h
    right
    have hzneg : z.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff z).mp hflagFalse
    have hzabs_ne : z.abs ≠ DistinctionNat.zero := by
      apply SignedOrbit.abs_ne_zero_of_toInt_ne_zero
      omega
    have hq_ne :
        DistinctionNat.quotient z.abs d hd ≠ DistinctionNat.zero :=
      DistinctionNat.quotient_ne_zero_of_divides
        (n := z.abs) (d := d) hd hdiv hzabs_ne
    have hq_pos : 0 < (DistinctionNat.quotient z.abs d hd).toNat := by
      have hq_nat_ne : (DistinctionNat.quotient z.abs d hd).toNat ≠ 0 := by
        intro hzero
        apply hq_ne
        apply DistinctionNat.toNat_inj
        rw [hzero, DistinctionNat.toNat_zero]
      omega
    constructor
    · simp [hflagFalse, SignedOrbit.negate_toInt,
        SignedOrbit.ofOrbit_toInt]
      exact hq_pos
    · rw [if_neg hflag]
      rw [signedOrbit_neg_ofOrbit_abs_self]

theorem normalizeRatio_reduced_signCanonical (q : RatioOrbit) :
    PRCRatioReducedSignCanonical (DistinctionNat.normalizeRatio q) := by
  constructor
  · exact DistinctionNat.normalizeRatio_coprime q
  · unfold DistinctionNat.normalizeRatio
    exact signedQuotient_signCanonical_of_divides
      q.num (DistinctionNat.gcd q.num.abs q.den)
      (DistinctionNat.gcd_ne_zero_of_right_ne_zero
        q.num.abs q.den q.den_ne_zero)
      (DistinctionNat.gcd_divides_left q.num.abs q.den)

theorem PRCSignedOrbitSignCanonical.eq_of_toInt_eq
    {z w : SignedOrbit}
    (hz : PRCSignedOrbitSignCanonical z)
    (hw : PRCSignedOrbitSignCanonical w)
    (hzw : z.toInt = w.toInt) :
    z = w := by
  rcases hz with ⟨hzNonneg, hzCanon⟩ | ⟨hzNeg, hzCanon⟩
  · rcases hw with ⟨_hwNonneg, hwCanon⟩ | ⟨hwNeg, _hwCanon⟩
    · calc
        z = SignedOrbit.ofOrbit z.abs := hzCanon
        _ = SignedOrbit.ofOrbit w.abs := by
          have habs : z.abs = w.abs := by
            apply DistinctionNat.toNat_inj
            rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat, hzw]
          exact congrArg SignedOrbit.ofOrbit habs
        _ = w := hwCanon.symm
    · rw [hzw] at hzNonneg
      omega
  · rcases hw with ⟨hwNonneg, _hwCanon⟩ | ⟨_hwNeg, hwCanon⟩
    · rw [hzw] at hzNeg
      omega
    · calc
        z = SignedOrbit.negate (SignedOrbit.ofOrbit z.abs) := hzCanon
        _ = SignedOrbit.negate (SignedOrbit.ofOrbit w.abs) := by
          have habs : z.abs = w.abs := by
            apply DistinctionNat.toNat_inj
            rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat, hzw]
          exact congrArg (fun n => SignedOrbit.negate (SignedOrbit.ofOrbit n)) habs
        _ = w := hwCanon.symm

theorem PRCReducedSignCanonical_den_divides_of_crossEq
    {q r : RatioOrbit}
    (hq : PRCRatioReducedSignCanonical q)
    (_hr : PRCRatioReducedSignCanonical r)
    (hqr : RatioOrbit.crossEq q r) :
    DistinctionNat.divides q.den r.den := by
  have hcrossZ : q.num.toInt * (r.den.toNat : ℤ) =
      r.num.toInt * (q.den.toNat : ℤ) := by
    unfold RatioOrbit.crossEq at hqr
    have hdisplay :=
      (SignedOrbit.balanced_iff_toInt_eq
        (q.num.scaleByNat r.den) (r.num.scaleByNat q.den)).mp hqr
    rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt] at hdisplay
    exact hdisplay
  have hcrossNat :
      q.num.abs.toNat * r.den.toNat =
        r.num.abs.toNat * q.den.toNat := by
    have h := congrArg Int.natAbs hcrossZ
    rw [Int.natAbs_mul, Int.natAbs_mul,
      ← SignedOrbit.abs_toNat q.num, ← SignedOrbit.abs_toNat r.num,
      Int.natAbs_natCast, Int.natAbs_natCast] at h
    exact h
  have hdivMul :
      DistinctionNat.divides q.den (q.num.abs * r.den) := by
    rw [DistinctionNat.divides_iff_toNat_dvd, DistinctionNat.toNat_mul]
    rw [hcrossNat]
    exact Nat.dvd_mul_left q.den.toNat r.num.abs.toNat
  exact DistinctionNat.coprime_divides_of_divides_mul_left hq.1 hdivMul

theorem PRCReducedSignCanonical_den_dvd_of_crossEq
    {q r : RatioOrbit}
    (hq : PRCRatioReducedSignCanonical q)
    (hr : PRCRatioReducedSignCanonical r)
    (hqr : RatioOrbit.crossEq q r) :
    q.den.toNat ∣ r.den.toNat := by
  exact (DistinctionNat.divides_iff_toNat_dvd q.den r.den).mp
    (PRCReducedSignCanonical_den_divides_of_crossEq hq hr hqr)

theorem PRCReducedSignCanonical_den_eq_of_crossEq
    {q r : RatioOrbit}
    (hq : PRCRatioReducedSignCanonical q)
    (hr : PRCRatioReducedSignCanonical r)
    (hqr : RatioOrbit.crossEq q r) :
    q.den = r.den := by
  exact DistinctionNat.divides_antisymm
    (PRCReducedSignCanonical_den_divides_of_crossEq hq hr hqr)
    (PRCReducedSignCanonical_den_divides_of_crossEq hr hq
      (RatioOrbit.crossEq_symm hqr))

theorem PRCReducedSignCanonical_num_eq_of_crossEq
    {q r : RatioOrbit}
    (hq : PRCRatioReducedSignCanonical q)
    (hr : PRCRatioReducedSignCanonical r)
    (hqr : RatioOrbit.crossEq q r) :
    q.num = r.num := by
  have hden : q.den = r.den :=
    PRCReducedSignCanonical_den_eq_of_crossEq hq hr hqr
  have hcrossZ : q.num.toInt * (r.den.toNat : ℤ) =
      r.num.toInt * (q.den.toNat : ℤ) := by
    unfold RatioOrbit.crossEq at hqr
    have hdisplay :=
      (SignedOrbit.balanced_iff_toInt_eq
        (q.num.scaleByNat r.den) (r.num.scaleByNat q.den)).mp hqr
    rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt] at hdisplay
    exact hdisplay
  have hdenInt : (q.den.toNat : ℤ) ≠ 0 := by
    exact_mod_cast q.den_toNat_ne_zero
  have hnum : q.num.toInt = r.num.toInt := by
    rw [← hden] at hcrossZ
    exact mul_right_cancel₀ hdenInt hcrossZ
  exact PRCSignedOrbitSignCanonical.eq_of_toInt_eq hq.2 hr.2 hnum

/-- Reduced sign-canonical uniqueness is the exact remaining raw-display
number-theory blocker for canonical normalization. It says two reduced,
sign-canonical ratio displays with the same cross-multiplication class are
definitionally the same raw ratio orbit. -/
def PRCReducedSignCanonicalRatioUniqueTarget : Prop :=
  ∀ q r : RatioOrbit,
    PRCRatioReducedSignCanonical q →
      PRCRatioReducedSignCanonical r →
        RatioOrbit.crossEq q r →
          q = r

theorem PRCReducedSignCanonicalRatioUniqueTarget_proved :
    PRCReducedSignCanonicalRatioUniqueTarget := by
  intro q r hq hr hqr
  cases q with
  | mk qnum qden qden_ne_zero =>
    cases r with
    | mk rnum rden rden_ne_zero =>
      have hnum :
          qnum = rnum :=
        PRCReducedSignCanonical_num_eq_of_crossEq
          (q := ⟨qnum, qden, qden_ne_zero⟩)
          (r := ⟨rnum, rden, rden_ne_zero⟩) hq hr hqr
      have hden :
          qden = rden :=
        PRCReducedSignCanonical_den_eq_of_crossEq
          (q := ⟨qnum, qden, qden_ne_zero⟩)
          (r := ⟨rnum, rden, rden_ne_zero⟩) hq hr hqr
      subst hnum
      subst hden
      rfl

theorem PRCNormalizeRatioCanonicalTarget_of_reduced_signCanonical_unique
    (hunique : PRCReducedSignCanonicalRatioUniqueTarget) :
    PRCNormalizeRatioCanonicalTarget := by
  intro q r hqr
  apply hunique
  · exact normalizeRatio_reduced_signCanonical q
  · exact normalizeRatio_reduced_signCanonical r
  · exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm (DistinctionNat.normalizeRatio_crossEq q))
      (RatioOrbit.crossEq_trans hqr (DistinctionNat.normalizeRatio_crossEq r))

theorem PRCNormalizeRatioCanonicalTarget_proved :
    PRCNormalizeRatioCanonicalTarget :=
  PRCNormalizeRatioCanonicalTarget_of_reduced_signCanonical_unique
    PRCReducedSignCanonicalRatioUniqueTarget_proved

theorem PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcanon : PRCNormalizeRatioCanonicalTarget) :
    PRCCharacterRespectsCrossEq χ := by
  intro q r hqr
  exact RatioOrbit.crossEq_trans
    (hχ.normalized_invariant q)
    (RatioOrbit.crossEq_trans
      (by
        rw [hcanon q r hqr]
        exact RatioOrbit.crossEq_refl (χ (DistinctionNat.normalizeRatio r)))
      (RatioOrbit.crossEq_symm (hχ.normalized_invariant r)))

theorem PRCDoubledTraceRespectsCrossEq_of_normalizeRatio_canonical
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hcanon : PRCNormalizeRatioCanonicalTarget) :
    PRCDoubledTraceRespectsCrossEq T := by
  intro q r hqr
  exact RatioOrbit.crossEq_trans
    (hT.normalized_invariant q)
    (RatioOrbit.crossEq_trans
      (by
        rw [hcanon q r hqr]
        exact RatioOrbit.crossEq_refl (T (DistinctionNat.normalizeRatio r)))
      (RatioOrbit.crossEq_symm (hT.normalized_invariant r)))

theorem PRCDoubledTraceRespectsCrossEq_proved
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T) :
    PRCDoubledTraceRespectsCrossEq T :=
  PRCDoubledTraceRespectsCrossEq_of_normalizeRatio_canonical hT
    PRCNormalizeRatioCanonicalTarget_proved

theorem traceRootCandidate_one_of_trace_respect
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hrespect : PRCDoubledTraceRespectsCrossEq T) :
    RatioOrbit.crossEq (traceRootCandidate T RatioOrbit.one) RatioOrbit.one := by
  have htwoOne :
      RatioOrbit.crossEq (RatioOrbit.mul two RatioOrbit.one) two := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat, two_toRat,
      RatioOrbit.one_toRat]
    norm_num
  have htwoMulVal :
      (T (RatioOrbit.mul two RatioOrbit.one)).toRat = (T two).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq
      (T (RatioOrbit.mul two RatioOrbit.one)) (T two)).mp
        (hrespect (RatioOrbit.mul two RatioOrbit.one) two htwoOne)
  have htwoVal : (T two).toRat = (5 / 2 : ℚ) := by
    have h := hT.two_trace
    rw [RatioOrbit.crossEq_iff_toRat_eq] at h
    rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
      onRatioOrbit_toRat, two_toRat] at h
    norm_num at h
    exact h
  have honeVal : (T RatioOrbit.one).toRat = 2 := by
    have h := hT.unit_trace
    rw [RatioOrbit.crossEq_iff_toRat_eq, two_toRat] at h
    exact h
  rw [RatioOrbit.crossEq_iff_toRat_eq]
  rw [traceRootCandidate_toRat_of_nonzero T (by
    rw [RatioOrbit.one_toRat]
    norm_num : RatioOrbit.one.toRat ≠ 0)]
  rw [htwoMulVal, htwoVal, honeVal, RatioOrbit.one_toRat]
  norm_num

theorem traceRootCandidate_recip_toRat_of_nonzero
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hrespect : PRCDoubledTraceRespectsCrossEq T)
    {q : RatioOrbit} (hq : q.toRat ≠ 0) :
    (traceRootCandidate T (RatioOrbit.recip q)).toRat =
      (T q).toRat - (traceRootCandidate T q).toRat := by
  have hrecNonzero : (RatioOrbit.recip q).toRat ≠ 0 := by
    rw [RatioOrbit.recip_toRat]
    exact inv_ne_zero hq
  have htwoVal : (T two).toRat = (5 / 2 : ℚ) := by
    have h := hT.two_trace
    rw [RatioOrbit.crossEq_iff_toRat_eq] at h
    rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
      onRatioOrbit_toRat, two_toRat] at h
    norm_num at h
    exact h
  have hrecTraceVal : (T (RatioOrbit.recip q)).toRat = (T q).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq
      (T (RatioOrbit.recip q)) (T q)).mp
      (RatioOrbit.crossEq_symm (hT.reciprocal q))
  have htwoRecEq :
      RatioOrbit.crossEq
        (RatioOrbit.mul two (RatioOrbit.recip q))
        (div two q) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat, div_toRat,
      RatioOrbit.recip_toRat]
    rfl
  have htwoRecVal :
      (T (RatioOrbit.mul two (RatioOrbit.recip q))).toRat =
        (T (div two q)).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq
      (T (RatioOrbit.mul two (RatioOrbit.recip q))) (T (div two q))).mp
      (hrespect (RatioOrbit.mul two (RatioOrbit.recip q)) (div two q)
        htwoRecEq)
  have hdA := hT.dAlembert (x := two) (y := q)
    (by
      rw [two_toRat]
      norm_num : two.toRat ≠ 0)
    hq
  have hdAVal :
      (T (RatioOrbit.mul two q)).toRat + (T (div two q)).toRat =
        (T two).toRat * (T q).toRat := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.mul_toRat] at hdA
    exact hdA
  have hsum :
      (T (RatioOrbit.mul two q)).toRat + (T (div two q)).toRat =
        (5 / 2 : ℚ) * (T q).toRat := by
    rw [hdAVal, htwoVal]
  rw [traceRootCandidate_toRat_of_nonzero T hrecNonzero,
    traceRootCandidate_toRat_of_nonzero T hq]
  rw [htwoRecVal, hrecTraceVal]
  linarith

def PRCDoubledTraceLinearRootQuadraticTarget
    (T : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q : RatioOrbit, q.toRat ≠ 0 →
    RatioOrbit.crossEq
      (RatioOrbit.mul
        (traceRootCandidate T q)
        (RatioOrbit.sub (T q) (traceRootCandidate T q)))
      RatioOrbit.one

theorem traceRootCandidate_quadratic_of_trace_respect
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hrespect : PRCDoubledTraceRespectsCrossEq T) :
    PRCDoubledTraceLinearRootQuadraticTarget T := by
  intro q hq
  have htwoNonzero : two.toRat ≠ 0 := by
    rw [two_toRat]
    norm_num
  have htwoVal : (T two).toRat = (5 / 2 : ℚ) := by
    have h := hT.two_trace
    rw [RatioOrbit.crossEq_iff_toRat_eq] at h
    rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
      onRatioOrbit_toRat, two_toRat] at h
    norm_num at h
    exact h
  have honeVal : (T RatioOrbit.one).toRat = 2 := by
    have h := hT.unit_trace
    rw [RatioOrbit.crossEq_iff_toRat_eq, two_toRat] at h
    exact h
  have htwoTwoDA := hT.dAlembert (x := two) (y := two)
    htwoNonzero htwoNonzero
  have hdivTwoTwoEq :
      RatioOrbit.crossEq (div two two) RatioOrbit.one := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, div_toRat, two_toRat,
      RatioOrbit.one_toRat]
    norm_num
  have hdivTwoTwoVal :
      (T (div two two)).toRat = (T RatioOrbit.one).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
      (hrespect _ _ hdivTwoTwoEq)
  have htwoTwoVal :
      (T (RatioOrbit.mul two two)).toRat = (17 / 4 : ℚ) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.mul_toRat] at htwoTwoDA
    rw [hdivTwoTwoVal, htwoVal, honeVal] at htwoTwoDA
    linarith
  have hqqDA := hT.dAlembert (x := q) (y := q) hq hq
  have hdivqqEq :
      RatioOrbit.crossEq (div q q) RatioOrbit.one := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, div_toRat, RatioOrbit.one_toRat]
    field_simp [hq]
  have hdivqqVal :
      (T (div q q)).toRat = (T RatioOrbit.one).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
      (hrespect _ _ hdivqqEq)
  have hqqVal :
      (T (RatioOrbit.mul q q)).toRat = (T q).toRat ^ 2 - 2 := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.mul_toRat] at hqqDA
    rw [hdivqqVal, honeVal] at hqqDA
    nlinarith
  have hdivNonzero : (div two q).toRat ≠ 0 := by
    rw [div_toRat]
    exact div_ne_zero htwoNonzero hq
  have htwoqNonzero : (RatioOrbit.mul two q).toRat ≠ 0 := by
    rw [RatioOrbit.mul_toRat]
    exact mul_ne_zero htwoNonzero hq
  have hprodEq :
      RatioOrbit.crossEq
        (RatioOrbit.mul (RatioOrbit.mul two q) (div two q))
        (RatioOrbit.mul two two) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, div_toRat]
    field_simp [hq]
  have hquotEq :
      RatioOrbit.crossEq
        (div (RatioOrbit.mul two q) (div two q))
        (RatioOrbit.mul q q) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, div_toRat, RatioOrbit.mul_toRat,
      RatioOrbit.mul_toRat, div_toRat]
    field_simp [hq]
  have hprodVal :
      (T (RatioOrbit.mul (RatioOrbit.mul two q) (div two q))).toRat =
        (T (RatioOrbit.mul two two)).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
      (hrespect _ _ hprodEq)
  have hquotVal :
      (T (div (RatioOrbit.mul two q) (div two q))).toRat =
        (T (RatioOrbit.mul q q)).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
      (hrespect _ _ hquotEq)
  have hBDDA := hT.dAlembert
    (x := RatioOrbit.mul two q) (y := div two q)
    htwoqNonzero hdivNonzero
  have hBDVal :
      (T (RatioOrbit.mul two q)).toRat * (T (div two q)).toRat =
        (T q).toRat ^ 2 + (9 / 4 : ℚ) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.mul_toRat] at hBDDA
    rw [hprodVal, hquotVal, htwoTwoVal, hqqVal] at hBDDA
    nlinarith
  have hsumDA := hT.dAlembert (x := two) (y := q) htwoNonzero hq
  have hsumVal :
      (T (RatioOrbit.mul two q)).toRat + (T (div two q)).toRat =
        (5 / 2 : ℚ) * (T q).toRat := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.mul_toRat] at hsumDA
    rw [htwoVal] at hsumDA
    exact hsumDA
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.sub_toRat, RatioOrbit.one_toRat]
  rw [traceRootCandidate_toRat_of_nonzero T hq]
  have hgoal :
      ((2 * (T (RatioOrbit.mul two q)).toRat - (T q).toRat) / 3) *
        ((T q).toRat -
          ((2 * (T (RatioOrbit.mul two q)).toRat - (T q).toRat) / 3)) =
        1 := by
    have hDexpr :
        (T (div two q)).toRat =
          (5 / 2 : ℚ) * (T q).toRat -
            (T (RatioOrbit.mul two q)).toRat := by
      linarith
    have hBrel :
        (T (RatioOrbit.mul two q)).toRat *
          ((5 / 2 : ℚ) * (T q).toRat -
            (T (RatioOrbit.mul two q)).toRat) =
          (T q).toRat ^ 2 + (9 / 4 : ℚ) := by
      rw [← hDexpr]
      exact hBDVal
    nlinarith
  exact hgoal

theorem traceRootCandidate_reciprocal_of_quadratic
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hrespect : PRCDoubledTraceRespectsCrossEq T)
    (hquadratic : PRCDoubledTraceLinearRootQuadraticTarget T) :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq
        (traceRootCandidate T (RatioOrbit.recip q))
        (RatioOrbit.recip (traceRootCandidate T q)) := by
  intro q
  by_cases hq : q.toRat = 0
  · rw [RatioOrbit.crossEq_iff_toRat_eq]
    have hrecZero : (RatioOrbit.recip q).toRat = 0 := by
      rw [RatioOrbit.recip_toRat, hq]
      norm_num
    rw [traceRootCandidate, if_pos hrecZero]
    rw [traceRootCandidate, if_pos hq]
    rw [RatioOrbit.recip_toRat, RatioOrbit.zero_toRat]
    norm_num
  · have hrecSum := traceRootCandidate_recip_toRat_of_nonzero
      hT hrespect hq
    have hquad := hquadratic q hq
    rw [RatioOrbit.crossEq_iff_toRat_eq] at hquad ⊢
    rw [RatioOrbit.mul_toRat, RatioOrbit.sub_toRat,
      RatioOrbit.one_toRat] at hquad
    rw [RatioOrbit.recip_toRat]
    rw [hrecSum]
    have hx :
        (traceRootCandidate T q).toRat ≠ 0 := by
      intro hzero
      rw [hzero] at hquad
      norm_num at hquad
    field_simp [hx]
    exact hquad

theorem traceRootCandidate_nonzero_of_quadratic
    {T : RatioOrbit → RatioOrbit}
    (hquadratic : PRCDoubledTraceLinearRootQuadraticTarget T) :
    ∀ {q : RatioOrbit}, q.toRat ≠ 0 → (traceRootCandidate T q).toRat ≠ 0 := by
  intro q hq hzero
  have hquad := hquadratic q hq
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.sub_toRat, RatioOrbit.one_toRat] at hquad
  rw [hzero] at hquad
  norm_num at hquad

theorem traceRootCandidate_trace_of_quadratic
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hrespect : PRCDoubledTraceRespectsCrossEq T)
    (hzero : PRCDoubledTraceZeroCalibrated T)
    (hquadratic : PRCDoubledTraceLinearRootQuadraticTarget T) :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.add
          (traceRootCandidate T q)
          (RatioOrbit.recip (traceRootCandidate T q)))
        (T q) := by
  intro q
  by_cases hq : q.toRat = 0
  · rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      traceRootCandidate, if_pos hq, RatioOrbit.recip_toRat,
      RatioOrbit.zero_toRat]
    have hzeroVal : (T RatioOrbit.zero).toRat = 0 := by
      rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
        RatioOrbit.zero_toRat] at hzero
      exact hzero
    have hqZero :
        RatioOrbit.crossEq q RatioOrbit.zero := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat]
      exact hq
    have hTqZero :
        (T q).toRat = (T RatioOrbit.zero).toRat := by
      exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
        (hrespect q RatioOrbit.zero hqZero)
    rw [hTqZero, hzeroVal]
    norm_num
  · have hrecSum := traceRootCandidate_recip_toRat_of_nonzero
      hT hrespect hq
    have hrecCross := traceRootCandidate_reciprocal_of_quadratic
      hT hrespect hquadratic q
    have hrecVal :
        (RatioOrbit.recip (traceRootCandidate T q)).toRat =
          (traceRootCandidate T (RatioOrbit.recip q)).toRat := by
      exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
        (RatioOrbit.crossEq_symm hrecCross)
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat]
    rw [hrecVal, hrecSum]
    ring

theorem traceRootCandidate_normalized_of_trace_respect
    {T : RatioOrbit → RatioOrbit}
    (hrespect : PRCDoubledTraceRespectsCrossEq T) :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq (traceRootCandidate T q)
        (traceRootCandidate T (DistinctionNat.normalizeRatio q)) := by
  intro q
  by_cases hq : q.toRat = 0
  · have hnormZero : (DistinctionNat.normalizeRatio q).toRat = 0 := by
      rw [DistinctionNat.normalizeRatio_toRat, hq]
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    rw [traceRootCandidate, if_pos hq]
    rw [traceRootCandidate, if_pos hnormZero]
  · have hnormNonzero : (DistinctionNat.normalizeRatio q).toRat ≠ 0 := by
      rw [DistinctionNat.normalizeRatio_toRat]
      exact hq
    have hTqVal :
        (T q).toRat = (T (DistinctionNat.normalizeRatio q)).toRat := by
      exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
        (hrespect q (DistinctionNat.normalizeRatio q)
          (DistinctionNat.normalizeRatio_crossEq q))
    have htwoEq :
        RatioOrbit.crossEq
          (RatioOrbit.mul two q)
          (RatioOrbit.mul two (DistinctionNat.normalizeRatio q)) := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
        RatioOrbit.mul_toRat, DistinctionNat.normalizeRatio_toRat]
    have htwoVal :
        (T (RatioOrbit.mul two q)).toRat =
          (T (RatioOrbit.mul two (DistinctionNat.normalizeRatio q))).toRat := by
      exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
        (hrespect _ _ htwoEq)
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    rw [traceRootCandidate_toRat_of_nonzero T hq,
      traceRootCandidate_toRat_of_nonzero T hnormNonzero]
    rw [htwoVal, hTqVal]

theorem traceRootCandidate_multiplicative_of_trace_respect
    {T : RatioOrbit → RatioOrbit}
    (hT : PRCDoubledTraceHypotheses T)
    (hrespect : PRCDoubledTraceRespectsCrossEq T) :
    ∀ x y : RatioOrbit,
      RatioOrbit.crossEq (traceRootCandidate T (RatioOrbit.mul x y))
        (RatioOrbit.mul (traceRootCandidate T x) (traceRootCandidate T y)) := by
  intro x y
  by_cases hx : x.toRat = 0
  · have hxyZero : (RatioOrbit.mul x y).toRat = 0 := by
      rw [RatioOrbit.mul_toRat, hx]
      ring
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat]
    simp [traceRootCandidate, hxyZero, hx, RatioOrbit.zero_toRat]
  · by_cases hy : y.toRat = 0
    · have hxyZero : (RatioOrbit.mul x y).toRat = 0 := by
        rw [RatioOrbit.mul_toRat, hy]
        ring
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat]
      simp [traceRootCandidate, hxyZero, hx, hy, RatioOrbit.zero_toRat]
    · have htwoNonzero : two.toRat ≠ 0 := by
        rw [two_toRat]
        norm_num
      have hxyNonzero : (RatioOrbit.mul x y).toRat ≠ 0 := by
        rw [RatioOrbit.mul_toRat]
        exact mul_ne_zero hx hy
      have htwoXNonzero : (RatioOrbit.mul two x).toRat ≠ 0 := by
        rw [RatioOrbit.mul_toRat]
        exact mul_ne_zero htwoNonzero hx
      have htwoYNonzero : (RatioOrbit.mul two y).toRat ≠ 0 := by
        rw [RatioOrbit.mul_toRat]
        exact mul_ne_zero htwoNonzero hy
      have htwoXYNonzero :
          (RatioOrbit.mul two (RatioOrbit.mul x y)).toRat ≠ 0 := by
        rw [RatioOrbit.mul_toRat]
        exact mul_ne_zero htwoNonzero hxyNonzero
      have hdivXYNonzero : (div x y).toRat ≠ 0 := by
        rw [div_toRat]
        exact div_ne_zero hx hy
      have htwoVal : (T two).toRat = (5 / 2 : ℚ) := by
        have h := hT.two_trace
        rw [RatioOrbit.crossEq_iff_toRat_eq] at h
        rw [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
          RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
          onRatioOrbit_toRat, two_toRat] at h
        norm_num at h
        exact h
      have hACDA := hT.dAlembert (x := x) (y := y) hx hy
      have hACVal :
          (T x).toRat * (T y).toRat =
            (T (RatioOrbit.mul x y)).toRat + (T (div x y)).toRat := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
          RatioOrbit.mul_toRat] at hACDA
        exact hACDA.symm
      have hBDDA := hT.dAlembert
        (x := RatioOrbit.mul two x) (y := RatioOrbit.mul two y)
        htwoXNonzero htwoYNonzero
      have hBDProdEq :
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.mul two x) (RatioOrbit.mul two y))
            (RatioOrbit.mul two (RatioOrbit.mul two (RatioOrbit.mul x y))) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq]
        simp [RatioOrbit.mul_toRat]
        ring
      have hBDQuotEq :
          RatioOrbit.crossEq
            (div (RatioOrbit.mul two x) (RatioOrbit.mul two y))
            (div x y) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, div_toRat, div_toRat,
          RatioOrbit.mul_toRat, RatioOrbit.mul_toRat]
        field_simp [hy]
      have hBDProdVal :
          (T (RatioOrbit.mul (RatioOrbit.mul two x) (RatioOrbit.mul two y))).toRat =
            (T (RatioOrbit.mul two (RatioOrbit.mul two (RatioOrbit.mul x y)))).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hBDProdEq)
      have hBDQuotVal :
          (T (div (RatioOrbit.mul two x) (RatioOrbit.mul two y))).toRat =
            (T (div x y)).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hBDQuotEq)
      have hBDVal :
          (T (RatioOrbit.mul two x)).toRat *
            (T (RatioOrbit.mul two y)).toRat =
            (T (RatioOrbit.mul two (RatioOrbit.mul two (RatioOrbit.mul x y)))).toRat +
              (T (div x y)).toRat := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
          RatioOrbit.mul_toRat] at hBDDA
        rw [hBDProdVal, hBDQuotVal] at hBDDA
        exact hBDDA.symm
      have hBCDA := hT.dAlembert
        (x := RatioOrbit.mul two x) (y := y) htwoXNonzero hy
      have hBCProdEq :
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.mul two x) y)
            (RatioOrbit.mul two (RatioOrbit.mul x y)) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq]
        simp [RatioOrbit.mul_toRat]
        ring
      have hBCProdVal :
          (T (RatioOrbit.mul (RatioOrbit.mul two x) y)).toRat =
            (T (RatioOrbit.mul two (RatioOrbit.mul x y))).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hBCProdEq)
      have hBCVal :
          (T (RatioOrbit.mul two x)).toRat * (T y).toRat =
            (T (RatioOrbit.mul two (RatioOrbit.mul x y))).toRat +
              (T (div (RatioOrbit.mul two x) y)).toRat := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
          RatioOrbit.mul_toRat] at hBCDA
        rw [hBCProdVal] at hBCDA
        exact hBCDA.symm
      have hADDA := hT.dAlembert
        (x := x) (y := RatioOrbit.mul two y) hx htwoYNonzero
      have hADProdEq :
          RatioOrbit.crossEq
            (RatioOrbit.mul x (RatioOrbit.mul two y))
            (RatioOrbit.mul two (RatioOrbit.mul x y)) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq]
        simp [RatioOrbit.mul_toRat]
        ring
      have hADProdVal :
          (T (RatioOrbit.mul x (RatioOrbit.mul two y))).toRat =
            (T (RatioOrbit.mul two (RatioOrbit.mul x y))).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hADProdEq)
      have hADVal :
          (T x).toRat * (T (RatioOrbit.mul two y)).toRat =
            (T (RatioOrbit.mul two (RatioOrbit.mul x y))).toRat +
              (T (div x (RatioOrbit.mul two y))).toRat := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
          RatioOrbit.mul_toRat] at hADDA
        rw [hADProdVal] at hADDA
        exact hADDA.symm
      have hVWSumDA := hT.dAlembert (x := two) (y := div x y)
        htwoNonzero hdivXYNonzero
      have hVEq :
          RatioOrbit.crossEq
            (RatioOrbit.mul two (div x y))
            (div (RatioOrbit.mul two x) y) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
          div_toRat, div_toRat, RatioOrbit.mul_toRat]
        field_simp [hy]
      have hWEqRec :
          RatioOrbit.crossEq
            (div two (div x y))
            (RatioOrbit.recip (div x (RatioOrbit.mul two y))) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, div_toRat, div_toRat,
          RatioOrbit.recip_toRat, div_toRat, RatioOrbit.mul_toRat]
        field_simp [hx, hy]
      have hVVal :
          (T (RatioOrbit.mul two (div x y))).toRat =
            (T (div (RatioOrbit.mul two x) y)).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hVEq)
      have hWRecVal :
          (T (div two (div x y))).toRat =
            (T (RatioOrbit.recip (div x (RatioOrbit.mul two y)))).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hWEqRec)
      have hWVal :
          (T (RatioOrbit.recip (div x (RatioOrbit.mul two y)))).toRat =
            (T (div x (RatioOrbit.mul two y))).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (RatioOrbit.crossEq_symm
            (hT.reciprocal (div x (RatioOrbit.mul two y))))
      have hVWSumVal :
          (T (div (RatioOrbit.mul two x) y)).toRat +
            (T (div x (RatioOrbit.mul two y))).toRat =
            (5 / 2 : ℚ) * (T (div x y)).toRat := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
          RatioOrbit.mul_toRat] at hVWSumDA
        rw [hVVal, hWRecVal, hWVal, htwoVal] at hVWSumDA
        exact hVWSumDA
      have hGDA := hT.dAlembert
        (x := two) (y := RatioOrbit.mul two (RatioOrbit.mul x y))
        htwoNonzero htwoXYNonzero
      have hGQuotEq :
          RatioOrbit.crossEq
            (div two (RatioOrbit.mul two (RatioOrbit.mul x y)))
            (RatioOrbit.recip (RatioOrbit.mul x y)) := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, div_toRat,
          RatioOrbit.recip_toRat, RatioOrbit.mul_toRat,
          RatioOrbit.mul_toRat]
        field_simp [hx, hy]
      have hGQuotVal :
          (T (div two (RatioOrbit.mul two (RatioOrbit.mul x y)))).toRat =
            (T (RatioOrbit.recip (RatioOrbit.mul x y))).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (hrespect _ _ hGQuotEq)
      have hGRecVal :
          (T (RatioOrbit.recip (RatioOrbit.mul x y))).toRat =
            (T (RatioOrbit.mul x y)).toRat := by
        exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
          (RatioOrbit.crossEq_symm
            (hT.reciprocal (RatioOrbit.mul x y)))
      have hGVal :
          (T (RatioOrbit.mul two (RatioOrbit.mul two (RatioOrbit.mul x y)))).toRat +
            (T (RatioOrbit.mul x y)).toRat =
            (5 / 2 : ℚ) *
              (T (RatioOrbit.mul two (RatioOrbit.mul x y))).toRat := by
        rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
          RatioOrbit.mul_toRat] at hGDA
        rw [hGQuotVal, hGRecVal, htwoVal] at hGDA
        exact hGDA
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat]
      rw [traceRootCandidate_toRat_of_nonzero T hxyNonzero,
        traceRootCandidate_toRat_of_nonzero T hx,
        traceRootCandidate_toRat_of_nonzero T hy]
      nlinarith

theorem PRCDoubledTraceZeroCalibratedLinearRootTarget_proved :
    PRCDoubledTraceZeroCalibratedLinearRootTarget := by
  intro T hT hzero
  have hrespect : PRCDoubledTraceRespectsCrossEq T :=
    PRCDoubledTraceRespectsCrossEq_proved hT
  have hquadratic : PRCDoubledTraceLinearRootQuadraticTarget T :=
    traceRootCandidate_quadratic_of_trace_respect hT hrespect
  constructor
  · exact
      { unit := traceRootCandidate_one_of_trace_respect hT hrespect,
        multiplicative :=
          traceRootCandidate_multiplicative_of_trace_respect hT hrespect,
        reciprocal :=
          traceRootCandidate_reciprocal_of_quadratic hT hrespect hquadratic,
        normalized_invariant :=
          traceRootCandidate_normalized_of_trace_respect hrespect,
        nonzero_preserving :=
          traceRootCandidate_nonzero_of_quadratic hquadratic }
  · exact traceRootCandidate_trace_of_quadratic hT hrespect hzero hquadratic

theorem PRCDoubledTraceZeroCalibratedCoherentRootTarget_proved :
    PRCDoubledTraceZeroCalibratedCoherentRootTarget :=
  PRCDoubledTraceZeroCalibratedCoherentRootTarget_of_linear_root
    PRCDoubledTraceZeroCalibratedLinearRootTarget_proved

/-- Exact upstream zero-orbit blocker left after the coherent-root theorem:
native cost hypotheses must force the generated doubled trace to have zero
trace at the zero orbit. -/
def PRCNativeCostDoubledTraceZeroCalibratedTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

theorem PRCNativeCostCharacterTraceLiftTarget_of_doubled_trace_zero_calibrated
    (hzero : PRCNativeCostDoubledTraceZeroCalibratedTarget) :
    PRCNativeCostCharacterTraceLiftTarget := by
  intro F hF
  have hT : PRCDoubledTraceHypotheses (nativeCostDoubledTrace F) :=
    nativeCostDoubledTrace_hypotheses_of_native_cost_hypotheses hF
  have hz : PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F) :=
    hzero F hF
  rcases PRCDoubledTraceZeroCalibratedCoherentRootTarget_proved
      (nativeCostDoubledTrace F) hT hz with
    ⟨χ, hχ, htrace⟩
  exact ⟨χ, hχ, htrace⟩

theorem PRCNativeCostCharacterFactorizationTarget_of_doubled_trace_zero_calibrated
    (hzero : PRCNativeCostDoubledTraceZeroCalibratedTarget) :
    PRCNativeCostCharacterFactorizationTarget :=
  PRCNativeCostCharacterFactorizationTarget_of_trace_lift
    (PRCNativeCostCharacterTraceLiftTarget_of_doubled_trace_zero_calibrated
      hzero)

/-- Native zero-spike cost: canonical on every nonzero ratio orbit, but flattened
to `0` at the zero orbit. This satisfies the native cost interface because the
RCL only quantifies over nonzero inputs. -/
noncomputable def zeroFlatNativeCost (q : RatioOrbit) : RatioOrbit :=
  by
    classical
    exact if q.toRat = 0 then RatioOrbit.zero
      else if q = RatioOrbit.one then RatioOrbit.zero
      else onRatioOrbit q

theorem zeroFlatNativeCost_zero :
    zeroFlatNativeCost RatioOrbit.zero = RatioOrbit.zero := by
  classical
  rw [zeroFlatNativeCost, if_pos RatioOrbit.zero_toRat]

theorem zeroFlatNativeCost_one :
    zeroFlatNativeCost RatioOrbit.one = RatioOrbit.zero := by
  classical
  rw [zeroFlatNativeCost, if_neg (by
    rw [RatioOrbit.one_toRat]
    norm_num : RatioOrbit.one.toRat ≠ 0)]
  rw [if_pos rfl]

theorem zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero
    {q : RatioOrbit} (hq : q.toRat ≠ 0) :
    RatioOrbit.crossEq (zeroFlatNativeCost q) (onRatioOrbit q) := by
  classical
  by_cases hone : q = RatioOrbit.one
  · subst q
    rw [zeroFlatNativeCost_one]
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat,
      onRatioOrbit_toRat, RatioOrbit.one_toRat]
    norm_num
  · rw [zeroFlatNativeCost, if_neg hq, if_neg hone]
    exact RatioOrbit.crossEq_refl _

theorem zeroFlatNativeCost_hypotheses :
    PRCNativeCostHypotheses zeroFlatNativeCost where
  reciprocal := by
    intro q
    by_cases hq : q.toRat = 0
    · have hrec : (RatioOrbit.recip q).toRat = 0 := by
        rw [RatioOrbit.recip_toRat, hq]
        norm_num
      rw [RatioOrbit.crossEq_iff_toRat_eq]
      rw [zeroFlatNativeCost, if_pos hq]
      rw [zeroFlatNativeCost, if_pos hrec]
    · have hrec : (RatioOrbit.recip q).toRat ≠ 0 := by
        rw [RatioOrbit.recip_toRat]
        exact inv_ne_zero hq
      exact RatioOrbit.crossEq_trans
        (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hq)
        (RatioOrbit.crossEq_trans
          (reciprocal_symmetric q)
          (RatioOrbit.crossEq_symm
            (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hrec)))
  normalized_invariant := by
    intro q
    by_cases hq : q.toRat = 0
    · have hnorm : (DistinctionNat.normalizeRatio q).toRat = 0 := by
        rw [DistinctionNat.normalizeRatio_toRat, hq]
      rw [RatioOrbit.crossEq_iff_toRat_eq]
      rw [zeroFlatNativeCost, if_pos hq]
      rw [zeroFlatNativeCost, if_pos hnorm]
    · have hnorm : (DistinctionNat.normalizeRatio q).toRat ≠ 0 := by
        rw [DistinctionNat.normalizeRatio_toRat]
        exact hq
      exact RatioOrbit.crossEq_trans
        (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hq)
        (RatioOrbit.crossEq_trans
          (normalized_invariant q)
          (RatioOrbit.crossEq_symm
            (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hnorm)))
  canonical_rcl := by
    intro x y hx hy
    have hxy : (RatioOrbit.mul x y).toRat ≠ 0 := by
      rw [RatioOrbit.mul_toRat]
      exact mul_ne_zero hx hy
    have hdiv : (div x y).toRat ≠ 0 := by
      rw [div_toRat]
      exact div_ne_zero hx hy
    have hleft :
        RatioOrbit.crossEq
          (RatioOrbit.add
            (zeroFlatNativeCost (RatioOrbit.mul x y))
            (zeroFlatNativeCost (div x y)))
          (RatioOrbit.add
            (onRatioOrbit (RatioOrbit.mul x y))
            (onRatioOrbit (div x y))) := by
      exact ratioOrbit_add_congr
        (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hxy)
        (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hdiv)
    have hxF := zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hx
    have hyF := zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero hy
    have hmulInner :
        RatioOrbit.crossEq
          (RatioOrbit.mul (onRatioOrbit x) (onRatioOrbit y))
          (RatioOrbit.mul (zeroFlatNativeCost x) (zeroFlatNativeCost y)) :=
      ratioOrbit_mul_congr
        (RatioOrbit.crossEq_symm hxF)
        (RatioOrbit.crossEq_symm hyF)
    have hterm₁ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two
            (RatioOrbit.mul (onRatioOrbit x) (onRatioOrbit y)))
          (RatioOrbit.mul two
            (RatioOrbit.mul (zeroFlatNativeCost x)
              (zeroFlatNativeCost y))) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two) hmulInner
    have hterm₂ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (onRatioOrbit x))
          (RatioOrbit.mul two (zeroFlatNativeCost x)) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two)
        (RatioOrbit.crossEq_symm hxF)
    have hterm₃ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (onRatioOrbit y))
          (RatioOrbit.mul two (zeroFlatNativeCost y)) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two)
        (RatioOrbit.crossEq_symm hyF)
    have hright :
        RatioOrbit.crossEq
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two
                (RatioOrbit.mul (onRatioOrbit x) (onRatioOrbit y)))
              (RatioOrbit.mul two (onRatioOrbit x)))
            (RatioOrbit.mul two (onRatioOrbit y)))
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two
                (RatioOrbit.mul (zeroFlatNativeCost x)
                  (zeroFlatNativeCost y)))
              (RatioOrbit.mul two (zeroFlatNativeCost x)))
            (RatioOrbit.mul two (zeroFlatNativeCost y))) :=
      ratioOrbit_add_congr (ratioOrbit_add_congr hterm₁ hterm₂) hterm₃
    exact RatioOrbit.crossEq_trans hleft
      (RatioOrbit.crossEq_trans (canonical_rcl_surface hx hy) hright)
  unit_zero := zeroFlatNativeCost_one
  two_calibrated := by
    exact RatioOrbit.crossEq_trans
      (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero (by
        rw [two_toRat]
        norm_num : two.toRat ≠ 0))
      (RatioOrbit.crossEq_refl _)

theorem zeroFlatNativeCost_doubled_trace_zero :
    nativeCostDoubledTrace zeroFlatNativeCost RatioOrbit.zero =
      doubledTraceValue RatioOrbit.zero := by
  rw [nativeCostDoubledTrace, zeroFlatNativeCost_zero]

theorem zeroFlatNativeCost_not_doubled_trace_zero_calibrated :
    ¬ PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace zeroFlatNativeCost) := by
  intro h
  rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
    zeroFlatNativeCost_doubled_trace_zero, doubledTraceValue,
    RatioOrbit.mul_toRat, RatioOrbit.add_toRat, two_toRat,
    RatioOrbit.zero_toRat, RatioOrbit.one_toRat] at h
  norm_num at h

theorem PRCNativeCostDoubledTraceZeroCalibratedTarget_refuted :
    ¬ PRCNativeCostDoubledTraceZeroCalibratedTarget := by
  intro hzero
  exact zeroFlatNativeCost_not_doubled_trace_zero_calibrated
    (hzero zeroFlatNativeCost zeroFlatNativeCost_hypotheses)

theorem zeroFlatNativeCost_no_character_trace :
    ¬ ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
          PRCCharacterTraceMatchesCost zeroFlatNativeCost χ := by
  intro h
  rcases h with ⟨χ, hχ, htrace⟩
  let a : ℚ := (χ RatioOrbit.zero).toRat
  let b : ℚ := (χ two).toRat
  have hrec := hχ.reciprocal RatioOrbit.zero
  have hrecRat : a = a⁻¹ := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_zero_eq,
      RatioOrbit.recip_toRat] at hrec
    exact hrec
  have htraceZero := htrace RatioOrbit.zero
  have htraceZeroRat : a + a⁻¹ = 2 := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.recip_toRat, nativeCostDoubledTrace,
      zeroFlatNativeCost_zero, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.zero_toRat,
      RatioOrbit.one_toRat] at htraceZero
    norm_num at htraceZero
    exact htraceZero
  have ha : a = 1 := by
    linarith
  have hzeroMul :
      RatioOrbit.crossEq (RatioOrbit.mul RatioOrbit.zero two) RatioOrbit.zero := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      RatioOrbit.zero_toRat]
    ring
  have hrespect : PRCCharacterRespectsCrossEq χ :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved
  have hleft :
      (χ (RatioOrbit.mul RatioOrbit.zero two)).toRat = a := by
    exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
      (hrespect (RatioOrbit.mul RatioOrbit.zero two) RatioOrbit.zero hzeroMul)
  have hmul := hχ.multiplicative RatioOrbit.zero two
  have hmulRat :
      (χ (RatioOrbit.mul RatioOrbit.zero two)).toRat = a * b := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat] at hmul
    exact hmul
  have hb : b = 1 := by
    rw [hleft] at hmulRat
    nlinarith
  have htraceTwo := htrace two
  have hFtwo :
      (zeroFlatNativeCost two).toRat = (onRatioOrbit two).toRat := by
    exact (RatioOrbit.crossEq_iff_toRat_eq _ _).mp
      (zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero (by
        rw [two_toRat]
        norm_num : two.toRat ≠ 0))
  have htraceTwoRat : b + b⁻¹ = (5 / 2 : ℚ) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
      RatioOrbit.recip_toRat, nativeCostDoubledTrace, doubledTraceValue,
      RatioOrbit.mul_toRat, RatioOrbit.add_toRat, two_toRat,
      RatioOrbit.one_toRat] at htraceTwo
    rw [hFtwo, onRatioOrbit_toRat, two_toRat] at htraceTwo
    norm_num at htraceTwo
    exact htraceTwo
  rw [hb] at htraceTwoRat
  norm_num at htraceTwoRat

theorem PRCNativeCostCharacterTraceLiftTarget_refuted :
    ¬ PRCNativeCostCharacterTraceLiftTarget := by
  intro htrace
  exact zeroFlatNativeCost_no_character_trace
    (htrace zeroFlatNativeCost zeroFlatNativeCost_hypotheses)

theorem PRCNativeCostCharacterFactorizationTarget_refuted :
    ¬ PRCNativeCostCharacterFactorizationTarget := by
  intro hfactor
  exact PRCNativeCostCharacterTraceLiftTarget_refuted
    (PRCNativeCostCharacterTraceLiftTarget_of_factorization hfactor)

/-- Repaired native cost interface for character lifting: the native hypotheses
plus explicit zero calibration of the generated doubled trace. Pass 294 proves
the unqualified target is false, so this is the exact replacement surface. -/
def PRCZeroCalibratedNativeCostCharacterTraceLiftTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F) →
        ∃ χ : RatioOrbit → RatioOrbit,
          PRCRatioCharacter χ ∧
            PRCCharacterTraceMatchesCost F χ

def PRCZeroCalibratedNativeCostCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F) →
        ∃ χ : RatioOrbit → RatioOrbit,
          PRCRatioCharacter χ ∧
            ∀ q : RatioOrbit,
              RatioOrbit.crossEq (F q) (costFromCharacter χ q)

def PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget :
    Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F) →
        ∃ χ : RatioOrbit → RatioOrbit,
          PRCSignedAdmissibleRatioCharacter χ ∧
            ∀ q : RatioOrbit,
              RatioOrbit.crossEq (F q) (costFromCharacter χ q)

def PRCZeroCalibratedNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F) →
        ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)

theorem PRCZeroCalibratedNativeCostCharacterTraceLiftTarget_proved :
    PRCZeroCalibratedNativeCostCharacterTraceLiftTarget := by
  intro F hF hzero
  have hT : PRCDoubledTraceHypotheses (nativeCostDoubledTrace F) :=
    nativeCostDoubledTrace_hypotheses_of_native_cost_hypotheses hF
  rcases PRCDoubledTraceZeroCalibratedCoherentRootTarget_proved
      (nativeCostDoubledTrace F) hT hzero with
    ⟨χ, hχ, htrace⟩
  exact ⟨χ, hχ, htrace⟩

theorem PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved :
    PRCZeroCalibratedNativeCostCharacterFactorizationTarget := by
  intro F hF hzero
  rcases PRCZeroCalibratedNativeCostCharacterTraceLiftTarget_proved
      F hF hzero with
    ⟨χ, hχ, htrace⟩
  exact ⟨χ, hχ, cost_crossEq_of_PRCCharacterTraceMatchesCost htrace⟩

theorem PRCZeroCalibratedNativeCostUniquenessTarget_of_character_targets
    (hfactor : PRCZeroCalibratedNativeCostCharacterFactorizationTarget)
    (hrigid : PRCNativeCostCharacterRigidityTarget) :
    PRCZeroCalibratedNativeCostUniquenessTarget := by
  intro F hF hzero q
  rcases hfactor F hF hzero with ⟨χ, hχ, hFχ⟩
  have hcal :
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ two)) hF.two_calibrated
  exact RatioOrbit.crossEq_trans (hFχ q) (hrigid χ hχ hcal q)

theorem PRCZeroCalibratedNativeCostCharacterFactorizationTarget_not_old :
    PRCZeroCalibratedNativeCostCharacterFactorizationTarget ∧
      ¬ PRCNativeCostCharacterFactorizationTarget := by
  exact ⟨PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved,
    PRCNativeCostCharacterFactorizationTarget_refuted⟩

theorem PRCCharacterOrbitProductDisplayCompatible_of_crossEq_respect
    {χ : RatioOrbit → RatioOrbit}
    (hrespect : PRCCharacterRespectsCrossEq χ) :
    PRCCharacterOrbitProductDisplayCompatible χ := by
  intro a b p ha hb hp hmul
  exact hrespect (orbitDirection p hp)
    (RatioOrbit.mul (orbitDirection a ha) (orbitDirection b hb))
    (orbitDirection_mul_crossEq a b p ha hb hp hmul)

/-- Product factors cannot be mixed identity/reciprocal oriented. This is the
exact obstruction left after the pure same-orientation product algebra is
discharged. -/
def PRCCharacterOrbitProductNoMixedOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ a b p : DistinctionNat,
    ∀ ha : a ≠ DistinctionNat.zero, ∀ hb : b ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit a →
        ¬ DistinctionNat.unit b →
          ∀ _hp : p ≠ DistinctionNat.zero,
            ¬ DistinctionNat.unit p →
              a * b = p →
                (¬ (PRCCharacterOrbitDirectionIdentity χ a ha ∧
                  PRCCharacterOrbitDirectionReciprocal χ b hb)) ∧
                (¬ (PRCCharacterOrbitDirectionReciprocal χ a ha ∧
                  PRCCharacterOrbitDirectionIdentity χ b hb))

/-- Nonunit orbit orientation is coherent when every nonunit orbit direction
chooses the same branch: all identity or all reciprocal. This is the exact
coherence statement strong enough to rule out mixed product factors. -/
def PRCCharacterNonunitOrbitOrientationCoherent
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionIdentity χ p hp) ∨
  (∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionReciprocal χ p hp)

/-- Cross-nonunit no-mixing: identity orientation at one nonunit orbit direction
cannot coexist with reciprocal orientation at another. This is the branch-coupling
part of global nonunit coherence, separated from local orientation existence. -/
def PRCCharacterNoMixedNonunitOrbitOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
        ¬ DistinctionNat.unit r →
          PRCCharacterOrbitDirectionIdentity χ p hp →
            PRCCharacterOrbitDirectionReciprocal χ r hr →
              False

/-- Positive branch transport form of nonunit coherence: if one nonunit orbit
direction is identity-oriented, every nonunit orbit direction is identity-oriented.
This is the same branch-coupling law as no-mixing once local orientation is known,
but it states the missing transport direction directly. -/
def PRCCharacterNonunitIdentityBranchTransport
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionIdentity χ p hp →
        ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
          ¬ DistinctionNat.unit r →
            PRCCharacterOrbitDirectionIdentity χ r hr

/-- Witness form of identity branch transport: one identity-oriented nonunit
direction, if it exists, fixes the identity branch globally. -/
def PRCCharacterNonunitIdentityWitnessGlobalizes
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
    ∃ _hunit : ¬ DistinctionNat.unit p,
      PRCCharacterOrbitDirectionIdentity χ p hp) →
    ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit r →
        PRCCharacterOrbitDirectionIdentity χ r hr

/-- One-sided exclusion form of branch coupling: once any nonunit identity
witness exists, no nonunit reciprocal witness can coexist with it. Local
orientation is not bundled into this statement. -/
def PRCCharacterNonunitIdentityWitnessExcludesReciprocal
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  (∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
    ∃ _hunit : ¬ DistinctionNat.unit p,
      PRCCharacterOrbitDirectionIdentity χ p hp) →
    ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit r →
        PRCCharacterOrbitDirectionReciprocal χ r hr → False

/-- Existential no-mixed-witness form of branch coupling: there cannot
simultaneously be an identity-oriented nonunit witness and a reciprocal-oriented
nonunit witness. -/
def PRCCharacterNonunitNoMixedWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ¬ ((∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
        ∃ _hunit : ¬ DistinctionNat.unit p,
          PRCCharacterOrbitDirectionIdentity χ p hp) ∧
      (∃ r : DistinctionNat, ∃ hr : r ≠ DistinctionNat.zero,
        ∃ _hunit : ¬ DistinctionNat.unit r,
          PRCCharacterOrbitDirectionReciprocal χ r hr))

/-- The exact composite bridge still needed after prime witnesses are isolated:
prime no-mixing must control arbitrary nonunit witnesses. -/
def PRCCharacterPrimeWitnessesControlNonunitWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  PRCCharacterNoMixedPrimeWitnesses χ →
    PRCCharacterNonunitNoMixedWitnesses χ

/-- Contrapositive/reflection form of the composite bridge: if mixed nonunit
witnesses exist, then mixed prime-axis witnesses must already exist. This is the
exact reverse direction not supplied by product propagation. -/
def PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ((∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
      ∃ _hunit : ¬ DistinctionNat.unit p,
        PRCCharacterOrbitDirectionIdentity χ p hp) ∧
    (∃ r : DistinctionNat, ∃ hr : r ≠ DistinctionNat.zero,
      ∃ _hunit : ¬ DistinctionNat.unit r,
        PRCCharacterOrbitDirectionReciprocal χ r hr)) →
    ((∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) ∧
      (∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
        RatioOrbit.crossEq (χ (primeDirection r hr))
          (RatioOrbit.recip (primeDirection r hr))))

/-- Identity half of the mixed-context reflection law: in the presence of mixed
nonunit witnesses, the identity-oriented nonunit witness must reflect down to an
identity-oriented prime-axis witness. -/
def PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ((∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
      ∃ _hunit : ¬ DistinctionNat.unit p,
        PRCCharacterOrbitDirectionIdentity χ p hp) ∧
    (∃ r : DistinctionNat, ∃ hr : r ≠ DistinctionNat.zero,
      ∃ _hunit : ¬ DistinctionNat.unit r,
        PRCCharacterOrbitDirectionReciprocal χ r hr)) →
    ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)

/-- Reciprocal half of the mixed-context reflection law: in the presence of mixed
nonunit witnesses, the reciprocal-oriented nonunit witness must reflect down to a
reciprocal-oriented prime-axis witness. -/
def PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ((∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
      ∃ _hunit : ¬ DistinctionNat.unit p,
        PRCCharacterOrbitDirectionIdentity χ p hp) ∧
    (∃ r : DistinctionNat, ∃ hr : r ≠ DistinctionNat.zero,
      ∃ _hunit : ¬ DistinctionNat.unit r,
        PRCCharacterOrbitDirectionReciprocal χ r hr)) →
    ∃ r : DistinctionNat, ∃ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq (χ (primeDirection r hr))
        (RatioOrbit.recip (primeDirection r hr))

/-- Split form of mixed nonunit reflection: the identity and reciprocal witnesses
each pull back to the prime axis under the same mixed-context antecedent. -/
def PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness χ ∧
    PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness χ

/-- Reciprocal branch transport form of nonunit coherence: if one nonunit orbit
direction is reciprocal-oriented, every nonunit orbit direction is
reciprocal-oriented. Pass 57 isolates this as the dual half of two-branch
agreement. -/
def PRCCharacterNonunitReciprocalBranchTransport
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionReciprocal χ p hp →
        ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
          ¬ DistinctionNat.unit r →
            PRCCharacterOrbitDirectionReciprocal χ r hr

/-- Split transport form of two-branch agreement. -/
def PRCCharacterNonunitBranchTransportPair
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  PRCCharacterNonunitIdentityBranchTransport χ ∧
    PRCCharacterNonunitReciprocalBranchTransport χ

/-- Trace-order form of nonunit identity transport: identity orientation at one
nonunit orbit direction transports to another nonunit direction when their
finite δ-orbit traces are comparable. Since orbit traces are structurally
comparable, this is equivalent to global nonunit identity-branch transport, but
it exposes the next proof obligation as a trace-order law. -/
def PRCCharacterNonunitIdentityRespectsComparableTrace
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
        ¬ DistinctionNat.unit r →
          (Trace.Extends (orbitPositionTrace p) (orbitPositionTrace r) ∨
            Trace.Extends (orbitPositionTrace r) (orbitPositionTrace p)) →
            PRCCharacterOrbitDirectionIdentity χ p hp →
              PRCCharacterOrbitDirectionIdentity χ r hr

theorem orbit_mul_not_unit_of_left_not_unit
    {p r : DistinctionNat} (hunit : ¬ DistinctionNat.unit p) :
    ¬ DistinctionNat.unit (p * r) := by
  intro hprodUnit
  have hprodNat : (p * r).toNat = 1 :=
    (DistinctionNat.unit_iff_toNat_eq_one (p * r)).mp hprodUnit
  have hpNat1 : p.toNat ≠ 1 := by
    intro hone
    exact hunit ((DistinctionNat.unit_iff_toNat_eq_one p).mpr hone)
  rw [DistinctionNat.toNat_mul] at hprodNat
  have hpOne : p.toNat = 1 := Nat.eq_one_of_mul_eq_one_right hprodNat
  exact hpNat1 hpOne

theorem PRCCharacterNonunitOrbitLocalOrientation_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNonunitOrbitLocalOrientation χ := by
  intro p hp hunit
  rcases hcoh with hallId | hallRec
  · exact Or.inl (hallId p hp hunit)
  · exact Or.inr (hallRec p hp hunit)

theorem PRCCharacterNoMixedNonunitOrbitOrientation_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNoMixedNonunitOrbitOrientation χ := by
  intro p hp hunit r hr hrUnit hpId hrRec
  rcases hcoh with hallId | hallRec
  · have hrId := hallId r hr hrUnit
    have hself :
        RatioOrbit.crossEq (orbitDirection r hr)
          (RatioOrbit.recip (orbitDirection r hr)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
    exact orbitDirection_nonunit_not_crossEq_recip r hr hrUnit hself
  · have hpRec := hallRec p hp hunit
    have hself :
        RatioOrbit.crossEq (orbitDirection p hp)
          (RatioOrbit.recip (orbitDirection p hp)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
    exact orbitDirection_nonunit_not_crossEq_recip p hp hunit hself

theorem PRCCharacterNoMixedNonunitOrbitOrientation_of_product_no_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterOrbitProductNoMixedOrientation χ) :
    PRCCharacterNoMixedNonunitOrbitOrientation χ := by
  intro p hp hpUnit r hr hrUnit hpId hrRec
  exact ((hnomix p r (p * r) hp hr hpUnit hrUnit
    (DistinctionNat.mul_ne_zero hp hr)
    (orbit_mul_not_unit_of_left_not_unit hpUnit) rfl).1
      ⟨hpId, hrRec⟩)

theorem PRCCharacterOrbitProductNoMixedOrientation_of_no_mixed_nonunit
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNoMixedNonunitOrbitOrientation χ) :
    PRCCharacterOrbitProductNoMixedOrientation χ := by
  intro a b p ha hb haUnit hbUnit _hp _hpUnit _hmul
  constructor
  · rintro ⟨haId, hbRec⟩
    exact hnomix a ha haUnit b hb hbUnit haId hbRec
  · rintro ⟨haRec, hbId⟩
    exact hnomix b hb hbUnit a ha haUnit hbId haRec

theorem PRCCharacterOrbitProductNoMixedOrientation_iff_no_mixed_nonunit
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterOrbitProductNoMixedOrientation χ ↔
      PRCCharacterNoMixedNonunitOrbitOrientation χ :=
  ⟨PRCCharacterNoMixedNonunitOrbitOrientation_of_product_no_mixed,
    PRCCharacterOrbitProductNoMixedOrientation_of_no_mixed_nonunit⟩

theorem PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_branch_transport
    {χ : RatioOrbit → RatioOrbit}
    (htransport : PRCCharacterNonunitIdentityBranchTransport χ) :
    PRCCharacterNoMixedNonunitOrbitOrientation χ := by
  intro p hp hpUnit r hr hrUnit hpId hrRec
  have hrId := htransport p hp hpUnit hpId r hr hrUnit
  have hself :
      RatioOrbit.crossEq (orbitDirection r hr)
        (RatioOrbit.recip (orbitDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact orbitDirection_nonunit_not_crossEq_recip r hr hrUnit hself

theorem PRCCharacterOrbitProductNoMixedOrientation_of_identity_branch_transport
    {χ : RatioOrbit → RatioOrbit}
    (htransport : PRCCharacterNonunitIdentityBranchTransport χ) :
    PRCCharacterOrbitProductNoMixedOrientation χ :=
  PRCCharacterOrbitProductNoMixedOrientation_of_no_mixed_nonunit
    (PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_branch_transport
      htransport)

theorem PRCCharacterNonunitIdentityBranchTransport_of_local_no_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hnomix : PRCCharacterNoMixedNonunitOrbitOrientation χ) :
    PRCCharacterNonunitIdentityBranchTransport χ := by
  intro p hp hpUnit hpId r hr hrUnit
  rcases hlocal r hr hrUnit with hrId | hrRec
  · exact hrId
  · exact False.elim (hnomix p hp hpUnit r hr hrUnit hpId hrRec)

theorem PRCCharacterNonunitIdentityBranchTransport_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNonunitIdentityBranchTransport χ := by
  intro p hp hpUnit hpId r hr hrUnit
  rcases hcoh with hallId | hallRec
  · exact hallId r hr hrUnit
  · have hpRec := hallRec p hp hpUnit
    have hself :
        RatioOrbit.crossEq (orbitDirection p hp)
          (RatioOrbit.recip (orbitDirection p hp)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
    exact False.elim
      (orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself)

theorem PRCCharacterNonunitIdentityWitnessGlobalizes_of_branch_transport
    {χ : RatioOrbit → RatioOrbit}
    (htransport : PRCCharacterNonunitIdentityBranchTransport χ) :
    PRCCharacterNonunitIdentityWitnessGlobalizes χ := by
  rintro ⟨p, hp, hpUnit, hpId⟩ r hr hrUnit
  exact htransport p hp hpUnit hpId r hr hrUnit

theorem PRCCharacterNonunitIdentityBranchTransport_of_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hwitness : PRCCharacterNonunitIdentityWitnessGlobalizes χ) :
    PRCCharacterNonunitIdentityBranchTransport χ := by
  intro p hp hpUnit hpId r hr hrUnit
  exact hwitness ⟨p, hp, hpUnit, hpId⟩ r hr hrUnit

theorem PRCCharacterNonunitIdentityWitnessGlobalizes_iff_branch_transport
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNonunitIdentityWitnessGlobalizes χ ↔
      PRCCharacterNonunitIdentityBranchTransport χ :=
  ⟨PRCCharacterNonunitIdentityBranchTransport_of_witness_globalizes,
    PRCCharacterNonunitIdentityWitnessGlobalizes_of_branch_transport⟩

theorem PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_no_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNoMixedNonunitOrbitOrientation χ) :
    PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ := by
  rintro ⟨p, hp, hpUnit, hpId⟩ r hr hrUnit hrRec
  exact hnomix p hp hpUnit r hr hrUnit hpId hrRec

theorem PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_witness_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ) :
    PRCCharacterNoMixedNonunitOrbitOrientation χ := by
  intro p hp hpUnit r hr hrUnit hpId hrRec
  exact hexcl ⟨p, hp, hpUnit, hpId⟩ r hr hrUnit hrRec

theorem PRCCharacterNonunitIdentityWitnessExcludesReciprocal_iff_no_mixed
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ ↔
      PRCCharacterNoMixedNonunitOrbitOrientation χ :=
  ⟨PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_witness_excludes,
    PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_no_mixed⟩

theorem PRCCharacterNonunitNoMixedWitnesses_of_identity_witness_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ) :
    PRCCharacterNonunitNoMixedWitnesses χ := by
  rintro ⟨hid, hrec⟩
  rcases hrec with ⟨r, hr, hrUnit, hrRec⟩
  exact hexcl hid r hr hrUnit hrRec

theorem PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_no_mixed_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNonunitNoMixedWitnesses χ) :
    PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ := by
  intro hid r hr hrUnit hrRec
  exact hnomix ⟨hid, ⟨r, hr, hrUnit, hrRec⟩⟩

theorem PRCCharacterNonunitNoMixedWitnesses_iff_identity_witness_excludes
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNonunitNoMixedWitnesses χ ↔
      PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ :=
  ⟨PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_no_mixed_witnesses,
    PRCCharacterNonunitNoMixedWitnesses_of_identity_witness_excludes⟩

theorem PRCCharacterNoMixedPrimeWitnesses_of_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNoMixedPrimeOrientation χ) :
    PRCCharacterNoMixedPrimeWitnesses χ := by
  rintro ⟨hid, hrec⟩
  rcases hid with ⟨p, hp, hpId⟩
  rcases hrec with ⟨r, hr, hrRec⟩
  exact hnomix p hp r hr hpId hrRec

theorem PRCCharacterNoMixedPrimeOrientation_of_no_mixed_prime_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNoMixedPrimeWitnesses χ) :
    PRCCharacterNoMixedPrimeOrientation χ := by
  intro p hp r hr hpId hrRec
  exact hnomix ⟨⟨p, hp, hpId⟩, ⟨r, hr, hrRec⟩⟩

theorem PRCCharacterNoMixedPrimeWitnesses_iff_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNoMixedPrimeWitnesses χ ↔
      PRCCharacterNoMixedPrimeOrientation χ :=
  ⟨PRCCharacterNoMixedPrimeOrientation_of_no_mixed_prime_witnesses,
    PRCCharacterNoMixedPrimeWitnesses_of_no_mixed_prime_orientation⟩

theorem PRCCharacterNoMixedPrimeWitnesses_iff_not_mixed_prime_witnesses
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNoMixedPrimeWitnesses χ ↔
      ¬ PRCCharacterMixedPrimeWitnesses χ := by
  rfl

theorem PRCCharacterMixedPrimePairWitnesses_of_mixed_prime_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hmixed : PRCCharacterMixedPrimeWitnesses χ) :
    PRCCharacterMixedPrimePairWitnesses χ := by
  rcases hmixed with ⟨hid, hrec⟩
  rcases hid with ⟨p, hp, hpId⟩
  rcases hrec with ⟨r, hr, hrRec⟩
  exact ⟨p, hp, r, hr, hpId, hrRec⟩

theorem PRCCharacterMixedPrimeWitnesses_of_pair_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hpair : PRCCharacterMixedPrimePairWitnesses χ) :
    PRCCharacterMixedPrimeWitnesses χ := by
  rcases hpair with ⟨p, hp, r, hr, hpId, hrRec⟩
  exact ⟨⟨p, hp, hpId⟩, ⟨r, hr, hrRec⟩⟩

theorem PRCCharacterMixedPrimeWitnesses_iff_pair_witnesses
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterMixedPrimeWitnesses χ ↔
      PRCCharacterMixedPrimePairWitnesses χ :=
  ⟨PRCCharacterMixedPrimePairWitnesses_of_mixed_prime_witnesses,
    PRCCharacterMixedPrimeWitnesses_of_pair_witnesses⟩

theorem PRCCharacterNoMixedPrimeWitnesses_iff_not_mixed_prime_pair_witnesses
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNoMixedPrimeWitnesses χ ↔
      ¬ PRCCharacterMixedPrimePairWitnesses χ := by
  constructor
  · intro hnomix hpair
    exact hnomix (PRCCharacterMixedPrimeWitnesses_of_pair_witnesses hpair)
  · intro hnoPair hmixed
    exact hnoPair
      (PRCCharacterMixedPrimePairWitnesses_of_mixed_prime_witnesses hmixed)

theorem PRCCharacterMixedPrimePairWitnesses_same_or_distinct
    {χ : RatioOrbit → RatioOrbit}
    (hpair : PRCCharacterMixedPrimePairWitnesses χ) :
    PRCCharacterSamePrimeMixedPairWitnesses χ ∨
      PRCCharacterDistinctPrimeMixedPairWitnesses χ := by
  rcases hpair with ⟨p, hp, r, hr, hpId, hrRec⟩
  by_cases hEq : p = r
  · exact Or.inl ⟨p, hp, r, hr, hEq, hpId, hrRec⟩
  · exact Or.inr ⟨p, hp, r, hr, hEq, hpId, hrRec⟩

theorem PRCCharacterMixedPrimePairWitnesses_of_same
    {χ : RatioOrbit → RatioOrbit}
    (hsame : PRCCharacterSamePrimeMixedPairWitnesses χ) :
    PRCCharacterMixedPrimePairWitnesses χ := by
  rcases hsame with ⟨p, hp, r, hr, _hEq, hpId, hrRec⟩
  exact ⟨p, hp, r, hr, hpId, hrRec⟩

theorem PRCCharacterMixedPrimePairWitnesses_of_distinct
    {χ : RatioOrbit → RatioOrbit}
    (hdistinct : PRCCharacterDistinctPrimeMixedPairWitnesses χ) :
    PRCCharacterMixedPrimePairWitnesses χ := by
  rcases hdistinct with ⟨p, hp, r, hr, _hNe, hpId, hrRec⟩
  exact ⟨p, hp, r, hr, hpId, hrRec⟩

theorem PRCCharacterMixedPrimePairWitnesses_of_same_or_distinct
    {χ : RatioOrbit → RatioOrbit}
    (hsplit :
      PRCCharacterSamePrimeMixedPairWitnesses χ ∨
        PRCCharacterDistinctPrimeMixedPairWitnesses χ) :
    PRCCharacterMixedPrimePairWitnesses χ := by
  cases hsplit with
  | inl hsame => exact PRCCharacterMixedPrimePairWitnesses_of_same hsame
  | inr hdistinct => exact PRCCharacterMixedPrimePairWitnesses_of_distinct hdistinct

theorem PRCCharacterMixedPrimePairWitnesses_iff_same_or_distinct
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterMixedPrimePairWitnesses χ ↔
      PRCCharacterSamePrimeMixedPairWitnesses χ ∨
        PRCCharacterDistinctPrimeMixedPairWitnesses χ :=
  ⟨PRCCharacterMixedPrimePairWitnesses_same_or_distinct,
    PRCCharacterMixedPrimePairWitnesses_of_same_or_distinct⟩

theorem PRCCharacterNoMixedPrimeWitnesses_iff_no_same_and_no_distinct_pair
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNoMixedPrimeWitnesses χ ↔
      ¬ PRCCharacterSamePrimeMixedPairWitnesses χ ∧
        ¬ PRCCharacterDistinctPrimeMixedPairWitnesses χ := by
  constructor
  · intro hnomix
    constructor
    · intro hsame
      exact hnomix (PRCCharacterMixedPrimeWitnesses_of_pair_witnesses
        (PRCCharacterMixedPrimePairWitnesses_of_same hsame))
    · intro hdistinct
      exact hnomix (PRCCharacterMixedPrimeWitnesses_of_pair_witnesses
        (PRCCharacterMixedPrimePairWitnesses_of_distinct hdistinct))
  · intro hnoSplit hmixed
    exact (PRCCharacterNoMixedPrimeWitnesses_iff_not_mixed_prime_pair_witnesses.mpr
      (fun hpair =>
        (PRCCharacterMixedPrimePairWitnesses_iff_same_or_distinct.mp hpair).elim
          hnoSplit.1 hnoSplit.2)) hmixed

theorem PRCCharacterSamePrimeMixedPairWitnesses_absurd
    {χ : RatioOrbit → RatioOrbit} :
    ¬ PRCCharacterSamePrimeMixedPairWitnesses χ := by
  intro hsame
  rcases hsame with ⟨p, hp, r, hr, hEq, hpId, hrRec⟩
  subst r
  have hdir : primeDirection p hp = primeDirection p hr := by
    rfl
  have hpRec :
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)) := by
    simpa [hdir] using hrRec
  have hself :
      RatioOrbit.crossEq (primeDirection p hp)
        (RatioOrbit.recip (primeDirection p hp)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
  exact primeDirection_not_crossEq_recip p hp hself

theorem PRCCharacterNoMixedPrimeWitnesses_iff_not_distinct_prime_pair
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNoMixedPrimeWitnesses χ ↔
      ¬ PRCCharacterDistinctPrimeMixedPairWitnesses χ := by
  constructor
  · intro hnomix hdistinct
    exact hnomix (PRCCharacterMixedPrimeWitnesses_of_pair_witnesses
      (PRCCharacterMixedPrimePairWitnesses_of_distinct hdistinct))
  · intro hnoDistinct
    exact PRCCharacterNoMixedPrimeWitnesses_iff_no_same_and_no_distinct_pair.mpr
      ⟨PRCCharacterSamePrimeMixedPairWitnesses_absurd, hnoDistinct⟩

theorem PRCCharacterDistinctPrimeMixedPairWitnesses_absurd_of_branch_uniform
    {χ : RatioOrbit → RatioOrbit}
    (huniform : PRCCharacterPrimeIdentityBranchUniform χ) :
    ¬ PRCCharacterDistinctPrimeMixedPairWitnesses χ := by
  intro hdistinct
  rcases hdistinct with ⟨p, hp, r, hr, _hne, hpId, hrRec⟩
  have hrId := huniform p hp r hr hpId
  have hself :
      RatioOrbit.crossEq (primeDirection r hr)
        (RatioOrbit.recip (primeDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact primeDirection_not_crossEq_recip r hr hself

theorem PRCCharacterPrimeIdentityBranchUniform_of_local_no_distinct_prime_pair
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hnoDistinct : ¬ PRCCharacterDistinctPrimeMixedPairWitnesses χ) :
    PRCCharacterPrimeIdentityBranchUniform χ := by
  intro p hp r hr hpId
  by_cases hEq : p = r
  · subst r
    simpa [primeDirection] using hpId
  · rcases hlocal r hr with hrId | hrRec
    · exact hrId
    · exact False.elim (hnoDistinct ⟨p, hp, r, hr, hEq, hpId, hrRec⟩)

theorem PRCCharacterPrimeIdentityBranchUniform_iff_no_distinct_prime_pair_of_local
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ) :
    PRCCharacterPrimeIdentityBranchUniform χ ↔
      ¬ PRCCharacterDistinctPrimeMixedPairWitnesses χ :=
  ⟨PRCCharacterDistinctPrimeMixedPairWitnesses_absurd_of_branch_uniform,
    PRCCharacterPrimeIdentityBranchUniform_of_local_no_distinct_prime_pair hlocal⟩

theorem PRCCharacterPrimeIdentityBranchUniform_of_identity_iff_two
    {χ : RatioOrbit → RatioOrbit}
    (hiff : PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ) :
    PRCCharacterPrimeIdentityBranchUniform χ := by
  intro p hp r hr hpId
  exact (hiff r hr).mpr ((hiff p hp).mp hpId)

theorem PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_branch_uniform
    {χ : RatioOrbit → RatioOrbit}
    (huniform : PRCCharacterPrimeIdentityBranchUniform χ) :
    PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ := by
  intro p hp
  constructor
  · intro hpId
    exact huniform p hp twoOrbit twoOrbit_primeOrbit hpId
  · intro htwoId
    exact huniform twoOrbit twoOrbit_primeOrbit p hp htwoId

theorem PRCCharacterPrimeIdentityBranchUniform_iff_identity_iff_two
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityBranchUniform χ ↔
      PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ :=
  ⟨PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_branch_uniform,
    PRCCharacterPrimeIdentityBranchUniform_of_identity_iff_two⟩

theorem PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNoMixedPrimeOrientation χ) :
    PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ := by
  rintro ⟨p, hp, hpId⟩ r hr hrRec
  exact hnomix p hp r hr hpId hrRec

theorem PRCCharacterNoMixedPrimeOrientation_of_identity_witness_excludes_reciprocal
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ) :
    PRCCharacterNoMixedPrimeOrientation χ := by
  intro p hp r hr hpId hrRec
  exact hexcl ⟨p, hp, hpId⟩ r hr hrRec

theorem PRCCharacterPrimeIdentityWitnessExcludesReciprocal_iff_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ ↔
      PRCCharacterNoMixedPrimeOrientation χ :=
  ⟨PRCCharacterNoMixedPrimeOrientation_of_identity_witness_excludes_reciprocal,
    PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_orientation⟩

theorem PRCCharacterNoMixedPrimeWitnesses_of_identity_witness_excludes_reciprocal
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ) :
    PRCCharacterNoMixedPrimeWitnesses χ := by
  rintro ⟨hid, hrec⟩
  rcases hrec with ⟨r, hr, hrRec⟩
  exact hexcl hid r hr hrRec

theorem PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNoMixedPrimeWitnesses χ) :
    PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ := by
  intro hid r hr hrRec
  exact hnomix ⟨hid, ⟨r, hr, hrRec⟩⟩

theorem PRCCharacterNoMixedPrimeWitnesses_iff_identity_witness_excludes_reciprocal
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNoMixedPrimeWitnesses χ ↔
      PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ :=
  ⟨PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_witnesses,
    PRCCharacterNoMixedPrimeWitnesses_of_identity_witness_excludes_reciprocal⟩

theorem PRCCharacterPrimeReciprocalWitnessGlobalizes_of_local_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hnomix : PRCCharacterNoMixedPrimeOrientation χ) :
    PRCCharacterPrimeReciprocalWitnessGlobalizes χ := by
  rintro ⟨p, hp, hpRec⟩ r hr
  rcases hlocal r hr with hrId | hrRec
  · exact False.elim (hnomix r hr p hp hrId hpRec)
  · exact hrRec

theorem PRCCharacterNoMixedPrimeOrientation_of_reciprocal_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hglobal : PRCCharacterPrimeReciprocalWitnessGlobalizes χ) :
    PRCCharacterNoMixedPrimeOrientation χ := by
  intro p hp r hr hpId hrRec
  have hpRec := hglobal ⟨r, hr, hrRec⟩ p hp
  have hself :
      RatioOrbit.crossEq
        (primeDirection p hp)
        (RatioOrbit.recip (primeDirection p hp)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
  exact primeDirection_not_crossEq_recip p hp hself

theorem PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hglobal : PRCCharacterPrimeReciprocalWitnessGlobalizes χ) :
    PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ := by
  intro p hp hpRec
  exact hglobal ⟨p, hp, hpRec⟩ twoOrbit twoOrbit_primeOrbit

theorem PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_reciprocal_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hglobal : PRCCharacterPrimeReciprocalWitnessGlobalizes χ) :
    PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ := by
  intro htwoRec p hp
  exact hglobal ⟨twoOrbit, twoOrbit_primeOrbit, htwoRec⟩ p hp

theorem PRCCharacterPrimeReciprocalWitnessGlobalizesSplit_of_reciprocal_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hglobal : PRCCharacterPrimeReciprocalWitnessGlobalizes χ) :
    PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ :=
  ⟨PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_witness_globalizes
      hglobal,
    PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_reciprocal_witness_globalizes
      hglobal⟩

theorem PRCCharacterPrimeReciprocalWitnessGlobalizes_of_split
    {χ : RatioOrbit → RatioOrbit}
    (hsplit : PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ) :
    PRCCharacterPrimeReciprocalWitnessGlobalizes χ := by
  rintro ⟨p, hp, hpRec⟩ r hr
  exact hsplit.2 (hsplit.1 p hp hpRec) r hr

theorem PRCCharacterPrimeReciprocalWitnessGlobalizes_iff_split
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeReciprocalWitnessGlobalizes χ ↔
      PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ :=
  ⟨PRCCharacterPrimeReciprocalWitnessGlobalizesSplit_of_reciprocal_witness_globalizes,
    PRCCharacterPrimeReciprocalWitnessGlobalizes_of_split⟩

theorem PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_twist_identity_forces_two
    {χ : RatioOrbit → RatioOrbit}
    (hforces :
      PRCCharacterPrimeIdentityForcesTwoPrimeIdentity
        (PRCCharacterReciprocalTwist χ)) :
    PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ := by
  intro p hp hpRec
  have hpTwistId :
      RatioOrbit.crossEq
        (PRCCharacterReciprocalTwist χ (primeDirection p hp))
        (primeDirection p hp) :=
    (PRCCharacterReciprocalTwist_prime_identity_iff_reciprocal
      χ p hp).mpr hpRec
  have htwoTwistId := hforces p hp hpTwistId
  exact (PRCCharacterReciprocalTwist_two_identity_iff_reciprocal χ).mp
    htwoTwistId

theorem PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_reciprocal_twist_reciprocal_forces_two
    {χ : RatioOrbit → RatioOrbit}
    (hforces :
      PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal
        (PRCCharacterReciprocalTwist χ)) :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ := by
  intro p hp hpId
  have hpTwistRec :
      RatioOrbit.crossEq
        (PRCCharacterReciprocalTwist χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)) :=
    (PRCCharacterReciprocalTwist_prime_reciprocal_iff_identity
      χ p hp).mpr hpId
  have htwoTwistRec := hforces p hp hpTwistRec
  exact (PRCCharacterReciprocalTwist_two_reciprocal_iff_identity χ).mp
    htwoTwistRec

theorem PRCCharacterTwoPrimeBranchControlsPrimes_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterPrimeOrientationCoherent χ) :
    PRCCharacterTwoPrimeBranchControlsPrimes χ := by
  constructor
  · intro htwoId
    rcases hcoh with hallId | hallRec
    · exact hallId
    · have htwoRec := hallRec twoOrbit twoOrbit_primeOrbit
      have hself :
          RatioOrbit.crossEq twoPrimeDirection
            (RatioOrbit.recip twoPrimeDirection) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
      exact False.elim
        (primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself)
  · intro htwoRec
    rcases hcoh with hallId | hallRec
    · have htwoId := hallId twoOrbit twoOrbit_primeOrbit
      have hself :
          RatioOrbit.crossEq twoPrimeDirection
            (RatioOrbit.recip twoPrimeDirection) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
      exact False.elim
        (primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself)
    · exact hallRec

theorem PRCCharacterPrimeOrientationCoherent_of_local_two_prime_branch_controls
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hctrl : PRCCharacterTwoPrimeBranchControlsPrimes χ) :
    PRCCharacterPrimeOrientationCoherent χ := by
  rcases hlocal twoOrbit twoOrbit_primeOrbit with htwoId | htwoRec
  · exact Or.inl (hctrl.1 htwoId)
  · exact Or.inr (hctrl.2 htwoRec)

theorem PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_local_two_prime_branch_controls
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hctrl : PRCCharacterTwoPrimeBranchControlsPrimes χ) :
    PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ := by
  intro p hp
  constructor
  · intro hpId
    rcases hlocal twoOrbit twoOrbit_primeOrbit with htwoId | htwoRec
    · exact htwoId
    · have hpRec := hctrl.2 htwoRec p hp
      have hself :
          RatioOrbit.crossEq (primeDirection p hp)
            (RatioOrbit.recip (primeDirection p hp)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
      exact False.elim (primeDirection_not_crossEq_recip p hp hself)
  · intro htwoId
    exact hctrl.1 htwoId p hp

theorem PRCCharacterTwoPrimeBranchControlsPrimes_of_local_prime_identity_iff_two
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hiff : PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ) :
    PRCCharacterTwoPrimeBranchControlsPrimes χ := by
  constructor
  · intro htwoId p hp
    exact (hiff p hp).mpr htwoId
  · intro htwoRec p hp
    rcases hlocal p hp with hpId | hpRec
    · have htwoId := (hiff p hp).mp hpId
      have hself :
          RatioOrbit.crossEq twoPrimeDirection
            (RatioOrbit.recip twoPrimeDirection) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
      exact False.elim
        (primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself)
    · exact hpRec

theorem PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_identity_iff_two
    {χ : RatioOrbit → RatioOrbit}
    (hiff : PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ) :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ := by
  intro p hp hpId
  exact (hiff p hp).mp hpId

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_identity_forces_two
    {χ : RatioOrbit → RatioOrbit}
    (hforces : PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ := by
  intro htwoRec p hp hpId
  have htwoId := hforces p hp hpId
  have hself :
      RatioOrbit.crossEq twoPrimeDirection
        (RatioOrbit.recip twoPrimeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
  exact primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself

theorem PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_local_two_prime_reciprocal_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hexcl : PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ) :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ := by
  intro p hp hpId
  rcases hlocal twoOrbit twoOrbit_primeOrbit with htwoId | htwoRec
  · exact htwoId
  · exact False.elim ((hexcl htwoRec p hp) hpId)

theorem PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_iff_two_prime_reciprocal_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ) :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ ↔
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ :=
  ⟨PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_identity_forces_two,
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_local_two_prime_reciprocal_excludes
      hlocal⟩

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ := by
  intro htwoRec hwitness
  rcases hwitness with ⟨p, hp, hpId⟩
  exact (hexcl htwoRec p hp) hpId

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_witness_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ := by
  intro htwoRec p hp hpId
  exact hexcl htwoRec ⟨p, hp, hpId⟩

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_iff_witness :
    {χ : RatioOrbit → RatioOrbit} →
    (PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ ↔
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ) := by
  intro χ
  exact
    ⟨PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_excludes,
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_witness_excludes⟩

theorem PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_iff_two_prime_reciprocal_excludes_witness
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ) :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ ↔
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ :=
  (PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_iff_two_prime_reciprocal_excludes
    hlocal).trans
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_iff_witness

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_not_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hmix : ¬ PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ := by
  intro htwoRec hwitness
  exact hmix ⟨htwoRec, hwitness⟩

theorem PRCCharacter_not_mixed_of_two_prime_reciprocal_excludes_prime_identity_witness
    {χ : RatioOrbit → RatioOrbit}
    (hexcl : PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ) :
    ¬ PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ := by
  intro hmix
  exact hexcl hmix.1 hmix.2

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_iff_not_mixed :
    {χ : RatioOrbit → RatioOrbit} →
    (PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ ↔
      ¬ PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ) := by
  intro χ
  exact
    ⟨PRCCharacter_not_mixed_of_two_prime_reciprocal_excludes_prime_identity_witness,
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_not_mixed⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_of_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hmix : PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ) :
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ := by
  rcases hmix with ⟨htwoRec, p, hp, hpId⟩
  refine ⟨htwoRec, ?_⟩
  by_cases hptwo : p = twoOrbit
  · exfalso
    have hdir : primeDirection p hp = twoPrimeDirection := by
      subst hptwo
      rfl
    rw [hdir] at hpId
    have hself :
        RatioOrbit.crossEq twoPrimeDirection
          (RatioOrbit.recip twoPrimeDirection) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) htwoRec
    exact primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself
  · exact ⟨p, hp, hptwo, hpId⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed_of_non_two_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hmix : PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ) :
    PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ := by
  rcases hmix with ⟨htwoRec, p, hp, _hpne, hpId⟩
  exact ⟨htwoRec, p, hp, hpId⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed_iff_non_two :
    {χ : RatioOrbit → RatioOrbit} →
    (PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ ↔
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ) := by
  intro χ
  exact
    ⟨PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_of_mixed,
      PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed_of_non_two_mixed⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_non_two_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hmix : PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ) :
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ := by
  rcases hmix with ⟨htwoRec, p, hp, hpne, hpId⟩
  have hmulχ :
      RatioOrbit.crossEq
        (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
        (RatioOrbit.mul (χ twoPrimeDirection) (χ (primeDirection p hp))) :=
    hχ.multiplicative twoPrimeDirection (primeDirection p hp)
  have hmulTarget :
      RatioOrbit.crossEq
        (RatioOrbit.mul (χ twoPrimeDirection) (χ (primeDirection p hp)))
        (RatioOrbit.mul
          (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)) :=
    ratioOrbit_mul_congr htwoRec hpId
  exact ⟨htwoRec, p, hp, hpne, hpId,
    RatioOrbit.crossEq_trans hmulχ hmulTarget⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_of_composite_defect
    {χ : RatioOrbit → RatioOrbit}
    (hdefect :
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ) :
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ := by
  rcases hdefect with ⟨htwoRec, p, hp, hpne, hpId, _hprod⟩
  exact ⟨htwoRec, p, hp, hpne, hpId⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_iff_composite_defect_of_character
    {χ : RatioOrbit → RatioOrbit} (hχ : PRCRatioCharacter χ) :
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ ↔
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ :=
  ⟨PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_non_two_mixed hχ,
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_of_composite_defect⟩

theorem two_prime_composite_mixed_image_jcost_mismatch
    (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p) :
    ¬ RatioOrbit.crossEq
      (onRatioOrbit
        (RatioOrbit.mul
          (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)))
      (onRatioOrbit
        (RatioOrbit.mul twoPrimeDirection (primeDirection p hp))) := by
  intro hcost
  have hpNat0 : p.toNat ≠ 0 := by
    intro hzero
    apply hp.1
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hpNatQ0 : (p.toNat : ℚ) ≠ 0 := by
    exact_mod_cast hpNat0
  rw [RatioOrbit.crossEq_iff_toRat_eq, onRatioOrbit_toRat,
    onRatioOrbit_toRat, RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
    RatioOrbit.recip_toRat, twoPrimeDirection_toRat, primeDirection_toRat] at hcost
  field_simp [hpNatQ0] at hcost
  ring_nf at hcost
  have hsqQ : (p.toNat : ℚ) ^ 2 = 1 := by
    nlinarith
  have hsqNat : p.toNat ^ 2 = 1 := by
    exact_mod_cast hsqQ
  rw [pow_two] at hsqNat
  have hpOne : p.toNat = 1 := by
    have hle : p.toNat ≤ 1 := by
      by_contra hnot
      have hge : 2 ≤ p.toNat := by omega
      have hprodge : 2 ≤ p.toNat * p.toNat := by
        calc
          2 ≤ 2 * 2 := by norm_num
          _ ≤ p.toNat * p.toNat := Nat.mul_le_mul hge hge
      omega
    omega
  exact hp.2.1 ((DistinctionNat.unit_iff_toNat_eq_one p).mpr hpOne)

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect_of_composite_defect
    {χ : RatioOrbit → RatioOrbit}
    (hdefect :
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ) :
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ := by
  rcases hdefect with ⟨htwoRec, p, hp, hpne, hpId, hprod⟩
  have hcostImage :
      RatioOrbit.crossEq
        (costFromCharacter χ
          (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
        (onRatioOrbit
          (RatioOrbit.mul
            (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp))) :=
    onRatioOrbit_congr hprod
  refine ⟨htwoRec, p, hp, hpne, hpId, hprod, ?_⟩
  intro hcost
  exact
    two_prime_composite_mixed_image_jcost_mismatch p hp
      (RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hcostImage) hcost)

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_cost_defect
    {χ : RatioOrbit → RatioOrbit}
    (hdefect :
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ) :
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ := by
  rcases hdefect with ⟨htwoRec, p, hp, hpne, hpId, hprod, _hcost⟩
  exact ⟨htwoRec, p, hp, hpne, hpId, hprod⟩

theorem PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_iff_cost_defect :
    {χ : RatioOrbit → RatioOrbit} →
    (PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ ↔
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ) := by
  intro χ
  exact
    ⟨PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect_of_composite_defect,
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_cost_defect⟩

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_two_prime_reciprocal_forces
    {χ : RatioOrbit → RatioOrbit}
    (hforces : PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ := by
  intro htwoRec p hp hpId
  have hpRec := hforces htwoRec p hp
  have hself :
      RatioOrbit.crossEq (primeDirection p hp)
        (RatioOrbit.recip (primeDirection p hp)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
  exact primeDirection_not_crossEq_recip p hp hself

theorem PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_local_excludes_prime_identity
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hexcl : PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ) :
    PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ := by
  intro htwoRec p hp
  rcases hlocal p hp with hpId | hpRec
  · exact False.elim ((hexcl htwoRec p hp) hpId)
  · exact hpRec

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_iff_two_prime_reciprocal_forces
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ ↔
      PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ :=
  ⟨PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_local_excludes_prime_identity
      hlocal,
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_two_prime_reciprocal_forces⟩

theorem PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_trace_connected
    {χ : RatioOrbit → RatioOrbit}
    (htrace : PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ) :
    PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ := by
  intro htwoRec p hp
  exact htrace p hp
    (PRCPrimeAxisTraceConnected_proved twoOrbit twoOrbit_primeOrbit p hp)
    htwoRec

theorem PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_forces
    {χ : RatioOrbit → RatioOrbit}
    (hforces : PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ) :
    PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ := by
  intro p hp _hconn htwoRec
  exact hforces htwoRec p hp

theorem PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_iff_forces
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ ↔
      PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ :=
  ⟨PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_trace_connected,
    PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_forces⟩

theorem PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_reciprocal_twist_identity
    {χ : RatioOrbit → RatioOrbit}
    (htwist :
      PRCCharacterTwoPrimeIdentityRespectsTraceConnected
        (PRCCharacterReciprocalTwist χ)) :
    PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ := by
  intro p hp hconn htwoRec
  have htwistTwoId :
      RatioOrbit.crossEq
          (PRCCharacterReciprocalTwist χ twoPrimeDirection)
          twoPrimeDirection :=
    (PRCCharacterReciprocalTwist_two_identity_iff_reciprocal χ).mpr htwoRec
  have htwistPId := htwist p hp hconn htwistTwoId
  exact (PRCCharacterReciprocalTwist_prime_identity_iff_reciprocal
    χ p hp).mp htwistPId

theorem PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_reciprocal_twist_reciprocal
    {χ : RatioOrbit → RatioOrbit}
    (htwist :
      PRCCharacterTwoPrimeReciprocalRespectsTraceConnected
        (PRCCharacterReciprocalTwist χ)) :
    PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ := by
  intro p hp hconn htwoId
  have htwistTwoRec :
      RatioOrbit.crossEq
          (PRCCharacterReciprocalTwist χ twoPrimeDirection)
          (RatioOrbit.recip twoPrimeDirection) := by
    simpa [PRCCharacterReciprocalTwist] using
      (ratioOrbit_recip_congr htwoId)
  have htwistPRec := htwist p hp hconn htwistTwoRec
  have hpToRecipRecip :
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (RatioOrbit.recip (primeDirection p hp))) :=
    (ratioOrbit_recip_left_crossEq_iff
      (χ (primeDirection p hp))
      (RatioOrbit.recip (primeDirection p hp))).mp htwistPRec
  exact RatioOrbit.crossEq_trans hpToRecipRecip
    (ratioOrbit_recip_recip_crossEq_self (primeDirection p hp))

theorem PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_prime_identity_trace_connected
    {χ : RatioOrbit → RatioOrbit}
    (htrace : PRCCharacterPrimeIdentityRespectsTraceConnected χ) :
    PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ := by
  intro p hp hconn htwoId
  exact htrace twoOrbit twoOrbit_primeOrbit p hp hconn htwoId

theorem PRCCharacterPrimeIdentityRespectsTraceConnected_of_two_prime_identity_and_forces_two
    {χ : RatioOrbit → RatioOrbit}
    (htwo : PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ)
    (hforces : PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ) :
    PRCCharacterPrimeIdentityRespectsTraceConnected χ := by
  intro p hp r hr _hconn hpId
  have htwoId := hforces p hp hpId
  exact htwo r hr
    (PRCPrimeAxisTraceConnected_proved twoOrbit twoOrbit_primeOrbit r hr)
    htwoId

theorem PRCCharacterNoMixedPrimeWitnesses_of_coherent_prime_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterPrimeOrientationCoherent χ) :
    PRCCharacterNoMixedPrimeWitnesses χ := by
  rintro ⟨hid, hrec⟩
  rcases hid with ⟨p, hp, hpId⟩
  rcases hrec with ⟨r, hr, hrRec⟩
  rcases hcoh with hallId | hallRec
  · have hrId := hallId r hr
    have hself :
        RatioOrbit.crossEq (primeDirection r hr)
          (RatioOrbit.recip (primeDirection r hr)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
    exact primeDirection_not_crossEq_recip r hr hself
  · have hpRec := hallRec p hp
    have hself :
        RatioOrbit.crossEq (primeDirection p hp)
          (RatioOrbit.recip (primeDirection p hp)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
    exact primeDirection_not_crossEq_recip p hp hself

theorem PRCCharacterPrimeIdentityTraceCoherent_of_local_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hnomix : PRCCharacterNoMixedPrimeOrientation χ) :
    PRCCharacterPrimeIdentityTraceCoherent χ := by
  intro p hp r hr hpId
  rcases hlocal r hr with hrId | hrRec
  · exact hrId
  · exact False.elim (hnomix p hp r hr hpId hrRec)

theorem PRCCharacterNoMixedPrimeOrientation_of_branch_uniform
    {χ : RatioOrbit → RatioOrbit}
    (huniform : PRCCharacterPrimeIdentityBranchUniform χ) :
    PRCCharacterNoMixedPrimeOrientation χ := by
  intro p hp r hr hpId hrRec
  have hrId := huniform p hp r hr hpId
  have hself :
      RatioOrbit.crossEq
        (primeDirection r hr)
        (RatioOrbit.recip (primeDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact primeDirection_not_crossEq_recip r hr hself

theorem PRCCharacterPrimeIdentityBranchUniform_of_local_no_mixed_prime_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterPrimeLocalOrientation χ)
    (hnomix : PRCCharacterNoMixedPrimeOrientation χ) :
    PRCCharacterPrimeIdentityBranchUniform χ := by
  intro p hp r hr hpId
  rcases hlocal r hr with hrId | hrRec
  · exact hrId
  · exact False.elim (hnomix p hp r hr hpId hrRec)

theorem PRCCharacterNoMixedPrimeWitnesses_of_nonunit_no_mixed_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hnomix : PRCCharacterNonunitNoMixedWitnesses χ) :
    PRCCharacterNoMixedPrimeWitnesses χ := by
  rintro ⟨hid, hrec⟩
  rcases hid with ⟨p, hp, hpId⟩
  rcases hrec with ⟨r, hr, hrRec⟩
  have hpIdNonunit : PRCCharacterOrbitDirectionIdentity χ p hp.1 := by
    simpa [PRCCharacterOrbitDirectionIdentity, primeDirection] using hpId
  have hrRecNonunit : PRCCharacterOrbitDirectionReciprocal χ r hr.1 := by
    simpa [PRCCharacterOrbitDirectionReciprocal, primeDirection] using hrRec
  exact hnomix ⟨⟨p, hp.1, hp.2.1, hpIdNonunit⟩,
    ⟨r, hr.1, hr.2.1, hrRecNonunit⟩⟩

theorem PRCCharacterPrimeWitnessesControlNonunitWitnesses_of_mixed_reflects
    {χ : RatioOrbit → RatioOrbit}
    (hreflect : PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ) :
    PRCCharacterPrimeWitnessesControlNonunitWitnesses χ := by
  intro hprimeNoMix hnonunitMixed
  exact hprimeNoMix (hreflect hnonunitMixed)

theorem PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_of_prime_control
    {χ : RatioOrbit → RatioOrbit}
    (hcontrol : PRCCharacterPrimeWitnessesControlNonunitWitnesses χ) :
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ := by
  intro hnonunitMixed
  by_contra hnoPrimeMixed
  exact (hcontrol hnoPrimeMixed) hnonunitMixed

theorem PRCCharacterPrimeWitnessesControlNonunitWitnesses_iff_mixed_reflects
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeWitnessesControlNonunitWitnesses χ ↔
      PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ :=
  ⟨PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_of_prime_control,
    PRCCharacterPrimeWitnessesControlNonunitWitnesses_of_mixed_reflects⟩

theorem PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit_of_reflects
    {χ : RatioOrbit → RatioOrbit}
    (hreflect : PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ) :
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit χ := by
  constructor
  · intro hmixed
    exact (hreflect hmixed).1
  · intro hmixed
    exact (hreflect hmixed).2

theorem PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_of_split
    {χ : RatioOrbit → RatioOrbit}
    (hsplit : PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit χ) :
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ := by
  intro hmixed
  exact ⟨hsplit.1 hmixed, hsplit.2 hmixed⟩

theorem PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_iff_split
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ ↔
      PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit χ :=
  ⟨PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit_of_reflects,
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_of_split⟩

theorem PRCCharacterNonunitIdentityWitnessGlobalizes_of_local_excludes
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hexcl : PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ) :
    PRCCharacterNonunitIdentityWitnessGlobalizes χ := by
  intro hwitness r hr hrUnit
  rcases hlocal r hr hrUnit with hrId | hrRec
  · exact hrId
  · exact False.elim (hexcl hwitness r hr hrUnit hrRec)

theorem PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hwitness : PRCCharacterNonunitIdentityWitnessGlobalizes χ) :
    PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ := by
  intro hId r hr hrUnit hrRec
  have hrId := hwitness hId r hr hrUnit
  have hself :
      RatioOrbit.crossEq (orbitDirection r hr)
        (RatioOrbit.recip (orbitDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact orbitDirection_nonunit_not_crossEq_recip r hr hrUnit hself

theorem PRCCharacterNonunitOrbitOrientationCoherent_of_local_identity_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hwitness : PRCCharacterNonunitIdentityWitnessGlobalizes χ) :
    PRCCharacterNonunitOrbitOrientationCoherent χ := by
  by_cases hId :
      ∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
        ∃ hunit : ¬ DistinctionNat.unit p,
          PRCCharacterOrbitDirectionIdentity χ p hp
  · exact Or.inl (hwitness hId)
  · exact Or.inr (by
      intro q hq hqUnit
      rcases hlocal q hq hqUnit with hqId | hqRec
      · exact False.elim (hId ⟨q, hq, hqUnit, hqId⟩)
      · exact hqRec)

theorem PRCCharacterNonunitIdentityWitnessGlobalizes_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNonunitIdentityWitnessGlobalizes χ :=
  PRCCharacterNonunitIdentityWitnessGlobalizes_of_branch_transport
    (PRCCharacterNonunitIdentityBranchTransport_of_coherent hcoh)

theorem PRCCharacterNonunitReciprocalBranchTransport_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNonunitReciprocalBranchTransport χ := by
  intro p hp hpUnit hpRec r hr hrUnit
  rcases hcoh with hallId | hallRec
  · have hpId := hallId p hp hpUnit
    have hself :
        RatioOrbit.crossEq (orbitDirection p hp)
          (RatioOrbit.recip (orbitDirection p hp)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
    exact False.elim
      (orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself)
  · exact hallRec r hr hrUnit

theorem PRCCharacterNonunitBranchTransportPair_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNonunitBranchTransportPair χ :=
  ⟨PRCCharacterNonunitIdentityBranchTransport_of_coherent hcoh,
    PRCCharacterNonunitReciprocalBranchTransport_of_coherent hcoh⟩

theorem PRCCharacterNonunitIdentityBranchTransport_of_comparable_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcomp : PRCCharacterNonunitIdentityRespectsComparableTrace χ) :
    PRCCharacterNonunitIdentityBranchTransport χ := by
  intro p hp hpUnit hpId r hr hrUnit
  exact hcomp p hp hpUnit r hr hrUnit
    (orbitPositionTrace_comparable p r) hpId

theorem PRCCharacterNonunitIdentityRespectsComparableTrace_of_branch_transport
    {χ : RatioOrbit → RatioOrbit}
    (htransport : PRCCharacterNonunitIdentityBranchTransport χ) :
    PRCCharacterNonunitIdentityRespectsComparableTrace χ := by
  intro p hp hpUnit r hr hrUnit _hcomp hpId
  exact htransport p hp hpUnit hpId r hr hrUnit

theorem PRCCharacterNonunitIdentityRespectsComparableTrace_iff_branch_transport
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNonunitIdentityRespectsComparableTrace χ ↔
      PRCCharacterNonunitIdentityBranchTransport χ :=
  ⟨PRCCharacterNonunitIdentityBranchTransport_of_comparable_trace,
    PRCCharacterNonunitIdentityRespectsComparableTrace_of_branch_transport⟩

/-- Two-branch version of the global branch-coupling law: any nonunit
identity-oriented direction transports identity to every nonunit direction, and
any reciprocal-oriented direction transports reciprocal to every nonunit
direction. -/
def PRCCharacterNonunitBranchAgreement
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
        ¬ DistinctionNat.unit r →
          (PRCCharacterOrbitDirectionIdentity χ p hp →
            PRCCharacterOrbitDirectionIdentity χ r hr) ∧
          (PRCCharacterOrbitDirectionReciprocal χ p hp →
            PRCCharacterOrbitDirectionReciprocal χ r hr)

theorem PRCCharacterNonunitBranchAgreement_of_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterNonunitBranchAgreement χ := by
  intro p hp hpUnit r hr hrUnit
  rcases hcoh with hallId | hallRec
  · constructor
    · intro _hpId
      exact hallId r hr hrUnit
    · intro hpRec
      have hpId := hallId p hp hpUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection p hp)
            (RatioOrbit.recip (orbitDirection p hp)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
      exact False.elim
        (orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself)
  · constructor
    · intro hpId
      have hpRec := hallRec p hp hpUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection p hp)
            (RatioOrbit.recip (orbitDirection p hp)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
      exact False.elim
        (orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself)
    · intro _hpRec
      exact hallRec r hr hrUnit

theorem PRCCharacterNonunitBranchAgreement_of_transport_pair
    {χ : RatioOrbit → RatioOrbit}
    (hpair : PRCCharacterNonunitBranchTransportPair χ) :
    PRCCharacterNonunitBranchAgreement χ := by
  intro p hp hpUnit r hr hrUnit
  exact ⟨(by
      intro hpId
      exact hpair.1 p hp hpUnit hpId r hr hrUnit),
    (by
      intro hpRec
      exact hpair.2 p hp hpUnit hpRec r hr hrUnit)⟩

theorem PRCCharacterNonunitIdentityBranchTransport_of_branch_agreement
    {χ : RatioOrbit → RatioOrbit}
    (hagree : PRCCharacterNonunitBranchAgreement χ) :
    PRCCharacterNonunitIdentityBranchTransport χ := by
  intro p hp hpUnit hpId r hr hrUnit
  exact (hagree p hp hpUnit r hr hrUnit).1 hpId

theorem PRCCharacterNonunitReciprocalBranchTransport_of_branch_agreement
    {χ : RatioOrbit → RatioOrbit}
    (hagree : PRCCharacterNonunitBranchAgreement χ) :
    PRCCharacterNonunitReciprocalBranchTransport χ := by
  intro p hp hpUnit hpRec r hr hrUnit
  exact (hagree p hp hpUnit r hr hrUnit).2 hpRec

theorem PRCCharacterNonunitBranchTransportPair_of_branch_agreement
    {χ : RatioOrbit → RatioOrbit}
    (hagree : PRCCharacterNonunitBranchAgreement χ) :
    PRCCharacterNonunitBranchTransportPair χ :=
  ⟨PRCCharacterNonunitIdentityBranchTransport_of_branch_agreement hagree,
    PRCCharacterNonunitReciprocalBranchTransport_of_branch_agreement hagree⟩

theorem PRCCharacterNonunitBranchAgreement_iff_transport_pair
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterNonunitBranchAgreement χ ↔
      PRCCharacterNonunitBranchTransportPair χ :=
  ⟨PRCCharacterNonunitBranchTransportPair_of_branch_agreement,
    PRCCharacterNonunitBranchAgreement_of_transport_pair⟩

theorem PRCCharacterNonunitBranchAgreement_of_local_identity_branch_transport
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (htransport : PRCCharacterNonunitIdentityBranchTransport χ) :
    PRCCharacterNonunitBranchAgreement χ := by
  intro p hp hpUnit r hr hrUnit
  constructor
  · intro hpId
    exact htransport p hp hpUnit hpId r hr hrUnit
  · intro hpRec
    rcases hlocal r hr hrUnit with hrId | hrRec
    · have hpId := htransport r hr hrUnit hrId p hp hpUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection p hp)
            (RatioOrbit.recip (orbitDirection p hp)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
      exact False.elim
        (orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself)
    · exact hrRec

theorem PRCCharacterNonunitOrbitOrientationCoherent_of_local_branch_agreement
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hagree : PRCCharacterNonunitBranchAgreement χ) :
    PRCCharacterNonunitOrbitOrientationCoherent χ := by
  by_cases hId :
      ∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
        ∃ hunit : ¬ DistinctionNat.unit p,
          PRCCharacterOrbitDirectionIdentity χ p hp
  · rcases hId with ⟨p0, hp0, hunit0, hp0Id⟩
    exact Or.inl (by
      intro q hq hqUnit
      exact (hagree p0 hp0 hunit0 q hq hqUnit).1 hp0Id)
  · exact Or.inr (by
      intro q hq hqUnit
      rcases hlocal q hq hqUnit with hqId | hqRec
      · exact False.elim (hId ⟨q, hq, hqUnit, hqId⟩)
      · exact hqRec)

theorem PRCCharacterNonunitBranchAgreement_iff_coherent_of_local
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ) :
    PRCCharacterNonunitBranchAgreement χ ↔
      PRCCharacterNonunitOrbitOrientationCoherent χ :=
  ⟨PRCCharacterNonunitOrbitOrientationCoherent_of_local_branch_agreement
      hlocal,
    PRCCharacterNonunitBranchAgreement_of_coherent⟩

theorem PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_no_mixed
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hnomix : PRCCharacterNoMixedNonunitOrbitOrientation χ) :
    PRCCharacterNonunitOrbitOrientationCoherent χ := by
  by_cases hId :
      ∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
        ∃ hunit : ¬ DistinctionNat.unit p,
          PRCCharacterOrbitDirectionIdentity χ p hp
  · rcases hId with ⟨p0, hp0, hunit0, hp0Id⟩
    exact Or.inl (by
      intro q hq hqUnit
      rcases hlocal q hq hqUnit with hqId | hqRec
      · exact hqId
      · exact False.elim (hnomix p0 hp0 hunit0 q hq hqUnit hp0Id hqRec))
  · exact Or.inr (by
      intro q hq hqUnit
      rcases hlocal q hq hqUnit with hqId | hqRec
      · exact False.elim (hId ⟨q, hq, hqUnit, hqId⟩)
      · exact hqRec)

theorem PRCCharacterNonunitOrbitOrientationCoherent_of_local_identity_branch_transport
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (htransport : PRCCharacterNonunitIdentityBranchTransport χ) :
    PRCCharacterNonunitOrbitOrientationCoherent χ :=
  PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_no_mixed hlocal
    (PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_branch_transport
      htransport)

theorem PRCCharacterOrbitProductNoMixedOrientation_of_nonunit_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterOrbitProductNoMixedOrientation χ := by
  intro a b p ha hb haUnit hbUnit _hp _hpUnit _hmul
  rcases hcoh with hallId | hallRec
  · constructor
    · rintro ⟨_haId, hbRec⟩
      have hbId := hallId b hb hbUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection b hb)
            (RatioOrbit.recip (orbitDirection b hb)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hbId) hbRec
      exact orbitDirection_nonunit_not_crossEq_recip b hb hbUnit hself
    · rintro ⟨haRec, _hbId⟩
      have haId := hallId a ha haUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection a ha)
            (RatioOrbit.recip (orbitDirection a ha)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm haId) haRec
      exact orbitDirection_nonunit_not_crossEq_recip a ha haUnit hself
  · constructor
    · rintro ⟨haId, _hbRec⟩
      have haRec := hallRec a ha haUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection a ha)
            (RatioOrbit.recip (orbitDirection a ha)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm haId) haRec
      exact orbitDirection_nonunit_not_crossEq_recip a ha haUnit hself
    · rintro ⟨_haRec, hbId⟩
      have hbRec := hallRec b hb hbUnit
      have hself :
          RatioOrbit.crossEq (orbitDirection b hb)
            (RatioOrbit.recip (orbitDirection b hb)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hbId) hbRec
      exact orbitDirection_nonunit_not_crossEq_recip b hb hbUnit hself

theorem PRCCharacterOrbitProductIdentityIdentity
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    {a b p : DistinctionNat}
    (ha : a ≠ DistinctionNat.zero) (hb : b ≠ DistinctionNat.zero)
    (hp : p ≠ DistinctionNat.zero)
    (hmul : a * b = p)
    (haId : PRCCharacterOrbitDirectionIdentity χ a ha)
    (hbId : PRCCharacterOrbitDirectionIdentity χ b hb) :
    PRCCharacterOrbitDirectionIdentity χ p hp := by
  unfold PRCCharacterOrbitDirectionIdentity at *
  exact RatioOrbit.crossEq_trans
    (hcompat a b p ha hb hp hmul)
    (RatioOrbit.crossEq_trans
      (hχ.multiplicative (orbitDirection a ha) (orbitDirection b hb))
      (RatioOrbit.crossEq_trans
        (ratioOrbit_mul_congr haId hbId)
        (RatioOrbit.crossEq_symm
          (orbitDirection_mul_crossEq a b p ha hb hp hmul))))

theorem PRCCharacterOrbitProductReciprocalReciprocal
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    {a b p : DistinctionNat}
    (ha : a ≠ DistinctionNat.zero) (hb : b ≠ DistinctionNat.zero)
    (hp : p ≠ DistinctionNat.zero)
    (hmul : a * b = p)
    (haRec : PRCCharacterOrbitDirectionReciprocal χ a ha)
    (hbRec : PRCCharacterOrbitDirectionReciprocal χ b hb) :
    PRCCharacterOrbitDirectionReciprocal χ p hp := by
  unfold PRCCharacterOrbitDirectionReciprocal at *
  exact RatioOrbit.crossEq_trans
    (hcompat a b p ha hb hp hmul)
    (RatioOrbit.crossEq_trans
      (hχ.multiplicative (orbitDirection a ha) (orbitDirection b hb))
      (RatioOrbit.crossEq_trans
        (ratioOrbit_mul_congr haRec hbRec)
        (RatioOrbit.crossEq_trans
          (ratioOrbit_mul_recip_recip_crossEq_recip_mul
            (orbitDirection a ha) (orbitDirection b hb))
          (ratioOrbit_recip_congr
            (RatioOrbit.crossEq_symm
              (orbitDirection_mul_crossEq a b p ha hb hp hmul))))))

theorem PRCCharacterNonunitOrbitAllIdentity_of_all_prime_identity
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeId : ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) :
    ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit p →
        PRCCharacterOrbitDirectionIdentity χ p hp := by
  intro p hp hunit
  let P : Nat → Prop := fun n =>
    ∀ q : DistinctionNat, q.toNat = n →
      (hq : q ≠ DistinctionNat.zero) →
        ¬ DistinctionNat.unit q →
          PRCCharacterOrbitDirectionIdentity χ q hq
  have hP : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n := by
    intro n ih q hqNat hq0 hqUnit
    by_cases hqPrime : DistinctionNat.primeOrbit q
    · simpa [PRCCharacterOrbitDirectionIdentity, primeDirection]
        using hprimeId q hqPrime
    · have hfac : DistinctionNat.nontrivialFactorization q := by
        by_contra hnotFac
        exact hqPrime ⟨hq0, hqUnit, hnotFac⟩
      rcases hfac with ⟨a, b, ha0, hb0, haUnit, hbUnit, hmul⟩
      have hmulNat : a.toNat * b.toNat = n := by
        have hnat := congrArg DistinctionNat.toNat hmul
        rw [DistinctionNat.toNat_mul, hqNat] at hnat
        exact hnat
      have haNat0 : a.toNat ≠ 0 := by
        intro hz
        apply ha0
        apply DistinctionNat.toNat_inj
        rw [hz, DistinctionNat.toNat_zero]
      have hbNat0 : b.toNat ≠ 0 := by
        intro hz
        apply hb0
        apply DistinctionNat.toNat_inj
        rw [hz, DistinctionNat.toNat_zero]
      have haNat1 : a.toNat ≠ 1 := by
        intro hone
        exact haUnit ((DistinctionNat.unit_iff_toNat_eq_one a).mpr hone)
      have hbNat1 : b.toNat ≠ 1 := by
        intro hone
        exact hbUnit ((DistinctionNat.unit_iff_toNat_eq_one b).mpr hone)
      have haPos : 0 < a.toNat := by omega
      have hbPos : 0 < b.toNat := by omega
      have haGtOne : 1 < a.toNat := by omega
      have hbGtOne : 1 < b.toNat := by omega
      have ha_lt : a.toNat < n := by
        calc
          a.toNat = a.toNat * 1 := by rw [Nat.mul_one]
          _ < a.toNat * b.toNat :=
            Nat.mul_lt_mul_of_pos_left hbGtOne haPos
          _ = n := hmulNat
      have hb_lt : b.toNat < n := by
        calc
          b.toNat = 1 * b.toNat := by rw [Nat.one_mul]
          _ < a.toNat * b.toNat :=
            Nat.mul_lt_mul_of_pos_right haGtOne hbPos
          _ = n := hmulNat
      have haId : PRCCharacterOrbitDirectionIdentity χ a ha0 :=
        ih a.toNat ha_lt a rfl ha0 haUnit
      have hbId : PRCCharacterOrbitDirectionIdentity χ b hb0 :=
        ih b.toNat hb_lt b rfl hb0 hbUnit
      exact PRCCharacterOrbitProductIdentityIdentity hχ hcompat
        ha0 hb0 hq0 hmul haId hbId
  have hmain : P p.toNat :=
    Nat.strong_induction_on (p := P) p.toNat hP
  exact hmain p rfl hp hunit

theorem PRCCharacterNonunitOrbitAllReciprocal_of_all_prime_reciprocal
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeRec : ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp))) :
    ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit p →
        PRCCharacterOrbitDirectionReciprocal χ p hp := by
  intro p hp hunit
  let P : Nat → Prop := fun n =>
    ∀ q : DistinctionNat, q.toNat = n →
      (hq : q ≠ DistinctionNat.zero) →
        ¬ DistinctionNat.unit q →
          PRCCharacterOrbitDirectionReciprocal χ q hq
  have hP : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n := by
    intro n ih q hqNat hq0 hqUnit
    by_cases hqPrime : DistinctionNat.primeOrbit q
    · simpa [PRCCharacterOrbitDirectionReciprocal, primeDirection]
        using hprimeRec q hqPrime
    · have hfac : DistinctionNat.nontrivialFactorization q := by
        by_contra hnotFac
        exact hqPrime ⟨hq0, hqUnit, hnotFac⟩
      rcases hfac with ⟨a, b, ha0, hb0, haUnit, hbUnit, hmul⟩
      have hmulNat : a.toNat * b.toNat = n := by
        have hnat := congrArg DistinctionNat.toNat hmul
        rw [DistinctionNat.toNat_mul, hqNat] at hnat
        exact hnat
      have haNat0 : a.toNat ≠ 0 := by
        intro hz
        apply ha0
        apply DistinctionNat.toNat_inj
        rw [hz, DistinctionNat.toNat_zero]
      have hbNat0 : b.toNat ≠ 0 := by
        intro hz
        apply hb0
        apply DistinctionNat.toNat_inj
        rw [hz, DistinctionNat.toNat_zero]
      have haNat1 : a.toNat ≠ 1 := by
        intro hone
        exact haUnit ((DistinctionNat.unit_iff_toNat_eq_one a).mpr hone)
      have hbNat1 : b.toNat ≠ 1 := by
        intro hone
        exact hbUnit ((DistinctionNat.unit_iff_toNat_eq_one b).mpr hone)
      have haPos : 0 < a.toNat := by omega
      have hbPos : 0 < b.toNat := by omega
      have haGtOne : 1 < a.toNat := by omega
      have hbGtOne : 1 < b.toNat := by omega
      have ha_lt : a.toNat < n := by
        calc
          a.toNat = a.toNat * 1 := by rw [Nat.mul_one]
          _ < a.toNat * b.toNat :=
            Nat.mul_lt_mul_of_pos_left hbGtOne haPos
          _ = n := hmulNat
      have hb_lt : b.toNat < n := by
        calc
          b.toNat = 1 * b.toNat := by rw [Nat.one_mul]
          _ < a.toNat * b.toNat :=
            Nat.mul_lt_mul_of_pos_right haGtOne hbPos
          _ = n := hmulNat
      have haRec : PRCCharacterOrbitDirectionReciprocal χ a ha0 :=
        ih a.toNat ha_lt a rfl ha0 haUnit
      have hbRec : PRCCharacterOrbitDirectionReciprocal χ b hb0 :=
        ih b.toNat hb_lt b rfl hb0 hbUnit
      exact PRCCharacterOrbitProductReciprocalReciprocal hχ hcompat
        ha0 hb0 hq0 hmul haRec hbRec
  have hmain : P p.toNat :=
    Nat.strong_induction_on (p := P) p.toNat hP
  exact hmain p rfl hp hunit

theorem PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ) :
    PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness χ := by
  intro hmixed
  by_contra hnoPrimeId
  have hprimeRec :
      ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq (χ (primeDirection p hp))
          (RatioOrbit.recip (primeDirection p hp)) := by
    intro p hp
    rcases hprimeLocal p hp with hpId | hpRec
    · exact False.elim (hnoPrimeId ⟨p, hp, hpId⟩)
    · exact hpRec
  rcases hmixed.1 with ⟨p, hp, hpUnit, hpId⟩
  have hpRec : PRCCharacterOrbitDirectionReciprocal χ p hp :=
    PRCCharacterNonunitOrbitAllReciprocal_of_all_prime_reciprocal
      hχ hcompat hprimeRec p hp hpUnit
  have hself :
      RatioOrbit.crossEq (orbitDirection p hp)
        (RatioOrbit.recip (orbitDirection p hp)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
  exact orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself

theorem PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness_of_prime_local
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ) :
    PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness χ := by
  intro hmixed
  by_contra hnoPrimeRec
  have hprimeId :
      ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp) := by
    intro p hp
    rcases hprimeLocal p hp with hpId | hpRec
    · exact hpId
    · exact False.elim (hnoPrimeRec ⟨p, hp, hpRec⟩)
  rcases hmixed.2 with ⟨r, hr, hrUnit, hrRec⟩
  have hrId : PRCCharacterOrbitDirectionIdentity χ r hr :=
    PRCCharacterNonunitOrbitAllIdentity_of_all_prime_identity
      hχ hcompat hprimeId r hr hrUnit
  have hself :
      RatioOrbit.crossEq (orbitDirection r hr)
        (RatioOrbit.recip (orbitDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact orbitDirection_nonunit_not_crossEq_recip r hr hrUnit hself

theorem PRCCharacterNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ)
    {p : DistinctionNat} {hp : p ≠ DistinctionNat.zero}
    (hpUnit : ¬ DistinctionNat.unit p)
    (hpId : PRCCharacterOrbitDirectionIdentity χ p hp) :
    ∃ q : DistinctionNat, ∃ hq : DistinctionNat.primeOrbit q,
      RatioOrbit.crossEq (χ (primeDirection q hq)) (primeDirection q hq) := by
  by_contra hnoPrimeId
  have hprimeRec :
      ∀ q : DistinctionNat, ∀ hq : DistinctionNat.primeOrbit q,
        RatioOrbit.crossEq (χ (primeDirection q hq))
          (RatioOrbit.recip (primeDirection q hq)) := by
    intro q hq
    rcases hprimeLocal q hq with hqId | hqRec
    · exact False.elim (hnoPrimeId ⟨q, hq, hqId⟩)
    · exact hqRec
  have hpRec : PRCCharacterOrbitDirectionReciprocal χ p hp :=
    PRCCharacterNonunitOrbitAllReciprocal_of_all_prime_reciprocal
      hχ hcompat hprimeRec p hp hpUnit
  have hself :
      RatioOrbit.crossEq (orbitDirection p hp)
        (RatioOrbit.recip (orbitDirection p hp)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
  exact orbitDirection_nonunit_not_crossEq_recip p hp hpUnit hself

theorem PRCCharacterPrimeIdentityWitnessGlobalizesNonunit_of_no_mixed_prime_witnesses
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ)
    (hnomix : PRCCharacterNoMixedPrimeWitnesses χ) :
    PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ := by
  intro p hp hpId r hr hrUnit
  have hprimeId :
      ∀ s : DistinctionNat, ∀ hs : DistinctionNat.primeOrbit s,
        RatioOrbit.crossEq (χ (primeDirection s hs)) (primeDirection s hs) := by
    intro s hs
    rcases hprimeLocal s hs with hsId | hsRec
    · exact hsId
    · exact False.elim (hnomix ⟨⟨p, hp, hpId⟩, ⟨s, hs, hsRec⟩⟩)
  exact PRCCharacterNonunitOrbitAllIdentity_of_all_prime_identity
    hχ hcompat hprimeId r hr hrUnit

theorem PRCCharacterNoMixedPrimeWitnesses_of_prime_identity_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hglobal : PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ) :
    PRCCharacterNoMixedPrimeWitnesses χ := by
  rintro ⟨hid, hrec⟩
  rcases hid with ⟨p, hp, hpId⟩
  rcases hrec with ⟨r, hr, hrRec⟩
  have hrIdOrbit :
      PRCCharacterOrbitDirectionIdentity χ r hr.1 :=
    hglobal p hp hpId r hr.1 hr.2.1
  have hrId :
      RatioOrbit.crossEq (χ (primeDirection r hr)) (primeDirection r hr) := by
    simpa [primeDirection, PRCCharacterOrbitDirectionIdentity] using hrIdOrbit
  have hself :
      RatioOrbit.crossEq (primeDirection r hr)
        (RatioOrbit.recip (primeDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact primeDirection_not_crossEq_recip r hr hself

theorem PRCCharacterPrimeIdentityRespectsComparableTrace_of_nonunit_identity_comparable_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcomp : PRCCharacterNonunitIdentityRespectsComparableTrace χ) :
    PRCCharacterPrimeIdentityRespectsComparableTrace χ := by
  intro p hp r hr htrace hpId
  exact hcomp p hp.1 hp.2.1 r hr.1 hr.2.1 htrace hpId

theorem PRCCharacterNonunitIdentityRespectsComparableTrace_of_prime_comparable
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ)
    (hprimeComp : PRCCharacterPrimeIdentityRespectsComparableTrace χ) :
    PRCCharacterNonunitIdentityRespectsComparableTrace χ := by
  intro p hp hpUnit r hr hrUnit _htrace hpId
  rcases PRCCharacterNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
      hχ hcompat hprimeLocal hpUnit hpId with
    ⟨q, hq, hqId⟩
  have hprimeId :
      ∀ s : DistinctionNat, ∀ hs : DistinctionNat.primeOrbit s,
        RatioOrbit.crossEq (χ (primeDirection s hs)) (primeDirection s hs) := by
    intro s hs
    exact hprimeComp q hq s hs (orbitPositionTrace_comparable q s) hqId
  exact PRCCharacterNonunitOrbitAllIdentity_of_all_prime_identity
    hχ hcompat hprimeId r hr hrUnit

theorem PRCCharacterOrbitProductLocalOrientationPropagates_of_display_compatible_nomix
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hnomix : PRCCharacterOrbitProductNoMixedOrientation χ) :
    PRCCharacterOrbitProductLocalOrientationPropagates χ := by
  intro a b p ha hb haUnit hbUnit hp hpUnit hmul haLocal hbLocal
  rcases haLocal with haId | haRec
  · rcases hbLocal with hbId | hbRec
    · exact Or.inl
        (PRCCharacterOrbitProductIdentityIdentity hχ hcompat
          ha hb hp hmul haId hbId)
    · exact False.elim
        ((hnomix a b p ha hb haUnit hbUnit hp hpUnit hmul).1
          ⟨haId, hbRec⟩)
  · rcases hbLocal with hbId | hbRec
    · exact False.elim
        ((hnomix a b p ha hb haUnit hbUnit hp hpUnit hmul).2
          ⟨haRec, hbId⟩)
    · exact Or.inr
        (PRCCharacterOrbitProductReciprocalReciprocal hχ hcompat
          ha hb hp hmul haRec hbRec)

theorem PRCCharacterNonunitOrbitLocalOrientation_of_prime_and_product_local
    {χ : RatioOrbit → RatioOrbit}
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ)
    (hprod : PRCCharacterOrbitProductLocalOrientationPropagates χ) :
    PRCCharacterNonunitOrbitLocalOrientation χ := by
  intro p hp hunit
  let P : Nat → Prop := fun n =>
    ∀ q : DistinctionNat, q.toNat = n →
      (hq : q ≠ DistinctionNat.zero) →
        ¬ DistinctionNat.unit q →
          PRCCharacterOrbitDirectionIdentity χ q hq ∨
            PRCCharacterOrbitDirectionReciprocal χ q hq
  have hP : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n := by
    intro n ih q hqNat hq0 hqUnit
    by_cases hqPrime : DistinctionNat.primeOrbit q
    · simpa [primeDirection] using hprimeLocal q hqPrime
    · have hfac : DistinctionNat.nontrivialFactorization q := by
        by_contra hnotFac
        exact hqPrime ⟨hq0, hqUnit, hnotFac⟩
      rcases hfac with ⟨a, b, ha0, hb0, haUnit, hbUnit, hmul⟩
      have hmulNat : a.toNat * b.toNat = n := by
        have hnat := congrArg DistinctionNat.toNat hmul
        rw [DistinctionNat.toNat_mul, hqNat] at hnat
        exact hnat
      have haNat0 : a.toNat ≠ 0 := by
        intro hz
        apply ha0
        apply DistinctionNat.toNat_inj
        rw [hz, DistinctionNat.toNat_zero]
      have hbNat0 : b.toNat ≠ 0 := by
        intro hz
        apply hb0
        apply DistinctionNat.toNat_inj
        rw [hz, DistinctionNat.toNat_zero]
      have haNat1 : a.toNat ≠ 1 := by
        intro hone
        exact haUnit ((DistinctionNat.unit_iff_toNat_eq_one a).mpr hone)
      have hbNat1 : b.toNat ≠ 1 := by
        intro hone
        exact hbUnit ((DistinctionNat.unit_iff_toNat_eq_one b).mpr hone)
      have haPos : 0 < a.toNat := by omega
      have hbPos : 0 < b.toNat := by omega
      have haGtOne : 1 < a.toNat := by omega
      have hbGtOne : 1 < b.toNat := by omega
      have ha_lt : a.toNat < n := by
        calc
          a.toNat = a.toNat * 1 := by rw [Nat.mul_one]
          _ < a.toNat * b.toNat :=
            Nat.mul_lt_mul_of_pos_left hbGtOne haPos
          _ = n := hmulNat
      have hb_lt : b.toNat < n := by
        calc
          b.toNat = 1 * b.toNat := by rw [Nat.one_mul]
          _ < a.toNat * b.toNat :=
            Nat.mul_lt_mul_of_pos_right haGtOne hbPos
          _ = n := hmulNat
      have haLocal :
          PRCCharacterOrbitDirectionIdentity χ a ha0 ∨
            PRCCharacterOrbitDirectionReciprocal χ a ha0 :=
        ih a.toNat ha_lt a rfl ha0 haUnit
      have hbLocal :
          PRCCharacterOrbitDirectionIdentity χ b hb0 ∨
            PRCCharacterOrbitDirectionReciprocal χ b hb0 :=
        ih b.toNat hb_lt b rfl hb0 hbUnit
      exact hprod a b q ha0 hb0 haUnit hbUnit hq0 hqUnit hmul
        haLocal hbLocal
  have hmain : P p.toNat :=
    Nat.strong_induction_on (p := P) p.toNat hP
  exact hmain p rfl hp hunit

/-- Adjacent nonunit orbit steps cannot mix identity on one side with reciprocal
orientation on the other. This is the prime-floor version of the no-mixed
orientation law. -/
def PRCCharacterPrimeFloorNoAdjacentMixedOrientation
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      (¬ (PRCCharacterOrbitDirectionIdentity χ p hp ∧
        PRCCharacterOrbitDirectionReciprocal χ
          (DistinctionNat.succ p) (orbit_succ_ne_zero p))) ∧
      (¬ (PRCCharacterOrbitDirectionReciprocal χ p hp ∧
        PRCCharacterOrbitDirectionIdentity χ
          (DistinctionNat.succ p) (orbit_succ_ne_zero p)))

theorem PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_nonunit_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterNonunitOrbitOrientationCoherent χ) :
    PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ := by
  intro p hp hunit
  have hsuccUnit :
      ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
    orbit_succ_not_unit_of_nonzero_not_unit p hp hunit
  rcases hcoh with hallId | hallRec
  · constructor
    · rintro ⟨_hpId, hsuccRec⟩
      have hsuccId :=
        hallId (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit
      have hself :
          RatioOrbit.crossEq
            (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))
            (RatioOrbit.recip
              (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hsuccId) hsuccRec
      exact orbitDirection_nonunit_not_crossEq_recip
        (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit hself
    · rintro ⟨hpRec, _hsuccId⟩
      have hpId := hallId p hp hunit
      have hself :
          RatioOrbit.crossEq (orbitDirection p hp)
            (RatioOrbit.recip (orbitDirection p hp)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
      exact orbitDirection_nonunit_not_crossEq_recip p hp hunit hself
  · constructor
    · rintro ⟨hpId, _hsuccRec⟩
      have hpRec := hallRec p hp hunit
      have hself :
          RatioOrbit.crossEq (orbitDirection p hp)
            (RatioOrbit.recip (orbitDirection p hp)) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
      exact orbitDirection_nonunit_not_crossEq_recip p hp hunit hself
    · rintro ⟨_hpRec, hsuccId⟩
      have hsuccRec :=
        hallRec (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit
      have hself :
          RatioOrbit.crossEq
            (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))
            (RatioOrbit.recip
              (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hsuccId) hsuccRec
      exact orbitDirection_nonunit_not_crossEq_recip
        (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit hself

/-- Forward one-step identity transport above the unit floor. The unit orbit is
self-reciprocal, so forcing transport out of `1` would wrongly exclude the
globally reciprocal character branch. -/
def PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionIdentity χ p hp →
        PRCCharacterOrbitDirectionIdentity χ
          (DistinctionNat.succ p) (orbit_succ_ne_zero p)

/-- Backward one-step identity transport above the unit floor. -/
def PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
    ¬ DistinctionNat.unit p →
      PRCCharacterOrbitDirectionIdentity χ
        (DistinctionNat.succ p) (orbit_succ_ne_zero p) →
          PRCCharacterOrbitDirectionIdentity χ p hp

/-- The corrected successor-transport rule: identity orientation transports
along one δ-successor step only once the path is above the self-reciprocal unit
orbit. This is the exact layer needed for prime-to-prime trace coherence. -/
def PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport
    (χ : RatioOrbit → RatioOrbit) : Prop :=
  PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep χ ∧
    PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep χ

theorem PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep_of_local_adjacent_nomix
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hnomix : PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ) :
    PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep χ := by
  intro p hp hunit hpId
  have hsuccUnit :
      ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
    orbit_succ_not_unit_of_nonzero_not_unit p hp hunit
  rcases hlocal (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit
    with hsuccId | hsuccRec
  · exact hsuccId
  · exact False.elim ((hnomix p hp hunit).1 ⟨hpId, hsuccRec⟩)

theorem PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep_of_local_adjacent_nomix
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hnomix : PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ) :
    PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep χ := by
  intro p hp hunit hsuccId
  rcases hlocal p hp hunit with hpId | hpRec
  · exact hpId
  · exact False.elim ((hnomix p hp hunit).2 ⟨hpRec, hsuccId⟩)

theorem PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_local_adjacent_nomix
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hnomix : PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ) :
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ :=
  ⟨PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep_of_local_adjacent_nomix
      hlocal hnomix,
    PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep_of_local_adjacent_nomix
      hlocal hnomix⟩

theorem PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ := by
  intro p hp hunit
  have hsuccUnit :
      ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
    orbit_succ_not_unit_of_nonzero_not_unit p hp hunit
  constructor
  · rintro ⟨hpId, hsuccRec⟩
    have hsuccId :
        PRCCharacterOrbitDirectionIdentity χ
          (DistinctionNat.succ p) (orbit_succ_ne_zero p) :=
      hstep.1 p hp hunit hpId
    have hself :
        RatioOrbit.crossEq
          (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))
          (RatioOrbit.recip
            (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hsuccId) hsuccRec
    exact orbitDirection_nonunit_not_crossEq_recip
      (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit hself
  · rintro ⟨hpRec, hsuccId⟩
    have hpId : PRCCharacterOrbitDirectionIdentity χ p hp :=
      hstep.2 p hp hunit hsuccId
    have hself :
        RatioOrbit.crossEq (orbitDirection p hp)
          (RatioOrbit.recip (orbitDirection p hp)) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) hpRec
    exact orbitDirection_nonunit_not_crossEq_recip p hp hunit hself

theorem PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_iff_local_adjacent_nomix
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ) :
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ ↔
      PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ :=
  ⟨PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_successor_transport,
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_local_adjacent_nomix
      hlocal⟩

theorem PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_nonunit_identity_comparable_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcomp : PRCCharacterNonunitIdentityRespectsComparableTrace χ) :
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ := by
  constructor
  · intro p hp hunit hpId
    have hsuccUnit :
        ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
      orbit_succ_not_unit_of_nonzero_not_unit p hp hunit
    exact hcomp p hp hunit (DistinctionNat.succ p)
      (orbit_succ_ne_zero p) hsuccUnit
      (orbitPositionTrace_comparable p (DistinctionNat.succ p)) hpId
  · intro p hp hunit hsuccId
    have hsuccUnit :
        ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
      orbit_succ_not_unit_of_nonzero_not_unit p hp hunit
    exact hcomp (DistinctionNat.succ p) (orbit_succ_ne_zero p)
      hsuccUnit p hp hunit
      (orbitPositionTrace_comparable (DistinctionNat.succ p) p) hsuccId

theorem PRCCharacterOrbitIdentity_of_le_of_prime_floor_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    ∀ {p r : DistinctionNat}, (hp : p ≠ DistinctionNat.zero) →
      ¬ DistinctionNat.unit p →
        (hr : r ≠ DistinctionNat.zero) →
          p.toNat ≤ r.toNat →
            PRCCharacterOrbitDirectionIdentity χ p hp →
              PRCCharacterOrbitDirectionIdentity χ r hr := by
  intro p r
  revert p
  induction r with
  | zero =>
      intro p hp _hpu hr _hle _hpId
      exact False.elim (hr rfl)
  | succ n ih =>
      intro p hp hpu _hr hle hpId
      by_cases hEq : p = DistinctionNat.succ n
      · subst p
        simpa [PRCCharacterOrbitDirectionIdentity, orbitDirection] using hpId
      · have hle_n : p.toNat ≤ n.toNat := by
          have hnotNat : p.toNat ≠ Nat.succ n.toNat := by
            intro hnat
            apply hEq
            apply DistinctionNat.toNat_inj
            simpa [DistinctionNat.toNat_succ] using hnat
          rw [DistinctionNat.toNat_succ] at hle
          omega
        have hpNat0 : p.toNat ≠ 0 := by
          intro hz
          apply hp
          apply DistinctionNat.toNat_inj
          rw [hz, DistinctionNat.toNat_zero]
        have hpNat1 : p.toNat ≠ 1 := by
          intro hone
          exact hpu ((DistinctionNat.unit_iff_toNat_eq_one p).mpr hone)
        have hn0 : n ≠ DistinctionNat.zero := by
          intro hn
          have hnNat : n.toNat = 0 := by rw [hn, DistinctionNat.toNat_zero]
          omega
        have hnunit : ¬ DistinctionNat.unit n := by
          intro hunit
          have hnNat1 : n.toNat = 1 :=
            (DistinctionNat.unit_iff_toNat_eq_one n).mp hunit
          omega
        have hnId :
            PRCCharacterOrbitDirectionIdentity χ n hn0 :=
          ih hp hpu hn0 hle_n hpId
        exact hstep.1 n hn0 hnunit hnId

theorem PRCCharacterOrbitIdentity_of_ge_of_prime_floor_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    ∀ {p r : DistinctionNat}, (hp : p ≠ DistinctionNat.zero) →
      ¬ DistinctionNat.unit p →
        (hr : r ≠ DistinctionNat.zero) →
          ¬ DistinctionNat.unit r →
            r.toNat ≤ p.toNat →
              PRCCharacterOrbitDirectionIdentity χ p hp →
                PRCCharacterOrbitDirectionIdentity χ r hr := by
  intro p r
  revert r
  induction p with
  | zero =>
      intro r hp _hpu _hr _hru _hge _hpId
      exact False.elim (hp rfl)
  | succ n ih =>
      intro r _hp _hpu hr hru hge hpId
      by_cases hEq : r = DistinctionNat.succ n
      · subst r
        simpa [PRCCharacterOrbitDirectionIdentity, orbitDirection] using hpId
      · have hge_n : r.toNat ≤ n.toNat := by
          have hnotNat : r.toNat ≠ Nat.succ n.toNat := by
            intro hnat
            apply hEq
            apply DistinctionNat.toNat_inj
            simpa [DistinctionNat.toNat_succ] using hnat
          rw [DistinctionNat.toNat_succ] at hge
          omega
        have hrNat0 : r.toNat ≠ 0 := by
          intro hz
          apply hr
          apply DistinctionNat.toNat_inj
          rw [hz, DistinctionNat.toNat_zero]
        have hrNat1 : r.toNat ≠ 1 := by
          intro hone
          exact hru ((DistinctionNat.unit_iff_toNat_eq_one r).mpr hone)
        have hn0 : n ≠ DistinctionNat.zero := by
          intro hn
          have hnNat : n.toNat = 0 := by rw [hn, DistinctionNat.toNat_zero]
          omega
        have hnunit : ¬ DistinctionNat.unit n := by
          intro hunit
          have hnNat1 : n.toNat = 1 :=
            (DistinctionNat.unit_iff_toNat_eq_one n).mp hunit
          omega
        have hsuccId :
            PRCCharacterOrbitDirectionIdentity χ
              (DistinctionNat.succ n) (orbit_succ_ne_zero n) := by
          simpa [PRCCharacterOrbitDirectionIdentity, orbitDirection] using hpId
        have hnId :
            PRCCharacterOrbitDirectionIdentity χ n hn0 :=
          hstep.2 n hn0 hnunit hsuccId
        exact ih hn0 hnunit hr hru hge_n hnId

theorem PRCCharacterPrimeIdentityRespectsComparableTrace_of_prime_floor_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    PRCCharacterPrimeIdentityRespectsComparableTrace χ := by
  intro p hp r hr _hcomp hpId
  have hpOrbitId :
      PRCCharacterOrbitDirectionIdentity χ p hp.1 := by
    exact hpId
  rcases Nat.le_total p.toNat r.toNat with hle | hge
  · exact PRCCharacterOrbitIdentity_of_le_of_prime_floor_successor_transport
      hstep hp.1 hp.2.1 hr.1 hle hpOrbitId
  · exact PRCCharacterOrbitIdentity_of_ge_of_prime_floor_successor_transport
      hstep hp.1 hp.2.1 hr.1 hr.2.1 hge hpOrbitId

theorem PRCCharacterNonunitIdentityRespectsComparableTrace_of_prime_floor_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    PRCCharacterNonunitIdentityRespectsComparableTrace χ := by
  intro p hp hpUnit r hr hrUnit _hcomp hpId
  rcases Nat.le_total p.toNat r.toNat with hle | hge
  · exact PRCCharacterOrbitIdentity_of_le_of_prime_floor_successor_transport
      hstep hp hpUnit hr hle hpId
  · exact PRCCharacterOrbitIdentity_of_ge_of_prime_floor_successor_transport
      hstep hp hpUnit hr hrUnit hge hpId

theorem PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_prime_floor_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hlocal : PRCCharacterNonunitOrbitLocalOrientation χ)
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    PRCCharacterNonunitOrbitOrientationCoherent χ := by
  by_cases hId :
      ∃ p : DistinctionNat, ∃ hp : p ≠ DistinctionNat.zero,
        ∃ hunit : ¬ DistinctionNat.unit p,
          PRCCharacterOrbitDirectionIdentity χ p hp
  · rcases hId with ⟨p0, hp0, hunit0, hp0Id⟩
    exact Or.inl (by
      intro q hq hqUnit
      rcases Nat.le_total p0.toNat q.toNat with hle | hge
      · exact PRCCharacterOrbitIdentity_of_le_of_prime_floor_successor_transport
          hstep hp0 hunit0 hq hle hp0Id
      · exact PRCCharacterOrbitIdentity_of_ge_of_prime_floor_successor_transport
          hstep hp0 hunit0 hq hqUnit hge hp0Id)
  · exact Or.inr (by
      intro q hq hqUnit
      rcases hlocal q hq hqUnit with hqId | hqRec
      · exact False.elim (hId ⟨q, hq, hqUnit, hqId⟩)
      · exact hqRec)

theorem PRCCharacterPrimeIdentityWitnessGlobalizesNonunit_of_prime_floor_successor_transport
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ) :
    PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ := by
  intro p hp hpId r hr hrUnit
  have hpOrbitId :
      PRCCharacterOrbitDirectionIdentity χ p hp.1 := by
    simpa [PRCCharacterOrbitDirectionIdentity, primeDirection] using hpId
  rcases Nat.le_total p.toNat r.toNat with hle | hge
  · exact PRCCharacterOrbitIdentity_of_le_of_prime_floor_successor_transport
      hstep hp.1 hp.2.1 hr hle hpOrbitId
  · exact PRCCharacterOrbitIdentity_of_ge_of_prime_floor_successor_transport
      hstep hp.1 hp.2.1 hr hrUnit hge hpOrbitId

theorem PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_prime_identity_witness_globalizes
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeLocal : PRCCharacterPrimeLocalOrientation χ)
    (hglobal : PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ) :
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ := by
  constructor
  · intro p hp hpUnit hpId
    have hsuccUnit :
        ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
      orbit_succ_not_unit_of_nonzero_not_unit p hp hpUnit
    rcases PRCCharacterNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
        hχ hcompat hprimeLocal hpUnit hpId with
      ⟨q, hq, hqId⟩
    exact hglobal q hq hqId
      (DistinctionNat.succ p) (orbit_succ_ne_zero p) hsuccUnit
  · intro p hp hpUnit hsuccId
    have hsuccUnit :
        ¬ DistinctionNat.unit (DistinctionNat.succ p) :=
      orbit_succ_not_unit_of_nonzero_not_unit p hp hpUnit
    rcases PRCCharacterNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
        hχ hcompat hprimeLocal hsuccUnit hsuccId with
      ⟨q, hq, hqId⟩
    exact hglobal q hq hqId p hp hpUnit

theorem PRCCharacterOrbitIdentityRespectsSuccessorStep_of_transport
    {χ : RatioOrbit → RatioOrbit}
    (htransport : PRCCharacterOrbitIdentitySuccessorTransport χ) :
    PRCCharacterOrbitIdentityRespectsSuccessorStep χ := by
  intro p hp
  exact ⟨htransport.1 p hp, htransport.2 p hp⟩

theorem PRCCharacterOrbitIdentity_one_of_identity
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterOrbitIdentityRespectsSuccessorStep χ)
    {p : DistinctionNat} (hp : p ≠ DistinctionNat.zero)
    (hpId : PRCCharacterOrbitDirectionIdentity χ p hp) :
    PRCCharacterOrbitDirectionIdentity χ
      DistinctionNat.one DistinctionNat.one_ne_zero := by
  induction p with
  | zero =>
      exact False.elim (hp rfl)
  | succ n ih =>
      cases n with
      | zero =>
          exact hpId
      | succ m =>
          have hn : DistinctionNat.succ m ≠ DistinctionNat.zero :=
            orbit_succ_ne_zero m
          have hnId :
              PRCCharacterOrbitDirectionIdentity χ
                (DistinctionNat.succ m) hn :=
            (hstep (DistinctionNat.succ m) hn).2 hpId
          exact ih hn hnId

theorem PRCCharacterOrbitIdentity_of_one
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterOrbitIdentityRespectsSuccessorStep χ)
    {r : DistinctionNat} (hr : r ≠ DistinctionNat.zero)
    (honeId : PRCCharacterOrbitDirectionIdentity χ
      DistinctionNat.one DistinctionNat.one_ne_zero) :
    PRCCharacterOrbitDirectionIdentity χ r hr := by
  induction r with
  | zero =>
      exact False.elim (hr rfl)
  | succ n ih =>
      cases n with
      | zero =>
          exact honeId
      | succ m =>
          have hn : DistinctionNat.succ m ≠ DistinctionNat.zero :=
            orbit_succ_ne_zero m
          have hnId :
              PRCCharacterOrbitDirectionIdentity χ
                (DistinctionNat.succ m) hn :=
            ih hn
          exact (hstep (DistinctionNat.succ m) hn).1 hnId

theorem PRCCharacterPrimeIdentityRespectsComparableTrace_of_successor_step
    {χ : RatioOrbit → RatioOrbit}
    (hstep : PRCCharacterOrbitIdentityRespectsSuccessorStep χ) :
    PRCCharacterPrimeIdentityRespectsComparableTrace χ := by
  intro p hp r hr _hcomp hpId
  have hpOrbitId :
      PRCCharacterOrbitDirectionIdentity χ p hp.1 := by
    exact hpId
  have honeId :
      PRCCharacterOrbitDirectionIdentity χ
        DistinctionNat.one DistinctionNat.one_ne_zero :=
    PRCCharacterOrbitIdentity_one_of_identity hstep hp.1 hpOrbitId
  exact PRCCharacterOrbitIdentity_of_one hstep hr.1 honeId

theorem PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_comparable_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcomp : PRCCharacterPrimeIdentityRespectsComparableTrace χ) :
    PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ := by
  intro p hp r hr _T _hpT _hrT hpId
  exact hcomp p hp r hr (orbitPositionTrace_comparable p r) hpId

theorem PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_common_trace_extension
    {χ : RatioOrbit → RatioOrbit}
    (hcommon : PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ) :
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ := by
  intro p hp r hr hpT hrT hpId
  exact hcommon p hp r hr (orbitPositionTrace (p + r)) hpT hrT hpId

theorem PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_canonical_add_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcanon : PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ) :
    PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ := by
  intro p hp r hr _T _hpT _hrT hpId
  exact hcanon p hp r hr
    (orbitPositionTrace_add_extends_left p r)
    (orbitPositionTrace_add_extends_right p r) hpId

theorem PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_iff_common_trace_extension
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ ↔
      PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ :=
  ⟨PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_canonical_add_trace,
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_common_trace_extension⟩

theorem PRCCharacterPrimeIdentityRespectsTraceConnected_of_common_trace_extension
    {χ : RatioOrbit → RatioOrbit}
    (hcommon : PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ) :
    PRCCharacterPrimeIdentityRespectsTraceConnected χ := by
  intro p hp r hr hconn hpId
  rcases hconn with ⟨T, hpT, hrT⟩
  exact hcommon p hp r hr T hpT hrT hpId

theorem PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_trace_connected
    {χ : RatioOrbit → RatioOrbit}
    (hconn : PRCCharacterPrimeIdentityRespectsTraceConnected χ) :
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ := by
  intro p hp r hr _hpT _hrT hpId
  exact hconn p hp r hr (PRCPrimeAxisTraceConnected_proved p hp r hr) hpId

theorem PRCCharacterPrimeIdentityRespectsTraceConnected_of_canonical_add_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcanon : PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ) :
    PRCCharacterPrimeIdentityRespectsTraceConnected χ :=
  PRCCharacterPrimeIdentityRespectsTraceConnected_of_common_trace_extension
    (PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_canonical_add_trace
      hcanon)

theorem PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_iff_trace_connected
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ ↔
      PRCCharacterPrimeIdentityRespectsTraceConnected χ :=
  ⟨PRCCharacterPrimeIdentityRespectsTraceConnected_of_canonical_add_trace,
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_trace_connected⟩

theorem PRCCharacterPrimeIdentityBranchUniform_of_trace_coherence
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterPrimeIdentityTraceCoherent χ) :
    PRCCharacterPrimeIdentityBranchUniform χ := by
  intro p hp r hr hpId
  exact hcoh p hp r hr hpId

theorem PRCCharacterPrimeIdentityTraceCoherent_of_branch_uniform
    {χ : RatioOrbit → RatioOrbit}
    (huniform : PRCCharacterPrimeIdentityBranchUniform χ) :
    PRCCharacterPrimeIdentityTraceCoherent χ := by
  intro p hp r hr hpId
  exact huniform p hp r hr hpId

theorem PRCCharacterPrimeIdentityBranchUniform_iff_trace_coherence
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityBranchUniform χ ↔
      PRCCharacterPrimeIdentityTraceCoherent χ :=
  ⟨PRCCharacterPrimeIdentityTraceCoherent_of_branch_uniform,
    PRCCharacterPrimeIdentityBranchUniform_of_trace_coherence⟩

theorem PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_branch_uniform
    {χ : RatioOrbit → RatioOrbit}
    (huniform : PRCCharacterPrimeIdentityBranchUniform χ) :
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ := by
  intro p hp r hr _hpT _hrT hpId
  exact huniform p hp r hr hpId

theorem PRCCharacterPrimeIdentityBranchUniform_of_canonical_add_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcanon : PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ) :
    PRCCharacterPrimeIdentityBranchUniform χ := by
  intro p hp r hr hpId
  exact hcanon p hp r hr
    (orbitPositionTrace_add_extends_left p r)
    (orbitPositionTrace_add_extends_right p r) hpId

theorem PRCCharacterPrimeIdentityBranchUniform_iff_canonical_add_trace
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityBranchUniform χ ↔
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ :=
  ⟨PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_branch_uniform,
    PRCCharacterPrimeIdentityBranchUniform_of_canonical_add_trace⟩

theorem PRCCharacterPrimeIdentityRespectsComparableTrace_of_trace_coherence
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterPrimeIdentityTraceCoherent χ) :
    PRCCharacterPrimeIdentityRespectsComparableTrace χ := by
  intro p hp r hr _hcomp hpId
  exact hcoh p hp r hr hpId

theorem PRCCharacterPrimeIdentityTraceCoherent_of_comparable_trace
    {χ : RatioOrbit → RatioOrbit}
    (hcomp : PRCCharacterPrimeIdentityRespectsComparableTrace χ) :
    PRCCharacterPrimeIdentityTraceCoherent χ := by
  intro p hp r hr hpId
  exact hcomp p hp r hr (orbitPositionTrace_comparable p r) hpId

theorem PRCCharacterPrimeIdentityRespectsComparableTrace_iff_trace_coherence
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityRespectsComparableTrace χ ↔
      PRCCharacterPrimeIdentityTraceCoherent χ :=
  ⟨PRCCharacterPrimeIdentityTraceCoherent_of_comparable_trace,
    PRCCharacterPrimeIdentityRespectsComparableTrace_of_trace_coherence⟩

theorem PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_trace_coherence
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterPrimeIdentityTraceCoherent χ) :
    PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ :=
  PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_comparable_trace
    (PRCCharacterPrimeIdentityRespectsComparableTrace_of_trace_coherence hcoh)

theorem PRCCharacterPrimeIdentityTraceCoherent_of_common_trace_extension
    {χ : RatioOrbit → RatioOrbit}
    (hcommon : PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ) :
    PRCCharacterPrimeIdentityTraceCoherent χ := by
  intro p hp r hr hpId
  exact hcommon p hp r hr (orbitPositionTrace (p + r))
    (orbitPositionTrace_add_extends_left p r)
    (orbitPositionTrace_add_extends_right p r) hpId

theorem PRCCharacterPrimeIdentityRespectsCommonTraceExtension_iff_trace_coherence
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ ↔
      PRCCharacterPrimeIdentityTraceCoherent χ :=
  ⟨PRCCharacterPrimeIdentityTraceCoherent_of_common_trace_extension,
    PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_trace_coherence⟩

theorem PRCCharacterPrimeIdentityRespectsTraceConnected_of_trace_coherence
    {χ : RatioOrbit → RatioOrbit}
    (hcoh : PRCCharacterPrimeIdentityTraceCoherent χ) :
    PRCCharacterPrimeIdentityRespectsTraceConnected χ := by
  intro p hp r hr _hconn hpId
  exact hcoh p hp r hr hpId

theorem PRCCharacterPrimeIdentityTraceCoherent_of_trace_connected
    {χ : RatioOrbit → RatioOrbit}
    (hconn : PRCCharacterPrimeIdentityRespectsTraceConnected χ) :
    PRCCharacterPrimeIdentityTraceCoherent χ := by
  intro p hp r hr hpId
  exact hconn p hp r hr (PRCPrimeAxisTraceConnected_proved p hp r hr) hpId

theorem PRCCharacterPrimeIdentityRespectsTraceConnected_iff_trace_coherence
    {χ : RatioOrbit → RatioOrbit} :
    PRCCharacterPrimeIdentityRespectsTraceConnected χ ↔
      PRCCharacterPrimeIdentityTraceCoherent χ :=
  ⟨PRCCharacterPrimeIdentityTraceCoherent_of_trace_connected,
    PRCCharacterPrimeIdentityRespectsTraceConnected_of_trace_coherence⟩

/-- Local orientation target: prime cost calibration must at least orient each
prime axis as identity or reciprocal. -/
def PRCPrimeCalibrationForcesLocalPrimeOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeLocalOrientation χ

theorem PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved :
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget := by
  intro χ hχ hprime p hp
  have hq : (primeDirection p hp).toRat ≠ 0 :=
    primeDirection_toRat_ne_zero p hp
  have hχq : (χ (primeDirection p hp)).toRat ≠ 0 :=
    hχ.nonzero_preserving hq
  have hcal :
      RatioOrbit.crossEq
        (onRatioOrbit (χ (primeDirection p hp)))
        (onRatioOrbit (primeDirection p hp)) := by
    simpa [costFromCharacter] using hprime p hp
  exact jcost_eq_forces_same_or_reciprocal hχq hq hcal

/-- No-mixing target: prime cost calibration must forbid independent mixed
identity/reciprocal choices on different prime axes. -/
def PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNoMixedPrimeOrientation χ

/-- Existential prime-witness form of no-mixed prime orientation. -/
def PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNoMixedPrimeWitnesses χ

/-- One-sided prime witness-exclusion target: prime calibration should forbid any
reciprocal-oriented prime witness once an identity-oriented prime witness
exists. -/
def PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ

/-- Reciprocal-witness globalization target: if prime calibration allows one
reciprocal-oriented native prime witness, reciprocal orientation must hold on
every native prime axis. -/
def PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeReciprocalWitnessGlobalizes χ

/-- Distinguished-axis converse half of reciprocal globalization: any
reciprocal-oriented native prime axis must force the orbit-`2` prime axis onto
the reciprocal branch. -/
def PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ

/-- Distinguished-axis reciprocal branch target: once calibration puts the
orbit-`2` prime axis on the reciprocal branch, every native prime axis must be
on the reciprocal branch. -/
def PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ

/-- Split target for reciprocal globalization: arbitrary prime-to-two
reciprocal transport plus two-to-all reciprocal transport. -/
def PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget :
    Prop :=
  PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget ∧
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget

/-- Exact remaining trace-coherence target: prime calibration must make identity
orientation propagate across prime axes. -/
def PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityTraceCoherent χ

/-- Trace-free branch-uniformity target: prime calibration should force every
identity-oriented native prime axis to put all native prime axes on the identity
branch. -/
def PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityBranchUniform χ

/-- Smaller trace-transport target: prime calibration should make identity
orientation invariant along native prime-axis trace connections. The structural
connectivity of the prime-axis trace graph is already proved above. -/
def PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityRespectsTraceConnected χ

/-- Sharper form of the trace-transport target: prime calibration must force
identity orientation to respect an explicitly witnessed common finite δ-trace
extension. -/
def PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ

/-- Canonical-add-trace target: prime calibration should force identity
orientation to transport through the concrete finite common extension
`orbitPositionTrace (p + r)`. -/
def PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ

/-- Sharper trace-order target: prime calibration should force identity
orientation to respect comparability of finite δ-orbit traces. -/
def PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityRespectsComparableTrace χ

/-- Sharper one-step target: prime calibration should force identity orientation
to be invariant under one successor step on every nonzero orbit direction. -/
def PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterOrbitIdentityRespectsSuccessorStep χ

/-- Sharper directional successor target: prime calibration should force both
one-step directions separately. This exposes the exact additive-trace
compatibility missing from the purely multiplicative ratio-character laws. -/
def PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterOrbitIdentitySuccessorTransport χ

/-- Sharper additive successor target: prime calibration should force the ratio
character to respect the additive successor operation on nonzero orbit
directions. -/
def PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterOrbitSuccessorAdditiveCompatible χ

/-- Corrected successor target after the reciprocal-character check: prime
calibration should force successor transport above the self-reciprocal unit
floor, not additive transport out of the unit orbit itself. -/
def PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ

/-- Witness-globalized form of the prime-floor blocker: if any calibrated prime
axis picks identity, then every nonunit orbit direction must pick identity. -/
def PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ

/-- Forward half of the corrected prime-floor successor target. -/
def PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep χ

/-- Backward half of the corrected prime-floor successor target. -/
def PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep χ

/-- Split one-step form of the corrected prime-floor successor target. -/
def PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :
    Prop :=
  PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget ∧
    PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget

/-- First component of the prime-floor successor blocker: prime calibration
should orient every nonunit orbit direction, not only prime axes. -/
def PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitOrbitLocalOrientation χ

/-- Sharper source of nonunit local orientation: prime calibration should force
the product-factor propagation step that carries prime-axis orientation through
composite orbit positions. -/
def PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterOrbitProductLocalOrientationPropagates χ

/-- Product-display compatibility target: prime calibration should force the
character to respect the native equality between product orbit directions and
ratio products of factor directions. -/
def PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterOrbitProductDisplayCompatible χ

/-- Sharper source of product-display compatibility: prime calibration should
force the raw character to respect ratio cross-equivalence. Without this,
`χ : RatioOrbit → RatioOrbit` is not yet a quotient-native character. -/
def PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterRespectsCrossEq χ

theorem PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_of_normalizeRatio_canonical
    (hcanon : PRCNormalizeRatioCanonicalTarget) :
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget := by
  intro χ hχ _hprime
  exact PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ hcanon

theorem PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_of_reduced_signCanonical_unique
    (hunique : PRCReducedSignCanonicalRatioUniqueTarget) :
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget :=
  PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_of_normalizeRatio_canonical
    (PRCNormalizeRatioCanonicalTarget_of_reduced_signCanonical_unique hunique)

theorem PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_proved :
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget :=
  PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_of_reduced_signCanonical_unique
    PRCReducedSignCanonicalRatioUniqueTarget_proved

/-- Product no-mixing target: prime calibration should rule out mixed
identity/reciprocal factor orientations under native multiplication. -/
def PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterOrbitProductNoMixedOrientation χ

/-- Stronger replacement for product no-mixing: prime calibration should force a
single coherent orientation across all nonunit orbit directions. Once this is
available, mixed product factors are impossible by nonunit non-self-reciprocity. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitOrbitOrientationCoherent χ

/-- Branch-coupling target: prime calibration should prevent any identity-oriented
nonunit direction from coexisting with any reciprocal-oriented nonunit direction.
Together with local nonunit orientation this is exactly global nonunit
orientation coherence. -/
def PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNoMixedNonunitOrbitOrientation χ

/-- Positive transport form of the same branch-coupling blocker: if prime
calibration allows one nonunit direction to remain identity-oriented, that
identity branch must transport to every nonunit direction. -/
def PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitIdentityBranchTransport χ

/-- Witness-globalization form of the same branch-coupling blocker: if prime
calibration permits any identity-oriented nonunit direction, that witness fixes
the identity branch globally. -/
def PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitIdentityWitnessGlobalizes χ

/-- One-sided witness-exclusion target: prime calibration should make one
identity-oriented nonunit witness incompatible with every reciprocal-oriented
nonunit witness. This strips local orientation out of witness globalization. -/
def PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitIdentityWitnessExcludesReciprocal χ

/-- Existential no-mixed-witness target: prime calibration should forbid the
coexistence of any identity-oriented nonunit witness and any reciprocal-oriented
nonunit witness. -/
def PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitNoMixedWitnesses χ

/-- Composite bridge for the witness split: under prime calibration, prime
no-mixing should control arbitrary nonunit no-mixing. -/
def PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeWitnessesControlNonunitWitnesses χ

/-- Reflection form of the composite bridge: mixed nonunit witnesses must reflect
down to mixed prime-axis witnesses. -/
def PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses χ

/-- Identity half of the mixed-context reflection target. -/
def PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness χ

/-- Reciprocal half of the mixed-context reflection target. -/
def PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness χ

/-- Split form of the mixed nonunit reflection target. -/
def PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget :
    Prop :=
  PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget ∧
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget

/-- Split form of the current no-mixed-witness blocker: first rule out mixed
prime witnesses, then prove that prime-witness control reaches nonunit
composites. -/
def PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget : Prop :=
  PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ∧
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget

/-- Local-orientation plus one-sided witness exclusion is the split form of
witness globalization. -/
def PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget :
    Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget

/-- Dual transport target: reciprocal orientation at one nonunit direction must
transport to every nonunit direction. -/
def PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitReciprocalBranchTransport χ

/-- Split target for the two one-way nonunit branch transports. -/
def PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget ∧
    PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget

/-- Trace-order sharpening of nonunit identity-branch transport: prime
calibration should force identity orientation to respect comparability of finite
δ-orbit traces on nonunit directions. -/
def PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitIdentityRespectsComparableTrace χ

/-- Two-branch agreement target: prime calibration should force a nonunit branch
choice at one direction to agree with every other nonunit direction, for both
identity and reciprocal branches. -/
def PRCPrimeCalibrationForcesNonunitBranchAgreementTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterNonunitBranchAgreement χ

/-- Local orientation plus two-branch agreement is the positive normal form of
the global nonunit branch-coupling blocker. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget :
    Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget

/-- Local orientation plus identity-branch transport is the minimal positive
normal form: reciprocal transport follows from these two facts. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget :
    Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget

/-- Trace-layer version of the active local identity-transport target. The
identity-transport half is replaced by its equivalent finite δ-trace
comparability law. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget :
    Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget

/-- Sharpened source of global nonunit coherence: first prove every nonunit orbit
direction has a local branch, then prove the cross-nonunit no-mixing law. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget

/-- Product-layer sharpening of global nonunit coherence: local nonunit
orientation is already available, so the remaining branch-coupling obligation can
be carried by the product no-mixing law. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget

theorem PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedNonunitOrbitOrientation_of_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_product_no_mixed
    (hprod : PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget) :
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedNonunitOrbitOrientation_of_product_no_mixed
    (hprod χ hχ hprime)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_no_mixed_nonunit
    (hnomix : PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget) :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitProductNoMixedOrientation_of_no_mixed_nonunit
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_no_mixed_nonunit :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_product_no_mixed,
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_no_mixed_nonunit⟩

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_branch_transport
    (htransport : PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget) :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitProductNoMixedOrientation_of_identity_branch_transport
    (htransport χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityBranchTransport_of_comparable_trace
    (hcomp χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_transport_pair
    (hpair : PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget) :
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitBranchAgreement_of_transport_pair
    ⟨hpair.1 χ hχ hprime, hpair.2 χ hχ hprime⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_branch_agreement
    (hagree : PRCPrimeCalibrationForcesNonunitBranchAgreementTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityBranchTransport_of_branch_agreement
    (hagree χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget_of_branch_agreement
    (hagree : PRCPrimeCalibrationForcesNonunitBranchAgreementTarget) :
    PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitReciprocalBranchTransport_of_branch_agreement
    (hagree χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget_of_branch_agreement
    (hagree : PRCPrimeCalibrationForcesNonunitBranchAgreementTarget) :
    PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_branch_agreement
      hagree,
    PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget_of_branch_agreement
      hagree⟩

theorem PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_iff_transport_pair :
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget ↔
      PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget_of_branch_agreement,
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_transport_pair⟩

theorem PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_local_identity_transport
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget) :
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitBranchAgreement_of_local_identity_branch_transport
    (hsharp.1 χ hχ hprime) (hsharp.2 χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_of_local_branch_agreement
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget :=
  ⟨hsharp.1,
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_branch_agreement
      hsharp.2⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_of_local_identity_transport
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget :=
  ⟨hsharp.1,
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_local_identity_transport
      hsharp⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_iff_local_identity_transport :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_of_local_branch_agreement,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_of_local_identity_transport⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_local_identity_transport
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget :=
  ⟨hsharp.1,
    (by
      intro χ hχ hprime
      exact PRCCharacterNonunitIdentityRespectsComparableTrace_of_branch_transport
        (hsharp.2 χ hχ hprime))⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_of_local_comparable_trace
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget :=
  ⟨hsharp.1,
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_comparable_trace
      hsharp.2⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_iff_local_comparable_trace :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_local_identity_transport,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_of_local_comparable_trace⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_of_local_product_no_mixed
    (hsharp : PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget :=
  ⟨hsharp.1,
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_product_no_mixed
      hsharp.2⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_product_no_mixed
    (hsharp : PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_no_mixed
    (hsharp.1 χ hχ hprime)
    (PRCCharacterNoMixedNonunitOrbitOrientation_of_product_no_mixed
      (hsharp.2 χ hχ hprime))

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_of_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget :=
  ⟨(by
      intro χ hχ hprime
      exact PRCCharacterNonunitOrbitLocalOrientation_of_coherent
        (hcoh χ hχ hprime)),
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_coherent hcoh⟩

theorem PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitBranchAgreement_of_coherent (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_of_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget :=
  ⟨(by
      intro χ hχ hprime
      exact PRCCharacterNonunitOrbitLocalOrientation_of_coherent
        (hcoh χ hχ hprime)),
    PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_coherent hcoh⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_branch_agreement
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_branch_agreement
    (hsharp.1 χ hχ hprime) (hsharp.2 χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_local_branch_agreement :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_of_coherent,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_branch_agreement⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_no_mixed
    (hsharp : PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_no_mixed
    (hsharp.1 χ hχ hprime) (hsharp.2 χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityBranchTransport_of_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_local_no_mixed :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_of_coherent,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_no_mixed⟩

/-- Sharpened source of nonunit orientation coherence: local nonunit orientation
plus prime-floor successor transport force every nonunit orbit direction onto
one coherent identity/reciprocal branch. -/
def PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_and_prime_floor_successor_transport
    (hsharp : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_prime_floor_successor_transport
    (hsharp.1 χ hχ hprime) (hsharp.2 χ hχ hprime)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitProductNoMixedOrientation_of_nonunit_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitLocalOrientation_of_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_local_adjacent_nomix
    (PRCCharacterNonunitOrbitLocalOrientation_of_coherent (hcoh χ hχ hprime))
    (PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_nonunit_coherent
      (hcoh χ hχ hprime))

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_floor_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityRespectsComparableTrace_of_prime_floor_successor_transport
    (hstep χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_nonunit_coherent hcoh,
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_nonunit_coherent hcoh⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_sharpened :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget_of_nonunit_coherent,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_and_prime_floor_successor_transport⟩

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_nonunit_identity_comparable_trace
    (hcomp χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_prime_floor_successor_transport :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_identity_comparable_trace,
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_floor_successor_transport⟩

theorem PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_of_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget := by
  intro χ hχ hprime
  exact (hstep χ hχ hprime).1

theorem PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_of_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget := by
  intro χ hχ hprime
  exact (hstep χ hχ hprime).2

theorem PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_of_successor_transport
      hstep,
    PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_of_successor_transport
      hstep⟩

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_successor_step_pair
    (hpair :
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget) :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro χ hχ hprime
  exact ⟨hpair.1 χ hχ hprime, hpair.2 χ hχ hprime⟩

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_successor_step_pair :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_successor_transport,
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_successor_step_pair⟩

theorem PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_successor_transport
    (PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_identity_comparable_trace
      hcomp)

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_successor_step_pair
    (hpair :
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_floor_successor_transport
    (PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_successor_step_pair
      hpair)

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_successor_step_pair :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_identity_comparable_trace,
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_successor_step_pair⟩

/-- Pass-45 sharpening of product-local orientation: same-orientation products
are algebraic and product-display compatibility is proved through canonical
normalization. The remaining product commitment is nonunit orientation
coherence, which implies product no-mixing. -/
def PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget

theorem PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_of_crossEq_respect
    (hrespect : PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget) :
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitProductDisplayCompatible_of_crossEq_respect
    (hrespect χ hχ hprime)

theorem PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved :
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget :=
  PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_of_crossEq_respect
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_proved

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_prime_floor_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityWitnessGlobalizesNonunit_of_prime_floor_successor_transport
    (hstep χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_prime_identity_witness_globalizes
    (hglobal :
      PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget) :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro χ hχ hprime
  exact
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_prime_identity_witness_globalizes
      hχ
      (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
        χ hχ hprime)
      (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
      (hglobal χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_prime_identity_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_prime_floor_successor_transport,
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_prime_identity_witness_globalizes⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_no_mixed_prime_witnesses
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityWitnessGlobalizesNonunit_of_no_mixed_prime_witnesses
    hχ
    (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
      χ hχ hprime)
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_identity_witness_globalizes
    (hglobal :
      PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeWitnesses_of_prime_identity_witness_globalizes
    (hglobal χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_iff_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_identity_witness_globalizes,
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_no_mixed_prime_witnesses⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed
    (hprod : PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  intro χ hχ hprime
  have hprodLocal : PRCCharacterOrbitProductLocalOrientationPropagates χ :=
    PRCCharacterOrbitProductLocalOrientationPropagates_of_display_compatible_nomix
      hχ (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
        χ hχ hprime) (hprod χ hχ hprime)
  exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_no_mixed
    (PRCCharacterNonunitOrbitLocalOrientation_of_prime_and_product_local
      (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
      hprodLocal)
    (PRCCharacterNoMixedNonunitOrbitOrientation_of_product_no_mixed
      (hprod χ hχ hprime))

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_nonunit_coherent :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed,
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_nonunit_coherent⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_product_no_mixed
    (hprod : PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget :=
  PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_coherent
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed
      hprod)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_identity_branch_transport
    (htransport : PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityWitnessGlobalizes_of_branch_transport
    (htransport χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_identity_witness_globalizes
    (hwitness :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityBranchTransport_of_witness_globalizes
    (hwitness χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_identity_branch_transport :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_identity_witness_globalizes,
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_identity_branch_transport⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_product_no_mixed
    (hprod : PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget :=
  PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_identity_branch_transport
    (PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_product_no_mixed
      hprod)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_witness_globalizes
    (hwitness :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget :=
  PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_branch_transport
    (PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_identity_witness_globalizes
      hwitness)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_witness_globalizes :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_product_no_mixed,
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_witness_globalizes⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_identity_witness_globalizes
    (hwitness :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget :=
  PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed
    (PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_witness_globalizes
      hwitness)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityWitnessGlobalizes_of_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_identity_witness_globalizes :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_nonunit_coherent,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_identity_witness_globalizes⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed
    (hnomix : PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_no_mixed
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_identity_witness_excludes
    (hexcl :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget) :
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_witness_excludes
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_iff_no_mixed :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget ↔
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_identity_witness_excludes,
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed⟩

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_identity_witness_excludes
    (hexcl :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget) :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitNoMixedWitnesses_of_identity_witness_excludes
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed_witnesses
    (hnomix : PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_no_mixed_witnesses
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_identity_witness_excludes :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed_witnesses,
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_identity_witness_excludes⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_orientation
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeWitnesses_of_no_mixed_prime_orientation
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_no_mixed_prime_witnesses
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeOrientation_of_no_mixed_prime_witnesses
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_no_mixed_prime_witnesses,
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_orientation⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_orientation
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_orientation
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_identity_witness_excludes_reciprocal
    (hexcl :
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeOrientation_of_identity_witness_excludes_reciprocal
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_identity_witness_excludes_reciprocal,
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_orientation⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_identity_witness_excludes_reciprocal
    (hexcl :
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeWitnesses_of_identity_witness_excludes_reciprocal
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_witnesses
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_witnesses
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_witnesses,
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_identity_witness_excludes_reciprocal⟩

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_no_mixed_prime_orientation
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeReciprocalWitnessGlobalizes_of_local_no_mixed_prime_orientation
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_reciprocal_witness_globalizes
    (hglobal :
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeOrientation_of_reciprocal_witness_globalizes
    (hglobal χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_reciprocal_witness_globalizes,
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_no_mixed_prime_orientation⟩

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget :=
  PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_no_mixed_prime_orientation.trans
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_iff_no_mixed_prime_orientation.symm

theorem PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_reciprocal_witness_globalizes
    (hglobal :
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_witness_globalizes
    (hglobal χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_reciprocal_witness_globalizes
    (hglobal :
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_reciprocal_witness_globalizes
    (hglobal χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_reciprocal_witness_globalizes
    (hglobal :
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_reciprocal_witness_globalizes
      hglobal,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_reciprocal_witness_globalizes
      hglobal⟩

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_split
    (hsplit :
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget) :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeReciprocalWitnessGlobalizes_of_split
    ⟨hsplit.1 χ hχ hprime, hsplit.2 χ hχ hprime⟩

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_split :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_reciprocal_witness_globalizes,
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_split⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_nonunit_no_mixed_witnesses
    (hnomix : PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeWitnesses_of_nonunit_no_mixed_witnesses
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_nonunit_no_mixed_witnesses
    (hnomix : PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget) :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_nonunit_no_mixed_witnesses
      hnomix,
    by
      intro χ hχ hprime _hprimeWitnesses
      exact hnomix χ hχ hprime⟩

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_split
    (hsplit : PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget) :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget := by
  intro χ hχ hprime
  exact (hsplit.2 χ hχ hprime) (hsplit.1 χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_split :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_nonunit_no_mixed_witnesses,
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_split⟩

theorem PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_of_mixed_reflects
    (hreflect :
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeWitnessesControlNonunitWitnesses_of_mixed_reflects
    (hreflect χ hχ hprime)

theorem PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_prime_control
    (hcontrol :
      PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget) :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_of_prime_control
    (hcontrol χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_iff_mixed_reflects :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget ↔
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget :=
  ⟨PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_prime_control,
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_of_mixed_reflects⟩

theorem PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_of_reflects
    (hreflect :
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget := by
  constructor
  · intro χ hχ hprime
    exact (PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit_of_reflects
      (hreflect χ hχ hprime)).1
  · intro χ hχ hprime
    exact (PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit_of_reflects
      (hreflect χ hχ hprime)).2

theorem PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_split
    (hsplit :
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget) :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses_of_split
    ⟨hsplit.1 χ hχ hprime, hsplit.2 χ hχ hprime⟩

theorem PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_iff_split :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget :=
  ⟨PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_of_reflects,
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_split⟩

theorem PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget_proved :
    PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget := by
  intro χ hχ hprime
  exact PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
    hχ
    (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
      χ hχ hprime)
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)

theorem PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget_proved :
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget := by
  intro χ hχ hprime
  exact PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness_of_prime_local
    hχ
    (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
      χ hχ hprime)
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)

theorem PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_proved :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget :=
  ⟨PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget_proved,
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget_proved⟩

theorem PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_proved :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget :=
  PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_split
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_proved

theorem PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_proved :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget :=
  PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_of_mixed_reflects
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_proved

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_no_mixed_prime_witnesses
    (hprime : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget :=
  ⟨hprime, PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_proved⟩

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_no_mixed_prime_witnesses
    (hprime : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget :=
  PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_split
    (PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_no_mixed_prime_witnesses
      hprime)

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_nonunit_no_mixed_witnesses,
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_no_mixed_prime_witnesses⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_local_exclusion
    (hsharp :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityWitnessGlobalizes_of_local_excludes
    (hsharp.1 χ hχ hprime) (hsharp.2 χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_of_identity_witness_globalizes
    (hwitness :
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_nonunit_coherent
      (PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_identity_witness_globalizes
        hwitness),
    (by
      intro χ hχ hprime
      exact PRCCharacterNonunitIdentityWitnessExcludesReciprocal_of_globalizes
        (hwitness χ hχ hprime))⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_local_exclusion :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_of_identity_witness_globalizes,
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_local_exclusion⟩

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_branch_transport :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_product_no_mixed,
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_branch_transport⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_branch_transport
    (htransport : PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityRespectsComparableTrace_of_branch_transport
    (htransport χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_product_no_mixed
    (hprod : PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_branch_transport
    (PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_product_no_mixed
      hprod)

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_iff_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_branch_transport,
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_comparable_trace⟩

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_comparable_trace :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_product_no_mixed,
    fun hcomp =>
      PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_branch_transport
        (PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_comparable_trace
          hcomp)⟩

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_successor_step_pair
    (hpair :
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget) :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget :=
  (PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_comparable_trace.mpr
    (PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_successor_step_pair
      hpair))

theorem PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_product_no_mixed
    (hprod : PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget) :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_identity_comparable_trace
    (PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_product_no_mixed
      hprod)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_successor_step_pair :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_product_no_mixed,
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_successor_step_pair⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_successor_step_pair
    (hpair :
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget :=
  PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed
    (PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_successor_step_pair
      hpair)

theorem PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_successor_transport
    (PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_nonunit_coherent
      hcoh)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_successor_step_pair :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_nonunit_coherent,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_successor_step_pair⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_of_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitProductLocalOrientationPropagates_of_display_compatible_nomix
    hχ (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
      χ hχ hprime)
    ((PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_comparable_trace.mpr
      hcomp) χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitLocalOrientation_of_prime_and_product_local
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    ((PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_of_identity_comparable_trace
      hcomp) χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_identity_comparable_trace
      hcomp,
    hcomp⟩

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_local_comparable_trace
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  hsharp.2

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_iff_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_local_comparable_trace,
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_identity_comparable_trace⟩

/-- Second component of the prime-floor successor blocker: adjacent nonunit
orbit directions cannot carry opposite identity/reciprocal orientations. -/
def PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ

theorem PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_nonunit_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_of_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_successor_transport
    (hstep χ hχ hprime)

/-- The exact local version of the corrected successor blocker: local nonunit
orientation plus adjacent no-mixing is equivalent to local nonunit orientation
plus prime-floor successor transport. -/
def PRCPrimeFloorSuccessorTransportLocalAdjacentTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget

/-- Pass-39 refinement of the prime-floor successor target. It separates local
nonunit orientation from adjacent no-mixing instead of bundling both facts under
successor transport. -/
def PRCPrimeFloorSuccessorTransportSharpenedTarget : Prop :=
  PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget ∧
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget

theorem PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget_of_additive_compat
    (hadd : PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget) :
    PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitIdentitySuccessorTransport_of_additive_compat
    (hadd χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_nomix
    (hsharp : PRCPrimeFloorSuccessorTransportSharpenedTarget) :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_local_adjacent_nomix
    (PRCCharacterNonunitOrbitLocalOrientation_of_coherent
      (hsharp.1 χ hχ hprime))
    (hsharp.2 χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_target
    (hsharp : PRCPrimeFloorSuccessorTransportLocalAdjacentTarget) :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_local_adjacent_nomix
    (hsharp.1 χ hχ hprime) (hsharp.2 χ hχ hprime)

theorem PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_of_local_successor_transport
    (hsharp :
      PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
        PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget :=
  ⟨hsharp.1,
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_of_successor_transport
      hsharp.2⟩

theorem PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_local_successor_transport :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget ↔
      (PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
        PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :=
  ⟨(fun hsharp =>
      ⟨hsharp.1,
        PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_target
          hsharp⟩),
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_of_local_successor_transport⟩

theorem PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_of_nonunit_coherent
    (hcoh : PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget) :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_nonunit_coherent hcoh,
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_of_nonunit_coherent
      hcoh⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_adjacent
    (hsharp : PRCPrimeFloorSuccessorTransportLocalAdjacentTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_and_prime_floor_successor_transport
    ⟨hsharp.1,
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_target
        hsharp⟩

theorem PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_nonunit_coherent :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_adjacent,
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_of_nonunit_coherent⟩

theorem PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_product_local_orientation
    (hprod : PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitOrbitLocalOrientation_of_prime_and_product_local
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hprod χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_of_display_compatible_nomix
    (hsharp : PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget) :
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitProductLocalOrientationPropagates_of_display_compatible_nomix
    hχ (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
      χ hχ hprime)
    (PRCCharacterOrbitProductNoMixedOrientation_of_nonunit_coherent
      (hsharp χ hχ hprime))

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_prime_floor_successor_transport
    (hstep : PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_prime_floor_successor_transport
    (hstep χ hχ hprime)

theorem PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_of_transport
    (htransport : PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget) :
    PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterOrbitIdentityRespectsSuccessorStep_of_transport
    (htransport χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_successor_step
    (hstep : PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_successor_step
    (hstep χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_comparable_trace
    (hcomp χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_common_trace_extension
    (hcommon : PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_common_trace_extension
    (hcommon χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_canonical_add_trace
    (hcanon : PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_canonical_add_trace
    (hcanon χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_iff_common_trace_extension :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_canonical_add_trace,
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_common_trace_extension⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_common_trace_extension
    (hcommon : PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_common_trace_extension
    (hcommon χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_trace_transport
    (htransport : PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_trace_connected
    (htransport χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_canonical_add_trace
    (hcanon : PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_canonical_add_trace
    (hcanon χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_iff_trace_transport :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_canonical_add_trace,
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_trace_transport⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_trace_coherence
    (hcoh : PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityBranchUniform_of_trace_coherence
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_branch_uniformity
    (huniform : PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityTraceCoherent_of_branch_uniform
    (huniform χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_trace_coherence :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_branch_uniformity,
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_trace_coherence⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_branch_uniformity
    (huniform : PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_branch_uniform
    (huniform χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_canonical_add_trace
    (hcanon : PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityBranchUniform_of_canonical_add_trace
    (hcanon χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_canonical_add_trace :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_branch_uniformity,
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_canonical_add_trace⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_trace_transport
    (htransport : PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget := by
  intro χ hχ hprime p hp r hr hpId
  exact htransport χ hχ hprime p hp r hr
    (PRCPrimeAxisTraceConnected_proved p hp r hr) hpId

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_trace_coherence
    (hcoh : PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_trace_coherence
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityTraceCoherent_of_comparable_trace
    (hcomp χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_comparable_trace :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_trace_coherence,
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_comparable_trace⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_trace_coherence
    (hcoh : PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_trace_coherence
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_common_trace_extension
    (hcommon : PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityTraceCoherent_of_common_trace_extension
    (hcommon χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_common_trace_extension :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_trace_coherence,
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_common_trace_extension⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_trace_coherence
    (hcoh : PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_trace_coherence
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_trace_transport :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_trace_coherence,
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_trace_transport⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_nonunit_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_nonunit_identity_comparable_trace
    (hcomp χ hχ hprime)

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_identity_comparable_trace
    (hcomp : PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget) :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget := by
  intro χ hχ hprime
  exact PRCCharacterNonunitIdentityRespectsComparableTrace_of_prime_comparable
    hχ
    (PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
      χ hχ hprime)
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hcomp χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_nonunit_identity_comparable_trace :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget :=
  ⟨PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_identity_comparable_trace,
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_nonunit_identity_comparable_trace⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_prime_floor_successor_transport :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_nonunit_identity_comparable_trace.trans
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_prime_floor_successor_transport

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_trace_coherence
    (htrace : PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget := by
  intro χ hχ hprime p hp r hr hpId hrRec
  have hrId := htrace χ hχ hprime p hp r hr hpId
  have hself :
      RatioOrbit.crossEq
        (primeDirection r hr)
        (RatioOrbit.recip (primeDirection r hr)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hrId) hrRec
  exact primeDirection_not_crossEq_recip r hr hself

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_no_mixed_prime_orientation
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityTraceCoherent_of_local_no_mixed_prime_orientation
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_iff_trace_coherence :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_no_mixed_prime_orientation,
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_trace_coherence⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_branch_uniformity
    (huniform : PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeOrientation_of_branch_uniform
    (huniform χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_mixed_prime_orientation
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityBranchUniform_of_local_no_mixed_prime_orientation
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hnomix χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_branch_uniformity,
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_mixed_prime_orientation⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_trace_coherence :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget :=
  PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_orientation.trans
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_iff_trace_coherence

/-- Sharper orientation blocker A: prime cost calibration must choose one
coherent orientation across all native prime axes. This is the place where
mixed independent prime inversions must be ruled out. -/
def PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeOrientationCoherent χ

/-- Distinguished-prime normal form of the same blocker: prime calibration must
make the branch chosen at orbit `2` control every native prime branch. -/
def PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterTwoPrimeBranchControlsPrimes χ

/-- Identity-iff-two target: prime calibration must force identity orientation
on any prime axis exactly when it forces identity on the distinguished orbit
`2` prime axis. -/
def PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ

/-- One-sided distinguished-axis target: prime calibration must force identity
at the orbit-`2` prime axis from identity at any calibrated prime axis. -/
def PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ

/-- Two-reciprocal exclusion target: if prime calibration leaves the orbit-`2`
axis on the reciprocal branch, no native prime axis may remain on identity. -/
def PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ

/-- Two-specific mixed-witness exclusion target: if the orbit-`2` prime axis is
reciprocal-oriented, no identity-oriented native prime witness may exist. -/
def PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget :
    Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ

/-- Exact calibrated mixed-character model whose nonexistence is equivalent to
the orbit-`2` mixed-witness exclusion target. Constructing this model would
refute the current character-rigidity route. -/
def PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter :
    Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ

/-- Sharpened calibrated mixed-character model: orbit `2` is reciprocal, while
a non-`2` native prime witness is identity-oriented. -/
def PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter :
    Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ

/-- Concrete calibrated two-adic axis-twist model. Constructing this object is
the native valuation route to refuting the current character-rigidity branch. -/
def PRCPrimeCalibratedTwoAdicAxisTwistCharacter : Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterTwoAdicAxisTwist χ

theorem PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist
    {χ : RatioOrbit → RatioOrbit}
    (htwist : PRCCharacterTwoAdicAxisTwist χ) :
    PRCCharacterPrimeDirectionCalibrated χ := by
  intro p hp
  by_cases hptwo : p = twoOrbit
  · subst p
    have hcost :
        RatioOrbit.crossEq
          (costFromCharacter χ twoPrimeDirection)
          (onRatioOrbit twoPrimeDirection) := by
      unfold costFromCharacter
      exact
        RatioOrbit.crossEq_trans
          (onRatioOrbit_congr htwist.1)
          (RatioOrbit.crossEq_symm (reciprocal_symmetric twoPrimeDirection))
    simpa [twoPrimeDirection, primeDirection] using hcost
  · unfold costFromCharacter
    exact onRatioOrbit_congr (htwist.2 p hp hptwo)

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
    (htwist : PRCTwoAdicAxisTwistRatioCharacter) :
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter := by
  rcases htwist with ⟨χ, hχ, hbranch⟩
  exact
    ⟨χ, hχ,
      PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist hbranch,
      hbranch⟩

theorem PRCTwoAdicAxisTwistRatioCharacter_of_calibrated_two_adic_axis_twist
    (htwist : PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    PRCTwoAdicAxisTwistRatioCharacter := by
  rcases htwist with ⟨χ, hχ, _hprime, hbranch⟩
  exact ⟨χ, hχ, hbranch⟩

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_iff_ratio_character_axis_twist :
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter ↔
      PRCTwoAdicAxisTwistRatioCharacter :=
  ⟨PRCTwoAdicAxisTwistRatioCharacter_of_calibrated_two_adic_axis_twist,
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist⟩

theorem PRCTwoAdicAxisTwistRatioCharacter_absurd_of_no_calibrated_twist
    (hno : ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    ¬ PRCTwoAdicAxisTwistRatioCharacter := by
  intro htwist
  exact hno
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
      htwist)

/-- Calibrated composite-defect model equivalent to the non-two mixed-prime
blocker, but with the forced composite image `χ(2*p)=p/2` exposed. -/
def PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter :
    Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ

/-- Calibrated cost-visible composite-defect model equivalent to the Pass 95
blocker, but now exposing the actual composite J-cost failure. -/
def PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter :
    Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ

/-- Calibrated mixed-prime witness model: a ratio character satisfies prime
calibration while carrying both an identity-oriented prime witness and a
reciprocal-oriented prime witness. Nonexistence of this model is definitionally
the current no-mixed-prime witness blocker. -/
def PRCPrimeCalibratedMixedPrimeWitnessesCharacter : Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterMixedPrimeWitnesses χ

/-- Fully unpacked calibrated mixed-prime pair model: a calibrated ratio
character plus named native prime axes `p` and `r`, with `p` identity-oriented
and `r` reciprocal-oriented. This is the current obstruction with no remaining
propositional packaging around the two branch witnesses. -/
def PRCPrimeCalibratedMixedPrimePairWitnessCharacter : Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterMixedPrimePairWitnesses χ

/-- Calibrated same-axis mixed-prime pair model: the mixed branch occurs at a
single native prime orbit. -/
def PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter : Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterSamePrimeMixedPairWitnesses χ

/-- Calibrated distinct-axis mixed-prime pair model: the mixed branch occurs
between two different native prime orbits. -/
def PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter : Prop :=
  ∃ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ ∧
      PRCCharacterPrimeDirectionCalibrated χ ∧
        PRCCharacterDistinctPrimeMixedPairWitnesses χ

theorem PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter_of_non_two_mixed
    (hmix :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  rcases hmix with ⟨χ, hχ, hprime, htwoRec, p, hp, hpne, hpId⟩
  exact
    ⟨χ, hχ, hprime, p, hp, twoOrbit, twoOrbit_primeOrbit, hpne, hpId,
      by simpa [twoPrimeDirection] using htwoRec⟩

/-- Trace-connected reciprocal target: prime calibration should force reciprocal
orientation at the orbit-`2` prime axis to transport along any finite δ-trace
connection to a native prime axis. -/
def PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ

/-- Two-prime identity trace-connected target: prime calibration should force
identity orientation at the orbit-`2` prime axis to transport along any finite
δ-trace connection to a native prime axis. Pass 81 isolates this as the same
blocker as reciprocal trace transport, seen through reciprocal twist. -/
def PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ

theorem PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_local_and_nomixed
    (hlocal : PRCPrimeCalibrationForcesLocalPrimeOrientationTarget)
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget := by
  intro χ hχ hprime
  have hloc := hlocal χ hχ hprime
  have hno := hnomix χ hχ hprime
  by_cases hId :
      ∃ p : DistinctionNat, ∃ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)
  · rcases hId with ⟨p0, hp0, hid0⟩
    exact Or.inl (by
      intro p hp
      rcases hloc p hp with hid | hrec
      · exact hid
      · exact False.elim (hno p0 hp0 p hp hid0 hrec))
  · exact Or.inr (by
      intro p hp
      rcases hloc p hp with hid | hrec
      · exact False.elim (hId ⟨p, hp, hid⟩)
      · exact hrec)

theorem PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_no_mixed_prime_witnesses
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget :=
  PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_local_and_nomixed
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved
    (PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_no_mixed_prime_witnesses
      hnomix)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_coherent_prime_orientation
    (hcoh : PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro χ hχ hprime
  exact PRCCharacterNoMixedPrimeWitnesses_of_coherent_prime_orientation
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_coherent_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_no_mixed_prime_witnesses,
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_coherent_prime_orientation⟩

theorem PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_coherent_prime_orientation
    (hcoh : PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeBranchControlsPrimes_of_coherent
    (hcoh χ hχ hprime)

theorem PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_two_prime_branch_controls
    (hctrl : PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget) :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeOrientationCoherent_of_local_two_prime_branch_controls
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hctrl χ hχ hprime)

theorem PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_iff_two_prime_branch_controls :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_coherent_prime_orientation,
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_two_prime_branch_controls⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_two_prime_branch_controls
    (hctrl : PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_local_two_prime_branch_controls
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hctrl χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_prime_identity_iff_two
    (hiff : PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeBranchControlsPrimes_of_local_prime_identity_iff_two
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hiff χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_iff_prime_identity_iff_two :
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_two_prime_branch_controls,
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_prime_identity_iff_two⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_identity_iff_two
    (hiff : PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_identity_iff_two
    (hiff χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget := by
  intro χ hχ hprime p hp
  constructor
  · exact hforces χ hχ hprime p hp
  · intro htwoId
    rcases PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime
        p hp with hpId | hpRec
    · exact hpId
    · have htwistId :
          RatioOrbit.crossEq
              (PRCCharacterReciprocalTwist χ (primeDirection p hp))
              (primeDirection p hp) :=
        (PRCCharacterReciprocalTwist_prime_identity_iff_reciprocal
          χ p hp).mpr hpRec
      have htwistTwoId :=
        hforces (PRCCharacterReciprocalTwist χ)
          hχ.reciprocalTwist hprime.reciprocalTwist p hp htwistId
      have htwoRec :
          RatioOrbit.crossEq (χ twoPrimeDirection)
            (RatioOrbit.recip twoPrimeDirection) :=
        (PRCCharacterReciprocalTwist_two_identity_iff_reciprocal
          χ).mp htwistTwoId
      have hself :
          RatioOrbit.crossEq twoPrimeDirection
            (RatioOrbit.recip twoPrimeDirection) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
      exact False.elim
        (primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself)

theorem PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_iff_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_identity_iff_two,
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_identity_forces_two⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_identity_forces_two
    (hforces χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
    (hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_local_two_prime_reciprocal_excludes
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_identity_forces_two,
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_two_prime_reciprocal_excludes
    (hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_excludes
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_witness
    (hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_witness_excludes
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_witness :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_two_prime_reciprocal_excludes,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_witness⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes_witness
    (hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_witness
      hexcl)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget :=
  PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_two_prime_reciprocal_excludes
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_identity_forces_two
      hforces)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_identity_forces_two,
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes_witness⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_no_mixed_character
    (hmix :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_not_mixed
    (by
      intro hcharMix
      exact hmix ⟨χ, hχ, hprime, hcharMix⟩)

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_absurd_of_witness_excludes
    (hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget) :
    ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter := by
  intro hmix
  rcases hmix with ⟨χ, hχ, hprime, hcharMix⟩
  exact
    (PRCCharacter_not_mixed_of_two_prime_reciprocal_excludes_prime_identity_witness
      (hexcl χ hχ hprime)) hcharMix

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_mixed_character :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter :=
  ⟨PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_absurd_of_witness_excludes,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_no_mixed_character⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_mixed
    (hmix : PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter := by
  rcases hmix with ⟨χ, hχ, hprime, hcharMix⟩
  exact
    ⟨χ, hχ, hprime,
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_of_mixed hcharMix⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_of_non_two_mixed
    (hmix :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter := by
  rcases hmix with ⟨χ, hχ, hprime, hcharMix⟩
  exact
    ⟨χ, hχ, hprime,
      PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed_of_non_two_mixed hcharMix⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_iff_non_two :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter ↔
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter :=
  ⟨PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_mixed,
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_of_non_two_mixed⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
    (htwist : PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter := by
  rcases htwist with ⟨χ, hχ, hprime, htwistχ⟩
  rcases htwistχ with ⟨htwoRec, hnonTwoId⟩
  exact
    ⟨χ, hχ, hprime,
      ⟨htwoRec, threeOrbit, threeOrbit_primeOrbit, threeOrbit_ne_twoOrbit,
        hnonTwoId threeOrbit threeOrbit_primeOrbit threeOrbit_ne_twoOrbit⟩⟩

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_no_non_two_mixed
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter := by
  intro htwist
  exact hno
    (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
      htwist)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_non_two_mixed_character :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter := by
  constructor
  · intro hexcl hnonTwo
    exact
      (PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_absurd_of_witness_excludes
        hexcl)
        (PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_of_non_two_mixed
          hnonTwo)
  · intro hnonTwo
    exact
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_no_mixed_character
        (by
          intro hmix
          exact hnonTwo
            (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_mixed
              hmix))

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed
    (hmix :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter := by
  rcases hmix with ⟨χ, hχ, hprime, hcharMix⟩
  exact
    ⟨χ, hχ, hprime,
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_non_two_mixed
        hχ hcharMix⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_composite_defect
    (hdefect :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter := by
  rcases hdefect with ⟨χ, hχ, hprime, hcharDefect⟩
  exact
    ⟨χ, hχ, hprime,
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_of_composite_defect
        hcharDefect⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_iff_composite_defect :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter ↔
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter :=
  ⟨PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed,
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_composite_defect⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_defect_character :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter := by
  constructor
  · intro hexcl hdefect
    exact
      (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_non_two_mixed_character.mp
        hexcl)
        (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_composite_defect
          hdefect)
  · intro hdefect
    exact
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_non_two_mixed_character.mpr
        (by
          intro hmix
          exact hdefect
            (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed
              hmix))

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_composite_defect
    (hdefect :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter := by
  rcases hdefect with ⟨χ, hχ, hprime, hcharDefect⟩
  exact
    ⟨χ, hχ, hprime,
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect_of_composite_defect
        hcharDefect⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_cost_defect
    (hdefect :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter := by
  rcases hdefect with ⟨χ, hχ, hprime, hcharDefect⟩
  exact
    ⟨χ, hχ, hprime,
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_cost_defect
        hcharDefect⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_iff_cost_defect :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter ↔
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter :=
  ⟨PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_composite_defect,
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_cost_defect⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_cost_defect_character :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter := by
  constructor
  · intro hexcl hdefect
    exact
      (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_defect_character.mp
        hexcl)
        (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_cost_defect
          hdefect)
  · intro hdefect
    exact
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_defect_character.mpr
        (by
          intro hplain
          exact hdefect
            (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_composite_defect
              hplain))

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_no_composite_cost_defect
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter) :
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget := by
  intro χ hχ hprime htwoRec p hp hpne hpId
  by_contra hnotCost
  have hcharDefect :
      PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ :=
    PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect_of_composite_defect
      (PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_non_two_mixed
        hχ ⟨htwoRec, p, hp, hpne, hpId⟩)
  exact hno ⟨χ, hχ, hprime, hcharDefect⟩

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_absurd_of_mixed_composite_consistency
    (hconsistency :
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget) :
    ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter := by
  intro hdefect
  rcases hdefect with ⟨χ, hχ, hprime, hcharDefect⟩
  rcases hcharDefect with ⟨htwoRec, p, hp, hpne, hpId, _hprod, hnotCost⟩
  exact hnotCost (hconsistency χ hχ hprime htwoRec p hp hpne hpId)

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_composite_cost_defect_character :
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter :=
  ⟨PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_absurd_of_mixed_composite_consistency,
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_no_composite_cost_defect⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_mixed_composite_cost_consistency :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget := by
  constructor
  · intro hexcl
    exact
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_no_composite_cost_defect
        (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_cost_defect_character.mp
          hexcl)
  · intro hconsistency
    exact
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_cost_defect_character.mpr
        (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_absurd_of_mixed_composite_consistency
          hconsistency)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_mixed_composite_cost_consistency_direct
    (hconsistency :
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget := by
  intro χ hχ hprime htwoRec hwitness
  rcases hwitness with ⟨p, hp, hpId⟩
  by_cases hpne : p ≠ twoOrbit
  · have hcost :=
      hconsistency χ hχ hprime htwoRec p hp hpne hpId
    have hmulχ :
        RatioOrbit.crossEq
          (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
          (RatioOrbit.mul (χ twoPrimeDirection) (χ (primeDirection p hp))) :=
      hχ.multiplicative twoPrimeDirection (primeDirection p hp)
    have hmulTarget :
        RatioOrbit.crossEq
          (RatioOrbit.mul (χ twoPrimeDirection) (χ (primeDirection p hp)))
          (RatioOrbit.mul
            (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)) :=
      ratioOrbit_mul_congr htwoRec hpId
    have hprod :
        RatioOrbit.crossEq
          (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
          (RatioOrbit.mul
            (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)) :=
      RatioOrbit.crossEq_trans hmulχ hmulTarget
    have hcostImage :
        RatioOrbit.crossEq
          (costFromCharacter χ
            (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
          (onRatioOrbit
            (RatioOrbit.mul
              (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp))) :=
      onRatioOrbit_congr hprod
    exact
      two_prime_composite_mixed_image_jcost_mismatch p hp
        (RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hcostImage) hcost)
  · have hpeq : p = twoOrbit := by
      by_contra h
      exact hpne h
    have hdir : primeDirection p hp = twoPrimeDirection := by
      subst hpeq
      rfl
    rw [hdir] at hpId
    have hself :
        RatioOrbit.crossEq twoPrimeDirection
          (RatioOrbit.recip twoPrimeDirection) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) htwoRec
    exact primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself

theorem PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_prime_pair_product_cost_consistent
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hpair : PRCCharacterPrimePairProductCostConsistent χ) :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ := by
  intro htwoRec hwitness
  rcases hwitness with ⟨p, hp, hpId⟩
  by_cases hpne : p ≠ twoOrbit
  · have hcost :=
      hpair twoOrbit twoOrbit_primeOrbit p hp
    have hmulχ :
        RatioOrbit.crossEq
          (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
          (RatioOrbit.mul (χ twoPrimeDirection) (χ (primeDirection p hp))) :=
      hχ.multiplicative twoPrimeDirection (primeDirection p hp)
    have hmulTarget :
        RatioOrbit.crossEq
          (RatioOrbit.mul (χ twoPrimeDirection) (χ (primeDirection p hp)))
          (RatioOrbit.mul
            (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)) :=
      ratioOrbit_mul_congr htwoRec hpId
    have hprod :
        RatioOrbit.crossEq
          (χ (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
          (RatioOrbit.mul
            (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp)) :=
      RatioOrbit.crossEq_trans hmulχ hmulTarget
    have hcostImage :
        RatioOrbit.crossEq
          (costFromCharacter χ
            (RatioOrbit.mul twoPrimeDirection (primeDirection p hp)))
          (onRatioOrbit
            (RatioOrbit.mul
              (RatioOrbit.recip twoPrimeDirection) (primeDirection p hp))) :=
      onRatioOrbit_congr hprod
    exact
      two_prime_composite_mixed_image_jcost_mismatch p hp
        (RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hcostImage) hcost)
  · have hpeq : p = twoOrbit := by
      by_contra h
      exact hpne h
    have hdir : primeDirection p hp = twoPrimeDirection := by
      subst hpeq
      rfl
    rw [hdir] at hpId
    have hself :
        RatioOrbit.crossEq twoPrimeDirection
          (RatioOrbit.recip twoPrimeDirection) :=
      RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hpId) htwoRec
    exact primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself

theorem PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_prime_pair_product_cost_consistent
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hprime : PRCCharacterPrimeDirectionCalibrated χ)
    (hpair : PRCCharacterPrimePairProductCostConsistent χ) :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ := by
  have hlocal :=
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime
  have hexclWitness :
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ :=
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness_of_prime_pair_product_cost_consistent
      hχ hpair
  have hexcl :
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ :=
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_witness_excludes
      hexclWitness
  exact
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_local_two_prime_reciprocal_excludes
      hlocal hexcl

theorem PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_admissible
    {χ : RatioOrbit → RatioOrbit}
    (hadm : PRCAdmissibleRatioCharacter χ) :
    PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ := by
  have hforces :
      PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ :=
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_prime_pair_product_cost_consistent
      hadm.ratio_character hadm.prime_calibrated
      hadm.prime_pair_product_cost
  intro p hp
  constructor
  · exact hforces p hp
  · intro htwoId
    rcases PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved
        χ hadm.ratio_character hadm.prime_calibrated p hp with hpId | hpRec
    · exact hpId
    · have htwistAdmissible :
        PRCAdmissibleRatioCharacter (PRCCharacterReciprocalTwist χ) :=
        hadm.reciprocalTwist
      have htwistForces :
          PRCCharacterPrimeIdentityForcesTwoPrimeIdentity
            (PRCCharacterReciprocalTwist χ) :=
        PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_prime_pair_product_cost_consistent
          htwistAdmissible.ratio_character
          htwistAdmissible.prime_calibrated
          htwistAdmissible.prime_pair_product_cost
      have htwistId :
          RatioOrbit.crossEq
              (PRCCharacterReciprocalTwist χ (primeDirection p hp))
              (primeDirection p hp) :=
        (PRCCharacterReciprocalTwist_prime_identity_iff_reciprocal
          χ p hp).mpr hpRec
      have htwistTwoId := htwistForces p hp htwistId
      have htwoRec :
          RatioOrbit.crossEq (χ twoPrimeDirection)
            (RatioOrbit.recip twoPrimeDirection) :=
        (PRCCharacterReciprocalTwist_two_identity_iff_reciprocal
          χ).mp htwistTwoId
      have hself :
          RatioOrbit.crossEq twoPrimeDirection
            (RatioOrbit.recip twoPrimeDirection) :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
      exact False.elim
        (primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself)

theorem PRCCharacterPrimeOrientationCoherent_of_admissible
    {χ : RatioOrbit → RatioOrbit}
    (hadm : PRCAdmissibleRatioCharacter χ) :
    PRCCharacterPrimeOrientationCoherent χ := by
  have hlocal :=
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved
      χ hadm.ratio_character hadm.prime_calibrated
  have hiff :
      PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ :=
    PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_admissible hadm
  have hctrl :
      PRCCharacterTwoPrimeBranchControlsPrimes χ :=
    PRCCharacterTwoPrimeBranchControlsPrimes_of_local_prime_identity_iff_two
      hlocal hiff
  exact
    PRCCharacterPrimeOrientationCoherent_of_local_two_prime_branch_controls
      hlocal hctrl

theorem PRCAdmissibleCharacterPrimeOrientationCoherentTarget_proved :
    PRCAdmissibleCharacterPrimeOrientationCoherentTarget := by
  intro χ hadm
  exact PRCCharacterPrimeOrientationCoherent_of_admissible hadm

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget := by
  intro χ hχ hprime _htwoRec p hp _hpne _hpId
  exact hpair χ hχ hprime twoOrbit twoOrbit_primeOrbit p hp

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_prime_calibration_propagation
    (hprop : PRCPrimeCalibrationPropagationTarget) :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget := by
  intro χ hχ hprime p hp r hr
  exact hprop χ hχ hprime
    (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_coherent_prime_orientation
    (hcoh : PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget) :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget := by
  intro χ hχ hprime p hp r hr
  let qp := primeDirection p hp
  let qr := primeDirection r hr
  rcases hcoh χ hχ hprime with hallId | hallRec
  · have hpId : RatioOrbit.crossEq (χ qp) qp := by
      simpa [qp] using hallId p hp
    have hrId : RatioOrbit.crossEq (χ qr) qr := by
      simpa [qr] using hallId r hr
    exact onRatioOrbit_congr
      (RatioOrbit.crossEq_trans
        (hχ.multiplicative qp qr)
        (ratioOrbit_mul_congr hpId hrId))
  · have hpRec :
        RatioOrbit.crossEq (χ qp) (RatioOrbit.recip qp) := by
      simpa [qp] using hallRec p hp
    have hrRec :
        RatioOrbit.crossEq (χ qr) (RatioOrbit.recip qr) := by
      simpa [qr] using hallRec r hr
    exact RatioOrbit.crossEq_trans
      (onRatioOrbit_congr
        (RatioOrbit.crossEq_trans
          (hχ.multiplicative qp qr)
          (RatioOrbit.crossEq_trans
            (ratioOrbit_mul_congr hpRec hrRec)
            (ratioOrbit_mul_recip_recip_crossEq_recip_mul qp qr))))
      (RatioOrbit.crossEq_symm (reciprocal_symmetric (RatioOrbit.mul qp qr)))

theorem PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget :=
  PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_two_prime_branch_controls
    (PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_prime_identity_iff_two
      (PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_identity_forces_two
        (PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes_witness
          (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_mixed_composite_cost_consistency_direct
            (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_prime_pair_product_cost_consistency
              hpair)))))

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_coherent_prime_orientation :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget :=
  ⟨PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_prime_pair_product_cost_consistency,
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_coherent_prime_orientation⟩

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_no_mixed_prime_witnesses
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_coherent_prime_orientation
    (PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_no_mixed_prime_witnesses
      hnomix)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget :=
  PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_coherent_prime_orientation
    (PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_prime_pair_product_cost_consistency
      hpair)

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget :=
  ⟨PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_pair_product_cost_consistency,
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_no_mixed_prime_witnesses⟩

theorem PRCPrimeCalibratedMixedPrimeWitnessesCharacter_absurd_of_no_mixed_prime_witnesses
    (hnomix : PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    ¬ PRCPrimeCalibratedMixedPrimeWitnessesCharacter := by
  intro hmixed
  rcases hmixed with ⟨χ, hχ, hprime, hcharMixed⟩
  exact (hnomix χ hχ hprime) hcharMixed

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_witness_character
    (hmixed : ¬ PRCPrimeCalibratedMixedPrimeWitnessesCharacter) :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro χ hχ hprime hcharMixed
  exact hmixed ⟨χ, hχ, hprime, hcharMixed⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_witness_character :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCPrimeCalibratedMixedPrimeWitnessesCharacter :=
  ⟨PRCPrimeCalibratedMixedPrimeWitnessesCharacter_absurd_of_no_mixed_prime_witnesses,
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_witness_character⟩

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witness_character :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCPrimeCalibratedMixedPrimeWitnessesCharacter :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witnesses.trans
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_witness_character

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_of_mixed_prime_witness_character
    (hmixed : PRCPrimeCalibratedMixedPrimeWitnessesCharacter) :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro hnomix
  exact (PRCPrimeCalibratedMixedPrimeWitnessesCharacter_absurd_of_no_mixed_prime_witnesses
    hnomix) hmixed

theorem PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_not_no_mixed_prime_witnesses
    (hnot : ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget) :
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter := by
  by_contra hmixed
  exact hnot
    (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_witness_character
      hmixed)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_mixed_prime_witness_character :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibratedMixedPrimeWitnessesCharacter :=
  ⟨PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_not_no_mixed_prime_witnesses,
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_of_mixed_prime_witness_character⟩

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_mixed_prime_witness_character
    (hmixed : PRCPrimeCalibratedMixedPrimeWitnessesCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget := by
  intro hpair
  exact (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_of_mixed_prime_witness_character
    hmixed)
    (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_pair_product_cost_consistency
      hpair)

theorem PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_not_prime_pair_product_cost_consistency
    (hnot : ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter := by
  by_contra hmixed
  exact hnot
    ((PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witness_character).mpr
      hmixed)

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_mixed_prime_witness_character :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibratedMixedPrimeWitnessesCharacter :=
  ⟨PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_not_prime_pair_product_cost_consistency,
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_mixed_prime_witness_character⟩

theorem PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_mixed_prime_witness_character
    (hmixed : PRCPrimeCalibratedMixedPrimeWitnessesCharacter) :
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter := by
  rcases hmixed with ⟨χ, hχ, hprime, hcharMixed⟩
  exact ⟨χ, hχ, hprime,
    PRCCharacterMixedPrimePairWitnesses_of_mixed_prime_witnesses hcharMixed⟩

theorem PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_pair_witness_character
    (hpair : PRCPrimeCalibratedMixedPrimePairWitnessCharacter) :
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter := by
  rcases hpair with ⟨χ, hχ, hprime, hcharPair⟩
  exact ⟨χ, hχ, hprime,
    PRCCharacterMixedPrimeWitnesses_of_pair_witnesses hcharPair⟩

theorem PRCPrimeCalibratedMixedPrimeWitnessesCharacter_iff_pair_witness_character :
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter ↔
      PRCPrimeCalibratedMixedPrimePairWitnessCharacter :=
  ⟨PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_mixed_prime_witness_character,
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_pair_witness_character⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_pair_witness_character :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCPrimeCalibratedMixedPrimePairWitnessCharacter :=
  PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_witness_character.trans
    (not_congr PRCPrimeCalibratedMixedPrimeWitnessesCharacter_iff_pair_witness_character)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_mixed_prime_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibratedMixedPrimePairWitnessCharacter :=
  PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_mixed_prime_witness_character.trans
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter_iff_pair_witness_character

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_pair_witness_character :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCPrimeCalibratedMixedPrimePairWitnessCharacter :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witness_character.trans
    (not_congr PRCPrimeCalibratedMixedPrimeWitnessesCharacter_iff_pair_witness_character)

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_mixed_prime_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibratedMixedPrimePairWitnessCharacter :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_mixed_prime_witness_character.trans
    PRCPrimeCalibratedMixedPrimeWitnessesCharacter_iff_pair_witness_character

theorem PRCPrimeCalibratedMixedPrimePairWitnessCharacter_same_or_distinct
    (hpair : PRCPrimeCalibratedMixedPrimePairWitnessCharacter) :
    PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
      PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  rcases hpair with ⟨χ, hχ, hprime, hcharPair⟩
  cases PRCCharacterMixedPrimePairWitnesses_same_or_distinct hcharPair with
  | inl hsame => exact Or.inl ⟨χ, hχ, hprime, hsame⟩
  | inr hdistinct => exact Or.inr ⟨χ, hχ, hprime, hdistinct⟩

theorem PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_same
    (hsame : PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter) :
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter := by
  rcases hsame with ⟨χ, hχ, hprime, hcharSame⟩
  exact ⟨χ, hχ, hprime,
    PRCCharacterMixedPrimePairWitnesses_of_same hcharSame⟩

theorem PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_distinct
    (hdistinct : PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter) :
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter := by
  rcases hdistinct with ⟨χ, hχ, hprime, hcharDistinct⟩
  exact ⟨χ, hχ, hprime,
    PRCCharacterMixedPrimePairWitnesses_of_distinct hcharDistinct⟩

theorem PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_same_or_distinct
    (hsplit :
      PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter) :
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter := by
  cases hsplit with
  | inl hsame => exact PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_same hsame
  | inr hdistinct =>
      exact PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_distinct hdistinct

theorem PRCPrimeCalibratedMixedPrimePairWitnessCharacter_iff_same_or_distinct :
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter ↔
      PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter :=
  ⟨PRCPrimeCalibratedMixedPrimePairWitnessCharacter_same_or_distinct,
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_same_or_distinct⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_same_and_no_distinct_pair_witness_character :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∧
        ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro htarget
    constructor
    · intro hsame
      exact (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_pair_witness_character.mp
        htarget)
        (PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_same hsame)
    · intro hdistinct
      exact (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_pair_witness_character.mp
        htarget)
        (PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_distinct hdistinct)
  · intro hnoSplit
    exact PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_pair_witness_character.mpr
      (fun hpair =>
        (PRCPrimeCalibratedMixedPrimePairWitnessCharacter_iff_same_or_distinct.mp hpair).elim
          hnoSplit.1 hnoSplit.2)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_same_or_distinct_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter :=
  PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_mixed_prime_pair_witness_character.trans
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter_iff_same_or_distinct

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_same_and_no_distinct_pair_witness_character :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∧
        ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro htarget
    exact PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_same_and_no_distinct_pair_witness_character.mp
      (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_pair_product_cost_consistency
        htarget)
  · intro hnoSplit
    exact PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_pair_witness_character.mpr
      (fun hpair =>
        (PRCPrimeCalibratedMixedPrimePairWitnessCharacter_iff_same_or_distinct.mp hpair).elim
          hnoSplit.1 hnoSplit.2)

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_same_or_distinct_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_mixed_prime_pair_witness_character.trans
    PRCPrimeCalibratedMixedPrimePairWitnessCharacter_iff_same_or_distinct

theorem PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd :
    ¬ PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter := by
  intro hsame
  rcases hsame with ⟨χ, _hχ, _hprime, hcharSame⟩
  exact PRCCharacterSamePrimeMixedPairWitnesses_absurd hcharSame

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_distinct_prime_pair_witness_character :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro htarget hdistinct
    exact (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_same_and_no_distinct_pair_witness_character.mp
      htarget).2 hdistinct
  · intro hnoDistinct
    exact PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_same_and_no_distinct_pair_witness_character.mpr
      ⟨PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd, hnoDistinct⟩

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro hnot
    rcases (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_same_or_distinct_pair_witness_character.mp
      hnot) with hsame | hdistinct
    · exact False.elim
        (PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd hsame)
    · exact hdistinct
  · intro hdistinct htarget
    exact (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_distinct_prime_pair_witness_character.mp
      htarget) hdistinct

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_distinct_prime_pair_witness_character :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro htarget hdistinct
    exact (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_same_and_no_distinct_pair_witness_character.mp
      htarget).2 hdistinct
  · intro hnoDistinct
    exact PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_same_and_no_distinct_pair_witness_character.mpr
      ⟨PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd, hnoDistinct⟩

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro hnot
    rcases (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_same_or_distinct_pair_witness_character.mp
      hnot) with hsame | hdistinct
    · exact False.elim
        (PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd hsame)
    · exact hdistinct
  · intro hdistinct htarget
    exact (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_distinct_prime_pair_witness_character.mp
      htarget) hdistinct

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_distinct_prime_pair_witness_character
    (hnoDistinct : ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter) :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityBranchUniform_of_local_no_distinct_prime_pair
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime) (by
      intro hdistinct
      exact hnoDistinct ⟨χ, hχ, hprime, hdistinct⟩)

theorem PRCPrimeCalibrationForcesNoDistinctPrimePairWitnessCharacter_of_prime_identity_branch_uniformity
    (huniform : PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  intro hdistinct
  rcases hdistinct with ⟨χ, hχ, hprime, hcharDistinct⟩
  exact PRCCharacterDistinctPrimeMixedPairWitnesses_absurd_of_branch_uniform
    (huniform χ hχ hprime) hcharDistinct

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_distinct_prime_pair_witness_character :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      ¬ PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter :=
  ⟨PRCPrimeCalibrationForcesNoDistinctPrimePairWitnessCharacter_of_prime_identity_branch_uniformity,
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_distinct_prime_pair_witness_character⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro hnot
    by_contra hnoDistinct
    exact hnot
      (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_distinct_prime_pair_witness_character
        hnoDistinct)
  · intro hdistinct huniform
    exact (PRCPrimeCalibrationForcesNoDistinctPrimePairWitnessCharacter_of_prime_identity_branch_uniformity
      huniform) hdistinct

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_branch_uniformity :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  exact
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_distinct_prime_pair_witness_character.trans
      (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_distinct_prime_pair_witness_character.symm)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_identity_iff_two
    (hiff : PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityBranchUniform_of_identity_iff_two
    (hiff χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_branch_uniformity
    (huniform : PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_branch_uniform
    (huniform χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_iff_two :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_branch_uniformity,
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_identity_iff_two⟩

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_iff_two.trans
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_iff_identity_forces_two

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_forces_two :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_branch_uniformity.trans
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_forces_two

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter := by
  constructor
  · intro hnot
    exact PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_iff_distinct_prime_pair_witness_character.mp
      (fun huniform =>
        hnot
          (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_forces_two.mp
            huniform))
  · intro hdistinct hforces
    exact
      (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_iff_distinct_prime_pair_witness_character.mpr
        hdistinct)
        (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_forces_two.mpr
          hforces)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_two_prime_mixed_character :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness.trans
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_mixed_character

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_mixed_character :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness.trans
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_non_two_mixed_character

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_composite_defect_character :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness.trans
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_defect_character

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_composite_cost_defect_character :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness.trans
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_cost_defect_character

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_mixed_composite_cost_consistency :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness.trans
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_mixed_composite_cost_consistency

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_mixed_composite_cost_consistency :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_forces_two.trans
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_mixed_composite_cost_consistency

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_non_two_mixed_character :
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter :=
  PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_mixed_composite_cost_consistency.symm.trans
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_non_two_mixed_character

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_iff_non_two_mixed_character :
    ¬ PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter := by
  constructor
  · intro hnot
    by_contra hnoMixed
    exact hnot
      (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_non_two_mixed_character.mpr
        hnoMixed)
  · intro hmixed htarget
    exact
      (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_non_two_mixed_character.mp
        htarget) hmixed

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_mixed_composite_cost_consistency
    (hconsistency :
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget) :
    ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter := by
  intro htwist
  exact
    (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_non_two_mixed_character.mp
      hconsistency)
      (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
        htwist)

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter :=
  PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_mixed_composite_cost_consistency
    (PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_mixed_composite_cost_consistency.mp
      hforces)

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter :=
  PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_mixed_composite_cost_consistency
    (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_mixed_composite_cost_consistency.mp
      hpair)

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_two_adic_axis_twist
    (htwist :
      PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    ¬ PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget := by
  intro hconsistency
  exact
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_mixed_composite_cost_consistency
      hconsistency) htwist

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_two_adic_axis_twist
    (htwist :
      PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget := by
  intro hforces
  exact
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_identity_forces_two
      hforces) htwist

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_two_adic_axis_twist
    (htwist :
      PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget := by
  intro hpair
  exact
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_pair_product_cost_consistency
      hpair) htwist

theorem PRCTwoAdicAxisTwistRatioCharacter_absurd_of_mixed_composite_cost_consistency
    (hconsistency :
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget) :
    ¬ PRCTwoAdicAxisTwistRatioCharacter :=
  PRCTwoAdicAxisTwistRatioCharacter_absurd_of_no_calibrated_twist
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_mixed_composite_cost_consistency
      hconsistency)

theorem PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    ¬ PRCTwoAdicAxisTwistRatioCharacter :=
  PRCTwoAdicAxisTwistRatioCharacter_absurd_of_no_calibrated_twist
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_identity_forces_two
      hforces)

theorem PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    ¬ PRCTwoAdicAxisTwistRatioCharacter :=
  PRCTwoAdicAxisTwistRatioCharacter_absurd_of_no_calibrated_twist
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_pair_product_cost_consistency
      hpair)

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_ratio_character_axis_twist
    (htwist :
      PRCTwoAdicAxisTwistRatioCharacter) :
    ¬ PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget := by
  exact
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_two_adic_axis_twist
      (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
        htwist)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_ratio_character_axis_twist
    (htwist :
      PRCTwoAdicAxisTwistRatioCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget := by
  exact
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_two_adic_axis_twist
      (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
        htwist)

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_ratio_character_axis_twist
    (htwist :
      PRCTwoAdicAxisTwistRatioCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget := by
  exact
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_two_adic_axis_twist
      (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
        htwist)

theorem twoThreePrimeMixedDirection_not_crossEq_composite :
    ¬ RatioOrbit.crossEq twoThreePrimeMixedDirection
      twoThreePrimeCompositeDirection := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  rw [twoThreePrimeMixedDirection_toRat,
    twoThreePrimeCompositeDirection_toRat] at h
  norm_num at h

theorem twoThreePrimeMixedDirection_not_crossEq_composite_recip :
    ¬ RatioOrbit.crossEq twoThreePrimeMixedDirection
      (RatioOrbit.recip twoThreePrimeCompositeDirection) := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  rw [twoThreePrimeMixedDirection_toRat, RatioOrbit.recip_toRat,
    twoThreePrimeCompositeDirection_toRat] at h
  norm_num at h

theorem PRCCharacterTwoAdicAxisTwist_two_three_mixed_image
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (htwist : PRCCharacterTwoAdicAxisTwist χ) :
    RatioOrbit.crossEq (χ twoThreePrimeCompositeDirection)
      twoThreePrimeMixedDirection := by
  have hthreeId :
      RatioOrbit.crossEq (χ threePrimeDirection) threePrimeDirection := by
    simpa [threePrimeDirection] using
      htwist.2 threeOrbit threeOrbit_primeOrbit threeOrbit_ne_twoOrbit
  exact
    RatioOrbit.crossEq_trans
      (by
        simpa [twoThreePrimeCompositeDirection] using
          hχ.multiplicative twoPrimeDirection threePrimeDirection)
      (by
        simpa [twoThreePrimeMixedDirection] using
          ratioOrbit_mul_congr htwist.1 hthreeId)

theorem PRCCharacterTwoAdicAxisTwist_two_three_local_orientation_absurd
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (htwist : PRCCharacterTwoAdicAxisTwist χ) :
    ¬ PRCCharacterTwoThreeCompositeLocalOrientation χ := by
  intro hlocal
  have himage :=
    PRCCharacterTwoAdicAxisTwist_two_three_mixed_image hχ htwist
  rcases hlocal with hidentity | hreciprocal
  · exact twoThreePrimeMixedDirection_not_crossEq_composite
      (RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm himage) hidentity)
  · exact twoThreePrimeMixedDirection_not_crossEq_composite_recip
      (RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm himage) hreciprocal)

theorem PRCTwoAdicAxisTwistRatioCharacter_forces_two_three_local_orientation_failure
    (htwist : PRCTwoAdicAxisTwistRatioCharacter) :
    ∃ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ ∧
        PRCCharacterTwoAdicAxisTwist χ ∧
          ¬ PRCCharacterTwoThreeCompositeLocalOrientation χ := by
  rcases htwist with ⟨χ, hχ, hbranch⟩
  exact ⟨χ, hχ, hbranch,
    PRCCharacterTwoAdicAxisTwist_two_three_local_orientation_absurd hχ hbranch⟩

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_of_ratio_character_axis_twist
    (htwist : PRCTwoAdicAxisTwistRatioCharacter) :
    PRCTwoThreeCompositeLocalOrientationFailureCharacter :=
  PRCTwoAdicAxisTwistRatioCharacter_forces_two_three_local_orientation_failure
    htwist

theorem PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    PRCTwoAdicAxisTwistRatioCharacter := by
  rcases hfail with ⟨χ, hχ, hbranch, _hnotLocal⟩
  exact ⟨χ, hχ, hbranch⟩

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_ratio_character_axis_twist :
    PRCTwoThreeCompositeLocalOrientationFailureCharacter ↔
      PRCTwoAdicAxisTwistRatioCharacter :=
  ⟨PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character,
    PRCTwoThreeCompositeLocalOrientationFailureCharacter_of_ratio_character_axis_twist⟩

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_calibrated_two_adic_axis_twist :
    PRCTwoThreeCompositeLocalOrientationFailureCharacter ↔
      PRCPrimeCalibratedTwoAdicAxisTwistCharacter :=
  PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_ratio_character_axis_twist.trans
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter_iff_ratio_character_axis_twist.symm

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_ratio_character_axis_twist
    (hno : ¬ PRCTwoAdicAxisTwistRatioCharacter) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget := by
  intro χ hχ hbranch
  exfalso
  exact hno ⟨χ, hχ, hbranch⟩

theorem PRCTwoAdicAxisTwistRatioCharacter_absurd_of_two_three_local_orientation_target
    (htarget :
      PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget) :
    ¬ PRCTwoAdicAxisTwistRatioCharacter := by
  intro htwist
  rcases htwist with ⟨χ, hχ, hbranch⟩
  exact
    (PRCCharacterTwoAdicAxisTwist_two_three_local_orientation_absurd hχ hbranch)
      (htarget χ hχ hbranch)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCTwoAdicAxisTwistRatioCharacter :=
  ⟨PRCTwoAdicAxisTwistRatioCharacter_absurd_of_two_three_local_orientation_target,
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_ratio_character_axis_twist⟩

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_two_three_local_orientation_target
    (htarget :
      PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter := by
  intro hfail
  exact
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_two_three_local_orientation_target
      htarget)
      (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
        hfail)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist.trans
    (not_congr
      PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_ratio_character_axis_twist.symm)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_calibrated_two_adic_axis_twist :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character.trans
    (not_congr
      PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_calibrated_two_adic_axis_twist)

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_two_three_local_orientation_target
    (htarget :
      PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget) :
    ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_calibrated_two_adic_axis_twist.mp
    htarget

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_failure_character
    (hno : ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character.mpr
    hno

/-- Closed certificate for the exact `2*3` two-adic fork. It packages the
constructive branch (`failure` / `ratio twist` / `calibrated twist`) and the
positive branch (local orientation as the negation of each equivalent witness)
under one name, so downstream certificate wiring does not have to repeat the
equivalence chain. -/
structure PRCTwoThreeCompositeLocalForkCertificate : Prop where
  failure_iff_ratio_character_axis_twist :
    PRCTwoThreeCompositeLocalOrientationFailureCharacter ↔
      PRCTwoAdicAxisTwistRatioCharacter
  calibrated_two_adic_axis_twist_iff_ratio_character_axis_twist :
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter ↔
      PRCTwoAdicAxisTwistRatioCharacter
  failure_iff_calibrated_two_adic_axis_twist :
    PRCTwoThreeCompositeLocalOrientationFailureCharacter ↔
      PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  target_iff_no_ratio_character_axis_twist :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCTwoAdicAxisTwistRatioCharacter
  target_iff_no_failure_character :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter
  target_iff_no_calibrated_two_adic_axis_twist :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  target_excludes_calibrated_two_adic_axis_twist :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget →
      ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  no_failure_character_forces_target :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  mixed_composite_cost_consistency_excludes_failure_character :
    PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_identity_forces_two_excludes_failure_character :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_pair_product_cost_consistency_excludes_failure_character :
    PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter

def prcTwoThreeCompositeLocalForkCertificate :
    PRCTwoThreeCompositeLocalForkCertificate where
  failure_iff_ratio_character_axis_twist :=
    PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_ratio_character_axis_twist
  calibrated_two_adic_axis_twist_iff_ratio_character_axis_twist :=
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter_iff_ratio_character_axis_twist
  failure_iff_calibrated_two_adic_axis_twist :=
    PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_calibrated_two_adic_axis_twist
  target_iff_no_ratio_character_axis_twist :=
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist
  target_iff_no_failure_character :=
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character
  target_iff_no_calibrated_two_adic_axis_twist :=
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_calibrated_two_adic_axis_twist
  target_excludes_calibrated_two_adic_axis_twist :=
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_two_three_local_orientation_target
  no_failure_character_forces_target :=
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_failure_character
  mixed_composite_cost_consistency_excludes_failure_character := by
    intro hconsistency hfail
    exact
      (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_mixed_composite_cost_consistency
        hconsistency)
        (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
          hfail)
  prime_identity_forces_two_excludes_failure_character := by
    intro hforces hfail
    exact
      (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_forces_two
        hforces)
        (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
          hfail)
  prime_pair_product_cost_consistency_excludes_failure_character := by
    intro hpair hfail
    exact
      (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_pair_product_cost_consistency
        hpair)
        (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
          hfail)

theorem PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    PRCPrimeCalibratedTwoAdicAxisTwistCharacter :=
  PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
    (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter :=
  PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter :=
  PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed
    (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter :=
  PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_composite_defect
    (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    ¬ PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget :=
  PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_ratio_character_axis_twist
    (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_ratio_character_axis_twist
    (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_two_three_local_orientation_failure_character
    (hfail : PRCTwoThreeCompositeLocalOrientationFailureCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget :=
  PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_ratio_character_axis_twist
    (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_calibrated_two_adic_axis_twist
    (hno : ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter := by
  intro hfail
  exact hno
    (PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_mixed_character
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter := by
  intro hfail
  exact hno
    (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_composite_defect_character
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter := by
  intro hfail
  exact hno
    (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_composite_cost_defect_character
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter := by
  intro hfail
  exact hno
    (PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_two_three_local_orientation_failure_character
      hfail)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_calibrated_two_adic_axis_twist
    (hno : ¬ PRCPrimeCalibratedTwoAdicAxisTwistCharacter) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character.mpr
    (PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_calibrated_two_adic_axis_twist
      hno)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_non_two_mixed_character
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character.mpr
    (PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_mixed_character
      hno)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_non_two_composite_defect_character
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character.mpr
    (PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_composite_defect_character
      hno)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_non_two_composite_cost_defect_character
    (hno :
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character.mpr
    (PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_composite_cost_defect_character
      hno)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_mixed_composite_cost_consistency
    (hconsistency :
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist.mpr
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_mixed_composite_cost_consistency
      hconsistency)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist.mpr
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_forces_two
      hforces)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist.mpr
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_pair_product_cost_consistency
      hpair)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_mixed_composite_cost_consistency
    (hconsistency :
      PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter :=
  PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_two_three_local_orientation_target
    (PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_mixed_composite_cost_consistency
      hconsistency)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_prime_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter :=
  PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_two_three_local_orientation_target
    (PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_identity_forces_two
      hforces)

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter :=
  PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_two_three_local_orientation_target
    (PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_pair_product_cost_consistency
      hpair)

theorem PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_branch_uniformity
    (huniform :
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    ¬ PRCTwoAdicAxisTwistRatioCharacter := by
  intro htwist
  rcases htwist with ⟨χ, hχ, haxis⟩
  have hprime : PRCCharacterPrimeDirectionCalibrated χ :=
    PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist haxis
  have hthreeId :
      RatioOrbit.crossEq (χ threePrimeDirection) threePrimeDirection := by
    simpa [threePrimeDirection] using
      haxis.2 threeOrbit threeOrbit_primeOrbit threeOrbit_ne_twoOrbit
  have htwoId :
      RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection :=
    huniform χ hχ hprime threeOrbit threeOrbit_primeOrbit
      twoOrbit twoOrbit_primeOrbit hthreeId
  have hself :
      RatioOrbit.crossEq twoPrimeDirection
        (RatioOrbit.recip twoPrimeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) haxis.1
  exact primeDirection_not_crossEq_recip twoOrbit twoOrbit_primeOrbit hself

theorem PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_prime_identity_branch_uniformity
    (huniform :
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    ¬ PRCTwoThreeCompositeLocalOrientationFailureCharacter := by
  intro hfail
  exact
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_branch_uniformity
      huniform)
      (PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
        hfail)

theorem PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_identity_branch_uniformity
    (huniform :
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget) :
    PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget :=
  PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_ratio_character_axis_twist
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_branch_uniformity
      huniform)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_of_non_two_mixed_character
    (hmix :
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro huniform
  exact
    (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_distinct_prime_pair_witness_character.mp
      huniform)
      (PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter_of_non_two_mixed
        hmix)

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_of_ratio_character_axis_twist
    (htwist :
      PRCTwoAdicAxisTwistRatioCharacter) :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget := by
  intro huniform
  exact
    (PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_branch_uniformity
      huniform) htwist

theorem PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_of_ratio_character_axis_twist
    PRCTwoAdicAxisTwistRatioCharacter_constructed

theorem PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget := by
  intro hpair
  exact PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_refuted
    (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_branch_uniformity.mp
      hpair)

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget := by
  intro hconsistency
  exact PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_refuted
    (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_mixed_composite_cost_consistency.mpr
      hconsistency)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_refuted
    (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_forces_two.mpr
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_iff_identity_forces_two.mp
      htarget)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_refuted
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_mixed_composite_cost_consistency.mp
      htarget)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_refuted
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_witness.mp
      htarget)

theorem PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_refuted
    (PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_iff_prime_identity_iff_two.mp
      htarget)

theorem PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_refuted
    (PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_iff_two_prime_branch_controls.mp
      htarget)

theorem PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_refuted
    (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_coherent_prime_orientation.mp
      htarget)

theorem PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_refuted
    (PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_orientation.mpr
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_trace_coherence.mpr
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_trace_transport.mpr
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_common_trace_extension.mpr
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_canonical_add_trace.mpr
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_comparable_trace.mpr
      htarget)

theorem twoAdicAxisTwistCharacter_not_prime_pair_product_cost_consistent :
    ¬ PRCCharacterPrimePairProductCostConsistent
      twoAdicAxisTwistCharacter := by
  intro hconsistent
  have hcost :
      RatioOrbit.crossEq
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) := by
    simpa [twoThreePrimeCompositeDirection, twoPrimeDirection,
      threePrimeDirection] using
      hconsistent twoOrbit twoOrbit_primeOrbit
        threeOrbit threeOrbit_primeOrbit
  have himage :
      RatioOrbit.crossEq
        (twoAdicAxisTwistCharacter twoThreePrimeCompositeDirection)
        twoThreePrimeMixedDirection :=
    PRCCharacterTwoAdicAxisTwist_two_three_mixed_image
      twoAdicAxisTwistCharacter_ratio_character
      twoAdicAxisTwistCharacter_branch
  have hcostImage :
      RatioOrbit.crossEq
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeMixedDirection) := by
    unfold costFromCharacter
    exact onRatioOrbit_congr himage
  exact
    two_prime_composite_mixed_image_jcost_mismatch
      threeOrbit threeOrbit_primeOrbit
      (by
        simpa [twoThreePrimeMixedDirection, twoThreePrimeCompositeDirection,
          threePrimeDirection] using
          RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hcostImage) hcost)

theorem twoAdicAxisTwistCharacter_not_admissible :
    ¬ PRCAdmissibleRatioCharacter twoAdicAxisTwistCharacter := by
  intro hadm
  exact twoAdicAxisTwistCharacter_not_prime_pair_product_cost_consistent
    hadm.prime_pair_product_cost

theorem costFromCharacter_reciprocal_congr
    (χ : RatioOrbit → RatioOrbit) (hχ : PRCRatioCharacter χ)
    (q : RatioOrbit) :
    RatioOrbit.crossEq (costFromCharacter χ q)
      (costFromCharacter χ (RatioOrbit.recip q)) := by
  unfold costFromCharacter
  exact RatioOrbit.crossEq_trans
    (reciprocal_symmetric (χ q))
    (RatioOrbit.crossEq_symm (onRatioOrbit_congr (hχ.reciprocal q)))

theorem costFromCharacter_normalized_congr
    (χ : RatioOrbit → RatioOrbit) (hχ : PRCRatioCharacter χ)
    (q : RatioOrbit) :
    RatioOrbit.crossEq (costFromCharacter χ q)
      (costFromCharacter χ (DistinctionNat.normalizeRatio q)) := by
  unfold costFromCharacter
  exact onRatioOrbit_congr (hχ.normalized_invariant q)

theorem costFromCharacter_mul_congr
    (χ : RatioOrbit → RatioOrbit) (hχ : PRCRatioCharacter χ)
    (x y : RatioOrbit) :
    RatioOrbit.crossEq (costFromCharacter χ (RatioOrbit.mul x y))
      (onRatioOrbit (RatioOrbit.mul (χ x) (χ y))) := by
  unfold costFromCharacter
  exact onRatioOrbit_congr (hχ.multiplicative x y)

theorem costFromCharacter_div_congr
    (χ : RatioOrbit → RatioOrbit) (hχ : PRCRatioCharacter χ)
    (x y : RatioOrbit) :
    RatioOrbit.crossEq (costFromCharacter χ (div x y))
      (onRatioOrbit (div (χ x) (χ y))) := by
  unfold costFromCharacter div
  exact onRatioOrbit_congr
    (RatioOrbit.crossEq_trans
      (hχ.multiplicative x (RatioOrbit.recip y))
      (ratioOrbit_mul_congr (RatioOrbit.crossEq_refl (χ x))
        (hχ.reciprocal y)))

theorem costFromCharacter_canonical_rcl
    (χ : RatioOrbit → RatioOrbit) (hχ : PRCRatioCharacter χ)
    {x y : RatioOrbit} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    RatioOrbit.crossEq
      (RatioOrbit.add
        (costFromCharacter χ (RatioOrbit.mul x y))
        (costFromCharacter χ (div x y)))
      (RatioOrbit.add
        (RatioOrbit.add
          (RatioOrbit.mul two
            (RatioOrbit.mul (costFromCharacter χ x)
              (costFromCharacter χ y)))
          (RatioOrbit.mul two (costFromCharacter χ x)))
        (RatioOrbit.mul two (costFromCharacter χ y))) := by
  let X := χ x
  let Y := χ y
  have hX : X.toRat ≠ 0 := by
    exact hχ.nonzero_preserving hx
  have hY : Y.toRat ≠ 0 := by
    exact hχ.nonzero_preserving hy
  have hcanon :
      RatioOrbit.crossEq
        (RatioOrbit.add (onRatioOrbit (RatioOrbit.mul X Y))
          (onRatioOrbit (div X Y)))
        (RatioOrbit.add
          (RatioOrbit.add
            (RatioOrbit.mul two
              (RatioOrbit.mul (onRatioOrbit X) (onRatioOrbit Y)))
            (RatioOrbit.mul two (onRatioOrbit X)))
          (RatioOrbit.mul two (onRatioOrbit Y))) :=
    canonical_rcl_surface hX hY
  have hleft :
      RatioOrbit.crossEq
        (RatioOrbit.add
          (costFromCharacter χ (RatioOrbit.mul x y))
          (costFromCharacter χ (div x y)))
        (RatioOrbit.add (onRatioOrbit (RatioOrbit.mul X Y))
          (onRatioOrbit (div X Y))) := by
    exact ratioOrbit_add_congr
      (costFromCharacter_mul_congr χ hχ x y)
      (costFromCharacter_div_congr χ hχ x y)
  have hright :
      RatioOrbit.crossEq
        (RatioOrbit.add
          (RatioOrbit.add
            (RatioOrbit.mul two
              (RatioOrbit.mul (onRatioOrbit X) (onRatioOrbit Y)))
            (RatioOrbit.mul two (onRatioOrbit X)))
          (RatioOrbit.mul two (onRatioOrbit Y)))
        (RatioOrbit.add
          (RatioOrbit.add
            (RatioOrbit.mul two
              (RatioOrbit.mul (costFromCharacter χ x)
                (costFromCharacter χ y)))
            (RatioOrbit.mul two (costFromCharacter χ x)))
          (RatioOrbit.mul two (costFromCharacter χ y))) := by
    unfold costFromCharacter X Y
    exact RatioOrbit.crossEq_refl _
  exact RatioOrbit.crossEq_trans hleft
    (RatioOrbit.crossEq_trans hcanon hright)

/-- Exact remaining construction target for refuting the admissibility-upgrade
route: find an exact-unit-zero native cost cross-equivalent to the two-adic
generated character cost. The generated cost has the right quotient behavior;
the only delicate point is satisfying the `PRCNativeCostHypotheses` interface
whose `unit_zero` field is definitional equality, not cross-equivalence. -/
def PRCTwoAdicAxisTwistGeneratedCostNativeHypothesesTarget : Prop :=
  ∃ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F ∧
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q)
          (costFromCharacter twoAdicAxisTwistCharacter q)

noncomputable def twoAdicGeneratedNativeCost (q : RatioOrbit) : RatioOrbit :=
  by
    classical
    exact if q = RatioOrbit.one then RatioOrbit.zero
      else costFromCharacter twoAdicAxisTwistCharacter q

theorem twoAdicGeneratedNativeCost_crossEq_generated (q : RatioOrbit) :
    RatioOrbit.crossEq (twoAdicGeneratedNativeCost q)
      (costFromCharacter twoAdicAxisTwistCharacter q) := by
  classical
  by_cases hq : q = RatioOrbit.one
  · subst q
    rw [twoAdicGeneratedNativeCost, if_pos rfl]
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat,
      costFromCharacter_toRat, twoAdicAxisTwistCharacter_toRat,
      RatioOrbit.one_toRat]
    rw [twoAdicTwistRat_one]
    norm_num
  · rw [twoAdicGeneratedNativeCost, if_neg hq]
    exact RatioOrbit.crossEq_refl _

theorem twoAdicGeneratedNativeCost_hypotheses :
    PRCNativeCostHypotheses twoAdicGeneratedNativeCost where
  reciprocal := by
    intro q
    exact RatioOrbit.crossEq_trans
      (twoAdicGeneratedNativeCost_crossEq_generated q)
      (RatioOrbit.crossEq_trans
        (costFromCharacter_reciprocal_congr
          twoAdicAxisTwistCharacter
          twoAdicAxisTwistCharacter_ratio_character q)
        (RatioOrbit.crossEq_symm
          (twoAdicGeneratedNativeCost_crossEq_generated
            (RatioOrbit.recip q))))
  normalized_invariant := by
    intro q
    exact RatioOrbit.crossEq_trans
      (twoAdicGeneratedNativeCost_crossEq_generated q)
      (RatioOrbit.crossEq_trans
        (costFromCharacter_normalized_congr
          twoAdicAxisTwistCharacter
          twoAdicAxisTwistCharacter_ratio_character q)
        (RatioOrbit.crossEq_symm
          (twoAdicGeneratedNativeCost_crossEq_generated
            (DistinctionNat.normalizeRatio q))))
  canonical_rcl := by
    intro x y hx hy
    let C := costFromCharacter twoAdicAxisTwistCharacter
    have hC :
        RatioOrbit.crossEq
          (RatioOrbit.add (C (RatioOrbit.mul x y)) (C (div x y)))
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two (RatioOrbit.mul (C x) (C y)))
              (RatioOrbit.mul two (C x)))
            (RatioOrbit.mul two (C y))) :=
      costFromCharacter_canonical_rcl twoAdicAxisTwistCharacter
        twoAdicAxisTwistCharacter_ratio_character hx hy
    have hleft :
        RatioOrbit.crossEq
          (RatioOrbit.add
            (twoAdicGeneratedNativeCost (RatioOrbit.mul x y))
            (twoAdicGeneratedNativeCost (div x y)))
          (RatioOrbit.add (C (RatioOrbit.mul x y)) (C (div x y))) := by
      exact ratioOrbit_add_congr
        (twoAdicGeneratedNativeCost_crossEq_generated (RatioOrbit.mul x y))
        (twoAdicGeneratedNativeCost_crossEq_generated (div x y))
    have hxF := twoAdicGeneratedNativeCost_crossEq_generated x
    have hyF := twoAdicGeneratedNativeCost_crossEq_generated y
    have hmulInner :
        RatioOrbit.crossEq
          (RatioOrbit.mul (C x) (C y))
          (RatioOrbit.mul (twoAdicGeneratedNativeCost x)
            (twoAdicGeneratedNativeCost y)) :=
      ratioOrbit_mul_congr
        (RatioOrbit.crossEq_symm hxF)
        (RatioOrbit.crossEq_symm hyF)
    have hterm₁ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (RatioOrbit.mul (C x) (C y)))
          (RatioOrbit.mul two
            (RatioOrbit.mul (twoAdicGeneratedNativeCost x)
              (twoAdicGeneratedNativeCost y))) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two) hmulInner
    have hterm₂ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (C x))
          (RatioOrbit.mul two (twoAdicGeneratedNativeCost x)) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two)
        (RatioOrbit.crossEq_symm hxF)
    have hterm₃ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (C y))
          (RatioOrbit.mul two (twoAdicGeneratedNativeCost y)) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two)
        (RatioOrbit.crossEq_symm hyF)
    have hright :
        RatioOrbit.crossEq
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two (RatioOrbit.mul (C x) (C y)))
              (RatioOrbit.mul two (C x)))
            (RatioOrbit.mul two (C y)))
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two
                (RatioOrbit.mul (twoAdicGeneratedNativeCost x)
                  (twoAdicGeneratedNativeCost y)))
              (RatioOrbit.mul two (twoAdicGeneratedNativeCost x)))
            (RatioOrbit.mul two (twoAdicGeneratedNativeCost y))) :=
      ratioOrbit_add_congr (ratioOrbit_add_congr hterm₁ hterm₂) hterm₃
    exact RatioOrbit.crossEq_trans hleft
      (RatioOrbit.crossEq_trans hC hright)
  unit_zero := by
    classical
    rw [twoAdicGeneratedNativeCost, if_pos rfl]
  two_calibrated := by
    have hFtwo := twoAdicGeneratedNativeCost_crossEq_generated two
    have htwistTwo :
        RatioOrbit.crossEq (twoAdicAxisTwistCharacter two)
          (RatioOrbit.recip two) := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, twoAdicAxisTwistCharacter_toRat,
        RatioOrbit.recip_toRat, two_toRat]
      rw [twoAdicTwistRat_two]
    have hcost :
        RatioOrbit.crossEq
          (costFromCharacter twoAdicAxisTwistCharacter two)
          (onRatioOrbit two) := by
      unfold costFromCharacter
      exact RatioOrbit.crossEq_trans
        (onRatioOrbit_congr htwistTwo)
        (RatioOrbit.crossEq_symm (reciprocal_symmetric two))
    exact RatioOrbit.crossEq_trans hFtwo hcost

theorem PRCTwoAdicAxisTwistGeneratedCostNativeHypothesesTarget_constructed :
    PRCTwoAdicAxisTwistGeneratedCostNativeHypothesesTarget :=
  ⟨twoAdicGeneratedNativeCost,
    twoAdicGeneratedNativeCost_hypotheses,
    twoAdicGeneratedNativeCost_crossEq_generated⟩

theorem PRCNoAdmissibleFactorForTwoAdicAxisTwistGeneratedCost
    {F : RatioOrbit → RatioOrbit}
    (hFtwist :
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q)
          (costFromCharacter twoAdicAxisTwistCharacter q)) :
    ¬ ∃ ψ : RatioOrbit → RatioOrbit,
      PRCAdmissibleRatioCharacter ψ ∧
        ∀ q : RatioOrbit,
          RatioOrbit.crossEq (F q) (costFromCharacter ψ q) := by
  intro hψ
  rcases hψ with ⟨ψ, hadm, hFψ⟩
  have hψcost :
      RatioOrbit.crossEq
        (costFromCharacter ψ twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) := by
    simpa [twoThreePrimeCompositeDirection, twoPrimeDirection,
      threePrimeDirection] using
      hadm.prime_pair_product_cost twoOrbit twoOrbit_primeOrbit
        threeOrbit threeOrbit_primeOrbit
  have himage :
      RatioOrbit.crossEq
        (twoAdicAxisTwistCharacter twoThreePrimeCompositeDirection)
        twoThreePrimeMixedDirection :=
    PRCCharacterTwoAdicAxisTwist_two_three_mixed_image
      twoAdicAxisTwistCharacter_ratio_character
      twoAdicAxisTwistCharacter_branch
  have htwistCost :
      RatioOrbit.crossEq
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeMixedDirection) := by
    unfold costFromCharacter
    exact onRatioOrbit_congr himage
  have htwistCanonical :
      RatioOrbit.crossEq
        (onRatioOrbit twoThreePrimeMixedDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwistCost)
      (RatioOrbit.crossEq_trans
        (RatioOrbit.crossEq_symm
          (hFtwist twoThreePrimeCompositeDirection))
        (RatioOrbit.crossEq_trans
          (hFψ twoThreePrimeCompositeDirection)
          hψcost))
  exact
    two_prime_composite_mixed_image_jcost_mismatch
      threeOrbit threeOrbit_primeOrbit
      (by
        simpa [twoThreePrimeMixedDirection, twoThreePrimeCompositeDirection,
          threePrimeDirection] using htwistCanonical)

theorem PRCNativeCostFactorizationAdmissibilityUpgradeTarget_not_of_two_adic_axis_twist_generated_cost
    (htwistCost :
      PRCTwoAdicAxisTwistGeneratedCostNativeHypothesesTarget) :
    ¬ PRCNativeCostFactorizationAdmissibilityUpgradeTarget := by
  intro hupgrade
  rcases htwistCost with ⟨F, hF, hFtwist⟩
  exact
    PRCNoAdmissibleFactorForTwoAdicAxisTwistGeneratedCost hFtwist
      (hupgrade F hF twoAdicAxisTwistCharacter
        twoAdicAxisTwistCharacter_ratio_character hFtwist)

theorem PRCNativeCostFactorizationAdmissibilityUpgradeTarget_refuted :
    ¬ PRCNativeCostFactorizationAdmissibilityUpgradeTarget :=
  PRCNativeCostFactorizationAdmissibilityUpgradeTarget_not_of_two_adic_axis_twist_generated_cost
    PRCTwoAdicAxisTwistGeneratedCostNativeHypothesesTarget_constructed

theorem PRCNativeCostUniquenessTarget_refuted :
    ¬ PRCNativeCostUniquenessTarget := by
  intro hunique
  have hcanonical :
      RatioOrbit.crossEq
        (twoAdicGeneratedNativeCost twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) :=
    hunique twoAdicGeneratedNativeCost
      twoAdicGeneratedNativeCost_hypotheses
      twoThreePrimeCompositeDirection
  have htwistGenerated :
      RatioOrbit.crossEq
        (twoAdicGeneratedNativeCost twoThreePrimeCompositeDirection)
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection) :=
    twoAdicGeneratedNativeCost_crossEq_generated
      twoThreePrimeCompositeDirection
  have himage :
      RatioOrbit.crossEq
        (twoAdicAxisTwistCharacter twoThreePrimeCompositeDirection)
        twoThreePrimeMixedDirection :=
    PRCCharacterTwoAdicAxisTwist_two_three_mixed_image
      twoAdicAxisTwistCharacter_ratio_character
      twoAdicAxisTwistCharacter_branch
  have htwistCost :
      RatioOrbit.crossEq
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeMixedDirection) := by
    unfold costFromCharacter
    exact onRatioOrbit_congr himage
  have hbad :
      RatioOrbit.crossEq
        (onRatioOrbit twoThreePrimeMixedDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwistCost)
      (RatioOrbit.crossEq_trans
        (RatioOrbit.crossEq_symm htwistGenerated)
        hcanonical)
  exact
    two_prime_composite_mixed_image_jcost_mismatch
      threeOrbit threeOrbit_primeOrbit
      (by
        simpa [twoThreePrimeMixedDirection, twoThreePrimeCompositeDirection,
          threePrimeDirection] using hbad)

/-- Cost-level repair for the native uniqueness hypotheses: a native cost must
already be canonical on products of native prime directions. This is the exact
surface where the two-adic generated cost slips through the older
`PRCNativeCostHypotheses`. -/
def PRCNativeCostPrimePairProductCalibrated
    (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
      RatioOrbit.crossEq
        (F (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))
        (onRatioOrbit
          (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))

/-- Strengthened native-cost interface after the two-adic no-go: keep the old
RCL/normalization/calibration fields, but add prime-pair product calibration at
the cost level. -/
structure PRCStrengthenedNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  native : PRCNativeCostHypotheses F
  prime_pair_product_cost :
    PRCNativeCostPrimePairProductCalibrated F

/-- Signed-unit repair for native costs: the cost must see the signed unit
`-1`, not only positive prime and prime-pair probes. -/
def PRCNativeCostSignedUnitCalibrated
    (F : RatioOrbit → RatioOrbit) : Prop :=
  RatioOrbit.crossEq (F negativeOneRatio) (onRatioOrbit negativeOneRatio)

/-- Signed repaired native-cost interface after the absolute-value no-go:
the pass-274 strengthened hypotheses plus direct calibration at the signed
unit. -/
structure PRCSignedStrengthenedNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  strengthened : PRCStrengthenedNativeCostHypotheses F
  signed_unit : PRCNativeCostSignedUnitCalibrated F

/-- Replacement target after pass 281: uniqueness is now asked only for native
costs that also calibrate the signed unit. -/
def PRCSignedStrengthenedNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSignedStrengthenedNativeCostHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Native cost-level all-prime calibration. Pass 283 refutes deriving this from
two calibration alone. -/
def PRCNativeCostPrimeDirectionCalibrated
    (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
    RatioOrbit.crossEq (F (primeDirection p hp))
      (onRatioOrbit (primeDirection p hp))

/-- Prime-signed repaired native-cost interface: signed strengthened hypotheses
plus direct all-prime calibration at the cost level. -/
structure PRCPrimeSignedStrengthenedNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  signed_strengthened : PRCSignedStrengthenedNativeCostHypotheses F
  prime_direction_cost : PRCNativeCostPrimeDirectionCalibrated F

/-- Zero-calibrated final native-cost interface for the character-factorization
route: the native cost has zero trace at the zero orbit, sees the signed unit,
and is calibrated on all native prime axes and prime-pair products. -/
structure PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  prime_signed : PRCPrimeSignedStrengthenedNativeCostHypotheses F
  zero_calibrated :
    PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

/-- Replacement uniqueness target after both no-go repairs: sign and every prime
axis are calibrated at the native-cost level. -/
def PRCPrimeSignedStrengthenedNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCPrimeSignedStrengthenedNativeCostHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Zero-calibrated replacement uniqueness target after the zero-flat and
absolute-value no-gos. -/
def PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Replacement target for the refuted old native uniqueness statement. -/
def PRCStrengthenedNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCStrengthenedNativeCostHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Strengthened factorization target: once the cost-level prime-pair field is
part of the native hypotheses, a factor character must be admissible. -/
def PRCStrengthenedNativeCostAdmissibleCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCStrengthenedNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCAdmissibleRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

theorem PRCStrengthenedNativeCostAdmissibleCharacterFactorizationTarget_of_character_factorization_and_two_calibration
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget) :
    PRCStrengthenedNativeCostAdmissibleCharacterFactorizationTarget := by
  intro F hF
  rcases hfactor F hF.native with ⟨χ, hχ, hFχ⟩
  have htwoCal :
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ two))
      hF.native.two_calibrated
  have hprime :
      PRCCharacterPrimeDirectionCalibrated χ :=
    htwo χ hχ htwoCal
  have hpair :
      PRCCharacterPrimePairProductCostConsistent χ := by
    intro p hp r hr
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm
        (hFχ (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))))
      (hF.prime_pair_product_cost p hp r hr)
  exact ⟨χ, ⟨hχ, hprime, hpair⟩, hFχ⟩

theorem PRCStrengthenedNativeCostUniquenessTarget_of_strengthened_admissible_factorization_and_rigidity
    (hfactor : PRCStrengthenedNativeCostAdmissibleCharacterFactorizationTarget)
    (hrigid : PRCNativeCostAdmissibleCharacterRigidityTarget) :
    PRCStrengthenedNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q) (hrigid χ hadm q)

theorem PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_rigidity
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hrigid : PRCNativeCostAdmissibleCharacterRigidityTarget) :
    PRCStrengthenedNativeCostUniquenessTarget :=
  PRCStrengthenedNativeCostUniquenessTarget_of_strengthened_admissible_factorization_and_rigidity
    (PRCStrengthenedNativeCostAdmissibleCharacterFactorizationTarget_of_character_factorization_and_two_calibration
      hfactor htwo)
    hrigid

theorem PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_global_orientation
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (horient : PRCAdmissibleCharacterGlobalOrientationTarget) :
    PRCStrengthenedNativeCostUniquenessTarget :=
  PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_rigidity
    hfactor htwo
    (PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_global_orientation
      horient)

theorem PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_prime_propagation
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hprop : PRCPrimeCalibrationPropagationTarget) :
    PRCStrengthenedNativeCostUniquenessTarget :=
  PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_rigidity
    hfactor htwo
    (PRCNativeCostAdmissibleCharacterRigidityTarget_of_prime_calibration_propagation
      hprop)

/-- Exact strengthened-hypothesis no-go target after the signed-unit analysis:
the absolute-value character generates a native cost satisfying the prime-pair
repair while erasing the signed unit. -/
def PRCAbsValueGeneratedCostStrengthenedNativeHypothesesTarget : Prop :=
  ∃ F : RatioOrbit → RatioOrbit,
    PRCStrengthenedNativeCostHypotheses F ∧
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q)
          (costFromCharacter absValueCharacter q)

noncomputable def absValueGeneratedNativeCost (q : RatioOrbit) : RatioOrbit :=
  by
    classical
    exact if q = RatioOrbit.one then RatioOrbit.zero
      else costFromCharacter absValueCharacter q

theorem absValueGeneratedNativeCost_crossEq_generated (q : RatioOrbit) :
    RatioOrbit.crossEq (absValueGeneratedNativeCost q)
      (costFromCharacter absValueCharacter q) := by
  classical
  by_cases hq : q = RatioOrbit.one
  · subst q
    rw [absValueGeneratedNativeCost, if_pos rfl]
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat,
      costFromCharacter_toRat, absValueCharacter_toRat, RatioOrbit.one_toRat]
    norm_num
  · rw [absValueGeneratedNativeCost, if_neg hq]
    exact RatioOrbit.crossEq_refl _

theorem absValueGeneratedNativeCost_native_hypotheses :
    PRCNativeCostHypotheses absValueGeneratedNativeCost where
  reciprocal := by
    intro q
    exact RatioOrbit.crossEq_trans
      (absValueGeneratedNativeCost_crossEq_generated q)
      (RatioOrbit.crossEq_trans
        (costFromCharacter_reciprocal_congr
          absValueCharacter
          absValueCharacter_ratio_character q)
        (RatioOrbit.crossEq_symm
          (absValueGeneratedNativeCost_crossEq_generated
            (RatioOrbit.recip q))))
  normalized_invariant := by
    intro q
    exact RatioOrbit.crossEq_trans
      (absValueGeneratedNativeCost_crossEq_generated q)
      (RatioOrbit.crossEq_trans
        (costFromCharacter_normalized_congr
          absValueCharacter
          absValueCharacter_ratio_character q)
        (RatioOrbit.crossEq_symm
          (absValueGeneratedNativeCost_crossEq_generated
            (DistinctionNat.normalizeRatio q))))
  canonical_rcl := by
    intro x y hx hy
    let C := costFromCharacter absValueCharacter
    have hC :
        RatioOrbit.crossEq
          (RatioOrbit.add (C (RatioOrbit.mul x y)) (C (div x y)))
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two (RatioOrbit.mul (C x) (C y)))
              (RatioOrbit.mul two (C x)))
            (RatioOrbit.mul two (C y))) :=
      costFromCharacter_canonical_rcl absValueCharacter
        absValueCharacter_ratio_character hx hy
    have hleft :
        RatioOrbit.crossEq
          (RatioOrbit.add
            (absValueGeneratedNativeCost (RatioOrbit.mul x y))
            (absValueGeneratedNativeCost (div x y)))
          (RatioOrbit.add (C (RatioOrbit.mul x y)) (C (div x y))) := by
      exact ratioOrbit_add_congr
        (absValueGeneratedNativeCost_crossEq_generated (RatioOrbit.mul x y))
        (absValueGeneratedNativeCost_crossEq_generated (div x y))
    have hxF := absValueGeneratedNativeCost_crossEq_generated x
    have hyF := absValueGeneratedNativeCost_crossEq_generated y
    have hmulInner :
        RatioOrbit.crossEq
          (RatioOrbit.mul (C x) (C y))
          (RatioOrbit.mul (absValueGeneratedNativeCost x)
            (absValueGeneratedNativeCost y)) :=
      ratioOrbit_mul_congr
        (RatioOrbit.crossEq_symm hxF)
        (RatioOrbit.crossEq_symm hyF)
    have hterm₁ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (RatioOrbit.mul (C x) (C y)))
          (RatioOrbit.mul two
            (RatioOrbit.mul (absValueGeneratedNativeCost x)
              (absValueGeneratedNativeCost y))) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two) hmulInner
    have hterm₂ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (C x))
          (RatioOrbit.mul two (absValueGeneratedNativeCost x)) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two)
        (RatioOrbit.crossEq_symm hxF)
    have hterm₃ :
        RatioOrbit.crossEq
          (RatioOrbit.mul two (C y))
          (RatioOrbit.mul two (absValueGeneratedNativeCost y)) :=
      ratioOrbit_mul_congr (RatioOrbit.crossEq_refl two)
        (RatioOrbit.crossEq_symm hyF)
    have hright :
        RatioOrbit.crossEq
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two (RatioOrbit.mul (C x) (C y)))
              (RatioOrbit.mul two (C x)))
            (RatioOrbit.mul two (C y)))
          (RatioOrbit.add
            (RatioOrbit.add
              (RatioOrbit.mul two
                (RatioOrbit.mul (absValueGeneratedNativeCost x)
                  (absValueGeneratedNativeCost y)))
              (RatioOrbit.mul two (absValueGeneratedNativeCost x)))
            (RatioOrbit.mul two (absValueGeneratedNativeCost y))) :=
      ratioOrbit_add_congr (ratioOrbit_add_congr hterm₁ hterm₂) hterm₃
    exact RatioOrbit.crossEq_trans hleft
      (RatioOrbit.crossEq_trans hC hright)
  unit_zero := by
    classical
    rw [absValueGeneratedNativeCost, if_pos rfl]
  two_calibrated := by
    have hFtwo := absValueGeneratedNativeCost_crossEq_generated two
    have hcost := absValueCharacter_prime_calibrated twoOrbit twoOrbit_primeOrbit
    simpa [twoPrimeDirection, primeDirection] using
      RatioOrbit.crossEq_trans hFtwo hcost

theorem absValueGeneratedNativeCost_prime_pair_product_cost :
    PRCNativeCostPrimePairProductCalibrated absValueGeneratedNativeCost := by
  intro p hp r hr
  exact RatioOrbit.crossEq_trans
    (absValueGeneratedNativeCost_crossEq_generated
      (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))
    (absValueCharacter_prime_pair_product_cost p hp r hr)

theorem absValueGeneratedNativeCost_prime_direction_cost :
    PRCNativeCostPrimeDirectionCalibrated absValueGeneratedNativeCost := by
  intro p hp
  exact RatioOrbit.crossEq_trans
    (absValueGeneratedNativeCost_crossEq_generated (primeDirection p hp))
    (absValueCharacter_prime_calibrated p hp)

theorem absValueGeneratedNativeCost_strengthened_hypotheses :
    PRCStrengthenedNativeCostHypotheses absValueGeneratedNativeCost where
  native := absValueGeneratedNativeCost_native_hypotheses
  prime_pair_product_cost := absValueGeneratedNativeCost_prime_pair_product_cost

theorem absValueGeneratedNativeCost_doubled_trace_zero_calibrated :
    PRCDoubledTraceZeroCalibrated
      (nativeCostDoubledTrace absValueGeneratedNativeCost) := by
  rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
    nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
    RatioOrbit.add_toRat, two_toRat, RatioOrbit.zero_toRat,
    RatioOrbit.one_toRat]
  rw [absValueGeneratedNativeCost, if_neg (by
    intro h
    have hrat := congrArg RatioOrbit.toRat h
    rw [RatioOrbit.zero_toRat, RatioOrbit.one_toRat] at hrat
    norm_num at hrat)]
  rw [costFromCharacter_toRat, absValueCharacter_toRat, RatioOrbit.zero_toRat]
  norm_num

theorem PRCAbsValueGeneratedCostStrengthenedNativeHypothesesTarget_constructed :
    PRCAbsValueGeneratedCostStrengthenedNativeHypothesesTarget :=
  ⟨absValueGeneratedNativeCost,
    absValueGeneratedNativeCost_strengthened_hypotheses,
    absValueGeneratedNativeCost_crossEq_generated⟩

theorem negativeOneRatio_ne_one :
    negativeOneRatio ≠ RatioOrbit.one := by
  intro h
  have hrat := congrArg RatioOrbit.toRat h
  rw [negativeOneRatio_toRat, RatioOrbit.one_toRat] at hrat
  norm_num at hrat

theorem absValueGeneratedNativeCost_negative_one_zero :
    RatioOrbit.crossEq (absValueGeneratedNativeCost negativeOneRatio)
      RatioOrbit.zero := by
  rw [absValueGeneratedNativeCost, if_neg negativeOneRatio_ne_one]
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat,
    absValueCharacter_toRat, negativeOneRatio_toRat, RatioOrbit.zero_toRat]
  norm_num

theorem onRatioOrbit_negativeOneRatio_toRat :
    (onRatioOrbit negativeOneRatio).toRat = -2 := by
  rw [onRatioOrbit_toRat, negativeOneRatio_toRat]
  norm_num

theorem absValueGeneratedNativeCost_negative_one_not_canonical :
    ¬ RatioOrbit.crossEq (absValueGeneratedNativeCost negativeOneRatio)
      (onRatioOrbit negativeOneRatio) := by
  intro h
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  have hzero :=
    (RatioOrbit.crossEq_iff_toRat_eq
      (absValueGeneratedNativeCost negativeOneRatio) RatioOrbit.zero).mp
      absValueGeneratedNativeCost_negative_one_zero
  rw [hzero, onRatioOrbit_negativeOneRatio_toRat] at h
  norm_num at h

theorem PRCStrengthenedNativeCostUniquenessTarget_refuted :
    ¬ PRCStrengthenedNativeCostUniquenessTarget := by
  intro huniq
  exact absValueGeneratedNativeCost_negative_one_not_canonical
    (huniq absValueGeneratedNativeCost
      absValueGeneratedNativeCost_strengthened_hypotheses negativeOneRatio)

theorem onRatioOrbit_signed_unit_calibrated :
    PRCNativeCostSignedUnitCalibrated onRatioOrbit :=
  RatioOrbit.crossEq_refl (onRatioOrbit negativeOneRatio)

theorem absValueGeneratedNativeCost_not_signed_unit_calibrated :
    ¬ PRCNativeCostSignedUnitCalibrated absValueGeneratedNativeCost :=
  absValueGeneratedNativeCost_negative_one_not_canonical

def PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
      PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F) →
        PRCNativeCostSignedUnitCalibrated F

theorem PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget_refuted :
    ¬ PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget := by
  intro htarget
  exact absValueGeneratedNativeCost_not_signed_unit_calibrated
    (htarget absValueGeneratedNativeCost
      absValueGeneratedNativeCost_native_hypotheses
      absValueGeneratedNativeCost_doubled_trace_zero_calibrated)

theorem absValueGeneratedNativeCost_not_signed_strengthened_hypotheses :
    ¬ PRCSignedStrengthenedNativeCostHypotheses absValueGeneratedNativeCost := by
  intro h
  exact absValueGeneratedNativeCost_not_signed_unit_calibrated h.signed_unit

theorem onRatioOrbit_prime_pair_product_calibrated :
    PRCNativeCostPrimePairProductCalibrated onRatioOrbit := by
  intro p hp r hr
  exact RatioOrbit.crossEq_refl
    (onRatioOrbit (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))

theorem twoAdicGeneratedNativeCost_not_prime_pair_product_calibrated :
    ¬ PRCNativeCostPrimePairProductCalibrated twoAdicGeneratedNativeCost := by
  intro hpair
  have hcanonical :
      RatioOrbit.crossEq
        (twoAdicGeneratedNativeCost twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) := by
    simpa [twoThreePrimeCompositeDirection, twoPrimeDirection,
      threePrimeDirection] using
      hpair twoOrbit twoOrbit_primeOrbit threeOrbit threeOrbit_primeOrbit
  have htwistGenerated :
      RatioOrbit.crossEq
        (twoAdicGeneratedNativeCost twoThreePrimeCompositeDirection)
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection) :=
    twoAdicGeneratedNativeCost_crossEq_generated
      twoThreePrimeCompositeDirection
  have himage :
      RatioOrbit.crossEq
        (twoAdicAxisTwistCharacter twoThreePrimeCompositeDirection)
        twoThreePrimeMixedDirection :=
    PRCCharacterTwoAdicAxisTwist_two_three_mixed_image
      twoAdicAxisTwistCharacter_ratio_character
      twoAdicAxisTwistCharacter_branch
  have htwistCost :
      RatioOrbit.crossEq
        (costFromCharacter twoAdicAxisTwistCharacter
          twoThreePrimeCompositeDirection)
        (onRatioOrbit twoThreePrimeMixedDirection) := by
    unfold costFromCharacter
    exact onRatioOrbit_congr himage
  have hbad :
      RatioOrbit.crossEq
        (onRatioOrbit twoThreePrimeMixedDirection)
        (onRatioOrbit twoThreePrimeCompositeDirection) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwistCost)
      (RatioOrbit.crossEq_trans
        (RatioOrbit.crossEq_symm htwistGenerated)
        hcanonical)
  exact
    two_prime_composite_mixed_image_jcost_mismatch
      threeOrbit threeOrbit_primeOrbit
      (by
        simpa [twoThreePrimeMixedDirection, twoThreePrimeCompositeDirection,
          threePrimeDirection] using hbad)

theorem twoAdicGeneratedNativeCost_not_strengthened_hypotheses :
    ¬ PRCStrengthenedNativeCostHypotheses twoAdicGeneratedNativeCost := by
  intro hstrong
  exact twoAdicGeneratedNativeCost_not_prime_pair_product_calibrated
    hstrong.prime_pair_product_cost

theorem PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_iff_non_two_composite_cost_defect_character :
    ¬ PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter := by
  constructor
  · intro hnot
    by_contra hnoDefect
    exact hnot
      (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_composite_cost_defect_character.mpr
        hnoDefect)
  · intro hdefect htarget
    exact
      (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_composite_cost_defect_character.mp
        htarget) hdefect

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_iff_non_two_composite_cost_defect_character :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter := by
  constructor
  · intro hnot
    by_contra hnoDefect
    exact hnot
      (PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_composite_cost_defect_character.mpr
        hnoDefect)
  · intro hdefect htarget
    exact
      (PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_composite_cost_defect_character.mp
        htarget) hdefect

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_prime_pair_product_cost_consistency
    (hpair :
      PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget :=
  PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_mixed_composite_cost_consistency_direct
    (PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_prime_pair_product_cost_consistency
      hpair)

theorem PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_identity_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget := by
  intro χ hχ hprime
  exact
    PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_twist_identity_forces_two
      (hforces
        (PRCCharacterReciprocalTwist χ)
        (PRCRatioCharacter.reciprocalTwist hχ)
        (PRCCharacterPrimeDirectionCalibrated.reciprocalTwist hprime))

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_prime_reciprocal_forces_two
    (hforces :
      PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget := by
  intro χ hχ hprime
  exact
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_reciprocal_twist_reciprocal_forces_two
      (hforces
        (PRCCharacterReciprocalTwist χ)
        (PRCRatioCharacter.reciprocalTwist hχ)
        (PRCCharacterPrimeDirectionCalibrated.reciprocalTwist hprime))

theorem PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_iff_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_prime_reciprocal_forces_two,
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_identity_forces_two⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces
    (hforces :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_two_prime_reciprocal_forces
    (hforces χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_two_prime_reciprocal_excludes
    (hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_local_excludes_prime_identity
    (PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved χ hχ hprime)
    (hexcl χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_two_prime_reciprocal_forces :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_two_prime_reciprocal_excludes,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_identity_forces_two
    (hidentity :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget :=
  PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_two_prime_reciprocal_excludes
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_identity_forces_two
      hidentity)

theorem PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_forces
    (hforces :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces
      hforces)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_iff_identity_forces_two :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_forces,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_identity_forces_two⟩

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_two_prime_reciprocal_forces
    (hforces :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget) :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget := by
  constructor
  · have hexcl :
        PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget :=
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces
        hforces
    have hidentity :
        PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
        hexcl
    exact
      PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_identity_forces_two
        hidentity
  · exact hforces

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_split
    (hsplit :
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget :=
  hsplit.2

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_iff_two_prime_reciprocal_forces :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_split,
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_two_prime_reciprocal_forces⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_trace_connected
    (htrace :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_trace_connected
    (htrace χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_forces
    (hforces :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget := by
  intro χ hχ hprime
  exact PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_forces
    (hforces χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_forces :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_trace_connected,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_forces⟩

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_identity_trace_connected
    (hidentity :
      PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget) :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget := by
  intro χ hχ hprime
  exact
    PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_reciprocal_twist_identity
      (hidentity (PRCCharacterReciprocalTwist χ)
        hχ.reciprocalTwist hprime.reciprocalTwist)

theorem PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_reciprocal_trace_connected
    (hreciprocal :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget) :
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget := by
  intro χ hχ hprime
  exact
    PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_reciprocal_twist_reciprocal
      (hreciprocal (PRCCharacterReciprocalTwist χ)
        hχ.reciprocalTwist hprime.reciprocalTwist)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_identity_trace_connected :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget :=
  ⟨PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_reciprocal_trace_connected,
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_identity_trace_connected⟩

theorem PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_prime_identity_trace_transport
    (htransport :
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget) :
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget := by
  intro χ hχ hprime
  exact
    PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_prime_identity_trace_connected
      (htransport χ hχ hprime)

theorem PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_two_prime_identity_trace_connected
    (htwo :
      PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget) :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget := by
  intro χ hχ hprime
  have hrecTrace :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_identity_trace_connected
      htwo
  have hrecForces :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_trace_connected
      hrecTrace
  have hexcl :
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces
      hrecForces
  have hforcesTwo :
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
      hexcl
  exact
    PRCCharacterPrimeIdentityRespectsTraceConnected_of_two_prime_identity_and_forces_two
      (htwo χ hχ hprime)
      (hforcesTwo χ hχ hprime)

theorem PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_iff_prime_identity_trace_transport :
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget :=
  ⟨PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_two_prime_identity_trace_connected,
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_prime_identity_trace_transport⟩

theorem PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_refuted
    (PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_iff_prime_identity_trace_transport.mp
      htarget)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_refuted
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_identity_trace_connected.mp
      htarget)

theorem PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_refuted
    (PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_iff_identity_forces_two.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_refuted
    (PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_iff_identity_forces_two.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_refuted
    (PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_iff_two_prime_reciprocal_forces.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_iff_no_mixed_prime_witnesses.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_refuted
    (PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_prime_identity_witness_globalizes.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_refuted
    (PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_prime_floor_successor_transport.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_refuted
    (PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_iff_comparable_trace.mp
      htarget)

theorem PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_refuted
    (PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_branch_transport.mp
      htarget)

theorem PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_refuted
    (PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_no_mixed_nonunit.mpr
      htarget)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_refuted
    (PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_identity_branch_transport.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_identity_witness_globalizes.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_refuted
    (PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_iff_no_mixed.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_refuted
    (PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_no_mixed_prime_witnesses.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_refuted
    (PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_successor_step_pair.mpr
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_sharpened.mpr
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget :=
  PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted

theorem PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_refuted :
    ¬ PRCPrimeFloorSuccessorTransportLocalAdjacentTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted
    (PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_nonunit_coherent.mp
      htarget)

theorem PRCPrimeFloorSuccessorTransportSharpenedTarget_refuted :
    ¬ PRCPrimeFloorSuccessorTransportSharpenedTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget_refuted
    htarget.1

theorem PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_refuted
    (PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_split.mpr htarget)

theorem PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_refuted
    (PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_local_exclusion.mpr
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_iff_identity_comparable_trace.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_local_no_mixed.mpr
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_product_no_mixed
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_iff_local_comparable_trace.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_iff_local_identity_transport.mp
      htarget)

theorem PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_successor_step
      htarget)

theorem PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_refuted
    (PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_of_transport htarget)

theorem PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_refuted
    (PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_iff_no_mixed_prime_orientation.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_refuted
    (PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_no_mixed_prime_orientation.mp
      htarget)

theorem PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget := by
  intro htarget
  have hprime :
      PRCCharacterPrimeDirectionCalibrated twoAdicAxisTwistCharacter :=
    PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist
      twoAdicAxisTwistCharacter_branch
  have hlocal :
      PRCCharacterNonunitOrbitLocalOrientation twoAdicAxisTwistCharacter :=
    htarget twoAdicAxisTwistCharacter twoAdicAxisTwistCharacter_ratio_character
      hprime
  have hprod0 : twoOrbit * threeOrbit ≠ DistinctionNat.zero :=
    DistinctionNat.mul_ne_zero twoOrbit_primeOrbit.1 threeOrbit_primeOrbit.1
  have hprodUnit : ¬ DistinctionNat.unit (twoOrbit * threeOrbit) :=
    orbit_mul_not_unit_of_left_not_unit
      (p := twoOrbit) (r := threeOrbit) twoOrbit_primeOrbit.2.1
  have hprodCross :
      RatioOrbit.crossEq (orbitDirection (twoOrbit * threeOrbit) hprod0)
        twoThreePrimeCompositeDirection := by
    simpa [twoThreePrimeCompositeDirection, twoPrimeDirection,
      threePrimeDirection, primeDirection] using
      orbitDirection_mul_crossEq twoOrbit threeOrbit (twoOrbit * threeOrbit)
        twoOrbit_primeOrbit.1 threeOrbit_primeOrbit.1 hprod0 rfl
  have hrespect : PRCCharacterRespectsCrossEq twoAdicAxisTwistCharacter :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical
      twoAdicAxisTwistCharacter_ratio_character
      PRCNormalizeRatioCanonicalTarget_proved
  have htwoThree :
      PRCCharacterTwoThreeCompositeLocalOrientation twoAdicAxisTwistCharacter := by
    rcases hlocal (twoOrbit * threeOrbit) hprod0 hprodUnit with hId | hRec
    · exact Or.inl
        (RatioOrbit.crossEq_trans
          (hrespect twoThreePrimeCompositeDirection
            (orbitDirection (twoOrbit * threeOrbit) hprod0)
            (RatioOrbit.crossEq_symm hprodCross))
          (RatioOrbit.crossEq_trans hId hprodCross))
    · exact Or.inr
        (RatioOrbit.crossEq_trans
          (hrespect twoThreePrimeCompositeDirection
            (orbitDirection (twoOrbit * threeOrbit) hprod0)
            (RatioOrbit.crossEq_symm hprodCross))
          (RatioOrbit.crossEq_trans hRec (ratioOrbit_recip_congr hprodCross)))
  exact PRCCharacterTwoAdicAxisTwist_two_three_local_orientation_absurd
    twoAdicAxisTwistCharacter_ratio_character
    twoAdicAxisTwistCharacter_branch htwoThree

theorem PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_refuted
    (PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_product_local_orientation
      htarget)

theorem PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget := by
  intro htarget
  have hprime :
      PRCCharacterPrimeDirectionCalibrated twoAdicAxisTwistCharacter :=
    PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist
      twoAdicAxisTwistCharacter_branch
  have htransport :
      PRCCharacterNonunitReciprocalBranchTransport twoAdicAxisTwistCharacter :=
    htarget twoAdicAxisTwistCharacter twoAdicAxisTwistCharacter_ratio_character
      hprime
  have htwoRec :
      PRCCharacterOrbitDirectionReciprocal twoAdicAxisTwistCharacter
        twoOrbit twoOrbit_primeOrbit.1 := by
    simpa [PRCCharacterOrbitDirectionReciprocal, twoPrimeDirection,
      primeDirection] using twoAdicAxisTwistCharacter_branch.1
  have hthreeRec :
      PRCCharacterOrbitDirectionReciprocal twoAdicAxisTwistCharacter
        threeOrbit threeOrbit_primeOrbit.1 :=
    htransport twoOrbit twoOrbit_primeOrbit.1 twoOrbit_primeOrbit.2.1 htwoRec
      threeOrbit threeOrbit_primeOrbit.1 threeOrbit_primeOrbit.2.1
  have hthreeId :
      PRCCharacterOrbitDirectionIdentity twoAdicAxisTwistCharacter
        threeOrbit threeOrbit_primeOrbit.1 := by
    simpa [PRCCharacterOrbitDirectionIdentity, threePrimeDirection,
      primeDirection] using
      twoAdicAxisTwistCharacter_branch.2 threeOrbit threeOrbit_primeOrbit
        threeOrbit_ne_twoOrbit
  have hself :
      RatioOrbit.crossEq (orbitDirection threeOrbit threeOrbit_primeOrbit.1)
        (RatioOrbit.recip (orbitDirection threeOrbit threeOrbit_primeOrbit.1)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hthreeId) hthreeRec
  exact orbitDirection_nonunit_not_crossEq_recip threeOrbit
    threeOrbit_primeOrbit.1 threeOrbit_primeOrbit.2.1 hself

theorem PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget_refuted
    htarget.2

theorem PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitBranchAgreementTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget_refuted
    (PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_iff_transport_pair.mp
      htarget)

theorem PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget := by
  intro htarget
  have hprime :
      PRCCharacterPrimeDirectionCalibrated twoAdicAxisTwistCharacter :=
    PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist
      twoAdicAxisTwistCharacter_branch
  have hnoAdj :
      PRCCharacterPrimeFloorNoAdjacentMixedOrientation
        twoAdicAxisTwistCharacter :=
    htarget twoAdicAxisTwistCharacter twoAdicAxisTwistCharacter_ratio_character
      hprime
  have htwoRec :
      PRCCharacterOrbitDirectionReciprocal twoAdicAxisTwistCharacter
        twoOrbit twoOrbit_primeOrbit.1 := by
    simpa [PRCCharacterOrbitDirectionReciprocal, twoPrimeDirection,
      primeDirection] using twoAdicAxisTwistCharacter_branch.1
  have hthreeId :
      PRCCharacterOrbitDirectionIdentity twoAdicAxisTwistCharacter
        (DistinctionNat.succ twoOrbit) (orbit_succ_ne_zero twoOrbit) := by
    simpa [PRCCharacterOrbitDirectionIdentity, threeOrbit,
      threePrimeDirection, primeDirection] using
      twoAdicAxisTwistCharacter_branch.2 threeOrbit threeOrbit_primeOrbit
        threeOrbit_ne_twoOrbit
  exact (hnoAdj twoOrbit twoOrbit_primeOrbit.1 twoOrbit_primeOrbit.2.1).2
    ⟨htwoRec, hthreeId⟩

theorem PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget := by
  intro htarget
  have hprime :
      PRCCharacterPrimeDirectionCalibrated twoAdicAxisTwistCharacter :=
    PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist
      twoAdicAxisTwistCharacter_branch
  have hcontracts :
      PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep
        twoAdicAxisTwistCharacter :=
    htarget twoAdicAxisTwistCharacter twoAdicAxisTwistCharacter_ratio_character
      hprime
  have hthreeId :
      PRCCharacterOrbitDirectionIdentity twoAdicAxisTwistCharacter
        (DistinctionNat.succ twoOrbit) (orbit_succ_ne_zero twoOrbit) := by
    simpa [PRCCharacterOrbitDirectionIdentity, threeOrbit,
      threePrimeDirection, primeDirection] using
      twoAdicAxisTwistCharacter_branch.2 threeOrbit threeOrbit_primeOrbit
        threeOrbit_ne_twoOrbit
  have htwoId :
      PRCCharacterOrbitDirectionIdentity twoAdicAxisTwistCharacter
        twoOrbit twoOrbit_primeOrbit.1 :=
    hcontracts twoOrbit twoOrbit_primeOrbit.1 twoOrbit_primeOrbit.2.1
      hthreeId
  have htwoRec :
      PRCCharacterOrbitDirectionReciprocal twoAdicAxisTwistCharacter
        twoOrbit twoOrbit_primeOrbit.1 := by
    simpa [PRCCharacterOrbitDirectionReciprocal, twoPrimeDirection,
      primeDirection] using twoAdicAxisTwistCharacter_branch.1
  have hself :
      RatioOrbit.crossEq (orbitDirection twoOrbit twoOrbit_primeOrbit.1)
        (RatioOrbit.recip (orbitDirection twoOrbit twoOrbit_primeOrbit.1)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) htwoRec
  exact orbitDirection_nonunit_not_crossEq_recip twoOrbit
    twoOrbit_primeOrbit.1 twoOrbit_primeOrbit.2.1 hself

theorem twoAdicTwistRat_four :
    twoAdicTwistRat 4 = (1 / 4 : ℚ) := by
  have hmul := twoAdicTwistRat_mul (2 : ℚ) (2 : ℚ)
  rw [twoAdicTwistRat_two] at hmul
  norm_num at hmul
  exact hmul

theorem twoAdicAxisTwistCharacter_succ_three_not_identity :
    ¬ PRCCharacterOrbitDirectionIdentity twoAdicAxisTwistCharacter
      (DistinctionNat.succ threeOrbit) (orbit_succ_ne_zero threeOrbit) := by
  intro hId
  rw [PRCCharacterOrbitDirectionIdentity, RatioOrbit.crossEq_iff_toRat_eq,
    twoAdicAxisTwistCharacter_toRat, orbitDirection_toRat,
    DistinctionNat.toNat_succ, threeOrbit_toNat] at hId
  norm_num [twoAdicTwistRat_four] at hId

theorem PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget := by
  intro htarget
  have hprime :
      PRCCharacterPrimeDirectionCalibrated twoAdicAxisTwistCharacter :=
    PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist
      twoAdicAxisTwistCharacter_branch
  have hextends :
      PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep
        twoAdicAxisTwistCharacter :=
    htarget twoAdicAxisTwistCharacter twoAdicAxisTwistCharacter_ratio_character
      hprime
  have hthreeId :
      PRCCharacterOrbitDirectionIdentity twoAdicAxisTwistCharacter
        threeOrbit threeOrbit_primeOrbit.1 := by
    simpa [PRCCharacterOrbitDirectionIdentity, threePrimeDirection,
      primeDirection] using
      twoAdicAxisTwistCharacter_branch.2 threeOrbit threeOrbit_primeOrbit
        threeOrbit_ne_twoOrbit
  exact twoAdicAxisTwistCharacter_succ_three_not_identity
    (hextends threeOrbit threeOrbit_primeOrbit.1 threeOrbit_primeOrbit.2.1
      hthreeId)

/-- Sharper orientation blocker B: once prime orientation is coherent, the
multiplicative character law and native rational factorization must propagate
that orientation to every ratio direction. -/
def PRCCoherentPrimeOrientationPropagatesToGlobalTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterPrimeOrientationCoherent χ →
        PRCCharacterGlobalCostOrientation χ

/-- Exact repaired orientation target after the absolute-value countermodel:
coherent prime orientation must be supplemented by signed-unit calibration before
one can ask for global pointwise identity-or-reciprocal orientation. -/
def PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCRatioCharacter χ →
      PRCCharacterSignedUnitCalibrated χ →
        PRCCharacterPrimeOrientationCoherent χ →
          PRCCharacterGlobalCostOrientation χ

/-- The admissible interface must also force signed-unit calibration. Pass 279
shows that the repaired prime-pair admissibility fields still do not do this. -/
def PRCAdmissibleCharacterSignedUnitCalibratedTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCAdmissibleRatioCharacter χ →
      PRCCharacterSignedUnitCalibrated χ

theorem PRCAdmissibleCharacterGlobalOrientationTarget_of_signed_global_propagation
    (hsign : PRCAdmissibleCharacterSignedUnitCalibratedTarget)
    (hprop : PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCAdmissibleCharacterGlobalOrientationTarget := by
  intro χ hadm
  exact hprop χ hadm.ratio_character (hsign χ hadm)
    (PRCAdmissibleCharacterPrimeOrientationCoherentTarget_proved χ hadm)

theorem absValueCharacter_negative_one_no_global_orientation :
    ¬ (RatioOrbit.crossEq (absValueCharacter negativeOneRatio) negativeOneRatio ∨
      RatioOrbit.crossEq (absValueCharacter negativeOneRatio)
        (RatioOrbit.recip negativeOneRatio)) := by
  intro horient
  rcases horient with hsame | hrec
  · rw [RatioOrbit.crossEq_iff_toRat_eq, absValueCharacter_toRat,
      negativeOneRatio_toRat] at hsame
    norm_num at hsame
  · rw [RatioOrbit.crossEq_iff_toRat_eq, absValueCharacter_toRat,
      negativeOneRatio_toRat, RatioOrbit.recip_toRat,
      negativeOneRatio_toRat] at hrec
    norm_num at hrec

/-- The coherent-prime-to-global target is false without a signed-unit
calibration. The absolute-value character fixes every positive prime axis, but
it sends `-1` to `+1`, so the global orientation conclusion fails exactly at the
signed unit. -/
theorem PRCCoherentPrimeOrientationPropagatesToGlobalTarget_refuted :
    ¬ PRCCoherentPrimeOrientationPropagatesToGlobalTarget := by
  intro hprop
  exact absValueCharacter_negative_one_no_global_orientation
    (hprop absValueCharacter absValueCharacter_ratio_character
      absValueCharacter_prime_orientation_coherent negativeOneRatio)

theorem PRCAdmissibleCharacterSignedUnitCalibratedTarget_refuted :
    ¬ PRCAdmissibleCharacterSignedUnitCalibratedTarget := by
  intro hsign
  exact absValueCharacter_not_signed_unit_calibrated
    (hsign absValueCharacter absValueCharacter_admissible)

theorem negativeOneRatio_self_recip :
    RatioOrbit.crossEq negativeOneRatio (RatioOrbit.recip negativeOneRatio) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, negativeOneRatio_toRat,
    RatioOrbit.recip_toRat, negativeOneRatio_toRat]
  norm_num

theorem PRCCharacterZero_of_prime_orientation_coherent
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcoh : PRCCharacterPrimeOrientationCoherent χ) :
    RatioOrbit.crossEq (χ RatioOrbit.zero) RatioOrbit.zero := by
  have hrespect : PRCCharacterRespectsCrossEq χ :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved
  have htwoNotOne :
      ¬ RatioOrbit.crossEq (χ twoPrimeDirection) RatioOrbit.one := by
    intro hone
    rcases hcoh with hallId | hallRec
    · have htwoId := hallId twoOrbit twoOrbit_primeOrbit
      have htwoOne :
          RatioOrbit.crossEq twoPrimeDirection RatioOrbit.one :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoId) hone
      rw [RatioOrbit.crossEq_iff_toRat_eq, twoPrimeDirection_toRat,
        RatioOrbit.one_toRat] at htwoOne
      norm_num at htwoOne
    · have htwoRec := hallRec twoOrbit twoOrbit_primeOrbit
      have hrecOne :
          RatioOrbit.crossEq (RatioOrbit.recip twoPrimeDirection)
            RatioOrbit.one :=
        RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm htwoRec) hone
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
        twoPrimeDirection_toRat, RatioOrbit.one_toRat] at hrecOne
      norm_num at hrecOne
  have hzeroMul :
      RatioOrbit.crossEq (RatioOrbit.mul RatioOrbit.zero twoPrimeDirection)
        RatioOrbit.zero := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      RatioOrbit.zero_toRat]
    norm_num
  have hχzeroMul :
      RatioOrbit.crossEq
        (χ (RatioOrbit.mul RatioOrbit.zero twoPrimeDirection))
        (χ RatioOrbit.zero) :=
    hrespect (RatioOrbit.mul RatioOrbit.zero twoPrimeDirection)
      RatioOrbit.zero hzeroMul
  have hmul :
      RatioOrbit.crossEq
        (χ (RatioOrbit.mul RatioOrbit.zero twoPrimeDirection))
        (RatioOrbit.mul (χ RatioOrbit.zero) (χ twoPrimeDirection)) :=
    hχ.multiplicative RatioOrbit.zero twoPrimeDirection
  have hzeroEq :
      RatioOrbit.crossEq (χ RatioOrbit.zero)
        (RatioOrbit.mul (χ RatioOrbit.zero) (χ twoPrimeDirection)) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm hχzeroMul) hmul
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat] at hzeroEq
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat]
  by_cases hy : (χ RatioOrbit.zero).toRat = 0
  · exact hy
  · have htwoRatOne : (χ twoPrimeDirection).toRat = 1 := by
      have hcancel :
          (χ RatioOrbit.zero).toRat * 1 =
            (χ RatioOrbit.zero).toRat * (χ twoPrimeDirection).toRat := by
        simpa [mul_one] using hzeroEq
      exact (mul_left_cancel₀ hy hcancel).symm
    exact False.elim (htwoNotOne (by
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.one_toRat]
      exact htwoRatOne))

theorem PRCCharacterPositiveOrbitIdentity_of_all_prime_identity
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hrespect : PRCCharacterRespectsCrossEq χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeId : ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp))
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero) :
    PRCCharacterOrbitDirectionIdentity χ p hp := by
  by_cases hunit : DistinctionNat.unit p
  · have hpOne :
        RatioOrbit.crossEq (orbitDirection p hp) RatioOrbit.one := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, orbitDirection_toRat,
        RatioOrbit.one_toRat]
      exact_mod_cast (DistinctionNat.unit_iff_toNat_eq_one p).mp hunit
    exact RatioOrbit.crossEq_trans (hrespect (orbitDirection p hp)
      RatioOrbit.one hpOne)
      (RatioOrbit.crossEq_trans hχ.unit (RatioOrbit.crossEq_symm hpOne))
  · exact PRCCharacterNonunitOrbitAllIdentity_of_all_prime_identity
      hχ hcompat hprimeId p hp hunit

theorem PRCCharacterPositiveOrbitReciprocal_of_all_prime_reciprocal
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hrespect : PRCCharacterRespectsCrossEq χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeRec : ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)))
    (p : DistinctionNat) (hp : p ≠ DistinctionNat.zero) :
    PRCCharacterOrbitDirectionReciprocal χ p hp := by
  by_cases hunit : DistinctionNat.unit p
  · have hpOne :
        RatioOrbit.crossEq (orbitDirection p hp) RatioOrbit.one := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, orbitDirection_toRat,
        RatioOrbit.one_toRat]
      exact_mod_cast (DistinctionNat.unit_iff_toNat_eq_one p).mp hunit
    have hrecOne :
        RatioOrbit.crossEq RatioOrbit.one
          (RatioOrbit.recip (orbitDirection p hp)) := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.one_toRat,
        RatioOrbit.recip_toRat, orbitDirection_toRat]
      rw [(DistinctionNat.unit_iff_toNat_eq_one p).mp hunit]
      norm_num
    exact RatioOrbit.crossEq_trans (hrespect (orbitDirection p hp)
      RatioOrbit.one hpOne)
      (RatioOrbit.crossEq_trans hχ.unit hrecOne)
  · exact PRCCharacterNonunitOrbitAllReciprocal_of_all_prime_reciprocal
      hχ hcompat hprimeRec p hp hunit

theorem PRCCharacterPositiveRatioIdentity_of_all_prime_identity
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hrespect : PRCCharacterRespectsCrossEq χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeId : ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp))
    {n d : DistinctionNat}
    (hn : n ≠ DistinctionNat.zero) (hd : d ≠ DistinctionNat.zero) :
    RatioOrbit.crossEq
      (χ (RatioOrbit.mul (orbitDirection n hn)
        (RatioOrbit.recip (orbitDirection d hd))))
      (RatioOrbit.mul (orbitDirection n hn)
        (RatioOrbit.recip (orbitDirection d hd))) := by
  have hnId := PRCCharacterPositiveOrbitIdentity_of_all_prime_identity
    hχ hrespect hcompat hprimeId n hn
  have hdId := PRCCharacterPositiveOrbitIdentity_of_all_prime_identity
    hχ hrespect hcompat hprimeId d hd
  have hrecD :
      RatioOrbit.crossEq
        (χ (RatioOrbit.recip (orbitDirection d hd)))
        (RatioOrbit.recip (orbitDirection d hd)) :=
    RatioOrbit.crossEq_trans (hχ.reciprocal (orbitDirection d hd))
      (ratioOrbit_recip_congr hdId)
  exact RatioOrbit.crossEq_trans
    (hχ.multiplicative (orbitDirection n hn)
      (RatioOrbit.recip (orbitDirection d hd)))
    (ratioOrbit_mul_congr hnId hrecD)

theorem PRCCharacterPositiveRatioReciprocal_of_all_prime_reciprocal
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hrespect : PRCCharacterRespectsCrossEq χ)
    (hcompat : PRCCharacterOrbitProductDisplayCompatible χ)
    (hprimeRec : ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      RatioOrbit.crossEq (χ (primeDirection p hp))
        (RatioOrbit.recip (primeDirection p hp)))
    {n d : DistinctionNat}
    (hn : n ≠ DistinctionNat.zero) (hd : d ≠ DistinctionNat.zero) :
    RatioOrbit.crossEq
      (χ (RatioOrbit.mul (orbitDirection n hn)
        (RatioOrbit.recip (orbitDirection d hd))))
      (RatioOrbit.recip
        (RatioOrbit.mul (orbitDirection n hn)
          (RatioOrbit.recip (orbitDirection d hd)))) := by
  have hnRec := PRCCharacterPositiveOrbitReciprocal_of_all_prime_reciprocal
    hχ hrespect hcompat hprimeRec n hn
  have hdRec := PRCCharacterPositiveOrbitReciprocal_of_all_prime_reciprocal
    hχ hrespect hcompat hprimeRec d hd
  have hrecD :
      RatioOrbit.crossEq
        (χ (RatioOrbit.recip (orbitDirection d hd)))
        (orbitDirection d hd) :=
    RatioOrbit.crossEq_trans (hχ.reciprocal (orbitDirection d hd))
      (RatioOrbit.crossEq_trans (ratioOrbit_recip_congr hdRec)
        (ratioOrbit_recip_recip_crossEq_self (orbitDirection d hd)))
  have hprod :
      RatioOrbit.crossEq
        (RatioOrbit.mul
          (RatioOrbit.recip (orbitDirection n hn)) (orbitDirection d hd))
        (RatioOrbit.recip
          (RatioOrbit.mul (orbitDirection n hn)
            (RatioOrbit.recip (orbitDirection d hd)))) :=
    RatioOrbit.crossEq_trans
      (ratioOrbit_mul_congr (RatioOrbit.crossEq_refl _)
        (RatioOrbit.crossEq_symm
          (ratioOrbit_recip_recip_crossEq_self (orbitDirection d hd))))
      (ratioOrbit_mul_recip_recip_crossEq_recip_mul
        (orbitDirection n hn) (RatioOrbit.recip (orbitDirection d hd)))
  exact RatioOrbit.crossEq_trans
    (hχ.multiplicative (orbitDirection n hn)
      (RatioOrbit.recip (orbitDirection d hd)))
    (RatioOrbit.crossEq_trans (ratioOrbit_mul_congr hnRec hrecD) hprod)

theorem PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget_proved :
    PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget := by
  intro χ hχ hsign hcoh q
  have hrespect : PRCCharacterRespectsCrossEq χ :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved
  have hcompat : PRCCharacterOrbitProductDisplayCompatible χ :=
    PRCCharacterOrbitProductDisplayCompatible_of_crossEq_respect hrespect
  by_cases hq0 : q.toRat = 0
  · have hqZero : RatioOrbit.crossEq q RatioOrbit.zero := by
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat]
      exact hq0
    have hχzero := PRCCharacterZero_of_prime_orientation_coherent hχ hcoh
    exact Or.inl
      (RatioOrbit.crossEq_trans (hrespect q RatioOrbit.zero hqZero)
        (RatioOrbit.crossEq_trans hχzero (RatioOrbit.crossEq_symm hqZero)))
  · rcases PRCSignedRatioDecompositionTarget_proved q hq0 with hpos | hneg
    · rcases hpos with ⟨n, d, hn, hd, hqpos⟩
      rcases hcoh with hallId | hallRec
      · have hposId :
            RatioOrbit.crossEq
              (χ (RatioOrbit.mul (orbitDirection n hn)
                (RatioOrbit.recip (orbitDirection d hd))))
              (RatioOrbit.mul (orbitDirection n hn)
                (RatioOrbit.recip (orbitDirection d hd))) :=
          PRCCharacterPositiveRatioIdentity_of_all_prime_identity
            hχ hrespect hcompat hallId hn hd
        exact Or.inl
          (RatioOrbit.crossEq_trans (hrespect q _ hqpos)
            (RatioOrbit.crossEq_trans hposId (RatioOrbit.crossEq_symm hqpos)))
      · have hposRec :
            RatioOrbit.crossEq
              (χ (RatioOrbit.mul (orbitDirection n hn)
                (RatioOrbit.recip (orbitDirection d hd))))
              (RatioOrbit.recip
                (RatioOrbit.mul (orbitDirection n hn)
                  (RatioOrbit.recip (orbitDirection d hd)))) :=
          PRCCharacterPositiveRatioReciprocal_of_all_prime_reciprocal
            hχ hrespect hcompat hallRec hn hd
        exact Or.inr
          (RatioOrbit.crossEq_trans (hrespect q _ hqpos)
            (RatioOrbit.crossEq_trans hposRec
              (ratioOrbit_recip_congr (RatioOrbit.crossEq_symm hqpos))))
    · rcases hneg with ⟨n, d, hn, hd, hqneg⟩
      let pos :=
        RatioOrbit.mul (orbitDirection n hn)
          (RatioOrbit.recip (orbitDirection d hd))
      rcases hcoh with hallId | hallRec
      · have hposId : RatioOrbit.crossEq (χ pos) pos :=
          PRCCharacterPositiveRatioIdentity_of_all_prime_identity
            hχ hrespect hcompat hallId hn hd
        have hnegId :
            RatioOrbit.crossEq
              (χ (RatioOrbit.mul negativeOneRatio pos))
              (RatioOrbit.mul negativeOneRatio pos) :=
          RatioOrbit.crossEq_trans
            (hχ.multiplicative negativeOneRatio pos)
            (ratioOrbit_mul_congr hsign hposId)
        exact Or.inl
          (RatioOrbit.crossEq_trans (hrespect q _ hqneg)
            (RatioOrbit.crossEq_trans hnegId (RatioOrbit.crossEq_symm hqneg)))
      · have hposRec : RatioOrbit.crossEq (χ pos) (RatioOrbit.recip pos) :=
          PRCCharacterPositiveRatioReciprocal_of_all_prime_reciprocal
            hχ hrespect hcompat hallRec hn hd
        have hnegRec :
            RatioOrbit.crossEq
              (χ (RatioOrbit.mul negativeOneRatio pos))
              (RatioOrbit.recip (RatioOrbit.mul negativeOneRatio pos)) :=
          RatioOrbit.crossEq_trans
            (hχ.multiplicative negativeOneRatio pos)
            (RatioOrbit.crossEq_trans
              (ratioOrbit_mul_congr hsign hposRec)
              (RatioOrbit.crossEq_trans
                (ratioOrbit_mul_congr negativeOneRatio_self_recip
                  (RatioOrbit.crossEq_refl _))
                (ratioOrbit_mul_recip_recip_crossEq_recip_mul
                  negativeOneRatio pos)))
        exact Or.inr
          (RatioOrbit.crossEq_trans (hrespect q _ hqneg)
            (RatioOrbit.crossEq_trans hnegRec
              (ratioOrbit_recip_congr (RatioOrbit.crossEq_symm hqneg))))

theorem PRCAdmissibleCharacterGlobalOrientationTarget_of_signed_unit_calibration
    (hsign : PRCAdmissibleCharacterSignedUnitCalibratedTarget) :
    PRCAdmissibleCharacterGlobalOrientationTarget :=
  PRCAdmissibleCharacterGlobalOrientationTarget_of_signed_global_propagation
    hsign PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget_proved

theorem PRCNativeCostAdmissibleCharacterRigidityTarget_of_signed_unit_calibration
    (hsign : PRCAdmissibleCharacterSignedUnitCalibratedTarget) :
    PRCNativeCostAdmissibleCharacterRigidityTarget :=
  PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_global_orientation
    (PRCAdmissibleCharacterGlobalOrientationTarget_of_signed_unit_calibration
      hsign)

theorem PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_signed_unit_calibration
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hsign : PRCAdmissibleCharacterSignedUnitCalibratedTarget) :
    PRCStrengthenedNativeCostUniquenessTarget :=
  PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_rigidity
    hfactor htwo
    (PRCNativeCostAdmissibleCharacterRigidityTarget_of_signed_unit_calibration
      hsign)

theorem PRCSignedAdmissibleRatioCharacter_global_orientation
    {χ : RatioOrbit → RatioOrbit}
    (hadm : PRCSignedAdmissibleRatioCharacter χ) :
    PRCCharacterGlobalCostOrientation χ :=
  PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget_proved χ
    hadm.admissible.ratio_character hadm.signed_unit
    (PRCAdmissibleCharacterPrimeOrientationCoherentTarget_proved χ
      hadm.admissible)

/-- Signed-admissible character rigidity is the repaired version of admissible
rigidity: once sign erasure is excluded, the character-generated cost is
canonical everywhere. -/
def PRCNativeCostSignedAdmissibleCharacterRigidityTarget : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit,
    PRCSignedAdmissibleRatioCharacter χ →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (costFromCharacter χ q) (onRatioOrbit q)

theorem PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved :
    PRCNativeCostSignedAdmissibleCharacterRigidityTarget := by
  intro χ hadm q
  rcases PRCSignedAdmissibleRatioCharacter_global_orientation hadm q with hsame | hinv
  · exact onRatioOrbit_congr hsame
  · exact RatioOrbit.crossEq_trans
      (onRatioOrbit_congr hinv)
      (RatioOrbit.crossEq_symm (reciprocal_symmetric q))

theorem PRCZeroCalibratedNativeCostUniquenessTarget_of_signed_admissible_factorization
    (hfactor : PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget) :
    PRCZeroCalibratedNativeCostUniquenessTarget := by
  intro F hF hzero q
  rcases hfactor F hF hzero with ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ hadm q)

theorem PRCNoSignedAdmissibleFactorForAbsValueGeneratedNativeCost :
    ¬ ∃ χ : RatioOrbit → RatioOrbit,
      PRCSignedAdmissibleRatioCharacter χ ∧
        ∀ q : RatioOrbit,
          RatioOrbit.crossEq (absValueGeneratedNativeCost q)
            (costFromCharacter χ q) := by
  intro hχ
  rcases hχ with ⟨χ, hadm, hFχ⟩
  have hcanonical :
      RatioOrbit.crossEq (absValueGeneratedNativeCost negativeOneRatio)
        (onRatioOrbit negativeOneRatio) :=
    RatioOrbit.crossEq_trans (hFχ negativeOneRatio)
      (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved
        χ hadm negativeOneRatio)
  exact absValueGeneratedNativeCost_negative_one_not_canonical hcanonical

theorem PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget_refuted :
    ¬ PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget := by
  intro hfactor
  exact PRCNoSignedAdmissibleFactorForAbsValueGeneratedNativeCost
    (hfactor absValueGeneratedNativeCost
      absValueGeneratedNativeCost_native_hypotheses
      absValueGeneratedNativeCost_doubled_trace_zero_calibrated)

theorem PRCZeroCalibratedNativeCostUniquenessTarget_refuted :
    ¬ PRCZeroCalibratedNativeCostUniquenessTarget := by
  intro huniq
  exact absValueGeneratedNativeCost_negative_one_not_canonical
    (huniq absValueGeneratedNativeCost
      absValueGeneratedNativeCost_native_hypotheses
      absValueGeneratedNativeCost_doubled_trace_zero_calibrated
      negativeOneRatio)

/-- Upstream repaired factorization target: a strengthened native cost must
factor through a signed-admissible character, not merely through the unsigned
admissible interface refuted by `absValueCharacter`. -/
def PRCStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCStrengthenedNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCSignedAdmissibleRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

theorem PRCStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
    (hfactor : PRCStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget) :
    PRCStrengthenedNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ hadm q)

theorem PRCStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_refuted :
    ¬ PRCStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget := by
  intro hfactor
  exact PRCStrengthenedNativeCostUniquenessTarget_refuted
    (PRCStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
      hfactor)

theorem costFromCharacter_negativeOne_forces_signed_unit
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hcost : RatioOrbit.crossEq
      (costFromCharacter χ negativeOneRatio)
      (onRatioOrbit negativeOneRatio)) :
    PRCCharacterSignedUnitCalibrated χ := by
  have hnegNonzero : negativeOneRatio.toRat ≠ 0 := by
    rw [negativeOneRatio_toRat]
    norm_num
  have hx : (χ negativeOneRatio).toRat ≠ 0 :=
    hχ.nonzero_preserving hnegNonzero
  rw [PRCCharacterSignedUnitCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
    negativeOneRatio_toRat]
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat,
    onRatioOrbit_negativeOneRatio_toRat] at hcost
  let x : ℚ := (χ negativeOneRatio).toRat
  have hx' : x ≠ 0 := hx
  have hsum : x + x⁻¹ = -2 := by
    linarith
  have hmul := congrArg (fun t : ℚ => t * x) hsum
  field_simp [hx'] at hmul
  nlinarith

/-- Zero-calibrated final factorization target: the repaired hypotheses are
strong enough to turn the zero-calibrated trace-root factor into a
signed-admissible character. -/
def PRCZeroCalibratedPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCSignedAdmissibleRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

theorem PRCZeroCalibratedPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_proved :
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget := by
  intro F hF
  rcases PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved
      F hF.prime_signed.signed_strengthened.strengthened.native
      hF.zero_calibrated with
    ⟨χ, hχ, hFχ⟩
  have hprime : PRCCharacterPrimeDirectionCalibrated χ := by
    intro p hp
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm (hFχ (primeDirection p hp)))
      (hF.prime_signed.prime_direction_cost p hp)
  have hpair : PRCCharacterPrimePairProductCostConsistent χ := by
    intro p hp r hr
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm
        (hFχ (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))))
      (hF.prime_signed.signed_strengthened.strengthened.prime_pair_product_cost
        p hp r hr)
  have hsignCost :
      RatioOrbit.crossEq (costFromCharacter χ negativeOneRatio)
        (onRatioOrbit negativeOneRatio) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ negativeOneRatio))
      hF.prime_signed.signed_strengthened.signed_unit
  have hsign : PRCCharacterSignedUnitCalibrated χ :=
    costFromCharacter_negativeOne_forces_signed_unit hχ hsignCost
  exact ⟨χ, ⟨⟨hχ, hprime, hpair⟩, hsign⟩, hFχ⟩

theorem PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget_proved :
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget := by
  intro F hF q
  rcases
      PRCZeroCalibratedPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_proved
        F hF with
    ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ hadm q)

/-- Signed repaired factorization target after pass 281: under the native
signed-unit cost field, a factor must be signed-admissible. -/
def PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSignedStrengthenedNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCSignedAdmissibleRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

theorem PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_of_character_factorization_and_two_calibration
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget) :
    PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget := by
  intro F hF
  rcases hfactor F hF.strengthened.native with ⟨χ, hχ, hFχ⟩
  have htwoCal :
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ two))
      hF.strengthened.native.two_calibrated
  have hprime :
      PRCCharacterPrimeDirectionCalibrated χ :=
    htwo χ hχ htwoCal
  have hpair :
      PRCCharacterPrimePairProductCostConsistent χ := by
    intro p hp r hr
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm
        (hFχ (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))))
      (hF.strengthened.prime_pair_product_cost p hp r hr)
  have hsignCost :
      RatioOrbit.crossEq (costFromCharacter χ negativeOneRatio)
        (onRatioOrbit negativeOneRatio) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ negativeOneRatio))
      hF.signed_unit
  have hsign : PRCCharacterSignedUnitCalibrated χ :=
    costFromCharacter_negativeOne_forces_signed_unit hχ hsignCost
  exact ⟨χ, ⟨⟨hχ, hprime, hpair⟩, hsign⟩, hFχ⟩

theorem PRCSignedStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
    (hfactor : PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget) :
    PRCSignedStrengthenedNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ hadm q)

theorem PRCSignedStrengthenedNativeCostUniquenessTarget_of_character_factorization_and_two_calibration
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget) :
    PRCSignedStrengthenedNativeCostUniquenessTarget :=
  PRCSignedStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
    (PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_of_character_factorization_and_two_calibration
      hfactor htwo)

/-- Final repaired factorization target at this layer: once the native cost
itself carries prime calibration and signed-unit calibration, ordinary character
factorization yields a signed-admissible factor. -/
def PRCPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCPrimeSignedStrengthenedNativeCostHypotheses F →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCSignedAdmissibleRatioCharacter χ ∧
          ∀ q : RatioOrbit,
            RatioOrbit.crossEq (F q) (costFromCharacter χ q)

theorem PRCPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_of_character_factorization
    (hfactor : PRCNativeCostCharacterFactorizationTarget) :
    PRCPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget := by
  intro F hF
  rcases hfactor F hF.signed_strengthened.strengthened.native with ⟨χ, hχ, hFχ⟩
  have hprime :
      PRCCharacterPrimeDirectionCalibrated χ := by
    intro p hp
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm (hFχ (primeDirection p hp)))
      (hF.prime_direction_cost p hp)
  have hpair :
      PRCCharacterPrimePairProductCostConsistent χ := by
    intro p hp r hr
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm
        (hFχ (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))))
      (hF.signed_strengthened.strengthened.prime_pair_product_cost p hp r hr)
  have hsignCost :
      RatioOrbit.crossEq (costFromCharacter χ negativeOneRatio)
        (onRatioOrbit negativeOneRatio) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ negativeOneRatio))
      hF.signed_strengthened.signed_unit
  have hsign : PRCCharacterSignedUnitCalibrated χ :=
    costFromCharacter_negativeOne_forces_signed_unit hχ hsignCost
  exact ⟨χ, ⟨⟨hχ, hprime, hpair⟩, hsign⟩, hFχ⟩

theorem PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
    (hfactor : PRCPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget) :
    PRCPrimeSignedStrengthenedNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hadm, hFχ⟩
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ hadm q)

theorem PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_of_character_factorization
    (hfactor : PRCNativeCostCharacterFactorizationTarget) :
    PRCPrimeSignedStrengthenedNativeCostUniquenessTarget :=
  PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
    (PRCPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_of_character_factorization
      hfactor)

theorem PRCAdmissibleCharacterGlobalOrientationTarget_of_prime_coherence_and_global_propagation
    (hcoh : PRCAdmissibleCharacterPrimeOrientationCoherentTarget)
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCAdmissibleCharacterGlobalOrientationTarget := by
  intro χ hadm
  exact hprop χ hadm.ratio_character (hcoh χ hadm)

theorem PRCAdmissibleCharacterGlobalOrientationTarget_of_global_propagation
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCAdmissibleCharacterGlobalOrientationTarget :=
  PRCAdmissibleCharacterGlobalOrientationTarget_of_prime_coherence_and_global_propagation
    PRCAdmissibleCharacterPrimeOrientationCoherentTarget_proved hprop

theorem PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_prime_coherence_and_global_propagation
    (hcoh : PRCAdmissibleCharacterPrimeOrientationCoherentTarget)
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCNativeCostAdmissibleCharacterRigidityTarget :=
  PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_global_orientation
    (PRCAdmissibleCharacterGlobalOrientationTarget_of_prime_coherence_and_global_propagation
      hcoh hprop)

theorem PRCNativeCostAdmissibleCharacterRigidityTarget_of_global_propagation
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCNativeCostAdmissibleCharacterRigidityTarget :=
  PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_global_orientation
    (PRCAdmissibleCharacterGlobalOrientationTarget_of_global_propagation hprop)

theorem PRCPrimeCalibrationForcesGlobalOrientationTarget_of_prime_orientation_targets
    (hcoherent : PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget)
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCPrimeCalibrationForcesGlobalOrientationTarget := by
  intro χ hχ hprime
  exact hprop χ hχ (hcoherent χ hχ hprime)

theorem PRCPrimeCalibrationPropagationTarget_of_global_orientation
    (horient : PRCPrimeCalibrationForcesGlobalOrientationTarget) :
    PRCPrimeCalibrationPropagationTarget := by
  intro χ hχ hprime q
  rcases horient χ hχ hprime q with hsame | hinv
  · exact onRatioOrbit_congr hsame
  · exact RatioOrbit.crossEq_trans
      (onRatioOrbit_congr hinv)
      (RatioOrbit.crossEq_symm (reciprocal_symmetric q))

/-- Pass-27 refinement of prime propagation. -/
def PRCPrimeCalibrationPropagationSharpenedTarget : Prop :=
  PRCPrimeFloorSuccessorTransportSharpenedTarget ∧
    PRCCoherentPrimeOrientationPropagatesToGlobalTarget

theorem PRCPrimeCalibrationPropagationTarget_of_sharpened_orientation
    (hsharp : PRCPrimeCalibrationPropagationSharpenedTarget) :
    PRCPrimeCalibrationPropagationTarget :=
  PRCPrimeCalibrationPropagationTarget_of_global_orientation
    (PRCPrimeCalibrationForcesGlobalOrientationTarget_of_prime_orientation_targets
      (PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_local_and_nomixed
        PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved
        (PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_trace_coherence
          (PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_trace_transport
            (PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_common_trace_extension
              (PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_comparable_trace
                (PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_prime_floor_successor_transport
                  (PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_nomix
                    hsharp.1)))))))
      hsharp.2)

theorem PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_admissible_prime_coherence_and_global_propagation
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hcoh : PRCAdmissibleCharacterPrimeOrientationCoherentTarget)
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCStrengthenedNativeCostUniquenessTarget :=
  PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_rigidity
    hfactor htwo
    (PRCNativeCostAdmissibleCharacterRigidityTarget_of_admissible_prime_coherence_and_global_propagation
      hcoh hprop)

theorem PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_coherent_global_propagation
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hprop : PRCCoherentPrimeOrientationPropagatesToGlobalTarget) :
    PRCStrengthenedNativeCostUniquenessTarget :=
  PRCStrengthenedNativeCostUniquenessTarget_of_character_factorization_two_calibration_and_admissible_rigidity
    hfactor htwo
    (PRCNativeCostAdmissibleCharacterRigidityTarget_of_global_propagation
      hprop)

theorem PRCNativeCostCharacterRigidityTarget_of_prime_targets
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hprop : PRCPrimeCalibrationPropagationTarget) :
    PRCNativeCostCharacterRigidityTarget := by
  intro χ hχ htwoCal q
  exact hprop χ hχ (htwo χ hχ htwoCal) q

theorem PRCNativeCostUniquenessTarget_of_prime_character_targets
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (htwo : PRCTwoCalibrationForcesPrimeCalibrationTarget)
    (hprop : PRCPrimeCalibrationPropagationTarget) :
    PRCNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hχ, hFχ⟩
  have hcal :
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ two)) hF.two_calibrated
  have hrigid :=
    PRCNativeCostCharacterRigidityTarget_of_prime_targets htwo hprop
  exact RatioOrbit.crossEq_trans (hFχ q) (hrigid χ hχ hcal q)

/-- The identity map is a ratio character. This sanity-check anchors the
character interface to the canonical cost. -/
theorem identity_ratio_character :
    PRCRatioCharacter (fun q : RatioOrbit => q) where
  unit := RatioOrbit.crossEq_refl RatioOrbit.one
  multiplicative := by
    intro x y
    exact RatioOrbit.crossEq_refl (RatioOrbit.mul x y)
  reciprocal := by
    intro x
    exact RatioOrbit.crossEq_refl (RatioOrbit.recip x)
  normalized_invariant := by
    intro q
    exact DistinctionNat.normalizeRatio_crossEq q
  nonzero_preserving := by
    intro q hq
    exact hq

theorem identity_character_rigid :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq
        (costFromCharacter (fun q : RatioOrbit => q) q)
        (onRatioOrbit q) := by
  intro q
  exact RatioOrbit.crossEq_refl (onRatioOrbit q)

theorem identity_character_prime_calibrated :
    PRCCharacterPrimeDirectionCalibrated (fun q : RatioOrbit => q) := by
  intro p hp
  exact identity_character_rigid (primeDirection p hp)

theorem identity_character_prime_pair_product_cost_consistent :
    PRCCharacterPrimePairProductCostConsistent
      (fun q : RatioOrbit => q) := by
  intro p hp r hr
  exact identity_character_rigid
    (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))

theorem identity_admissible_ratio_character :
    PRCAdmissibleRatioCharacter (fun q : RatioOrbit => q) where
  ratio_character := identity_ratio_character
  prime_calibrated := identity_character_prime_calibrated
  prime_pair_product_cost :=
    identity_character_prime_pair_product_cost_consistent

theorem identity_character_global_orientation :
    PRCCharacterGlobalCostOrientation (fun q : RatioOrbit => q) := by
  intro q
  exact Or.inl (RatioOrbit.crossEq_refl q)

theorem identity_character_prime_orientation_coherent :
    PRCCharacterPrimeOrientationCoherent (fun q : RatioOrbit => q) := by
  exact Or.inl (by
    intro p hp
    exact RatioOrbit.crossEq_refl (primeDirection p hp))

/-- The global reciprocal map is also a ratio character. This is the first
explicit witness that the multiplicative character laws alone do not choose the
identity orientation. -/
theorem reciprocal_ratio_character :
    PRCRatioCharacter (fun q : RatioOrbit => RatioOrbit.recip q) where
  unit := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
      RatioOrbit.one_toRat]
    norm_num
  multiplicative := by
    intro x y
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
      RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, RatioOrbit.recip_toRat,
      RatioOrbit.recip_toRat]
    by_cases hx : x.toRat = 0
    · simp [hx]
    · by_cases hy : y.toRat = 0
      · simp [hy]
      · field_simp [hx, hy]
  reciprocal := by
    intro x
    exact RatioOrbit.crossEq_refl (RatioOrbit.recip (RatioOrbit.recip x))
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
      RatioOrbit.recip_toRat]
    have hnorm :
        q.toRat = (DistinctionNat.normalizeRatio q).toRat :=
      (RatioOrbit.crossEq_iff_toRat_eq q (DistinctionNat.normalizeRatio q)).mp
        (DistinctionNat.normalizeRatio_crossEq q)
    exact congrArg Inv.inv hnorm
  nonzero_preserving := by
    intro q hq
    rw [RatioOrbit.recip_toRat]
    exact inv_ne_zero hq

theorem reciprocal_character_prime_calibrated :
    PRCCharacterPrimeDirectionCalibrated
      (fun q : RatioOrbit => RatioOrbit.recip q) := by
  intro p hp
  simpa [costFromCharacter] using
    RatioOrbit.crossEq_symm (reciprocal_symmetric (primeDirection p hp))

theorem reciprocal_character_prime_pair_product_cost_consistent :
    PRCCharacterPrimePairProductCostConsistent
      (fun q : RatioOrbit => RatioOrbit.recip q) := by
  intro p hp r hr
  simpa [costFromCharacter] using
    RatioOrbit.crossEq_symm
      (reciprocal_symmetric
        (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)))

theorem reciprocal_admissible_ratio_character :
    PRCAdmissibleRatioCharacter
      (fun q : RatioOrbit => RatioOrbit.recip q) where
  ratio_character := reciprocal_ratio_character
  prime_calibrated := reciprocal_character_prime_calibrated
  prime_pair_product_cost :=
    reciprocal_character_prime_pair_product_cost_consistent

theorem reciprocal_character_global_orientation :
    PRCCharacterGlobalCostOrientation
      (fun q : RatioOrbit => RatioOrbit.recip q) := by
  intro q
  exact Or.inr (RatioOrbit.crossEq_refl (RatioOrbit.recip q))

theorem reciprocal_character_prime_orientation_coherent :
    PRCCharacterPrimeOrientationCoherent
      (fun q : RatioOrbit => RatioOrbit.recip q) := by
  exact Or.inr (by
    intro p hp
    exact RatioOrbit.crossEq_refl (RatioOrbit.recip (primeDirection p hp)))

theorem reciprocal_character_not_successor_additive_compatible :
    ¬ PRCCharacterOrbitSuccessorAdditiveCompatible
      (fun q : RatioOrbit => RatioOrbit.recip q) := by
  intro hcompat
  have hstep := hcompat DistinctionNat.one DistinctionNat.one_ne_zero
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.add_toRat, RatioOrbit.recip_toRat, RatioOrbit.one_toRat,
    orbitDirection_toRat, orbitDirection_toRat, DistinctionNat.toNat_succ,
    DistinctionNat.one_toNat] at hstep
  norm_num at hstep

theorem PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget := by
  intro htarget
  exact reciprocal_character_not_successor_additive_compatible
    (htarget (fun q : RatioOrbit => RatioOrbit.recip q)
      reciprocal_ratio_character reciprocal_character_prime_calibrated)

/-- The sharpened replacement for the opaque native uniqueness blocker. -/
def PRCNativeCostUniquenessSharpenedTarget : Prop :=
  PRCNativeCostCharacterFactorizationTarget ∧
    PRCNativeCostCharacterRigidityTarget

theorem PRCNativeCostUniquenessSharpenedTarget_refuted :
    ¬ PRCNativeCostUniquenessSharpenedTarget := by
  intro htarget
  exact PRCNativeCostCharacterFactorizationTarget_refuted htarget.1

/-- Pass-26 refinement of the rigidity target. -/
def PRCNativeCostCharacterRigiditySharpenedTarget : Prop :=
  PRCTwoCalibrationForcesPrimeCalibrationTarget ∧
    PRCPrimeCalibrationPropagationTarget

theorem PRCPrimeCalibrationPropagationTarget_refuted :
    ¬ PRCPrimeCalibrationPropagationTarget := by
  intro htarget
  exact PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_refuted
    (PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_prime_calibration_propagation
      htarget)

theorem PRCPrimeCalibrationForcesGlobalOrientationTarget_refuted :
    ¬ PRCPrimeCalibrationForcesGlobalOrientationTarget := by
  intro htarget
  exact PRCPrimeCalibrationPropagationTarget_refuted
    (PRCPrimeCalibrationPropagationTarget_of_global_orientation htarget)

theorem PRCPrimeCalibrationPropagationSharpenedTarget_refuted :
    ¬ PRCPrimeCalibrationPropagationSharpenedTarget := by
  intro htarget
  exact PRCPrimeCalibrationPropagationTarget_refuted
    (PRCPrimeCalibrationPropagationTarget_of_sharpened_orientation htarget)

theorem PRCNativeCostCharacterRigiditySharpenedTarget_refuted :
    ¬ PRCNativeCostCharacterRigiditySharpenedTarget := by
  intro htarget
  exact PRCTwoCalibrationForcesPrimeCalibrationTarget_refuted htarget.1

theorem PRCNativeCostUniquenessTarget_of_character_targets
    (hfactor : PRCNativeCostCharacterFactorizationTarget)
    (hrigid : PRCNativeCostCharacterRigidityTarget) :
    PRCNativeCostUniquenessTarget := by
  intro F hF q
  rcases hfactor F hF with ⟨χ, hχ, hFχ⟩
  have hcal :
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ two)) hF.two_calibrated
  exact RatioOrbit.crossEq_trans (hFχ q) (hrigid χ hχ hcal q)

/-- Pass-25 certificate: native cost uniqueness is not closed, but the missing
mathematics is now split into exact Lean targets. -/
structure PRCNativeCostUniquenessBlockerCertificate : Prop where
  zero_calibrated_factorization_target :
    PRCZeroCalibratedNativeCostCharacterFactorizationTarget
  zero_calibrated_signed_admissible_factorization_refuted :
    ¬ PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget
  zero_calibration_signed_unit_target_refuted :
    ¬ PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget
  zero_calibrated_prime_signed_strengthened_factorization :
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget
  zero_calibrated_prime_signed_strengthened_uniqueness :
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget
  old_factorization_refuted :
    ¬ PRCNativeCostCharacterFactorizationTarget
  zero_calibrated_uniqueness_target :
    ¬ PRCZeroCalibratedNativeCostUniquenessTarget
  signed_admissible_rigidity_target :
    PRCNativeCostSignedAdmissibleCharacterRigidityTarget
  old_rigidity_refuted :
    ¬ PRCNativeCostCharacterRigidityTarget
  two_to_prime_target_refuted :
    ¬ PRCTwoCalibrationForcesPrimeCalibrationTarget
  prime_propagation_target_refuted :
    ¬ PRCPrimeCalibrationPropagationTarget
  global_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesGlobalOrientationTarget
  coherent_prime_orientation :
    PRCCharacterPrimeOrientationCoherent =
      PRCCharacterPrimeOrientationCoherent
  two_orbit_prime :
    DistinctionNat.primeOrbit twoOrbit
  two_prime_direction :
    twoPrimeDirection = twoPrimeDirection
  two_prime_branch_controls_primes :
    PRCCharacterTwoPrimeBranchControlsPrimes =
      PRCCharacterTwoPrimeBranchControlsPrimes
  prime_identity_iff_two_prime_identity :
    PRCCharacterPrimeIdentityIffTwoPrimeIdentity =
      PRCCharacterPrimeIdentityIffTwoPrimeIdentity
  prime_identity_forces_two_prime_identity :
    PRCCharacterPrimeIdentityForcesTwoPrimeIdentity =
      PRCCharacterPrimeIdentityForcesTwoPrimeIdentity
  two_prime_reciprocal_excludes_prime_identity :
    PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity =
      PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity
  two_prime_reciprocal_forces_prime_reciprocal :
    PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal =
      PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal
  two_prime_reciprocal_trace_connected :
    PRCCharacterTwoPrimeReciprocalRespectsTraceConnected =
      PRCCharacterTwoPrimeReciprocalRespectsTraceConnected
  two_prime_identity_trace_connected :
    PRCCharacterTwoPrimeIdentityRespectsTraceConnected =
      PRCCharacterTwoPrimeIdentityRespectsTraceConnected
  reciprocal_twist_character :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCRatioCharacter (PRCCharacterReciprocalTwist χ)
  reciprocal_twist_prime_calibrated :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeDirectionCalibrated χ →
        PRCCharacterPrimeDirectionCalibrated (PRCCharacterReciprocalTwist χ)
  reciprocal_twist_prime_identity_iff_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq
            (PRCCharacterReciprocalTwist χ (primeDirection p hp))
            (primeDirection p hp) ↔
          RatioOrbit.crossEq (χ (primeDirection p hp))
            (RatioOrbit.recip (primeDirection p hp))
  reciprocal_twist_two_identity_iff_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      RatioOrbit.crossEq
          (PRCCharacterReciprocalTwist χ twoPrimeDirection)
          twoPrimeDirection ↔
        RatioOrbit.crossEq (χ twoPrimeDirection)
          (RatioOrbit.recip twoPrimeDirection)
  reciprocal_twist_prime_reciprocal_iff_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
        RatioOrbit.crossEq
            (PRCCharacterReciprocalTwist χ (primeDirection p hp))
            (RatioOrbit.recip (primeDirection p hp)) ↔
          RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)
  reciprocal_twist_two_reciprocal_iff_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      RatioOrbit.crossEq
          (PRCCharacterReciprocalTwist χ twoPrimeDirection)
          (RatioOrbit.recip twoPrimeDirection) ↔
        RatioOrbit.crossEq (χ twoPrimeDirection) twoPrimeDirection
  two_prime_branch_controls_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeOrientationCoherent χ →
        PRCCharacterTwoPrimeBranchControlsPrimes χ
  coherent_from_local_two_prime_branch_controls :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterTwoPrimeBranchControlsPrimes χ →
          PRCCharacterPrimeOrientationCoherent χ
  prime_identity_iff_two_from_local_two_prime_branch_controls :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterTwoPrimeBranchControlsPrimes χ →
          PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ
  two_prime_branch_controls_from_local_prime_identity_iff_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ →
          PRCCharacterTwoPrimeBranchControlsPrimes χ
  prime_identity_forces_two_from_identity_iff_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ →
        PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ
  two_prime_reciprocal_excludes_from_identity_forces_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ →
        PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ
  prime_identity_forces_two_from_local_two_prime_reciprocal_excludes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ →
          PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ
  prime_identity_forces_two_iff_two_prime_reciprocal_excludes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        (PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ ↔
          PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ)
  two_prime_reciprocal_excludes_from_two_prime_reciprocal_forces :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ →
        PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ
  two_prime_reciprocal_forces_from_local_excludes_prime_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ →
          PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ
  two_prime_reciprocal_excludes_iff_two_prime_reciprocal_forces :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        (PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ ↔
          PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ)
  two_prime_reciprocal_forces_from_trace_connected :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ →
        PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ
  two_prime_reciprocal_trace_connected_from_forces :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ →
        PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ
  two_prime_reciprocal_trace_connected_iff_forces :
    ∀ χ : RatioOrbit → RatioOrbit,
      (PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ ↔
        PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ)
  two_prime_reciprocal_trace_connected_from_twist_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterTwoPrimeIdentityRespectsTraceConnected
          (PRCCharacterReciprocalTwist χ) →
        PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ
  two_prime_identity_trace_connected_from_twist_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterTwoPrimeReciprocalRespectsTraceConnected
          (PRCCharacterReciprocalTwist χ) →
        PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ
  two_prime_identity_trace_connected_from_prime_identity_trace_connected :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsTraceConnected χ →
        PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ
  prime_identity_trace_connected_from_two_prime_identity_and_forces_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ →
        PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ →
          PRCCharacterPrimeIdentityRespectsTraceConnected χ
  local_prime_orientation :
    PRCCharacterPrimeLocalOrientation =
      PRCCharacterPrimeLocalOrientation
  no_mixed_prime_orientation :
    PRCCharacterNoMixedPrimeOrientation =
      PRCCharacterNoMixedPrimeOrientation
  no_mixed_prime_witnesses :
    PRCCharacterNoMixedPrimeWitnesses =
      PRCCharacterNoMixedPrimeWitnesses
  prime_identity_witness_excludes_reciprocal :
    PRCCharacterPrimeIdentityWitnessExcludesReciprocal =
      PRCCharacterPrimeIdentityWitnessExcludesReciprocal
  prime_reciprocal_witness_globalizes :
    PRCCharacterPrimeReciprocalWitnessGlobalizes =
      PRCCharacterPrimeReciprocalWitnessGlobalizes
  prime_reciprocal_forces_two_prime_reciprocal :
    PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal =
      PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal
  prime_reciprocal_witness_globalizes_split :
    PRCCharacterPrimeReciprocalWitnessGlobalizesSplit =
      PRCCharacterPrimeReciprocalWitnessGlobalizesSplit
  prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_orientation :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNoMixedPrimeOrientation χ →
        PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ
  no_mixed_prime_orientation_from_identity_witness_excludes_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ →
        PRCCharacterNoMixedPrimeOrientation χ
  prime_identity_witness_excludes_reciprocal_iff_no_mixed_prime_orientation :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ ↔
        PRCCharacterNoMixedPrimeOrientation χ
  no_mixed_prime_witnesses_from_identity_witness_excludes_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ →
        PRCCharacterNoMixedPrimeWitnesses χ
  prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNoMixedPrimeWitnesses χ →
        PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ
  no_mixed_prime_witnesses_iff_identity_witness_excludes_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNoMixedPrimeWitnesses χ ↔
        PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ
  prime_reciprocal_witness_globalizes_from_local_no_mixed_prime_orientation :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterNoMixedPrimeOrientation χ →
          PRCCharacterPrimeReciprocalWitnessGlobalizes χ
  no_mixed_prime_orientation_from_prime_reciprocal_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalWitnessGlobalizes χ →
        PRCCharacterNoMixedPrimeOrientation χ
  prime_reciprocal_forces_two_from_reciprocal_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalWitnessGlobalizes χ →
        PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ
  two_prime_reciprocal_forces_from_reciprocal_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalWitnessGlobalizes χ →
        PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ
  prime_reciprocal_witness_globalizes_split_from_reciprocal_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalWitnessGlobalizes χ →
        PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ
  prime_reciprocal_witness_globalizes_from_split :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ →
        PRCCharacterPrimeReciprocalWitnessGlobalizes χ
  prime_reciprocal_witness_globalizes_iff_split :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalWitnessGlobalizes χ ↔
        PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ
  prime_reciprocal_forces_two_from_reciprocal_twist_identity_forces_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityForcesTwoPrimeIdentity
          (PRCCharacterReciprocalTwist χ) →
        PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ
  prime_identity_forces_two_from_reciprocal_twist_reciprocal_forces_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal
          (PRCCharacterReciprocalTwist χ) →
        PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ
  character_no_mixed_prime_witnesses_from_coherent_prime_orientation :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeOrientationCoherent χ →
        PRCCharacterNoMixedPrimeWitnesses χ
  mixed_nonunit_witnesses_reflect_prime_witnesses :
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses =
      PRCCharacterMixedNonunitWitnessesReflectPrimeWitnesses
  mixed_nonunit_identity_witness_reflects_prime_witness :
    PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness =
      PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness
  mixed_nonunit_reciprocal_witness_reflects_prime_witness :
    PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness =
      PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness
  mixed_nonunit_witnesses_reflect_prime_witnesses_split :
    PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit =
      PRCCharacterMixedNonunitWitnessesReflectPrimeWitnessesSplit
  prime_identity_trace_coherence :
    PRCCharacterPrimeIdentityTraceCoherent =
      PRCCharacterPrimeIdentityTraceCoherent
  prime_identity_branch_uniform :
    PRCCharacterPrimeIdentityBranchUniform =
      PRCCharacterPrimeIdentityBranchUniform
  prime_axis_trace_connected :
    PRCPrimeAxisTraceConnected =
      PRCPrimeAxisTraceConnected
  prime_axis_trace_connected_proved :
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
        PRCPrimeAxisTraceConnected p hp r hr
  orbit_trace_extends_of_toNat_le :
    ∀ p r : DistinctionNat,
      p.toNat ≤ r.toNat →
        Trace.Extends (orbitPositionTrace p) (orbitPositionTrace r)
  orbit_trace_comparable :
    ∀ p r : DistinctionNat,
      Trace.Extends (orbitPositionTrace p) (orbitPositionTrace r) ∨
        Trace.Extends (orbitPositionTrace r) (orbitPositionTrace p)
  orbit_direction_toRat :
    ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
      (orbitDirection p hp).toRat = (p.toNat : ℚ)
  orbit_direction_nonunit_not_crossEq_recip :
    ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
      ¬ DistinctionNat.unit p →
        ¬ RatioOrbit.crossEq
          (orbitDirection p hp)
          (RatioOrbit.recip (orbitDirection p hp))
  orbit_direction_succ_add_one :
    ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
      RatioOrbit.crossEq
        (orbitDirection (DistinctionNat.succ p) (orbit_succ_ne_zero p))
        (RatioOrbit.add (orbitDirection p hp) RatioOrbit.one)
  ratio_add_right_one_cancel :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.add a RatioOrbit.one)
        (RatioOrbit.add b RatioOrbit.one) →
          RatioOrbit.crossEq a b
  prime_identity_respects_trace_connected :
    PRCCharacterPrimeIdentityRespectsTraceConnected =
      PRCCharacterPrimeIdentityRespectsTraceConnected
  prime_identity_respects_common_trace_extension :
    PRCCharacterPrimeIdentityRespectsCommonTraceExtension =
      PRCCharacterPrimeIdentityRespectsCommonTraceExtension
  prime_identity_respects_canonical_add_trace :
    PRCCharacterPrimeIdentityRespectsCanonicalAddTrace =
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace
  prime_identity_respects_comparable_trace :
    PRCCharacterPrimeIdentityRespectsComparableTrace =
      PRCCharacterPrimeIdentityRespectsComparableTrace
  orbit_direction_identity :
    PRCCharacterOrbitDirectionIdentity =
      PRCCharacterOrbitDirectionIdentity
  orbit_direction_reciprocal :
    PRCCharacterOrbitDirectionReciprocal =
      PRCCharacterOrbitDirectionReciprocal
  prime_identity_witness_globalizes_nonunit :
    PRCCharacterPrimeIdentityWitnessGlobalizesNonunit =
      PRCCharacterPrimeIdentityWitnessGlobalizesNonunit
  prime_no_mixed_from_branch_uniform :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityBranchUniform χ →
        PRCCharacterNoMixedPrimeOrientation χ
  prime_identity_branch_uniform_from_local_no_mixed :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterNoMixedPrimeOrientation χ →
          PRCCharacterPrimeIdentityBranchUniform χ
  orbit_succ_not_unit :
    ∀ p : DistinctionNat, p ≠ DistinctionNat.zero →
      ¬ DistinctionNat.unit p →
        ¬ DistinctionNat.unit (DistinctionNat.succ p)
  orbit_identity_respects_successor_step :
    PRCCharacterOrbitIdentityRespectsSuccessorStep =
      PRCCharacterOrbitIdentityRespectsSuccessorStep
  orbit_identity_extends_successor_step :
    PRCCharacterOrbitIdentityExtendsSuccessorStep =
      PRCCharacterOrbitIdentityExtendsSuccessorStep
  orbit_identity_contracts_successor_step :
    PRCCharacterOrbitIdentityContractsSuccessorStep =
      PRCCharacterOrbitIdentityContractsSuccessorStep
  orbit_identity_successor_transport :
    PRCCharacterOrbitIdentitySuccessorTransport =
      PRCCharacterOrbitIdentitySuccessorTransport
  orbit_successor_additive_compat :
    PRCCharacterOrbitSuccessorAdditiveCompatible =
      PRCCharacterOrbitSuccessorAdditiveCompatible
  nonunit_orbit_local_orientation :
    PRCCharacterNonunitOrbitLocalOrientation =
      PRCCharacterNonunitOrbitLocalOrientation
  orbit_product_local_orientation :
    PRCCharacterOrbitProductLocalOrientationPropagates =
      PRCCharacterOrbitProductLocalOrientationPropagates
  ratio_mul_congr :
    ∀ a₁ a₂ b₁ b₂ : RatioOrbit,
      RatioOrbit.crossEq a₁ a₂ →
        RatioOrbit.crossEq b₁ b₂ →
          RatioOrbit.crossEq (RatioOrbit.mul a₁ b₁) (RatioOrbit.mul a₂ b₂)
  ratio_recip_congr :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq a b →
        RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b)
  ratio_mul_recip_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
        (RatioOrbit.recip (RatioOrbit.mul a b))
  orbit_direction_mul :
    ∀ a b p : DistinctionNat,
      ∀ ha : a ≠ DistinctionNat.zero, ∀ hb : b ≠ DistinctionNat.zero,
        ∀ hp : p ≠ DistinctionNat.zero,
          a * b = p →
            RatioOrbit.crossEq (orbitDirection p hp)
              (RatioOrbit.mul (orbitDirection a ha) (orbitDirection b hb))
  orbit_product_display_compatible :
    PRCCharacterOrbitProductDisplayCompatible =
      PRCCharacterOrbitProductDisplayCompatible
  orbit_character_respects_crossEq :
    PRCCharacterRespectsCrossEq =
      PRCCharacterRespectsCrossEq
  normalizeRatio_canonical_target :
    PRCNormalizeRatioCanonicalTarget
  signed_orbit_sign_canonical :
    PRCSignedOrbitSignCanonical =
      PRCSignedOrbitSignCanonical
  ratio_reduced_sign_canonical :
    PRCRatioReducedSignCanonical =
      PRCRatioReducedSignCanonical
  signed_ofOrbit_abs_self :
    ∀ n : DistinctionNat, (SignedOrbit.ofOrbit n).abs = n
  signed_neg_ofOrbit_abs_self :
    ∀ n : DistinctionNat,
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)).abs = n
  signedQuotient_signCanonical :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      ∀ hd : d ≠ DistinctionNat.zero,
        DistinctionNat.divides d z.abs →
          PRCSignedOrbitSignCanonical (DistinctionNat.signedQuotient z d hd)
  normalizeRatio_reduced_signCanonical :
    ∀ q : RatioOrbit,
      PRCRatioReducedSignCanonical (DistinctionNat.normalizeRatio q)
  signCanonical_toInt_injective :
    ∀ z w : SignedOrbit,
      PRCSignedOrbitSignCanonical z →
        PRCSignedOrbitSignCanonical w →
          z.toInt = w.toInt →
            z = w
  reduced_den_dvd :
    ∀ q r : RatioOrbit,
      PRCRatioReducedSignCanonical q →
        PRCRatioReducedSignCanonical r →
          RatioOrbit.crossEq q r →
            q.den.toNat ∣ r.den.toNat
  reduced_den_eq :
    ∀ q r : RatioOrbit,
      PRCRatioReducedSignCanonical q →
        PRCRatioReducedSignCanonical r →
          RatioOrbit.crossEq q r →
            q.den = r.den
  reduced_num_eq :
    ∀ q r : RatioOrbit,
      PRCRatioReducedSignCanonical q →
        PRCRatioReducedSignCanonical r →
          RatioOrbit.crossEq q r →
            q.num = r.num
  reduced_signCanonical_ratio_unique_target :
    PRCReducedSignCanonicalRatioUniqueTarget
  reduced_signCanonical_ratio_unique_proved :
    PRCReducedSignCanonicalRatioUniqueTarget
  normalizeRatio_canonical_from_reduced_signCanonical_unique :
    PRCReducedSignCanonicalRatioUniqueTarget →
      PRCNormalizeRatioCanonicalTarget
  normalizeRatio_canonical_proved :
    PRCNormalizeRatioCanonicalTarget
  orbit_character_crossEq_from_normalizeRatio_canonical :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCNormalizeRatioCanonicalTarget →
          PRCCharacterRespectsCrossEq χ
  orbit_product_display_from_crossEq :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterRespectsCrossEq χ →
        PRCCharacterOrbitProductDisplayCompatible χ
  orbit_product_no_mixed_orientation :
    PRCCharacterOrbitProductNoMixedOrientation =
      PRCCharacterOrbitProductNoMixedOrientation
  nonunit_orbit_orientation_coherent :
    PRCCharacterNonunitOrbitOrientationCoherent =
      PRCCharacterNonunitOrbitOrientationCoherent
  no_mixed_nonunit_orbit_orientation :
    PRCCharacterNoMixedNonunitOrbitOrientation =
      PRCCharacterNoMixedNonunitOrbitOrientation
  nonunit_identity_branch_transport :
    PRCCharacterNonunitIdentityBranchTransport =
      PRCCharacterNonunitIdentityBranchTransport
  nonunit_identity_witness_globalizes :
    PRCCharacterNonunitIdentityWitnessGlobalizes =
      PRCCharacterNonunitIdentityWitnessGlobalizes
  nonunit_reciprocal_branch_transport :
    PRCCharacterNonunitReciprocalBranchTransport =
      PRCCharacterNonunitReciprocalBranchTransport
  nonunit_branch_transport_pair :
    PRCCharacterNonunitBranchTransportPair =
      PRCCharacterNonunitBranchTransportPair
  nonunit_identity_respects_comparable_trace :
    PRCCharacterNonunitIdentityRespectsComparableTrace =
      PRCCharacterNonunitIdentityRespectsComparableTrace
  nonunit_branch_agreement :
    PRCCharacterNonunitBranchAgreement =
      PRCCharacterNonunitBranchAgreement
  nonunit_local_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNonunitOrbitLocalOrientation χ
  no_mixed_nonunit_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNoMixedNonunitOrbitOrientation χ
  orbit_mul_not_unit_left :
    ∀ p r : DistinctionNat,
      ¬ DistinctionNat.unit p →
        ¬ DistinctionNat.unit (p * r)
  no_mixed_nonunit_from_product_no_mixed :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitProductNoMixedOrientation χ →
        PRCCharacterNoMixedNonunitOrbitOrientation χ
  orbit_product_no_mixed_from_no_mixed_nonunit :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNoMixedNonunitOrbitOrientation χ →
        PRCCharacterOrbitProductNoMixedOrientation χ
  orbit_product_no_mixed_iff_no_mixed_nonunit :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitProductNoMixedOrientation χ ↔
        PRCCharacterNoMixedNonunitOrbitOrientation χ
  no_mixed_nonunit_from_identity_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityBranchTransport χ →
        PRCCharacterNoMixedNonunitOrbitOrientation χ
  orbit_product_no_mixed_from_identity_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityBranchTransport χ →
        PRCCharacterOrbitProductNoMixedOrientation χ
  nonunit_identity_branch_transport_from_local_no_mixed :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterNoMixedNonunitOrbitOrientation χ →
          PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_identity_branch_transport_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_identity_witness_globalizes_from_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityBranchTransport χ →
        PRCCharacterNonunitIdentityWitnessGlobalizes χ
  nonunit_identity_branch_transport_from_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityWitnessGlobalizes χ →
        PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_identity_witness_globalizes_iff_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityWitnessGlobalizes χ ↔
        PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_coherent_from_local_identity_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterNonunitIdentityWitnessGlobalizes χ →
          PRCCharacterNonunitOrbitOrientationCoherent χ
  nonunit_identity_witness_globalizes_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNonunitIdentityWitnessGlobalizes χ
  nonunit_reciprocal_branch_transport_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNonunitReciprocalBranchTransport χ
  nonunit_branch_transport_pair_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNonunitBranchTransportPair χ
  nonunit_identity_branch_transport_from_comparable_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityRespectsComparableTrace χ →
        PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_identity_comparable_trace_from_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityBranchTransport χ →
        PRCCharacterNonunitIdentityRespectsComparableTrace χ
  nonunit_identity_comparable_trace_iff_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityRespectsComparableTrace χ ↔
        PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_branch_agreement_from_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterNonunitBranchAgreement χ
  nonunit_branch_agreement_from_transport_pair :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitBranchTransportPair χ →
        PRCCharacterNonunitBranchAgreement χ
  nonunit_identity_branch_transport_from_branch_agreement :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitBranchAgreement χ →
        PRCCharacterNonunitIdentityBranchTransport χ
  nonunit_reciprocal_branch_transport_from_branch_agreement :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitBranchAgreement χ →
        PRCCharacterNonunitReciprocalBranchTransport χ
  nonunit_branch_transport_pair_from_branch_agreement :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitBranchAgreement χ →
        PRCCharacterNonunitBranchTransportPair χ
  nonunit_branch_agreement_iff_transport_pair :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitBranchAgreement χ ↔
        PRCCharacterNonunitBranchTransportPair χ
  nonunit_branch_agreement_from_local_identity_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterNonunitIdentityBranchTransport χ →
          PRCCharacterNonunitBranchAgreement χ
  prime_floor_successor_transport_from_nonunit_identity_comparable_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitIdentityRespectsComparableTrace χ →
        PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ
  nonunit_coherent_from_local_branch_agreement :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterNonunitBranchAgreement χ →
          PRCCharacterNonunitOrbitOrientationCoherent χ
  nonunit_branch_agreement_iff_coherent_of_local :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        (PRCCharacterNonunitBranchAgreement χ ↔
          PRCCharacterNonunitOrbitOrientationCoherent χ)
  nonunit_coherent_from_local_no_mixed :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterNoMixedNonunitOrbitOrientation χ →
          PRCCharacterNonunitOrbitOrientationCoherent χ
  nonunit_coherent_from_local_identity_branch_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterNonunitIdentityBranchTransport χ →
          PRCCharacterNonunitOrbitOrientationCoherent χ
  orbit_product_no_mixed_from_nonunit_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterOrbitProductNoMixedOrientation χ
  orbit_product_identity_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          ∀ a b p : DistinctionNat,
            ∀ ha : a ≠ DistinctionNat.zero, ∀ hb : b ≠ DistinctionNat.zero,
              ∀ hp : p ≠ DistinctionNat.zero,
                a * b = p →
                  PRCCharacterOrbitDirectionIdentity χ a ha →
                    PRCCharacterOrbitDirectionIdentity χ b hb →
                      PRCCharacterOrbitDirectionIdentity χ p hp
  orbit_product_reciprocal_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          ∀ a b p : DistinctionNat,
            ∀ ha : a ≠ DistinctionNat.zero, ∀ hb : b ≠ DistinctionNat.zero,
              ∀ hp : p ≠ DistinctionNat.zero,
                a * b = p →
                  PRCCharacterOrbitDirectionReciprocal χ a ha →
                    PRCCharacterOrbitDirectionReciprocal χ b hb →
                      PRCCharacterOrbitDirectionReciprocal χ p hp
  nonunit_all_identity_from_all_prime_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          (∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
            RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)) →
            ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
              ¬ DistinctionNat.unit p →
                PRCCharacterOrbitDirectionIdentity χ p hp
  nonunit_all_reciprocal_from_all_prime_reciprocal :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          (∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
            RatioOrbit.crossEq (χ (primeDirection p hp))
              (RatioOrbit.recip (primeDirection p hp))) →
            ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
              ¬ DistinctionNat.unit p →
                PRCCharacterOrbitDirectionReciprocal χ p hp
  mixed_identity_reflects_prime_from_prime_local :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          PRCCharacterPrimeLocalOrientation χ →
            PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness χ
  mixed_reciprocal_reflects_prime_from_prime_local :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          PRCCharacterPrimeLocalOrientation χ →
            PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness χ
  orbit_product_local_from_display_nomix :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          PRCCharacterOrbitProductNoMixedOrientation χ →
            PRCCharacterOrbitProductLocalOrientationPropagates χ
  nonunit_local_from_prime_product :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeLocalOrientation χ →
        PRCCharacterOrbitProductLocalOrientationPropagates χ →
          PRCCharacterNonunitOrbitLocalOrientation χ
  prime_floor_no_adjacent_mixed_orientation :
    PRCCharacterPrimeFloorNoAdjacentMixedOrientation =
      PRCCharacterPrimeFloorNoAdjacentMixedOrientation
  prime_floor_no_adjacent_from_nonunit_coherent :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitOrientationCoherent χ →
        PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ
  prime_floor_orbit_identity_extends_successor_step :
    PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep =
      PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep
  prime_floor_orbit_identity_contracts_successor_step :
    PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep =
      PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep
  prime_floor_orbit_identity_successor_transport :
    PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport =
      PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport
  prime_floor_extends_from_local_adjacent_nomix :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ →
          PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep χ
  prime_floor_contracts_from_local_adjacent_nomix :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ →
          PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep χ
  prime_floor_successor_transport_from_local_adjacent_nomix :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ →
          PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ
  prime_floor_no_adjacent_from_successor_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ →
        PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ
  prime_floor_successor_transport_iff_local_adjacent_nomix :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        (PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ ↔
          PRCCharacterPrimeFloorNoAdjacentMixedOrientation χ)
  prime_identity_comparable_from_prime_floor_successor_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ →
        PRCCharacterPrimeIdentityRespectsComparableTrace χ
  nonunit_identity_comparable_from_prime_floor_successor_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ →
        PRCCharacterNonunitIdentityRespectsComparableTrace χ
  nonunit_coherent_from_local_prime_floor_successor_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterNonunitOrbitLocalOrientation χ →
        PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ →
          PRCCharacterNonunitOrbitOrientationCoherent χ
  prime_identity_witness_globalizes_nonunit_from_successor_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ →
        PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ
  prime_floor_successor_transport_from_prime_identity_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          PRCCharacterPrimeLocalOrientation χ →
            PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ →
              PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport χ
  prime_identity_witness_globalizes_nonunit_from_no_mixed_prime_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCRatioCharacter χ →
        PRCCharacterOrbitProductDisplayCompatible χ →
          PRCCharacterPrimeLocalOrientation χ →
            PRCCharacterNoMixedPrimeWitnesses χ →
              PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ
  no_mixed_prime_witnesses_from_prime_identity_witness_globalizes :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityWitnessGlobalizesNonunit χ →
        PRCCharacterNoMixedPrimeWitnesses χ
  orbit_identity_extends_from_additive_compat :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitSuccessorAdditiveCompatible χ →
        PRCCharacterOrbitIdentityExtendsSuccessorStep χ
  orbit_identity_contracts_from_additive_compat :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitSuccessorAdditiveCompatible χ →
        PRCCharacterOrbitIdentityContractsSuccessorStep χ
  orbit_identity_successor_transport_from_additive_compat :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitSuccessorAdditiveCompatible χ →
        PRCCharacterOrbitIdentitySuccessorTransport χ
  orbit_identity_respects_successor_step_from_transport :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitIdentitySuccessorTransport χ →
        PRCCharacterOrbitIdentityRespectsSuccessorStep χ
  orbit_identity_one_of_identity :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitIdentityRespectsSuccessorStep χ →
        ∀ p : DistinctionNat, ∀ hp : p ≠ DistinctionNat.zero,
          PRCCharacterOrbitDirectionIdentity χ p hp →
            PRCCharacterOrbitDirectionIdentity χ
              DistinctionNat.one DistinctionNat.one_ne_zero
  orbit_identity_of_one :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitIdentityRespectsSuccessorStep χ →
        ∀ r : DistinctionNat, ∀ hr : r ≠ DistinctionNat.zero,
          PRCCharacterOrbitDirectionIdentity χ
            DistinctionNat.one DistinctionNat.one_ne_zero →
              PRCCharacterOrbitDirectionIdentity χ r hr
  prime_identity_comparable_from_successor_step :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterOrbitIdentityRespectsSuccessorStep χ →
        PRCCharacterPrimeIdentityRespectsComparableTrace χ
  prime_identity_common_trace_from_comparable_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsComparableTrace χ →
        PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ
  prime_identity_canonical_add_trace_from_common_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ →
        PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ
  prime_identity_common_trace_from_canonical_add_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ →
        PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ
  prime_identity_canonical_add_trace_iff_common_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ ↔
        PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ
  prime_identity_canonical_add_trace_from_trace_connected :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsTraceConnected χ →
        PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ
  prime_identity_trace_connected_from_canonical_add_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ →
        PRCCharacterPrimeIdentityRespectsTraceConnected χ
  prime_identity_canonical_add_trace_iff_trace_connected :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ ↔
        PRCCharacterPrimeIdentityRespectsTraceConnected χ
  prime_identity_branch_uniform_from_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityTraceCoherent χ →
        PRCCharacterPrimeIdentityBranchUniform χ
  prime_identity_trace_coherence_from_branch_uniform :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityBranchUniform χ →
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_branch_uniform_iff_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityBranchUniform χ ↔
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_canonical_add_trace_from_branch_uniform :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityBranchUniform χ →
        PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ
  prime_identity_branch_uniform_from_canonical_add_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ →
        PRCCharacterPrimeIdentityBranchUniform χ
  prime_identity_branch_uniform_iff_canonical_add_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityBranchUniform χ ↔
        PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ
  prime_identity_trace_connected_from_common_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ →
        PRCCharacterPrimeIdentityRespectsTraceConnected χ
  prime_identity_comparable_trace_from_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityTraceCoherent χ →
        PRCCharacterPrimeIdentityRespectsComparableTrace χ
  prime_identity_trace_coherence_from_comparable_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsComparableTrace χ →
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_comparable_trace_iff_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsComparableTrace χ ↔
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_common_trace_from_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityTraceCoherent χ →
        PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ
  prime_identity_trace_coherence_from_common_trace :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ →
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_common_trace_iff_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ ↔
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_trace_connected_from_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityTraceCoherent χ →
        PRCCharacterPrimeIdentityRespectsTraceConnected χ
  prime_identity_trace_coherence_from_trace_connected :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsTraceConnected χ →
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_identity_trace_connected_iff_trace_coherence :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCCharacterPrimeIdentityRespectsTraceConnected χ ↔
        PRCCharacterPrimeIdentityTraceCoherent χ
  prime_to_local_orientation_target :
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget
  prime_to_local_orientation_proved :
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget
  prime_no_mixed_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_identity_trace_coherence_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_branch_uniformity_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_trace_transport_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_common_trace_extension_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_comparable_trace_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  orbit_successor_identity_target_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget
  orbit_successor_transport_target_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget
  orbit_successor_additive_compat_target_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget
  prime_floor_successor_transport_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_identity_witness_globalizes_nonunit_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  prime_floor_identity_extends_successor_step_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget
  prime_floor_identity_contracts_successor_step_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget
  prime_floor_identity_successor_step_pair_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_local_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget
  prime_floor_nonunit_product_local_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget
  prime_floor_product_display_compatibility_target :
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget
  prime_floor_character_crossEq_respect_target :
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget
  prime_floor_character_crossEq_from_normalizeRatio_canonical :
    PRCNormalizeRatioCanonicalTarget →
      PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget
  prime_floor_character_crossEq_from_reduced_signCanonical_unique :
    PRCReducedSignCanonicalRatioUniqueTarget →
      PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget
  prime_floor_character_crossEq_respect_proved :
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget
  prime_floor_product_display_from_crossEq_respect :
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget →
      PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget
  prime_floor_product_display_compatibility_proved :
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget
  prime_floor_product_no_mixed_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_nonunit_orbit_orientation_coherent_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_no_mixed_nonunit_orbit_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_nonunit_identity_branch_transport_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_nonunit_identity_witness_globalizes_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_nonunit_identity_witness_excludes_reciprocal_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_nonunit_no_mixed_witnesses_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_no_mixed_prime_witnesses_target_refuted :
    ¬ PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget
  prime_floor_prime_reciprocal_forces_two_prime_reciprocal_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_prime_witnesses_control_nonunit_target :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget
  prime_floor_mixed_nonunit_witnesses_reflect_prime_target :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_mixed_nonunit_identity_witness_reflects_prime_target :
    PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_nonunit_reciprocal_witness_reflects_prime_target :
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_nonunit_witnesses_reflect_prime_split_target :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_nonunit_no_mixed_witnesses_split_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_nonunit_identity_witness_local_exclusion_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget
  prime_floor_nonunit_identity_comparable_trace_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_orbit_orientation_local_no_mixed_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget
  prime_floor_nonunit_orbit_orientation_local_product_no_mixed_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget
  prime_floor_no_mixed_nonunit_from_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_no_mixed_nonunit_from_product_no_mixed :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_product_no_mixed_from_no_mixed_nonunit :
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget →
      PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_product_no_mixed_iff_no_mixed_nonunit :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_product_no_mixed_from_identity_branch_transport :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget →
      PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_nonunit_identity_branch_transport_from_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_nonunit_identity_branch_transport_from_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_nonunit_local_no_mixed_from_local_product_no_mixed :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget
  prime_floor_nonunit_coherent_from_local_product_no_mixed :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_nonunit_coherent_from_product_no_mixed :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_product_no_mixed_iff_nonunit_coherent :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_nonunit_identity_branch_transport_from_product_no_mixed :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_product_no_mixed_iff_identity_branch_transport :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_identity_witness_globalizes_from_identity_branch_transport :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_identity_branch_transport_from_identity_witness_globalizes :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_identity_witness_globalizes_iff_identity_branch_transport :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_identity_witness_globalizes_from_product_no_mixed :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_product_no_mixed_from_identity_witness_globalizes :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_product_no_mixed_iff_identity_witness_globalizes :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_nonunit_coherent_from_identity_witness_globalizes :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_identity_witness_globalizes_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_nonunit_coherent_iff_identity_witness_globalizes :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_identity_witness_excludes_reciprocal_from_no_mixed :
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_from_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget →
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_identity_witness_excludes_reciprocal_iff_no_mixed :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget ↔
      PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_no_mixed_witnesses_from_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget →
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_identity_witness_excludes_reciprocal_from_no_mixed_witnesses :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_witnesses_iff_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_witnesses_from_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_no_mixed_prime_orientation_from_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_orientation_from_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_no_mixed_prime_witnesses_from_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_witnesses_iff_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_from_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget
  prime_floor_no_mixed_prime_orientation_from_reciprocal_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_reciprocal_witness_globalizes_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_reciprocal_witness_globalizes_iff_identity_witness_excludes_reciprocal :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_prime_reciprocal_forces_two_from_reciprocal_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget
  prime_floor_two_prime_reciprocal_forces_from_reciprocal_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_from_reciprocal_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_prime_reciprocal_witness_globalizes_from_split :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget →
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget
  prime_floor_prime_reciprocal_witness_globalizes_iff_split :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_prime_reciprocal_forces_two_from_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget
  prime_floor_prime_identity_forces_two_from_reciprocal_forces_two :
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget →
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_reciprocal_forces_two_iff_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_excludes :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_two_prime_reciprocal_excludes_from_identity_witness_excludes :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  prime_floor_two_prime_reciprocal_excludes_iff_identity_witness_excludes :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_prime_identity_forces_two_from_two_prime_reciprocal_excludes_identity_witness :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget →
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_prime_identity_forces_two_iff_two_prime_reciprocal_excludes_identity_witness :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_no_mixed_character :
    ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_no_mixed_character_from_two_prime_reciprocal_excludes_identity_witness :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget →
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_mixed_character :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  prime_floor_prime_reciprocal_witness_globalizes_split_from_two_prime_reciprocal_forces :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_two_prime_reciprocal_forces_from_split :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_iff_two_prime_reciprocal_forces :
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_identity_trace_coherence_from_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_no_mixed_prime_orientation_iff_trace_coherence :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_no_mixed_prime_orientation_from_branch_uniformity :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_identity_branch_uniformity_from_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_branch_uniformity_iff_no_mixed_prime_orientation :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_no_mixed_prime_witnesses_iff_trace_coherence :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  coherent_prime_orientation_from_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  no_mixed_prime_witnesses_from_coherent_prime_orientation :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  no_mixed_prime_witnesses_iff_coherent_prime_orientation :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  two_prime_branch_controls_target_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  two_prime_branch_controls_from_coherent_prime_orientation :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget →
      PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  coherent_prime_orientation_from_two_prime_branch_controls :
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget →
      PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  coherent_prime_orientation_iff_two_prime_branch_controls :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  prime_identity_iff_two_prime_identity_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_identity_forces_two_prime_identity_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_excludes_prime_identity_target_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  two_prime_reciprocal_excludes_prime_identity_witness_target_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  two_prime_reciprocal_identity_prime_mixed_character :
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter =
      PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  two_prime_reciprocal_forces_prime_reciprocal_target_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_trace_connected_target_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget
  two_prime_identity_trace_connected_target_refuted :
    ¬ PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  prime_identity_iff_two_from_two_prime_branch_controls :
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget →
      PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  two_prime_branch_controls_from_prime_identity_iff_two :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  two_prime_branch_controls_iff_prime_identity_iff_two :
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_identity_forces_two_from_identity_iff_two_target :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_identity_iff_two_from_identity_forces_two_target :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_identity_iff_two_iff_identity_forces_two :
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_excludes_from_identity_forces_two_target :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  prime_identity_forces_two_from_two_prime_reciprocal_excludes_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget →
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_identity_forces_two_target_iff_two_prime_reciprocal_excludes :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  two_prime_reciprocal_excludes_from_two_prime_reciprocal_forces_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  two_prime_reciprocal_forces_from_two_prime_reciprocal_excludes_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_excludes_target_iff_two_prime_reciprocal_forces :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_forces_from_identity_forces_two_target :
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_identity_forces_two_from_two_prime_reciprocal_forces_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_forces_target_iff_identity_forces_two :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_forces_from_trace_connected_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_trace_connected_from_forces_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget
  two_prime_reciprocal_trace_connected_target_iff_forces :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_trace_connected_from_identity_trace_connected_target :
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget →
      PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget
  two_prime_identity_trace_connected_from_reciprocal_trace_connected_target :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget →
      PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  two_prime_reciprocal_trace_connected_target_iff_identity_trace_connected :
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget ↔
      PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  two_prime_identity_trace_connected_from_prime_identity_trace_transport_target :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget →
      PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  prime_identity_trace_transport_from_two_prime_identity_trace_connected_target :
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  two_prime_identity_trace_connected_target_iff_prime_identity_trace_transport :
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_floor_no_mixed_prime_witnesses_from_nonunit_no_mixed_witnesses :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_nonunit_no_mixed_witnesses_split_from_nonunit_no_mixed_witnesses :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget →
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_nonunit_no_mixed_witnesses_from_split :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget →
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_nonunit_no_mixed_witnesses_iff_split :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_prime_witnesses_control_from_mixed_reflects :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget
  prime_floor_mixed_reflects_from_prime_witnesses_control :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget →
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_prime_witnesses_control_iff_mixed_reflects :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget ↔
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_mixed_reflection_split_from_reflects :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_mixed_reflection_from_split :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget →
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_mixed_reflection_iff_split :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget ↔
      PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_mixed_identity_reflects_prime_proved :
    PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_reciprocal_reflects_prime_proved :
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_reflection_split_proved :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_mixed_reflection_proved :
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_prime_witnesses_control_nonunit_proved :
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget
  prime_floor_nonunit_no_mixed_split_from_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_nonunit_no_mixed_from_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_nonunit_no_mixed_iff_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_identity_witness_globalizes_from_local_exclusion :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_identity_witness_local_exclusion_from_globalizes :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget
  prime_floor_identity_witness_globalizes_iff_local_exclusion :
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget
  prime_floor_nonunit_identity_comparable_trace_from_branch_transport :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget →
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_identity_comparable_trace_from_product_no_mixed :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_identity_branch_transport_iff_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_product_no_mixed_iff_identity_comparable_trace :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_product_local_orientation_from_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget
  prime_floor_nonunit_local_orientation_from_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget
  prime_floor_nonunit_local_comparable_trace_from_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget
  prime_floor_nonunit_identity_comparable_trace_from_local_comparable_trace :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget →
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_local_comparable_trace_iff_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_local_no_mixed_from_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget
  prime_floor_nonunit_coherent_from_local_no_mixed :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_nonunit_orbit_orientation_coherent_iff_local_no_mixed :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget
  prime_floor_nonunit_orbit_orientation_coherent_sharpened_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget
  prime_floor_nonunit_orbit_orientation_coherent_from_local_successor_transport :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_product_no_mixed_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_nonunit_local_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget
  prime_floor_no_adjacent_mixed_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget
  prime_floor_no_adjacent_mixed_from_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget
  prime_floor_successor_transport_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_nonunit_identity_comparable_trace_from_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_orbit_orientation_sharpened_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget
  prime_floor_nonunit_orbit_orientation_coherent_iff_sharpened :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget
  prime_floor_successor_transport_from_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_identity_extends_successor_step_from_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget
  prime_floor_identity_contracts_successor_step_from_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget
  prime_floor_identity_successor_step_pair_from_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_successor_transport_from_successor_step_pair :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_successor_transport_iff_successor_step_pair :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  target_prime_identity_witness_globalizes_nonunit_from_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  target_prime_floor_successor_transport_from_prime_identity_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget →
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  target_prime_floor_successor_transport_iff_prime_identity_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  target_prime_identity_witness_globalizes_nonunit_from_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  target_no_mixed_prime_witnesses_from_prime_identity_witness_globalizes :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  target_prime_identity_witness_globalizes_nonunit_iff_no_mixed_prime_witnesses :
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget ↔
      PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_identity_successor_step_pair_from_identity_comparable_trace :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_identity_comparable_trace_from_successor_step_pair :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_identity_comparable_trace_iff_successor_step_pair :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_product_no_mixed_from_successor_step_pair :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_identity_successor_step_pair_from_product_no_mixed :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_product_no_mixed_iff_successor_step_pair :
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_coherent_from_successor_step_pair :
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_identity_successor_step_pair_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_coherent_iff_successor_step_pair :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_identity_comparable_trace_iff_successor_transport :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_successor_transport_local_adjacent_target_refuted :
    ¬ PRCPrimeFloorSuccessorTransportLocalAdjacentTarget
  prime_floor_successor_transport_from_local_adjacent_target :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget →
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_local_adjacent_from_local_successor_transport :
    (PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget) →
        PRCPrimeFloorSuccessorTransportLocalAdjacentTarget
  prime_floor_local_adjacent_iff_local_successor_transport :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget ↔
      (PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
        PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget)
  prime_floor_local_adjacent_from_nonunit_coherent :
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCPrimeFloorSuccessorTransportLocalAdjacentTarget
  prime_floor_nonunit_coherent_from_local_adjacent :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget →
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_local_adjacent_iff_nonunit_coherent :
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget ↔
      PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_product_local_orientation_sharpened_target_refuted :
    ¬ PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget
  prime_floor_product_local_orientation_from_display_nomix :
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget →
      PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget
  prime_floor_nonunit_local_orientation_from_product_local :
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget →
      PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget
  prime_floor_no_adjacent_mixed_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget
  prime_floor_successor_transport_sharpened_target_refuted :
    ¬ PRCPrimeFloorSuccessorTransportSharpenedTarget
  prime_floor_successor_transport_target_from_local_adjacent_nomix :
    PRCPrimeFloorSuccessorTransportSharpenedTarget →
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  orbit_successor_transport_target_from_additive_compat :
    PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget →
      PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget
  prime_identity_comparable_trace_from_prime_floor_successor_transport :
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  orbit_successor_identity_target_from_transport :
    PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget →
      PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget
  prime_identity_comparable_trace_from_successor_step :
    PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget →
      PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  target_prime_identity_comparable_trace_from_nonunit_identity_comparable :
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  target_nonunit_identity_comparable_trace_from_prime_identity_comparable :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  target_prime_identity_comparable_trace_iff_nonunit_identity_comparable :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  target_prime_identity_comparable_trace_iff_prime_floor_successor_transport :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_identity_common_trace_extension_from_comparable_trace :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_from_common_trace_target :
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget →
      PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_common_trace_from_canonical_add_trace_target :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_target_iff_common_trace :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_from_trace_transport_target :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget →
      PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_trace_transport_from_canonical_add_trace_target :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_canonical_add_trace_target_iff_trace_transport :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_branch_uniformity_from_trace_coherence_target :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_trace_coherence_from_branch_uniformity_target :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_branch_uniformity_target_iff_trace_coherence :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_canonical_add_trace_from_branch_uniformity_target :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_branch_uniformity_from_canonical_add_trace_target :
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_branch_uniformity_target_iff_canonical_add_trace :
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_trace_transport_from_common_trace :
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_trace_coherence_from_transport :
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  target_prime_identity_comparable_trace_from_trace_coherence :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  target_prime_identity_trace_coherence_from_comparable_trace :
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  target_prime_identity_trace_coherence_iff_comparable_trace :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  target_prime_identity_common_trace_from_trace_coherence :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  target_prime_identity_trace_coherence_from_common_trace :
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  target_prime_identity_trace_coherence_iff_common_trace :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  target_prime_identity_trace_transport_from_trace_coherence :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  target_prime_identity_trace_coherence_iff_trace_transport :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_no_mixed_from_trace_coherence :
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  coherent_prime_orientation_reduction :
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget →
      PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
        PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  prime_to_coherent_orientation_target_refuted :
    ¬ PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  coherent_prime_orientation_propagation_target_refuted :
    ¬ PRCCoherentPrimeOrientationPropagatesToGlobalTarget
  admissible_prime_orientation_coherent_target :
    PRCAdmissibleCharacterPrimeOrientationCoherentTarget
  admissible_signed_unit_calibration_target_refuted :
    ¬ PRCAdmissibleCharacterSignedUnitCalibratedTarget
  signed_coherent_prime_orientation_propagation_target :
    PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget
  global_orientation_reduction :
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget →
      PRCCoherentPrimeOrientationPropagatesToGlobalTarget →
        PRCPrimeCalibrationForcesGlobalOrientationTarget
  prime_propagation_sharpened_target_refuted :
    ¬ PRCPrimeCalibrationPropagationSharpenedTarget
  prime_propagation_reduction :
    PRCPrimeCalibrationForcesGlobalOrientationTarget →
      PRCPrimeCalibrationPropagationTarget
  prime_propagation_sharpened_reduction :
    PRCPrimeCalibrationPropagationSharpenedTarget →
      PRCPrimeCalibrationPropagationTarget
  rigidity_sharpened_target_refuted :
    ¬ PRCNativeCostCharacterRigiditySharpenedTarget
  rigidity_reduction :
    PRCTwoCalibrationForcesPrimeCalibrationTarget →
      PRCPrimeCalibrationPropagationTarget →
        PRCNativeCostCharacterRigidityTarget
  identity_character : PRCRatioCharacter (fun q : RatioOrbit => q)
  identity_rigid :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq
        (costFromCharacter (fun q : RatioOrbit => q) q)
        (onRatioOrbit q)
  identity_orientation :
    PRCCharacterGlobalCostOrientation (fun q : RatioOrbit => q)
  identity_prime_orientation_coherent :
    PRCCharacterPrimeOrientationCoherent (fun q : RatioOrbit => q)
  reciprocal_character :
    PRCRatioCharacter (fun q : RatioOrbit => RatioOrbit.recip q)
  reciprocal_prime_calibrated :
    PRCCharacterPrimeDirectionCalibrated
      (fun q : RatioOrbit => RatioOrbit.recip q)
  reciprocal_orientation :
    PRCCharacterGlobalCostOrientation
      (fun q : RatioOrbit => RatioOrbit.recip q)
  reciprocal_prime_orientation_coherent :
    PRCCharacterPrimeOrientationCoherent
      (fun q : RatioOrbit => RatioOrbit.recip q)
  sharpened_target :
    ¬ PRCNativeCostUniquenessSharpenedTarget
  reduction :
    PRCNativeCostCharacterFactorizationTarget →
      PRCNativeCostCharacterRigidityTarget →
        PRCNativeCostUniquenessTarget
  prime_reduction :
    PRCNativeCostCharacterFactorizationTarget →
      PRCTwoCalibrationForcesPrimeCalibrationTarget →
        PRCPrimeCalibrationPropagationTarget →
          PRCNativeCostUniquenessTarget
  original_target :
    ¬ PRCNativeCostUniquenessTarget
  original_target_refuted :
    ¬ PRCNativeCostUniquenessTarget
  strength_tag : StrengthTag.deltaOnly = StrengthTag.deltaOnly

theorem prc_native_cost_uniqueness_blocker_certificate :
    PRCNativeCostUniquenessBlockerCertificate where
  zero_calibrated_factorization_target :=
    PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved
  zero_calibrated_signed_admissible_factorization_refuted :=
    PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget_refuted
  zero_calibration_signed_unit_target_refuted :=
    PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget_refuted
  zero_calibrated_prime_signed_strengthened_factorization :=
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_proved
  zero_calibrated_prime_signed_strengthened_uniqueness :=
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget_proved
  old_factorization_refuted := PRCNativeCostCharacterFactorizationTarget_refuted
  zero_calibrated_uniqueness_target :=
    PRCZeroCalibratedNativeCostUniquenessTarget_refuted
  signed_admissible_rigidity_target :=
    PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved
  old_rigidity_refuted := PRCNativeCostCharacterRigidityTarget_refuted
  two_to_prime_target_refuted := PRCTwoCalibrationForcesPrimeCalibrationTarget_refuted
  prime_propagation_target_refuted :=
    PRCPrimeCalibrationPropagationTarget_refuted
  global_orientation_target_refuted :=
    PRCPrimeCalibrationForcesGlobalOrientationTarget_refuted
  coherent_prime_orientation := rfl
  two_orbit_prime := twoOrbit_primeOrbit
  two_prime_direction := rfl
  two_prime_branch_controls_primes := rfl
  prime_identity_iff_two_prime_identity := rfl
  prime_identity_forces_two_prime_identity := rfl
  two_prime_reciprocal_excludes_prime_identity := rfl
  two_prime_reciprocal_forces_prime_reciprocal := rfl
  two_prime_reciprocal_trace_connected := rfl
  two_prime_identity_trace_connected := rfl
  reciprocal_twist_character := by
    intro χ
    exact PRCRatioCharacter.reciprocalTwist
  reciprocal_twist_prime_calibrated := by
    intro χ
    exact PRCCharacterPrimeDirectionCalibrated.reciprocalTwist
  reciprocal_twist_prime_identity_iff_reciprocal := by
    intro χ p hp
    exact PRCCharacterReciprocalTwist_prime_identity_iff_reciprocal χ p hp
  reciprocal_twist_two_identity_iff_reciprocal := by
    intro χ
    exact PRCCharacterReciprocalTwist_two_identity_iff_reciprocal χ
  reciprocal_twist_prime_reciprocal_iff_identity := by
    intro χ p hp
    exact PRCCharacterReciprocalTwist_prime_reciprocal_iff_identity χ p hp
  reciprocal_twist_two_reciprocal_iff_identity := by
    intro χ
    exact PRCCharacterReciprocalTwist_two_reciprocal_iff_identity χ
  two_prime_branch_controls_from_coherent := by
    intro χ
    exact PRCCharacterTwoPrimeBranchControlsPrimes_of_coherent
  coherent_from_local_two_prime_branch_controls := by
    intro χ
    exact PRCCharacterPrimeOrientationCoherent_of_local_two_prime_branch_controls
  prime_identity_iff_two_from_local_two_prime_branch_controls := by
    intro χ
    exact PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_local_two_prime_branch_controls
  two_prime_branch_controls_from_local_prime_identity_iff_two := by
    intro χ
    exact PRCCharacterTwoPrimeBranchControlsPrimes_of_local_prime_identity_iff_two
  prime_identity_forces_two_from_identity_iff_two := by
    intro χ
    exact PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_identity_iff_two
  two_prime_reciprocal_excludes_from_identity_forces_two := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_identity_forces_two
  prime_identity_forces_two_from_local_two_prime_reciprocal_excludes := by
    intro χ
    exact PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_local_two_prime_reciprocal_excludes
  prime_identity_forces_two_iff_two_prime_reciprocal_excludes := by
    intro χ
    exact PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_iff_two_prime_reciprocal_excludes
  two_prime_reciprocal_excludes_from_two_prime_reciprocal_forces := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_of_two_prime_reciprocal_forces
  two_prime_reciprocal_forces_from_local_excludes_prime_identity := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_local_excludes_prime_identity
  two_prime_reciprocal_excludes_iff_two_prime_reciprocal_forces := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_iff_two_prime_reciprocal_forces
  two_prime_reciprocal_forces_from_trace_connected := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_trace_connected
  two_prime_reciprocal_trace_connected_from_forces := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_forces
  two_prime_reciprocal_trace_connected_iff_forces := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_iff_forces
  two_prime_reciprocal_trace_connected_from_twist_identity := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_of_reciprocal_twist_identity
  two_prime_identity_trace_connected_from_twist_reciprocal := by
    intro χ
    exact PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_reciprocal_twist_reciprocal
  two_prime_identity_trace_connected_from_prime_identity_trace_connected := by
    intro χ
    exact PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_prime_identity_trace_connected
  prime_identity_trace_connected_from_two_prime_identity_and_forces_two := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_two_prime_identity_and_forces_two
  local_prime_orientation := rfl
  no_mixed_prime_orientation := rfl
  no_mixed_prime_witnesses := rfl
  prime_identity_witness_excludes_reciprocal := rfl
  prime_reciprocal_witness_globalizes := rfl
  prime_reciprocal_forces_two_prime_reciprocal := rfl
  prime_reciprocal_witness_globalizes_split := rfl
  prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_orientation := by
    intro χ
    exact PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_orientation
  no_mixed_prime_orientation_from_identity_witness_excludes_reciprocal := by
    intro χ
    exact PRCCharacterNoMixedPrimeOrientation_of_identity_witness_excludes_reciprocal
  prime_identity_witness_excludes_reciprocal_iff_no_mixed_prime_orientation := by
    intro χ
    exact PRCCharacterPrimeIdentityWitnessExcludesReciprocal_iff_no_mixed_prime_orientation
  no_mixed_prime_witnesses_from_identity_witness_excludes_reciprocal := by
    intro χ
    exact PRCCharacterNoMixedPrimeWitnesses_of_identity_witness_excludes_reciprocal
  prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_witnesses := by
    intro χ
    exact PRCCharacterPrimeIdentityWitnessExcludesReciprocal_of_no_mixed_prime_witnesses
  no_mixed_prime_witnesses_iff_identity_witness_excludes_reciprocal := by
    intro χ
    exact PRCCharacterNoMixedPrimeWitnesses_iff_identity_witness_excludes_reciprocal
  prime_reciprocal_witness_globalizes_from_local_no_mixed_prime_orientation := by
    intro χ
    exact PRCCharacterPrimeReciprocalWitnessGlobalizes_of_local_no_mixed_prime_orientation
  no_mixed_prime_orientation_from_prime_reciprocal_witness_globalizes := by
    intro χ
    exact PRCCharacterNoMixedPrimeOrientation_of_reciprocal_witness_globalizes
  prime_reciprocal_forces_two_from_reciprocal_witness_globalizes := by
    intro χ
    exact PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_witness_globalizes
  two_prime_reciprocal_forces_from_reciprocal_witness_globalizes := by
    intro χ
    exact PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_reciprocal_witness_globalizes
  prime_reciprocal_witness_globalizes_split_from_reciprocal_witness_globalizes := by
    intro χ
    exact PRCCharacterPrimeReciprocalWitnessGlobalizesSplit_of_reciprocal_witness_globalizes
  prime_reciprocal_witness_globalizes_from_split := by
    intro χ
    exact PRCCharacterPrimeReciprocalWitnessGlobalizes_of_split
  prime_reciprocal_witness_globalizes_iff_split := by
    intro χ
    exact PRCCharacterPrimeReciprocalWitnessGlobalizes_iff_split
  prime_reciprocal_forces_two_from_reciprocal_twist_identity_forces_two := by
    intro χ
    exact PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_twist_identity_forces_two
  prime_identity_forces_two_from_reciprocal_twist_reciprocal_forces_two := by
    intro χ
    exact PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_reciprocal_twist_reciprocal_forces_two
  character_no_mixed_prime_witnesses_from_coherent_prime_orientation := by
    intro χ
    exact PRCCharacterNoMixedPrimeWitnesses_of_coherent_prime_orientation
  mixed_nonunit_witnesses_reflect_prime_witnesses := rfl
  mixed_nonunit_identity_witness_reflects_prime_witness := rfl
  mixed_nonunit_reciprocal_witness_reflects_prime_witness := rfl
  mixed_nonunit_witnesses_reflect_prime_witnesses_split := rfl
  prime_identity_trace_coherence := rfl
  prime_identity_branch_uniform := rfl
  prime_axis_trace_connected := rfl
  prime_axis_trace_connected_proved :=
    PRCPrimeAxisTraceConnected_proved
  orbit_trace_extends_of_toNat_le := by
    intro p r
    exact orbitPositionTrace_extends_of_toNat_le
  orbit_trace_comparable :=
    orbitPositionTrace_comparable
  orbit_direction_toRat := by
    intro p
    exact orbitDirection_toRat p
  orbit_direction_nonunit_not_crossEq_recip := by
    intro p
    exact orbitDirection_nonunit_not_crossEq_recip p
  orbit_direction_succ_add_one := by
    intro p
    exact orbitDirection_succ_crossEq_add_one p
  ratio_add_right_one_cancel := by
    intro a b
    exact RatioOrbit.add_right_one_cancel
  prime_identity_respects_trace_connected := rfl
  prime_identity_respects_common_trace_extension := rfl
  prime_identity_respects_canonical_add_trace := rfl
  prime_identity_respects_comparable_trace := rfl
  orbit_direction_identity := rfl
  orbit_direction_reciprocal := rfl
  prime_identity_witness_globalizes_nonunit := rfl
  orbit_succ_not_unit := by
    intro p
    exact orbit_succ_not_unit_of_nonzero_not_unit p
  orbit_identity_respects_successor_step := rfl
  orbit_identity_extends_successor_step := rfl
  orbit_identity_contracts_successor_step := rfl
  orbit_identity_successor_transport := rfl
  orbit_successor_additive_compat := rfl
  nonunit_orbit_local_orientation := rfl
  orbit_product_local_orientation := rfl
  ratio_mul_congr := by
    intro a₁ a₂ b₁ b₂
    exact ratioOrbit_mul_congr
  ratio_recip_congr := by
    intro a b
    exact ratioOrbit_recip_congr
  ratio_mul_recip_recip :=
    ratioOrbit_mul_recip_recip_crossEq_recip_mul
  orbit_direction_mul := by
    intro a b p
    exact orbitDirection_mul_crossEq a b p
  orbit_product_display_compatible := rfl
  orbit_character_respects_crossEq := rfl
  normalizeRatio_canonical_target := PRCNormalizeRatioCanonicalTarget_proved
  signed_orbit_sign_canonical := rfl
  ratio_reduced_sign_canonical := rfl
  signed_ofOrbit_abs_self := signedOrbit_ofOrbit_abs_self
  signed_neg_ofOrbit_abs_self := signedOrbit_neg_ofOrbit_abs_self
  signedQuotient_signCanonical := by
    intro z d
    exact signedQuotient_signCanonical_of_divides z d
  normalizeRatio_reduced_signCanonical :=
    normalizeRatio_reduced_signCanonical
  signCanonical_toInt_injective := by
    intro z w
    exact PRCSignedOrbitSignCanonical.eq_of_toInt_eq
  reduced_den_dvd := by
    intro q r
    exact PRCReducedSignCanonical_den_dvd_of_crossEq
  reduced_den_eq := by
    intro q r
    exact PRCReducedSignCanonical_den_eq_of_crossEq
  reduced_num_eq := by
    intro q r
    exact PRCReducedSignCanonical_num_eq_of_crossEq
  reduced_signCanonical_ratio_unique_target :=
    PRCReducedSignCanonicalRatioUniqueTarget_proved
  reduced_signCanonical_ratio_unique_proved :=
    PRCReducedSignCanonicalRatioUniqueTarget_proved
  normalizeRatio_canonical_from_reduced_signCanonical_unique :=
    PRCNormalizeRatioCanonicalTarget_of_reduced_signCanonical_unique
  normalizeRatio_canonical_proved :=
    PRCNormalizeRatioCanonicalTarget_proved
  orbit_character_crossEq_from_normalizeRatio_canonical := by
    intro χ
    exact PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical
  orbit_product_display_from_crossEq := by
    intro χ
    exact PRCCharacterOrbitProductDisplayCompatible_of_crossEq_respect
  orbit_product_no_mixed_orientation := rfl
  nonunit_orbit_orientation_coherent := rfl
  no_mixed_nonunit_orbit_orientation := rfl
  nonunit_identity_branch_transport := rfl
  nonunit_identity_witness_globalizes := rfl
  nonunit_reciprocal_branch_transport := rfl
  nonunit_branch_transport_pair := rfl
  nonunit_identity_respects_comparable_trace := rfl
  nonunit_branch_agreement := rfl
  nonunit_local_from_coherent := by
    intro χ
    exact PRCCharacterNonunitOrbitLocalOrientation_of_coherent
  no_mixed_nonunit_from_coherent := by
    intro χ
    exact PRCCharacterNoMixedNonunitOrbitOrientation_of_coherent
  orbit_mul_not_unit_left := by
    intro p r
    exact orbit_mul_not_unit_of_left_not_unit
  no_mixed_nonunit_from_product_no_mixed := by
    intro χ
    exact PRCCharacterNoMixedNonunitOrbitOrientation_of_product_no_mixed
  orbit_product_no_mixed_from_no_mixed_nonunit := by
    intro χ
    exact PRCCharacterOrbitProductNoMixedOrientation_of_no_mixed_nonunit
  orbit_product_no_mixed_iff_no_mixed_nonunit := by
    intro χ
    exact PRCCharacterOrbitProductNoMixedOrientation_iff_no_mixed_nonunit
  no_mixed_nonunit_from_identity_branch_transport := by
    intro χ
    exact PRCCharacterNoMixedNonunitOrbitOrientation_of_identity_branch_transport
  orbit_product_no_mixed_from_identity_branch_transport := by
    intro χ
    exact PRCCharacterOrbitProductNoMixedOrientation_of_identity_branch_transport
  nonunit_identity_branch_transport_from_local_no_mixed := by
    intro χ
    exact PRCCharacterNonunitIdentityBranchTransport_of_local_no_mixed
  nonunit_identity_branch_transport_from_coherent := by
    intro χ
    exact PRCCharacterNonunitIdentityBranchTransport_of_coherent
  nonunit_identity_witness_globalizes_from_branch_transport := by
    intro χ
    exact PRCCharacterNonunitIdentityWitnessGlobalizes_of_branch_transport
  nonunit_identity_branch_transport_from_witness_globalizes := by
    intro χ
    exact PRCCharacterNonunitIdentityBranchTransport_of_witness_globalizes
  nonunit_identity_witness_globalizes_iff_branch_transport := by
    intro χ
    exact PRCCharacterNonunitIdentityWitnessGlobalizes_iff_branch_transport
  nonunit_coherent_from_local_identity_witness_globalizes := by
    intro χ
    exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_identity_witness_globalizes
  nonunit_identity_witness_globalizes_from_coherent := by
    intro χ
    exact PRCCharacterNonunitIdentityWitnessGlobalizes_of_coherent
  nonunit_reciprocal_branch_transport_from_coherent := by
    intro χ
    exact PRCCharacterNonunitReciprocalBranchTransport_of_coherent
  nonunit_branch_transport_pair_from_coherent := by
    intro χ
    exact PRCCharacterNonunitBranchTransportPair_of_coherent
  nonunit_identity_branch_transport_from_comparable_trace := by
    intro χ
    exact PRCCharacterNonunitIdentityBranchTransport_of_comparable_trace
  nonunit_identity_comparable_trace_from_branch_transport := by
    intro χ
    exact PRCCharacterNonunitIdentityRespectsComparableTrace_of_branch_transport
  nonunit_identity_comparable_trace_iff_branch_transport := by
    intro χ
    exact PRCCharacterNonunitIdentityRespectsComparableTrace_iff_branch_transport
  nonunit_branch_agreement_from_coherent := by
    intro χ
    exact PRCCharacterNonunitBranchAgreement_of_coherent
  nonunit_branch_agreement_from_transport_pair := by
    intro χ
    exact PRCCharacterNonunitBranchAgreement_of_transport_pair
  nonunit_identity_branch_transport_from_branch_agreement := by
    intro χ
    exact PRCCharacterNonunitIdentityBranchTransport_of_branch_agreement
  nonunit_reciprocal_branch_transport_from_branch_agreement := by
    intro χ
    exact PRCCharacterNonunitReciprocalBranchTransport_of_branch_agreement
  nonunit_branch_transport_pair_from_branch_agreement := by
    intro χ
    exact PRCCharacterNonunitBranchTransportPair_of_branch_agreement
  nonunit_branch_agreement_iff_transport_pair := by
    intro χ
    exact PRCCharacterNonunitBranchAgreement_iff_transport_pair
  nonunit_branch_agreement_from_local_identity_branch_transport := by
    intro χ
    exact PRCCharacterNonunitBranchAgreement_of_local_identity_branch_transport
  nonunit_coherent_from_local_branch_agreement := by
    intro χ
    exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_branch_agreement
  nonunit_branch_agreement_iff_coherent_of_local := by
    intro χ
    exact PRCCharacterNonunitBranchAgreement_iff_coherent_of_local
  nonunit_coherent_from_local_no_mixed := by
    intro χ
    exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_no_mixed
  nonunit_coherent_from_local_identity_branch_transport := by
    intro χ
    exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_identity_branch_transport
  orbit_product_no_mixed_from_nonunit_coherent := by
    intro χ
    exact PRCCharacterOrbitProductNoMixedOrientation_of_nonunit_coherent
  orbit_product_identity_identity := by
    intro χ
    exact PRCCharacterOrbitProductIdentityIdentity
  orbit_product_reciprocal_reciprocal := by
    intro χ
    exact PRCCharacterOrbitProductReciprocalReciprocal
  nonunit_all_identity_from_all_prime_identity := by
    intro χ
    exact PRCCharacterNonunitOrbitAllIdentity_of_all_prime_identity
  nonunit_all_reciprocal_from_all_prime_reciprocal := by
    intro χ
    exact PRCCharacterNonunitOrbitAllReciprocal_of_all_prime_reciprocal
  mixed_identity_reflects_prime_from_prime_local := by
    intro χ
    exact PRCCharacterMixedNonunitIdentityWitnessReflectsPrimeWitness_of_prime_local
  mixed_reciprocal_reflects_prime_from_prime_local := by
    intro χ
    exact PRCCharacterMixedNonunitReciprocalWitnessReflectsPrimeWitness_of_prime_local
  orbit_product_local_from_display_nomix := by
    intro χ
    exact PRCCharacterOrbitProductLocalOrientationPropagates_of_display_compatible_nomix
  nonunit_local_from_prime_product := by
    intro χ
    exact PRCCharacterNonunitOrbitLocalOrientation_of_prime_and_product_local
  prime_floor_no_adjacent_mixed_orientation := rfl
  prime_floor_no_adjacent_from_nonunit_coherent := by
    intro χ
    exact PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_nonunit_coherent
  prime_floor_orbit_identity_extends_successor_step := rfl
  prime_floor_orbit_identity_contracts_successor_step := rfl
  prime_floor_orbit_identity_successor_transport := rfl
  prime_floor_extends_from_local_adjacent_nomix := by
    intro χ
    exact PRCCharacterPrimeFloorOrbitIdentityExtendsSuccessorStep_of_local_adjacent_nomix
  prime_floor_contracts_from_local_adjacent_nomix := by
    intro χ
    exact PRCCharacterPrimeFloorOrbitIdentityContractsSuccessorStep_of_local_adjacent_nomix
  prime_floor_successor_transport_from_local_adjacent_nomix := by
    intro χ
    exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_local_adjacent_nomix
  prime_floor_no_adjacent_from_successor_transport := by
    intro χ
    exact PRCCharacterPrimeFloorNoAdjacentMixedOrientation_of_successor_transport
  prime_floor_successor_transport_iff_local_adjacent_nomix := by
    intro χ
    exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_iff_local_adjacent_nomix
  prime_floor_successor_transport_from_nonunit_identity_comparable_trace := by
    intro χ
    exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_nonunit_identity_comparable_trace
  prime_identity_comparable_from_prime_floor_successor_transport := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_prime_floor_successor_transport
  nonunit_identity_comparable_from_prime_floor_successor_transport := by
    intro χ
    exact PRCCharacterNonunitIdentityRespectsComparableTrace_of_prime_floor_successor_transport
  nonunit_coherent_from_local_prime_floor_successor_transport := by
    intro χ
    exact PRCCharacterNonunitOrbitOrientationCoherent_of_local_and_prime_floor_successor_transport
  prime_identity_witness_globalizes_nonunit_from_successor_transport := by
    intro χ
    exact PRCCharacterPrimeIdentityWitnessGlobalizesNonunit_of_prime_floor_successor_transport
  prime_floor_successor_transport_from_prime_identity_witness_globalizes := by
    intro χ
    exact PRCCharacterPrimeFloorOrbitIdentitySuccessorTransport_of_prime_identity_witness_globalizes
  prime_identity_witness_globalizes_nonunit_from_no_mixed_prime_witnesses := by
    intro χ
    exact PRCCharacterPrimeIdentityWitnessGlobalizesNonunit_of_no_mixed_prime_witnesses
  no_mixed_prime_witnesses_from_prime_identity_witness_globalizes := by
    intro χ
    exact PRCCharacterNoMixedPrimeWitnesses_of_prime_identity_witness_globalizes
  orbit_identity_extends_from_additive_compat := by
    intro χ
    exact PRCCharacterOrbitIdentityExtendsSuccessorStep_of_additive_compat
  orbit_identity_contracts_from_additive_compat := by
    intro χ
    exact PRCCharacterOrbitIdentityContractsSuccessorStep_of_additive_compat
  orbit_identity_successor_transport_from_additive_compat := by
    intro χ
    exact PRCCharacterOrbitIdentitySuccessorTransport_of_additive_compat
  orbit_identity_respects_successor_step_from_transport := by
    intro χ
    exact PRCCharacterOrbitIdentityRespectsSuccessorStep_of_transport
  orbit_identity_one_of_identity := by
    intro χ
    exact PRCCharacterOrbitIdentity_one_of_identity
  orbit_identity_of_one := by
    intro χ
    exact PRCCharacterOrbitIdentity_of_one
  prime_identity_comparable_from_successor_step := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_successor_step
  target_prime_identity_comparable_trace_from_nonunit_identity_comparable :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_nonunit_identity_comparable_trace
  target_nonunit_identity_comparable_trace_from_prime_identity_comparable :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_identity_comparable_trace
  target_prime_identity_comparable_trace_iff_nonunit_identity_comparable :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_nonunit_identity_comparable_trace
  target_prime_identity_comparable_trace_iff_prime_floor_successor_transport :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_prime_floor_successor_transport
  prime_identity_common_trace_from_comparable_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_comparable_trace
  prime_identity_canonical_add_trace_from_common_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_common_trace_extension
  prime_identity_common_trace_from_canonical_add_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_canonical_add_trace
  prime_identity_canonical_add_trace_iff_common_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_iff_common_trace_extension
  prime_identity_canonical_add_trace_from_trace_connected := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_trace_connected
  prime_identity_trace_connected_from_canonical_add_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_canonical_add_trace
  prime_identity_canonical_add_trace_iff_trace_connected := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_iff_trace_connected
  prime_identity_branch_uniform_from_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityBranchUniform_of_trace_coherence
  prime_identity_trace_coherence_from_branch_uniform := by
    intro χ
    exact PRCCharacterPrimeIdentityTraceCoherent_of_branch_uniform
  prime_identity_branch_uniform_iff_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityBranchUniform_iff_trace_coherence
  prime_identity_canonical_add_trace_from_branch_uniform := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_of_branch_uniform
  prime_identity_branch_uniform_from_canonical_add_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityBranchUniform_of_canonical_add_trace
  prime_identity_branch_uniform_iff_canonical_add_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityBranchUniform_iff_canonical_add_trace
  prime_no_mixed_from_branch_uniform := by
    intro χ
    exact PRCCharacterNoMixedPrimeOrientation_of_branch_uniform
  prime_identity_branch_uniform_from_local_no_mixed := by
    intro χ
    exact PRCCharacterPrimeIdentityBranchUniform_of_local_no_mixed_prime_orientation
  prime_identity_trace_connected_from_common_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_common_trace_extension
  prime_identity_comparable_trace_from_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsComparableTrace_of_trace_coherence
  prime_identity_trace_coherence_from_comparable_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityTraceCoherent_of_comparable_trace
  prime_identity_comparable_trace_iff_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsComparableTrace_iff_trace_coherence
  prime_identity_common_trace_from_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_of_trace_coherence
  prime_identity_trace_coherence_from_common_trace := by
    intro χ
    exact PRCCharacterPrimeIdentityTraceCoherent_of_common_trace_extension
  prime_identity_common_trace_iff_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsCommonTraceExtension_iff_trace_coherence
  prime_identity_trace_connected_from_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsTraceConnected_of_trace_coherence
  prime_identity_trace_coherence_from_trace_connected := by
    intro χ
    exact PRCCharacterPrimeIdentityTraceCoherent_of_trace_connected
  prime_identity_trace_connected_iff_trace_coherence := by
    intro χ
    exact PRCCharacterPrimeIdentityRespectsTraceConnected_iff_trace_coherence
  prime_to_local_orientation_target :=
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved
  prime_to_local_orientation_proved :=
    PRCPrimeCalibrationForcesLocalPrimeOrientationTarget_proved
  prime_no_mixed_orientation_target_refuted :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_refuted
  prime_identity_trace_coherence_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_refuted
  prime_identity_branch_uniformity_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_refuted
  prime_identity_trace_transport_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_refuted
  prime_identity_common_trace_extension_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_refuted
  prime_identity_canonical_add_trace_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_refuted
  prime_identity_comparable_trace_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_refuted
  orbit_successor_identity_target_refuted :=
    PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_refuted
  orbit_successor_transport_target_refuted :=
    PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget_refuted
  orbit_successor_additive_compat_target_refuted :=
    PRCPrimeCalibrationForcesOrbitSuccessorAdditiveCompatibilityTarget_refuted
  prime_floor_successor_transport_target_refuted :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_refuted
  prime_identity_witness_globalizes_nonunit_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_refuted
  prime_floor_identity_extends_successor_step_target_refuted :=
    PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_refuted
  prime_floor_identity_contracts_successor_step_target_refuted :=
    PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_refuted
  prime_floor_identity_successor_step_pair_target_refuted :=
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_refuted
  prime_floor_nonunit_local_orientation_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_refuted
  prime_floor_nonunit_product_local_orientation_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_refuted
  prime_floor_product_display_compatibility_target :=
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
  prime_floor_character_crossEq_respect_target :=
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_proved
  prime_floor_character_crossEq_from_normalizeRatio_canonical :=
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_of_normalizeRatio_canonical
  prime_floor_character_crossEq_from_reduced_signCanonical_unique :=
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_of_reduced_signCanonical_unique
  prime_floor_character_crossEq_respect_proved :=
    PRCPrimeCalibrationForcesCharacterCrossEqRespectTarget_proved
  prime_floor_product_display_from_crossEq_respect :=
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_of_crossEq_respect
  prime_floor_product_display_compatibility_proved :=
    PRCPrimeCalibrationForcesOrbitProductDisplayCompatibilityTarget_proved
  prime_floor_product_no_mixed_orientation_target_refuted :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_refuted
  prime_floor_nonunit_orbit_orientation_coherent_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted
  prime_floor_no_mixed_nonunit_orbit_orientation_target_refuted :=
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_refuted
  prime_floor_nonunit_identity_branch_transport_target_refuted :=
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_refuted
  prime_floor_nonunit_identity_witness_globalizes_target_refuted :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_refuted
  prime_floor_nonunit_identity_witness_excludes_reciprocal_target_refuted :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_refuted
  prime_floor_nonunit_no_mixed_witnesses_target_refuted :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_refuted
  prime_floor_no_mixed_prime_witnesses_target_refuted :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_refuted
  prime_floor_prime_identity_witness_excludes_reciprocal_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_refuted
  prime_floor_prime_reciprocal_witness_globalizes_target_refuted :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_refuted
  prime_floor_prime_reciprocal_forces_two_prime_reciprocal_target_refuted :=
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_refuted
  prime_floor_prime_reciprocal_witness_globalizes_split_target_refuted :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_refuted
  two_prime_reciprocal_excludes_prime_identity_witness_target_refuted :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_refuted
  two_prime_reciprocal_identity_prime_mixed_character := rfl
  prime_floor_prime_witnesses_control_nonunit_target :=
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_proved
  prime_floor_mixed_nonunit_witnesses_reflect_prime_target :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_proved
  prime_floor_mixed_nonunit_identity_witness_reflects_prime_target :=
    PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget_proved
  prime_floor_mixed_nonunit_reciprocal_witness_reflects_prime_target :=
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget_proved
  prime_floor_mixed_nonunit_witnesses_reflect_prime_split_target :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_proved
  prime_floor_nonunit_no_mixed_witnesses_split_target_refuted :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_refuted
  prime_floor_nonunit_identity_witness_local_exclusion_target_refuted :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_refuted
  prime_floor_nonunit_identity_comparable_trace_target_refuted :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_refuted
  prime_floor_nonunit_orbit_orientation_local_no_mixed_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_refuted
  prime_floor_nonunit_orbit_orientation_local_product_no_mixed_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget_refuted
  prime_floor_no_mixed_nonunit_from_coherent :=
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_coherent
  prime_floor_no_mixed_nonunit_from_product_no_mixed :=
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_product_no_mixed
  prime_floor_product_no_mixed_from_no_mixed_nonunit :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_no_mixed_nonunit
  prime_floor_product_no_mixed_iff_no_mixed_nonunit :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_no_mixed_nonunit
  prime_floor_product_no_mixed_from_identity_branch_transport :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_branch_transport
  prime_floor_nonunit_identity_branch_transport_from_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_comparable_trace
  prime_floor_nonunit_identity_branch_transport_from_coherent :=
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_coherent
  prime_floor_nonunit_local_no_mixed_from_local_product_no_mixed :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_of_local_product_no_mixed
  prime_floor_nonunit_coherent_from_local_product_no_mixed :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_product_no_mixed
  prime_floor_nonunit_coherent_from_product_no_mixed :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed
  prime_floor_product_no_mixed_iff_nonunit_coherent :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_nonunit_coherent
  prime_floor_nonunit_identity_branch_transport_from_product_no_mixed :=
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_product_no_mixed
  prime_floor_product_no_mixed_iff_identity_branch_transport :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_branch_transport
  prime_floor_identity_witness_globalizes_from_identity_branch_transport :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_identity_branch_transport
  prime_floor_identity_branch_transport_from_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_identity_witness_globalizes
  prime_floor_identity_witness_globalizes_iff_identity_branch_transport :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_identity_branch_transport
  prime_floor_identity_witness_globalizes_from_product_no_mixed :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_product_no_mixed
  prime_floor_product_no_mixed_from_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_witness_globalizes
  prime_floor_product_no_mixed_iff_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_witness_globalizes
  prime_floor_nonunit_coherent_from_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_identity_witness_globalizes
  prime_floor_identity_witness_globalizes_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_nonunit_coherent
  prime_floor_nonunit_coherent_iff_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_identity_witness_globalizes
  prime_floor_identity_witness_excludes_reciprocal_from_no_mixed :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed
  prime_floor_no_mixed_from_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_identity_witness_excludes
  prime_floor_identity_witness_excludes_reciprocal_iff_no_mixed :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_iff_no_mixed
  prime_floor_no_mixed_witnesses_from_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_identity_witness_excludes
  prime_floor_identity_witness_excludes_reciprocal_from_no_mixed_witnesses :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed_witnesses
  prime_floor_no_mixed_witnesses_iff_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_identity_witness_excludes
  prime_floor_no_mixed_prime_witnesses_from_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_orientation
  prime_floor_no_mixed_prime_orientation_from_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_no_mixed_prime_witnesses
  prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_orientation
  prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_orientation
  prime_floor_no_mixed_prime_orientation_from_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_identity_witness_excludes_reciprocal
  prime_floor_prime_identity_witness_excludes_reciprocal_iff_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_iff_no_mixed_prime_orientation
  prime_floor_no_mixed_prime_witnesses_from_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_identity_witness_excludes_reciprocal
  prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_witnesses
  prime_floor_no_mixed_prime_witnesses_iff_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_identity_witness_excludes_reciprocal
  prime_floor_prime_reciprocal_witness_globalizes_from_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_no_mixed_prime_orientation
  prime_floor_no_mixed_prime_orientation_from_reciprocal_witness_globalizes :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_reciprocal_witness_globalizes
  prime_floor_prime_reciprocal_witness_globalizes_iff_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_no_mixed_prime_orientation
  prime_floor_prime_reciprocal_witness_globalizes_iff_identity_witness_excludes_reciprocal :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_identity_witness_excludes_reciprocal
  prime_floor_prime_reciprocal_forces_two_from_reciprocal_witness_globalizes :=
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_reciprocal_witness_globalizes
  prime_floor_two_prime_reciprocal_forces_from_reciprocal_witness_globalizes :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_reciprocal_witness_globalizes
  prime_floor_prime_reciprocal_witness_globalizes_split_from_reciprocal_witness_globalizes :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_reciprocal_witness_globalizes
  prime_floor_prime_reciprocal_witness_globalizes_from_split :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_split
  prime_floor_prime_reciprocal_witness_globalizes_iff_split :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_split
  prime_floor_prime_reciprocal_forces_two_from_identity_forces_two :=
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_identity_forces_two
  prime_floor_prime_identity_forces_two_from_reciprocal_forces_two :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_prime_reciprocal_forces_two
  prime_floor_prime_reciprocal_forces_two_iff_identity_forces_two :=
    PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_iff_identity_forces_two
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_excludes :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_two_prime_reciprocal_excludes
  prime_floor_two_prime_reciprocal_excludes_from_identity_witness_excludes :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_witness
  prime_floor_two_prime_reciprocal_excludes_iff_identity_witness_excludes :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_witness
  prime_floor_prime_identity_forces_two_from_two_prime_reciprocal_excludes_identity_witness :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes_witness
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_identity_forces_two :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_identity_forces_two
  prime_floor_prime_identity_forces_two_iff_two_prime_reciprocal_excludes_identity_witness :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_no_mixed_character :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_no_mixed_character
  prime_floor_no_mixed_character_from_two_prime_reciprocal_excludes_identity_witness :=
    PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_absurd_of_witness_excludes
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_mixed_character :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_mixed_character
  prime_floor_prime_reciprocal_witness_globalizes_split_from_two_prime_reciprocal_forces :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_two_prime_reciprocal_forces
  prime_floor_two_prime_reciprocal_forces_from_split :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_split
  prime_floor_prime_reciprocal_witness_globalizes_split_iff_two_prime_reciprocal_forces :=
    PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_iff_two_prime_reciprocal_forces
  prime_identity_trace_coherence_from_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_no_mixed_prime_orientation
  prime_no_mixed_prime_orientation_iff_trace_coherence :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_iff_trace_coherence
  prime_no_mixed_prime_witnesses_iff_trace_coherence :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_trace_coherence
  coherent_prime_orientation_from_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_no_mixed_prime_witnesses
  no_mixed_prime_witnesses_from_coherent_prime_orientation :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_coherent_prime_orientation
  no_mixed_prime_witnesses_iff_coherent_prime_orientation :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_coherent_prime_orientation
  two_prime_branch_controls_target_refuted :=
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_refuted
  two_prime_branch_controls_from_coherent_prime_orientation :=
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_coherent_prime_orientation
  coherent_prime_orientation_from_two_prime_branch_controls :=
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_two_prime_branch_controls
  coherent_prime_orientation_iff_two_prime_branch_controls :=
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_iff_two_prime_branch_controls
  prime_identity_iff_two_prime_identity_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_refuted
  prime_identity_forces_two_prime_identity_target_refuted :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_refuted
  two_prime_reciprocal_excludes_prime_identity_target_refuted :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_refuted
  two_prime_reciprocal_forces_prime_reciprocal_target_refuted :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_refuted
  two_prime_reciprocal_trace_connected_target_refuted :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_refuted
  two_prime_identity_trace_connected_target_refuted :=
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_refuted
  prime_identity_iff_two_from_two_prime_branch_controls :=
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_two_prime_branch_controls
  two_prime_branch_controls_from_prime_identity_iff_two :=
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_prime_identity_iff_two
  two_prime_branch_controls_iff_prime_identity_iff_two :=
    PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_iff_prime_identity_iff_two
  prime_identity_forces_two_from_identity_iff_two_target :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_identity_iff_two
  prime_identity_iff_two_from_identity_forces_two_target :=
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_identity_forces_two
  prime_identity_iff_two_iff_identity_forces_two :=
    PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_iff_identity_forces_two
  two_prime_reciprocal_excludes_from_identity_forces_two_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_identity_forces_two
  prime_identity_forces_two_from_two_prime_reciprocal_excludes_target :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
  prime_identity_forces_two_target_iff_two_prime_reciprocal_excludes :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes
  two_prime_reciprocal_excludes_from_two_prime_reciprocal_forces_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces
  two_prime_reciprocal_forces_from_two_prime_reciprocal_excludes_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_two_prime_reciprocal_excludes
  two_prime_reciprocal_excludes_target_iff_two_prime_reciprocal_forces :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_two_prime_reciprocal_forces
  two_prime_reciprocal_forces_from_identity_forces_two_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_identity_forces_two
  prime_identity_forces_two_from_two_prime_reciprocal_forces_target :=
    PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_forces
  two_prime_reciprocal_forces_target_iff_identity_forces_two :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_iff_identity_forces_two
  two_prime_reciprocal_forces_from_trace_connected_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_trace_connected
  two_prime_reciprocal_trace_connected_from_forces_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_forces
  two_prime_reciprocal_trace_connected_target_iff_forces :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_forces
  two_prime_reciprocal_trace_connected_from_identity_trace_connected_target :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_identity_trace_connected
  two_prime_identity_trace_connected_from_reciprocal_trace_connected_target :=
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_reciprocal_trace_connected
  two_prime_reciprocal_trace_connected_target_iff_identity_trace_connected :=
    PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_identity_trace_connected
  two_prime_identity_trace_connected_from_prime_identity_trace_transport_target :=
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_prime_identity_trace_transport
  prime_identity_trace_transport_from_two_prime_identity_trace_connected_target :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_two_prime_identity_trace_connected
  two_prime_identity_trace_connected_target_iff_prime_identity_trace_transport :=
    PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_iff_prime_identity_trace_transport
  prime_floor_no_mixed_prime_witnesses_from_nonunit_no_mixed_witnesses :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_nonunit_no_mixed_witnesses
  prime_floor_nonunit_no_mixed_witnesses_split_from_nonunit_no_mixed_witnesses :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_nonunit_no_mixed_witnesses
  prime_floor_nonunit_no_mixed_witnesses_from_split :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_split
  prime_floor_nonunit_no_mixed_witnesses_iff_split :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_split
  prime_floor_prime_witnesses_control_from_mixed_reflects :=
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_of_mixed_reflects
  prime_floor_mixed_reflects_from_prime_witnesses_control :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_prime_control
  prime_floor_prime_witnesses_control_iff_mixed_reflects :=
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_iff_mixed_reflects
  prime_floor_mixed_reflection_split_from_reflects :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_of_reflects
  prime_floor_mixed_reflection_from_split :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_split
  prime_floor_mixed_reflection_iff_split :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_iff_split
  prime_floor_mixed_identity_reflects_prime_proved :=
    PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget_proved
  prime_floor_mixed_reciprocal_reflects_prime_proved :=
    PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget_proved
  prime_floor_mixed_reflection_split_proved :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_proved
  prime_floor_mixed_reflection_proved :=
    PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_proved
  prime_floor_prime_witnesses_control_nonunit_proved :=
    PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_proved
  prime_floor_nonunit_no_mixed_split_from_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_no_mixed_prime_witnesses
  prime_floor_nonunit_no_mixed_from_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_no_mixed_prime_witnesses
  prime_floor_nonunit_no_mixed_iff_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_no_mixed_prime_witnesses
  prime_floor_identity_witness_globalizes_from_local_exclusion :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_local_exclusion
  prime_floor_identity_witness_local_exclusion_from_globalizes :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_of_identity_witness_globalizes
  prime_floor_identity_witness_globalizes_iff_local_exclusion :=
    PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_local_exclusion
  prime_floor_nonunit_identity_comparable_trace_from_branch_transport :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_branch_transport
  prime_floor_nonunit_identity_comparable_trace_from_product_no_mixed :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_product_no_mixed
  prime_floor_nonunit_identity_branch_transport_iff_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_iff_comparable_trace
  prime_floor_product_no_mixed_iff_identity_comparable_trace :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_comparable_trace
  prime_floor_product_local_orientation_from_identity_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_of_identity_comparable_trace
  prime_floor_nonunit_local_orientation_from_identity_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_identity_comparable_trace
  prime_floor_nonunit_local_comparable_trace_from_identity_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_identity_comparable_trace
  prime_floor_nonunit_identity_comparable_trace_from_local_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_local_comparable_trace
  prime_floor_nonunit_local_comparable_trace_iff_identity_comparable_trace :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_iff_identity_comparable_trace
  prime_floor_nonunit_local_no_mixed_from_coherent :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_of_coherent
  prime_floor_nonunit_coherent_from_local_no_mixed :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_no_mixed
  prime_floor_nonunit_orbit_orientation_coherent_iff_local_no_mixed :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_local_no_mixed
  prime_floor_nonunit_orbit_orientation_coherent_sharpened_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget_refuted
  prime_floor_nonunit_orbit_orientation_coherent_from_local_successor_transport :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_and_prime_floor_successor_transport
  prime_floor_product_no_mixed_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_nonunit_coherent
  prime_floor_nonunit_local_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_nonunit_coherent
  prime_floor_no_adjacent_mixed_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_of_nonunit_coherent
  prime_floor_no_adjacent_mixed_from_successor_transport :=
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_of_successor_transport
  prime_floor_successor_transport_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_nonunit_coherent
  prime_floor_nonunit_identity_comparable_trace_from_successor_transport :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_floor_successor_transport
  prime_floor_nonunit_orbit_orientation_sharpened_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget_of_nonunit_coherent
  prime_floor_nonunit_orbit_orientation_coherent_iff_sharpened :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_sharpened
  prime_floor_successor_transport_from_identity_comparable_trace :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_identity_comparable_trace
  prime_floor_identity_extends_successor_step_from_successor_transport :=
    PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_of_successor_transport
  prime_floor_identity_contracts_successor_step_from_successor_transport :=
    PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_of_successor_transport
  prime_floor_identity_successor_step_pair_from_successor_transport :=
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_successor_transport
  prime_floor_successor_transport_from_successor_step_pair :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_successor_step_pair
  prime_floor_successor_transport_iff_successor_step_pair :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_successor_step_pair
  target_prime_identity_witness_globalizes_nonunit_from_successor_transport :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_prime_floor_successor_transport
  target_prime_floor_successor_transport_from_prime_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_prime_identity_witness_globalizes
  target_prime_floor_successor_transport_iff_prime_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_prime_identity_witness_globalizes
  target_prime_identity_witness_globalizes_nonunit_from_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_no_mixed_prime_witnesses
  target_no_mixed_prime_witnesses_from_prime_identity_witness_globalizes :=
    PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_identity_witness_globalizes
  target_prime_identity_witness_globalizes_nonunit_iff_no_mixed_prime_witnesses :=
    PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_iff_no_mixed_prime_witnesses
  prime_floor_identity_successor_step_pair_from_identity_comparable_trace :=
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_identity_comparable_trace
  prime_floor_nonunit_identity_comparable_trace_from_successor_step_pair :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_successor_step_pair
  prime_floor_nonunit_identity_comparable_trace_iff_successor_step_pair :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_successor_step_pair
  prime_floor_product_no_mixed_from_successor_step_pair :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_successor_step_pair
  prime_floor_identity_successor_step_pair_from_product_no_mixed :=
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_product_no_mixed
  prime_floor_product_no_mixed_iff_successor_step_pair :=
    PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_successor_step_pair
  prime_floor_nonunit_coherent_from_successor_step_pair :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_successor_step_pair
  prime_floor_identity_successor_step_pair_from_nonunit_coherent :=
    PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_nonunit_coherent
  prime_floor_nonunit_coherent_iff_successor_step_pair :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_successor_step_pair
  prime_floor_nonunit_identity_comparable_trace_iff_successor_transport :=
    PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_prime_floor_successor_transport
  prime_floor_successor_transport_local_adjacent_target_refuted :=
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_refuted
  prime_floor_successor_transport_from_local_adjacent_target :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_target
  prime_floor_local_adjacent_from_local_successor_transport :=
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_of_local_successor_transport
  prime_floor_local_adjacent_iff_local_successor_transport :=
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_local_successor_transport
  prime_floor_local_adjacent_from_nonunit_coherent :=
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_of_nonunit_coherent
  prime_floor_nonunit_coherent_from_local_adjacent :=
    PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_adjacent
  prime_floor_local_adjacent_iff_nonunit_coherent :=
    PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_nonunit_coherent
  prime_floor_product_local_orientation_sharpened_target_refuted :=
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget_refuted
  prime_floor_product_local_orientation_from_display_nomix :=
    PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_of_display_compatible_nomix
  prime_floor_nonunit_local_orientation_from_product_local :=
    PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_product_local_orientation
  prime_floor_no_adjacent_mixed_orientation_target_refuted :=
    PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_refuted
  prime_floor_successor_transport_sharpened_target_refuted :=
    PRCPrimeFloorSuccessorTransportSharpenedTarget_refuted
  prime_floor_successor_transport_target_from_local_adjacent_nomix :=
    PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_local_adjacent_nomix
  orbit_successor_transport_target_from_additive_compat :=
    PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget_of_additive_compat
  prime_identity_comparable_trace_from_prime_floor_successor_transport :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_prime_floor_successor_transport
  orbit_successor_identity_target_from_transport :=
    PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_of_transport
  prime_identity_comparable_trace_from_successor_step :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_successor_step
  prime_identity_common_trace_extension_from_comparable_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_comparable_trace
  prime_identity_canonical_add_trace_from_common_trace_target :=
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_common_trace_extension
  prime_identity_common_trace_from_canonical_add_trace_target :=
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_canonical_add_trace
  prime_identity_canonical_add_trace_target_iff_common_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_iff_common_trace_extension
  prime_identity_canonical_add_trace_from_trace_transport_target :=
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_trace_transport
  prime_identity_trace_transport_from_canonical_add_trace_target :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_canonical_add_trace
  prime_identity_canonical_add_trace_target_iff_trace_transport :=
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_iff_trace_transport
  prime_identity_branch_uniformity_from_trace_coherence_target :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_trace_coherence
  prime_identity_trace_coherence_from_branch_uniformity_target :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_branch_uniformity
  prime_identity_branch_uniformity_target_iff_trace_coherence :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_trace_coherence
  prime_identity_canonical_add_trace_from_branch_uniformity_target :=
    PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_branch_uniformity
  prime_identity_branch_uniformity_from_canonical_add_trace_target :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_canonical_add_trace
  prime_identity_branch_uniformity_target_iff_canonical_add_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_canonical_add_trace
  prime_identity_trace_transport_from_common_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_common_trace_extension
  prime_identity_trace_coherence_from_transport :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_trace_transport
  target_prime_identity_comparable_trace_from_trace_coherence :=
    PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_trace_coherence
  target_prime_identity_trace_coherence_from_comparable_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_comparable_trace
  target_prime_identity_trace_coherence_iff_comparable_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_comparable_trace
  target_prime_identity_common_trace_from_trace_coherence :=
    PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_trace_coherence
  target_prime_identity_trace_coherence_from_common_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_common_trace_extension
  target_prime_identity_trace_coherence_iff_common_trace :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_common_trace_extension
  target_prime_identity_trace_transport_from_trace_coherence :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_trace_coherence
  target_prime_identity_trace_coherence_iff_trace_transport :=
    PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_trace_transport
  prime_no_mixed_from_trace_coherence :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_trace_coherence
  prime_no_mixed_prime_orientation_from_branch_uniformity :=
    PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_branch_uniformity
  prime_identity_branch_uniformity_from_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_mixed_prime_orientation
  prime_identity_branch_uniformity_iff_no_mixed_prime_orientation :=
    PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_mixed_prime_orientation
  coherent_prime_orientation_reduction :=
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_local_and_nomixed
  prime_to_coherent_orientation_target_refuted :=
    PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_refuted
  coherent_prime_orientation_propagation_target_refuted :=
    PRCCoherentPrimeOrientationPropagatesToGlobalTarget_refuted
  admissible_prime_orientation_coherent_target :=
    PRCAdmissibleCharacterPrimeOrientationCoherentTarget_proved
  admissible_signed_unit_calibration_target_refuted :=
    PRCAdmissibleCharacterSignedUnitCalibratedTarget_refuted
  signed_coherent_prime_orientation_propagation_target :=
    PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget_proved
  global_orientation_reduction :=
    PRCPrimeCalibrationForcesGlobalOrientationTarget_of_prime_orientation_targets
  prime_propagation_sharpened_target_refuted :=
    PRCPrimeCalibrationPropagationSharpenedTarget_refuted
  prime_propagation_reduction :=
    PRCPrimeCalibrationPropagationTarget_of_global_orientation
  prime_propagation_sharpened_reduction :=
    PRCPrimeCalibrationPropagationTarget_of_sharpened_orientation
  rigidity_sharpened_target_refuted :=
    PRCNativeCostCharacterRigiditySharpenedTarget_refuted
  rigidity_reduction := PRCNativeCostCharacterRigidityTarget_of_prime_targets
  identity_character := identity_ratio_character
  identity_rigid := identity_character_rigid
  identity_orientation := identity_character_global_orientation
  identity_prime_orientation_coherent :=
    identity_character_prime_orientation_coherent
  reciprocal_character := reciprocal_ratio_character
  reciprocal_prime_calibrated := reciprocal_character_prime_calibrated
  reciprocal_orientation := reciprocal_character_global_orientation
  reciprocal_prime_orientation_coherent :=
    reciprocal_character_prime_orientation_coherent
  sharpened_target := PRCNativeCostUniquenessSharpenedTarget_refuted
  reduction := PRCNativeCostUniquenessTarget_of_character_targets
  prime_reduction := PRCNativeCostUniquenessTarget_of_prime_character_targets
  original_target := PRCNativeCostUniquenessTarget_refuted
  original_target_refuted := PRCNativeCostUniquenessTarget_refuted
  strength_tag := rfl

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
