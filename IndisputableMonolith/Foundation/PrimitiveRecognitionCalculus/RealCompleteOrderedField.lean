/-
  PrimitiveRecognitionCalculus/RealCompleteOrderedField.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10: start the complete ordered field surface over the
    closed null-distance quotient `PRCRealNullClosed`.

  This pass does not alias the carrier to Lean `ℝ`. It exposes the exact
  quotient-algebra blockers for addition, multiplication, negation, and order.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCostDistanceIncrementTriangle

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Raw completed-orbit rational ledger, before a Cauchy proof is attached. -/
abbrev PRCRawRatLedger := Nat → PRCRat

/-- Cauchy predicate on raw ledgers, using the same J-cost distance as
`PRCCauchySeq`. -/
def PRCRawCauchy (s : PRCRawRatLedger) : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      PRCRat.lt (PRCJCostDistance (s m) (s n)) eps

/-- Null equivalence on raw ledgers. -/
def PRCRawNullEquivalent (s t : PRCRawRatLedger) : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      PRCRat.lt (PRCJCostDistance (s n) (t n)) eps

namespace PRCCauchySeq

/-- Forget a Cauchy ledger to its raw rational ledger. -/
def raw (u : PRCCauchySeq) : PRCRawRatLedger :=
  u.term

theorem raw_cauchy (u : PRCCauchySeq) : PRCRawCauchy u.raw :=
  u.cauchy

@[simp] theorem raw_apply (u : PRCCauchySeq) (n : Nat) :
    u.raw n = u.term n := rfl

end PRCCauchySeq

/-- Pointwise addition of raw ledgers. -/
def PRCRawAdd (u v : PRCRawRatLedger) : PRCRawRatLedger :=
  fun n => u n + v n

/-- Pointwise negation of raw ledgers. -/
def PRCRawNeg (u : PRCRawRatLedger) : PRCRawRatLedger :=
  fun n => -u n

/-- Pointwise multiplication of raw ledgers. -/
def PRCRawMul (u v : PRCRawRatLedger) : PRCRawRatLedger :=
  fun n => u n * v n

/-- Pointwise non-strict order candidate for raw ledgers. -/
def PRCRawEventuallyLe (u v : PRCRawRatLedger) : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      PRCRat.lt (u n) (v n + eps)

/-- J-cost distance is invariant under translating both endpoints on the
right. -/
theorem PRCJCostDistance_add_right (a b c : PRCRat) :
    PRCJCostDistance (a + c) (b + c) = PRCJCostDistance a b := by
  apply PRCRat.toRat_injective
  rw [PRCJCostDistance_toRat, PRCJCostDistance_toRat]
  simp [PRCJCostDistanceRatDisplay]

/-- J-cost distance is invariant under translating both endpoints on the left. -/
theorem PRCJCostDistance_add_left (a b c : PRCRat) :
    PRCJCostDistance (c + a) (c + b) = PRCJCostDistance a b := by
  apply PRCRat.toRat_injective
  rw [PRCJCostDistance_toRat, PRCJCostDistance_toRat]
  simp [PRCJCostDistanceRatDisplay]

/-- J-cost distance is invariant under negating both endpoints. -/
theorem PRCJCostDistance_neg_neg (a b : PRCRat) :
    PRCJCostDistance (-a) (-b) = PRCJCostDistance a b := by
  apply PRCRat.toRat_injective
  rw [PRCJCostDistance_toRat, PRCJCostDistance_toRat]
  simp [PRCJCostDistanceRatDisplay]
  ring_nf

/-- Exact blocker for addition: pointwise sums of Cauchy ledgers are Cauchy. -/
def PRCRealAddClosureTarget : Prop :=
  ∀ u v : PRCCauchySeq, PRCRawCauchy (PRCRawAdd u.raw v.raw)

/-- Exact blocker for additive quotient well-definedness under null distance. -/
def PRCRealAddCongruenceTarget : Prop :=
  ∀ u u' v v' : PRCCauchySeq,
    PRCNullEquivalent u u' →
      PRCNullEquivalent v v' →
        PRCRawNullEquivalent
          (PRCRawAdd u.raw v.raw)
          (PRCRawAdd u'.raw v'.raw)

/-- Exact blocker for negation: pointwise negations of Cauchy ledgers are
Cauchy. -/
def PRCRealNegClosureTarget : Prop :=
  ∀ u : PRCCauchySeq, PRCRawCauchy (PRCRawNeg u.raw)

/-- Exact blocker for negation quotient well-definedness. -/
def PRCRealNegCongruenceTarget : Prop :=
  ∀ u v : PRCCauchySeq,
    PRCNullEquivalent u v →
      PRCRawNullEquivalent (PRCRawNeg u.raw) (PRCRawNeg v.raw)

/-- Exact blocker for multiplication: pointwise products of Cauchy ledgers are
Cauchy. This is expected to require a boundedness lemma for Cauchy ledgers. -/
def PRCRealMulClosureTarget : Prop :=
  ∀ u v : PRCCauchySeq, PRCRawCauchy (PRCRawMul u.raw v.raw)

/-- Exact blocker for multiplicative quotient well-definedness under null
distance. This is also expected to require eventual boundedness. -/
def PRCRealMulCongruenceTarget : Prop :=
  ∀ u u' v v' : PRCCauchySeq,
    PRCNullEquivalent u u' →
      PRCNullEquivalent v v' →
        PRCRawNullEquivalent
          (PRCRawMul u.raw v.raw)
          (PRCRawMul u'.raw v'.raw)

/-- Exact blocker for the order relation descending to the null-distance
quotient. -/
def PRCRealOrderCongruenceTarget : Prop :=
  ∀ u u' v v' : PRCCauchySeq,
    PRCNullEquivalent u u' →
      PRCNullEquivalent v v' →
        (PRCRawEventuallyLe u.raw v.raw ↔
          PRCRawEventuallyLe u'.raw v'.raw)

/-- Quantitative closeness for two raw ledgers at a fixed PRC tolerance. -/
def PRCRawEventuallyClose (s t : PRCRawRatLedger) (eps : PRCRat) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n →
    PRCRat.lt (PRCJCostDistance (s n) (t n)) eps

/-- A sequence of Cauchy ledgers is Cauchy as a sequence of null-quotient
representatives when its representative tails are eventually close at every
positive PRC tolerance. -/
def PRCRealRepresentativeCauchy (U : Nat → PRCCauchySeq) : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      PRCRawEventuallyClose (U m).raw (U n).raw eps

/-- A Cauchy ledger `L` is a representative limit of a sequence of null-quotient
representatives. -/
def PRCRealRepresentativeLimit (U : Nat → PRCCauchySeq)
    (L : PRCCauchySeq) : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      PRCRawEventuallyClose (U n).raw L.raw eps

/-- Exact blocker for completeness of the internal null quotient. This is the
diagonal theorem: every Cauchy sequence of Cauchy-ledger representatives has a
Cauchy-ledger representative limit. -/
def PRCRealCompletenessTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    PRCRealRepresentativeCauchy U →
      ∃ L : PRCCauchySeq, PRCRealRepresentativeLimit U L

/-- Pointwise sums of Cauchy ledgers are Cauchy. -/
theorem PRCRealAddClosureTarget_proved : PRCRealAddClosureTarget := by
  intro u v eps heps
  rcases PRCJCostDistanceTriangleModulusTarget_proved eps heps with
    ⟨delta, hdelta_pos, hdelta⟩
  rcases u.cauchy delta hdelta_pos with ⟨Nu, hNu⟩
  rcases v.cauchy delta hdelta_pos with ⟨Nv, hNv⟩
  refine ⟨max Nu Nv, ?_⟩
  intro m n hm hn
  have hmu : Nu ≤ m := le_trans (Nat.le_max_left Nu Nv) hm
  have hnu : Nu ≤ n := le_trans (Nat.le_max_left Nu Nv) hn
  have hmv : Nv ≤ m := le_trans (Nat.le_max_right Nu Nv) hm
  have hnv : Nv ≤ n := le_trans (Nat.le_max_right Nu Nv) hn
  exact hdelta
    ((u.term m) + (v.term m))
    ((u.term n) + (v.term m))
    ((u.term n) + (v.term n))
    (by
      rw [PRCJCostDistance_add_right]
      exact hNu m n hmu hnu)
    (by
      rw [PRCJCostDistance_add_left]
      exact hNv m n hmv hnv)

/-- Pointwise negations of Cauchy ledgers are Cauchy. -/
theorem PRCRealNegClosureTarget_proved : PRCRealNegClosureTarget := by
  intro u eps heps
  rcases u.cauchy eps heps with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hm hn
  change PRCRat.lt (PRCJCostDistance (-(u.term m)) (-(u.term n))) eps
  rw [PRCJCostDistance_neg_neg]
  exact hN m n hm hn

/-- Addition respects null equivalence. -/
theorem PRCRealAddCongruenceTarget_proved :
    PRCRealAddCongruenceTarget := by
  intro u u' v v' huu hvv eps heps
  rcases PRCJCostDistanceTriangleModulusTarget_proved eps heps with
    ⟨delta, hdelta_pos, hdelta⟩
  rcases huu delta hdelta_pos with ⟨Nu, hNu⟩
  rcases hvv delta hdelta_pos with ⟨Nv, hNv⟩
  refine ⟨max Nu Nv, ?_⟩
  intro n hn
  have hnu : Nu ≤ n := le_trans (Nat.le_max_left Nu Nv) hn
  have hnv : Nv ≤ n := le_trans (Nat.le_max_right Nu Nv) hn
  exact hdelta
    ((u.term n) + (v.term n))
    ((u'.term n) + (v.term n))
    ((u'.term n) + (v'.term n))
    (by
      rw [PRCJCostDistance_add_right]
      exact hNu n hnu)
    (by
      rw [PRCJCostDistance_add_left]
      exact hNv n hnv)

/-- Negation respects null equivalence. -/
theorem PRCRealNegCongruenceTarget_proved :
    PRCRealNegCongruenceTarget := by
  intro u v huv eps heps
  rcases huv eps heps with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change PRCRat.lt (PRCJCostDistance (-(u.term n)) (-(v.term n))) eps
  rw [PRCJCostDistance_neg_neg]
  exact hN n hn

/-- Conditional construction of a pointwise-sum Cauchy ledger from the addition
closure target. -/
def PRCCauchySeq.addOf
    (hadd : PRCRealAddClosureTarget) (u v : PRCCauchySeq) : PRCCauchySeq where
  term := PRCRawAdd u.raw v.raw
  cauchy := hadd u v

/-- Conditional construction of a pointwise-negation Cauchy ledger from the
negation closure target. -/
def PRCCauchySeq.negOf
    (hneg : PRCRealNegClosureTarget) (u : PRCCauchySeq) : PRCCauchySeq where
  term := PRCRawNeg u.raw
  cauchy := hneg u

/-- Conditional construction of a pointwise-product Cauchy ledger from the
multiplication closure target. -/
def PRCCauchySeq.mulOf
    (hmul : PRCRealMulClosureTarget) (u v : PRCCauchySeq) : PRCCauchySeq where
  term := PRCRawMul u.raw v.raw
  cauchy := hmul u v

/-- Conditional addition on the closed null quotient. -/
noncomputable def PRCRealNullClosed.addOf
    (hadd : PRCRealAddClosureTarget)
    (hcong : PRCRealAddCongruenceTarget) :
    PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed :=
  Quot.lift₂
    (fun u v =>
      Quot.mk (PRCNullDistanceSetoidOfTransitive PRCNullDistanceTransitiveTarget_proved)
        (PRCCauchySeq.addOf hadd u v))
    (by
      intro u v₁ v₂ hv
      apply Quot.sound
      exact hcong u u v₁ v₂ (PRCNullEquivalent.refl u) hv)
    (by
      intro u₁ u₂ v hu
      apply Quot.sound
      exact hcong u₁ u₂ v v hu (PRCNullEquivalent.refl v))

/-- Conditional negation on the closed null quotient. -/
noncomputable def PRCRealNullClosed.negOf
    (hneg : PRCRealNegClosureTarget)
    (hcong : PRCRealNegCongruenceTarget) :
    PRCRealNullClosed → PRCRealNullClosed :=
  Quot.lift
    (fun u =>
      Quot.mk (PRCNullDistanceSetoidOfTransitive PRCNullDistanceTransitiveTarget_proved)
        (PRCCauchySeq.negOf hneg u))
    (by
      intro u v huv
      apply Quot.sound
      exact hcong u v huv)

/-- Conditional multiplication on the closed null quotient. -/
noncomputable def PRCRealNullClosed.mulOf
    (hmul : PRCRealMulClosureTarget)
    (hcong : PRCRealMulCongruenceTarget) :
    PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed :=
  Quot.lift₂
    (fun u v =>
      Quot.mk (PRCNullDistanceSetoidOfTransitive PRCNullDistanceTransitiveTarget_proved)
        (PRCCauchySeq.mulOf hmul u v))
    (by
      intro u v₁ v₂ hv
      apply Quot.sound
      exact hcong u u v₁ v₂ (PRCNullEquivalent.refl u) hv)
    (by
      intro u₁ u₂ v hu
      apply Quot.sound
      exact hcong u₁ u₂ v v hu (PRCNullEquivalent.refl v))

/-- Bundle of exact blockers for the next real-completion phase. -/
structure PRCRealCompleteOrderedFieldTargets : Prop where
  add_closure : PRCRealAddClosureTarget
  add_congruence : PRCRealAddCongruenceTarget
  neg_closure : PRCRealNegClosureTarget
  neg_congruence : PRCRealNegCongruenceTarget
  mul_closure : PRCRealMulClosureTarget = PRCRealMulClosureTarget
  mul_congruence : PRCRealMulCongruenceTarget = PRCRealMulCongruenceTarget
  order_congruence : PRCRealOrderCongruenceTarget = PRCRealOrderCongruenceTarget
  completeness : PRCRealCompletenessTarget = PRCRealCompletenessTarget

/-- Conditional first complete-ordered-field surface. It records that the
carrier and rational embedding are closed, while algebra/order/completeness are
reduced to named exact targets. -/
structure PRCRealCompleteOrderedFieldConditionalCertificate : Prop where
  carrier : Nonempty PRCRealNullClosed
  rat_embedding : Nonempty (PRCRat → PRCRealNullClosed)
  targets : PRCRealCompleteOrderedFieldTargets
  add_operation_from_targets :
    PRCRealAddClosureTarget →
      PRCRealAddCongruenceTarget →
        Nonempty (PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed)
  neg_operation_from_targets :
    PRCRealNegClosureTarget →
      PRCRealNegCongruenceTarget →
        Nonempty (PRCRealNullClosed → PRCRealNullClosed)
  mul_operation_from_targets :
    PRCRealMulClosureTarget →
      PRCRealMulCongruenceTarget →
        Nonempty (PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed)
  strength_tag : StrengthTag.traceClosure = StrengthTag.traceClosure

/-- Build Order step 10, first pass: quotient algebra is reduced to exact
closure and congruence targets. -/
theorem prc_real_complete_ordered_field_conditional_certificate :
    PRCRealCompleteOrderedFieldConditionalCertificate where
  carrier := ⟨PRCRealNullClosed.ofRat 0⟩
  rat_embedding := ⟨PRCRealNullClosed.ofRat⟩
  targets := {
    add_closure := PRCRealAddClosureTarget_proved
    add_congruence := PRCRealAddCongruenceTarget_proved
    neg_closure := PRCRealNegClosureTarget_proved
    neg_congruence := PRCRealNegCongruenceTarget_proved
    mul_closure := rfl
    mul_congruence := rfl
    order_congruence := rfl
    completeness := rfl
  }
  add_operation_from_targets := by
    intro hadd hcong
    exact ⟨PRCRealNullClosed.addOf hadd hcong⟩
  neg_operation_from_targets := by
    intro hneg hcong
    exact ⟨PRCRealNullClosed.negOf hneg hcong⟩
  mul_operation_from_targets := by
    intro hmul hcong
    exact ⟨PRCRealNullClosed.mulOf hmul hcong⟩
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
