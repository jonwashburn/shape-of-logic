/-
  PrimitiveRecognitionCalculus/RealCauchy.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 8: start the internal PRC real completion by forming
    Cauchy ledgers over `PRCRat`, a J-cost-derived closeness relation, and the
    first internal quotient carrier.

  Strength: δ + trace-closure. The completed sequence index is the completed
  orbit ledger from `TraceClosure`; verifier rationals appear only in display
  theorems and proofs.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RationalField
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.TraceClosure

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

namespace PRCRat

/-! ## Rational comparison surface used by Cauchy ledgers -/

/-- PRC-native strict order on rationals: `a < b` means the positive gap
`b - a` has a positive ratio-orbit representative. -/
def lt (a b : PRCRat) : Prop :=
  positive (b - a)

theorem lt_iff_toRat_lt (a b : PRCRat) :
    lt a b ↔ a.toRat < b.toRat := by
  unfold lt
  rw [positive_iff_toRat_pos]
  rw [PRCRat.sub_eq, PRCRat.toRat_sub]
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem zero_lt_of_positive {q : PRCRat}
    (h : positive q) : lt 0 q := by
  rw [lt_iff_toRat_lt]
  simpa using (positive_iff_toRat_pos q).mp h

end PRCRat

/-! ## J-cost-derived distance on PRC rationals -/

/-- A positive comparison gap for additive rational separation. The square
removes the need for a rational absolute value in this first Cauchy pass. -/
def PRCSquareGap (a b : PRCRat) : PRCRat :=
  1 + (a - b) * (a - b)

theorem PRCSquareGap_toRat (a b : PRCRat) :
    (PRCSquareGap a b).toRat = 1 + (a.toRat - b.toRat) * (a.toRat - b.toRat) := by
  unfold PRCSquareGap
  rw [PRCRat.toRat_add', PRCRat.toRat_mul']
  simp [PRCRat.sub_eq]

/-- J-cost distance used by the first PRC Cauchy surface. It sends additive
separation through the positive ratio `1 + (a-b)^2`, then applies the PRC
rational J-cost. -/
def PRCJCostDistance (a b : PRCRat) : PRCRat :=
  PRCJCost.onPRCRat (PRCSquareGap a b)

theorem PRCJCostDistance_self_zero (a : PRCRat) :
    PRCJCostDistance a a = 0 := by
  apply PRCRat.toRat_injective
  unfold PRCJCostDistance
  rw [PRCJCost.onPRCRat_toRat, PRCSquareGap_toRat]
  simp

theorem PRCJCostDistance_symmetric (a b : PRCRat) :
    PRCJCostDistance a b = PRCJCostDistance b a := by
  apply PRCRat.toRat_injective
  unfold PRCJCostDistance
  rw [PRCJCost.onPRCRat_toRat, PRCJCost.onPRCRat_toRat,
    PRCSquareGap_toRat, PRCSquareGap_toRat]
  ring

/-! ## PRC Cauchy ledgers -/

/-- A PRC Cauchy sequence is a completed orbit-indexed rational ledger whose
J-cost distance eventually falls below every positive PRC rational tolerance. -/
structure PRCCauchySeq where
  term : Nat → PRCRat
  cauchy :
    ∀ eps : PRCRat, PRCRat.positive eps →
      ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
        PRCRat.lt (PRCJCostDistance (term m) (term n)) eps

namespace PRCCauchySeq

/-- Constant rational ledgers are Cauchy. -/
def constant (q : PRCRat) : PRCCauchySeq where
  term := fun _ => q
  cauchy := by
    intro eps heps
    refine ⟨0, ?_⟩
    intro m n _hm _hn
    rw [PRCJCostDistance_self_zero]
    exact PRCRat.zero_lt_of_positive heps

@[simp] theorem constant_term (q : PRCRat) (n : Nat) :
    (constant q).term n = q := by
  rfl

end PRCCauchySeq

/-- The intended null-distance relation between two Cauchy ledgers. This is
the relation that should become the final real quotient once transitivity is
proved from the J-cost distance surface. -/
def PRCNullEquivalent (u v : PRCCauchySeq) : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      PRCRat.lt (PRCJCostDistance (u.term n) (v.term n)) eps

theorem PRCNullEquivalent.refl (u : PRCCauchySeq) :
    PRCNullEquivalent u u := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro n _hn
  rw [PRCJCostDistance_self_zero]
  exact PRCRat.zero_lt_of_positive heps

theorem PRCNullEquivalent.symm {u v : PRCCauchySeq}
    (h : PRCNullEquivalent u v) : PRCNullEquivalent v u := by
  intro eps heps
  rcases h eps heps with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [PRCJCostDistance_symmetric]
  exact hN n hn

/-- Exact blocker for the final null-distance quotient: prove triangle-style
transitivity for the J-cost distance surface. -/
def PRCNullDistanceTransitiveTarget : Prop :=
  ∀ u v w : PRCCauchySeq,
    PRCNullEquivalent u v →
      PRCNullEquivalent v w →
        PRCNullEquivalent u w

/-- Exact target that turns the intended null-distance relation into the real
setoid. Reflexivity and symmetry are proved above; transitivity is the live
mathematical obligation. -/
def PRCNullDistanceSetoidTarget : Prop :=
  Equivalence PRCNullEquivalent

/-! ## First internal quotient carrier -/

/-- Sequence identity, used only as the first quotient carrier while the
null-distance transitivity target remains open. -/
def PRCSameTerm (u v : PRCCauchySeq) : Prop :=
  ∀ n : Nat, u.term n = v.term n

theorem PRCSameTerm.equivalence : Equivalence PRCSameTerm := by
  constructor
  · intro u n
    rfl
  · intro u v h n
    exact (h n).symm
  · intro u v w huv hvw n
    exact (huv n).trans (hvw n)

/-- The first internal setoid available without the null-distance triangle
lemma. It is intentionally stronger than the final null-distance setoid. -/
def PRCSameTermSetoid : Setoid PRCCauchySeq where
  r := PRCSameTerm
  iseqv := PRCSameTerm.equivalence

/-- First internal PRC real carrier. It is a Cauchy-ledger quotient, not Lean
`ℝ`; the final quotient relation is recorded as `PRCNullDistanceSetoidTarget`. -/
def PRCReal : Type :=
  Quot PRCSameTermSetoid

namespace PRCReal

/-- Embed a PRC rational as a constant Cauchy ledger. -/
def ofRat (q : PRCRat) : PRCReal :=
  Quot.mk PRCSameTermSetoid (PRCCauchySeq.constant q)

end PRCReal

/-- K1/R9. Audit record: internal Cauchy real ledgers require trace closure. -/
def realCauchyClaim : StrengthClaim where
  label := "BuildOrder8_real_cauchy_internal_quotient"
  tag := StrengthTag.traceClosure
  statement :=
    "PRC Cauchy ledgers and their first internal quotient use completed orbit indexing."

/-- First-pass real Cauchy certificate. The carrier is internal and
trace-closure tagged. The final null-distance quotient is left as an exact
Lean target rather than hidden behind a classical real alias. -/
structure PRCRealCauchyCertificate : Prop where
  cauchy_sequences : Nonempty PRCCauchySeq
  constant_embedding_exists : Nonempty (PRCRat → PRCCauchySeq)
  jcost_distance_self_zero :
    ∀ q : PRCRat, PRCJCostDistance q q = 0
  null_relation_reflexive :
    ∀ u : PRCCauchySeq, PRCNullEquivalent u u
  null_relation_symmetric :
    ∀ u v : PRCCauchySeq, PRCNullEquivalent u v → PRCNullEquivalent v u
  same_term_setoid : Nonempty (Setoid PRCCauchySeq)
  real_quotient : Nonempty PRCReal
  rat_embedding : Nonempty (PRCRat → PRCReal)
  null_transitivity_target :
    PRCNullDistanceTransitiveTarget = PRCNullDistanceTransitiveTarget
  null_setoid_target :
    PRCNullDistanceSetoidTarget = PRCNullDistanceSetoidTarget
  strength_tag : realCauchyClaim.tag = StrengthTag.traceClosure

/-- Build Order step 8, first pass: internal Cauchy ledgers and an internal
quotient carrier exist, with the exact null-distance setoid target named. -/
theorem real_cauchy_certificate : PRCRealCauchyCertificate where
  cauchy_sequences := ⟨PRCCauchySeq.constant 0⟩
  constant_embedding_exists := ⟨PRCCauchySeq.constant⟩
  jcost_distance_self_zero := PRCJCostDistance_self_zero
  null_relation_reflexive := PRCNullEquivalent.refl
  null_relation_symmetric := by
    intro u v h
    exact PRCNullEquivalent.symm h
  same_term_setoid := ⟨PRCSameTermSetoid⟩
  real_quotient := ⟨PRCReal.ofRat 0⟩
  rat_embedding := ⟨PRCReal.ofRat⟩
  null_transitivity_target := rfl
  null_setoid_target := rfl
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
