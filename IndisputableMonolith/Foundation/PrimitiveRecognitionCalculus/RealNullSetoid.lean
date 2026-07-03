/-
  PrimitiveRecognitionCalculus/RealNullSetoid.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 9: promote the first Cauchy-ledger carrier toward the
    final null-distance quotient.

  This pass isolates the exact analytic blocker. The quotient bookkeeping is
  closed conditionally: a local triangle modulus for `PRCJCostDistance` implies
  `PRCNullEquivalent` is transitive, hence a setoid.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCauchy

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Exact analytic blocker for the null-distance quotient. It says the
J-cost-derived rational distance has a local triangle modulus: for each
positive tolerance there is a positive smaller tolerance so that two small
legs force the composed leg below the original tolerance. -/
def PRCJCostDistanceTriangleModulusTarget : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ delta : PRCRat, PRCRat.positive delta ∧
      ∀ a b c : PRCRat,
        PRCRat.lt (PRCJCostDistance a b) delta →
          PRCRat.lt (PRCJCostDistance b c) delta →
            PRCRat.lt (PRCJCostDistance a c) eps

/-- The analytic triangle modulus is sufficient for null-distance
transitivity. All remaining work here is completed-orbit index bookkeeping. -/
theorem PRCNullDistanceTransitiveTarget_of_triangle_modulus
    (htri : PRCJCostDistanceTriangleModulusTarget) :
    PRCNullDistanceTransitiveTarget := by
  intro u v w huv hvw eps heps
  rcases htri eps heps with ⟨delta, hdelta_pos, hdelta⟩
  rcases huv delta hdelta_pos with ⟨Nuv, hNuv⟩
  rcases hvw delta hdelta_pos with ⟨Nvw, hNvw⟩
  refine ⟨max Nuv Nvw, ?_⟩
  intro n hn
  have hn_uv : Nuv ≤ n := le_trans (Nat.le_max_left Nuv Nvw) hn
  have hn_vw : Nvw ≤ n := le_trans (Nat.le_max_right Nuv Nvw) hn
  exact hdelta (u.term n) (v.term n) (w.term n)
    (hNuv n hn_uv) (hNvw n hn_vw)

/-- A transitivity proof turns `PRCNullEquivalent` into a setoid. -/
def PRCNullDistanceSetoidOfTransitive
    (htrans : PRCNullDistanceTransitiveTarget) : Setoid PRCCauchySeq where
  r := PRCNullEquivalent
  iseqv := by
    constructor
    · exact PRCNullEquivalent.refl
    · intro u v
      exact PRCNullEquivalent.symm
    · intro u v w
      exact htrans u v w

/-- Conditional final real carrier: once the analytic triangle modulus is
proved, this is the intended PRC real quotient by null distance. -/
def PRCRealNull (htrans : PRCNullDistanceTransitiveTarget) : Type :=
  Quot (PRCNullDistanceSetoidOfTransitive htrans)

namespace PRCRealNull

/-- Embed a rational as a null-distance quotient class, conditional on the
transitivity proof. -/
def ofRat (htrans : PRCNullDistanceTransitiveTarget) (q : PRCRat) :
    PRCRealNull htrans :=
  Quot.mk (PRCNullDistanceSetoidOfTransitive htrans) (PRCCauchySeq.constant q)

end PRCRealNull

/-- The exact setoid target follows from transitivity. -/
theorem PRCNullDistanceSetoidTarget_of_transitive
    (htrans : PRCNullDistanceTransitiveTarget) :
    PRCNullDistanceSetoidTarget := by
  exact (PRCNullDistanceSetoidOfTransitive htrans).iseqv

/-- The exact setoid target follows from the sharper triangle-modulus target. -/
theorem PRCNullDistanceSetoidTarget_of_triangle_modulus
    (htri : PRCJCostDistanceTriangleModulusTarget) :
    PRCNullDistanceSetoidTarget :=
  PRCNullDistanceSetoidTarget_of_transitive
    (PRCNullDistanceTransitiveTarget_of_triangle_modulus htri)

/-- K1/R9. Audit record: the final null-distance quotient still lives under
trace closure; the open obligation is analytic, not a new primitive. -/
def realNullSetoidClaim : StrengthClaim where
  label := "BuildOrder9_real_null_distance_setoid"
  tag := StrengthTag.traceClosure
  statement :=
    "The PRC real null-distance setoid follows from the J-cost distance triangle modulus."

/-- Conditional certificate for Build Order step 9. It records the precise
remaining theorem and proves that this theorem is sufficient to construct the
null-distance setoid and quotient carrier. -/
structure PRCRealNullSetoidConditionalCertificate : Prop where
  triangle_modulus_target :
    PRCJCostDistanceTriangleModulusTarget = PRCJCostDistanceTriangleModulusTarget
  transitive_from_triangle :
    PRCJCostDistanceTriangleModulusTarget → PRCNullDistanceTransitiveTarget
  setoid_from_transitive :
    PRCNullDistanceTransitiveTarget → PRCNullDistanceSetoidTarget
  setoid_from_triangle :
    PRCJCostDistanceTriangleModulusTarget → PRCNullDistanceSetoidTarget
  quotient_from_transitive :
    ∀ htrans : PRCNullDistanceTransitiveTarget, Nonempty (PRCRealNull htrans)
  rat_embedding_from_transitive :
    ∀ htrans : PRCNullDistanceTransitiveTarget, Nonempty (PRCRat → PRCRealNull htrans)
  strength_tag : realNullSetoidClaim.tag = StrengthTag.traceClosure

/-- Build Order step 9 conditional closure: no quotient mechanics remain once
the local J-cost triangle modulus is proved. -/
theorem real_null_setoid_conditional_certificate :
    PRCRealNullSetoidConditionalCertificate where
  triangle_modulus_target := rfl
  transitive_from_triangle := PRCNullDistanceTransitiveTarget_of_triangle_modulus
  setoid_from_transitive := PRCNullDistanceSetoidTarget_of_transitive
  setoid_from_triangle := PRCNullDistanceSetoidTarget_of_triangle_modulus
  quotient_from_transitive := by
    intro htrans
    exact ⟨PRCRealNull.ofRat htrans 0⟩
  rat_embedding_from_transitive := by
    intro htrans
    exact ⟨PRCRealNull.ofRat htrans⟩
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
