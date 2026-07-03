/-
  PrimitiveRecognitionCalculus/RealMulBoundedContinuity.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10a: reduce multiplication on `PRCRealNullClosed` to
    boundedness and bounded product-continuity moduli.

  The object-level carrier remains the PRC null quotient. Verifier rationals
  appear only in display lemmas for analytic moduli.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCompleteOrderedField

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Eventual PRC-native boundedness for a raw rational ledger. -/
def PRCRawEventuallyBounded (s : PRCRawRatLedger) : Prop :=
  ∃ B : PRCRat, PRCRat.positive B ∧
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      PRCRat.lt (-B) (s n) ∧ PRCRat.lt (s n) B

/-- Exact boundedness target for Cauchy ledgers. -/
def PRCCauchySeqEventuallyBoundedTarget : Prop :=
  ∀ u : PRCCauchySeq, PRCRawEventuallyBounded u.raw

/-- A rational lies inside the symmetric PRC interval `[-B,B]`. -/
def PRCRat.InBound (B x : PRCRat) : Prop :=
  PRCRat.lt (-B) x ∧ PRCRat.lt x B

/-- Enlarging a symmetric PRC rational bound preserves membership in it. -/
theorem PRCRat.InBound_mono {B C x : PRCRat}
    (hCB : C.toRat ≤ B.toRat) (hx : PRCRat.InBound C x) :
    PRCRat.InBound B x := by
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · rw [PRCRat.lt_iff_toRat_lt] at hlo ⊢
    have hnegB : (-B).toRat = -B.toRat := by simp
    have hnegC : (-C).toRat = -C.toRat := by simp
    rw [hnegC] at hlo
    rw [hnegB]
    nlinarith
  · rw [PRCRat.lt_iff_toRat_lt] at hhi ⊢
    exact lt_of_lt_of_le hhi hCB

/-- Exact product-continuity modulus on bounded rational windows. This is the
local analytic input needed by Cauchy multiplication and multiplication
congruence. -/
def PRCJCostDistanceMulBoundedContinuityTarget : Prop :=
  ∀ eps B : PRCRat, PRCRat.positive eps → PRCRat.positive B →
    ∃ delta : PRCRat, PRCRat.positive delta ∧
      ∀ a a' b b' : PRCRat,
        PRCRat.InBound B a →
          PRCRat.InBound B a' →
            PRCRat.InBound B b →
              PRCRat.InBound B b' →
                PRCRat.lt (PRCJCostDistance a a') delta →
                  PRCRat.lt (PRCJCostDistance b b') delta →
                    PRCRat.lt (PRCJCostDistance (a * b) (a' * b')) eps

/-- Conditional proof of product Cauchy closure from eventual boundedness and
bounded product-continuity. -/
theorem PRCRealMulClosureTarget_of_bounded_continuity
    (hbounded : PRCCauchySeqEventuallyBoundedTarget)
    (hmul_cont : PRCJCostDistanceMulBoundedContinuityTarget) :
    PRCRealMulClosureTarget := by
  intro u v eps heps
  rcases hbounded u with ⟨Bu, hBu_pos, NuB, hNuB⟩
  rcases hbounded v with ⟨Bv, hBv_pos, NvB, hNvB⟩
  let B : PRCRat := Bu + Bv + 1
  have hB_pos : PRCRat.positive B := by
    rw [PRCRat.positive_iff_toRat_pos]
    have hBu : (0 : ℚ) < Bu.toRat := (PRCRat.positive_iff_toRat_pos Bu).mp hBu_pos
    have hBv : (0 : ℚ) < Bv.toRat := (PRCRat.positive_iff_toRat_pos Bv).mp hBv_pos
    simp [B]
    nlinarith
  have hBu_le_B : Bu.toRat ≤ B.toRat := by
    have hBv : (0 : ℚ) < Bv.toRat := (PRCRat.positive_iff_toRat_pos Bv).mp hBv_pos
    simp [B]
    nlinarith
  have hBv_le_B : Bv.toRat ≤ B.toRat := by
    have hBu : (0 : ℚ) < Bu.toRat := (PRCRat.positive_iff_toRat_pos Bu).mp hBu_pos
    simp [B]
    nlinarith
  rcases hmul_cont eps B heps hB_pos with ⟨delta, hdelta_pos, hdelta⟩
  rcases u.cauchy delta hdelta_pos with ⟨NuC, hNuC⟩
  rcases v.cauchy delta hdelta_pos with ⟨NvC, hNvC⟩
  let N := max (max NuB NvB) (max NuC NvC)
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hNuB_m : NuB ≤ m := le_trans (le_trans (Nat.le_max_left NuB NvB)
    (Nat.le_max_left (max NuB NvB) (max NuC NvC))) hm
  have hNuB_n : NuB ≤ n := le_trans (le_trans (Nat.le_max_left NuB NvB)
    (Nat.le_max_left (max NuB NvB) (max NuC NvC))) hn
  have hNvB_m : NvB ≤ m := le_trans (le_trans (Nat.le_max_right NuB NvB)
    (Nat.le_max_left (max NuB NvB) (max NuC NvC))) hm
  have hNvB_n : NvB ≤ n := le_trans (le_trans (Nat.le_max_right NuB NvB)
    (Nat.le_max_left (max NuB NvB) (max NuC NvC))) hn
  have hNuC_m : NuC ≤ m := le_trans (le_trans (Nat.le_max_left NuC NvC)
    (Nat.le_max_right (max NuB NvB) (max NuC NvC))) hm
  have hNuC_n : NuC ≤ n := le_trans (le_trans (Nat.le_max_left NuC NvC)
    (Nat.le_max_right (max NuB NvB) (max NuC NvC))) hn
  have hNvC_m : NvC ≤ m := le_trans (le_trans (Nat.le_max_right NuC NvC)
    (Nat.le_max_right (max NuB NvB) (max NuC NvC))) hm
  have hNvC_n : NvC ≤ n := le_trans (le_trans (Nat.le_max_right NuC NvC)
    (Nat.le_max_right (max NuB NvB) (max NuC NvC))) hn
  have hu_m_small : PRCRat.InBound B (u.term m) :=
    PRCRat.InBound_mono hBu_le_B (hNuB m hNuB_m)
  have hu_n_small : PRCRat.InBound B (u.term n) :=
    PRCRat.InBound_mono hBu_le_B (hNuB n hNuB_n)
  have hv_m_small : PRCRat.InBound B (v.term m) :=
    PRCRat.InBound_mono hBv_le_B (hNvB m hNvB_m)
  have hv_n_small : PRCRat.InBound B (v.term n) :=
    PRCRat.InBound_mono hBv_le_B (hNvB n hNvB_n)
  exact hdelta (u.term m) (u.term n) (v.term m) (v.term n)
    hu_m_small hu_n_small hv_m_small hv_n_small
    (hNuC m n hNuC_m hNuC_n)
    (hNvC m n hNvC_m hNvC_n)

/-- Conditional proof of product congruence from eventual boundedness and
bounded product-continuity. -/
theorem PRCRealMulCongruenceTarget_of_bounded_continuity
    (hbounded : PRCCauchySeqEventuallyBoundedTarget)
    (hmul_cont : PRCJCostDistanceMulBoundedContinuityTarget) :
    PRCRealMulCongruenceTarget := by
  intro u u' v v' huu hvv eps heps
  rcases hbounded u with ⟨Bu, hBu_pos, NuB, hNuB⟩
  rcases hbounded u' with ⟨Bu', hBu'_pos, Nu'B, hNu'B⟩
  rcases hbounded v with ⟨Bv, hBv_pos, NvB, hNvB⟩
  rcases hbounded v' with ⟨Bv', hBv'_pos, Nv'B, hNv'B⟩
  let B : PRCRat := Bu + Bu' + Bv + Bv' + 1
  have hB_pos : PRCRat.positive B := by
    rw [PRCRat.positive_iff_toRat_pos]
    have hBu : (0 : ℚ) < Bu.toRat := (PRCRat.positive_iff_toRat_pos Bu).mp hBu_pos
    have hBu' : (0 : ℚ) < Bu'.toRat := (PRCRat.positive_iff_toRat_pos Bu').mp hBu'_pos
    have hBv : (0 : ℚ) < Bv.toRat := (PRCRat.positive_iff_toRat_pos Bv).mp hBv_pos
    have hBv' : (0 : ℚ) < Bv'.toRat := (PRCRat.positive_iff_toRat_pos Bv').mp hBv'_pos
    simp [B]
    nlinarith
  have hBu_le_B : Bu.toRat ≤ B.toRat := by
    have hBu' : (0 : ℚ) < Bu'.toRat := (PRCRat.positive_iff_toRat_pos Bu').mp hBu'_pos
    have hBv : (0 : ℚ) < Bv.toRat := (PRCRat.positive_iff_toRat_pos Bv).mp hBv_pos
    have hBv' : (0 : ℚ) < Bv'.toRat := (PRCRat.positive_iff_toRat_pos Bv').mp hBv'_pos
    simp [B]
    nlinarith
  have hBu'_le_B : Bu'.toRat ≤ B.toRat := by
    have hBu : (0 : ℚ) < Bu.toRat := (PRCRat.positive_iff_toRat_pos Bu).mp hBu_pos
    have hBv : (0 : ℚ) < Bv.toRat := (PRCRat.positive_iff_toRat_pos Bv).mp hBv_pos
    have hBv' : (0 : ℚ) < Bv'.toRat := (PRCRat.positive_iff_toRat_pos Bv').mp hBv'_pos
    simp [B]
    nlinarith
  have hBv_le_B : Bv.toRat ≤ B.toRat := by
    have hBu : (0 : ℚ) < Bu.toRat := (PRCRat.positive_iff_toRat_pos Bu).mp hBu_pos
    have hBu' : (0 : ℚ) < Bu'.toRat := (PRCRat.positive_iff_toRat_pos Bu').mp hBu'_pos
    have hBv' : (0 : ℚ) < Bv'.toRat := (PRCRat.positive_iff_toRat_pos Bv').mp hBv'_pos
    simp [B]
    nlinarith
  have hBv'_le_B : Bv'.toRat ≤ B.toRat := by
    have hBu : (0 : ℚ) < Bu.toRat := (PRCRat.positive_iff_toRat_pos Bu).mp hBu_pos
    have hBu' : (0 : ℚ) < Bu'.toRat := (PRCRat.positive_iff_toRat_pos Bu').mp hBu'_pos
    have hBv : (0 : ℚ) < Bv.toRat := (PRCRat.positive_iff_toRat_pos Bv).mp hBv_pos
    simp [B]
    nlinarith
  rcases hmul_cont eps B heps hB_pos with ⟨delta, hdelta_pos, hdelta⟩
  rcases huu delta hdelta_pos with ⟨NuC, hNuC⟩
  rcases hvv delta hdelta_pos with ⟨NvC, hNvC⟩
  let N := max (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)
  refine ⟨N, ?_⟩
  intro n hn
  have hNuB_n : NuB ≤ n := le_trans
    (le_trans (Nat.le_max_left NuB Nu'B) (Nat.le_max_left (max NuB Nu'B) (max NvB Nv'B)))
    (le_trans (Nat.le_max_left (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)) hn)
  have hNu'B_n : Nu'B ≤ n := le_trans
    (le_trans (Nat.le_max_right NuB Nu'B) (Nat.le_max_left (max NuB Nu'B) (max NvB Nv'B)))
    (le_trans (Nat.le_max_left (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)) hn)
  have hNvB_n : NvB ≤ n := le_trans
    (le_trans (Nat.le_max_left NvB Nv'B) (Nat.le_max_right (max NuB Nu'B) (max NvB Nv'B)))
    (le_trans (Nat.le_max_left (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)) hn)
  have hNv'B_n : Nv'B ≤ n := le_trans
    (le_trans (Nat.le_max_right NvB Nv'B) (Nat.le_max_right (max NuB Nu'B) (max NvB Nv'B)))
    (le_trans (Nat.le_max_left (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)) hn)
  have hNuC_n : NuC ≤ n :=
    le_trans (Nat.le_max_left NuC NvC)
      (le_trans (Nat.le_max_right (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)) hn)
  have hNvC_n : NvC ≤ n :=
    le_trans (Nat.le_max_right NuC NvC)
      (le_trans (Nat.le_max_right (max (max NuB Nu'B) (max NvB Nv'B)) (max NuC NvC)) hn)
  exact hdelta (u.term n) (u'.term n) (v.term n) (v'.term n)
    (PRCRat.InBound_mono hBu_le_B (hNuB n hNuB_n))
    (PRCRat.InBound_mono hBu'_le_B (hNu'B n hNu'B_n))
    (PRCRat.InBound_mono hBv_le_B (hNvB n hNvB_n))
    (PRCRat.InBound_mono hBv'_le_B (hNv'B n hNv'B_n))
    (hNuC n hNuC_n)
    (hNvC n hNvC_n)

/-- Conditional certificate: the multiplication targets reduce to eventual
boundedness plus bounded product continuity. -/
structure PRCRealMulBoundedContinuityConditionalCertificate : Prop where
  boundedness_target :
    PRCCauchySeqEventuallyBoundedTarget = PRCCauchySeqEventuallyBoundedTarget
  product_continuity_target :
    PRCJCostDistanceMulBoundedContinuityTarget =
      PRCJCostDistanceMulBoundedContinuityTarget
  mul_closure_from_targets :
    PRCCauchySeqEventuallyBoundedTarget →
      PRCJCostDistanceMulBoundedContinuityTarget →
        PRCRealMulClosureTarget
  mul_congruence_from_targets :
    PRCCauchySeqEventuallyBoundedTarget →
      PRCJCostDistanceMulBoundedContinuityTarget →
        PRCRealMulCongruenceTarget
  mul_operation_from_targets :
    PRCCauchySeqEventuallyBoundedTarget →
      PRCJCostDistanceMulBoundedContinuityTarget →
        Nonempty (PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed)

theorem prc_real_mul_bounded_continuity_conditional_certificate :
    PRCRealMulBoundedContinuityConditionalCertificate where
  boundedness_target := rfl
  product_continuity_target := rfl
  mul_closure_from_targets := PRCRealMulClosureTarget_of_bounded_continuity
  mul_congruence_from_targets := PRCRealMulCongruenceTarget_of_bounded_continuity
  mul_operation_from_targets := by
    intro hbounded hcont
    exact ⟨PRCRealNullClosed.mulOf
      (PRCRealMulClosureTarget_of_bounded_continuity hbounded hcont)
      (PRCRealMulCongruenceTarget_of_bounded_continuity hbounded hcont)⟩

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
