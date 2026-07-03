/-
  PrimitiveRecognitionCalculus/Factorization/ChartTransition.lean

  δ-native factoring starts as a chart-transition problem. The positional
  orbit chart gives a product/magnitude. The multiplicative chart asks for
  factor coordinates. This file proves the small finite statements that keep
  those two surfaces separate.

  Strength: δ-native statements with verifier Nat display lemmas. No project
  axioms and no computational oracle for factoring.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitEuclidean

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- A native factor pair for an orbit position `n`. -/
structure FactorPair (n : DistinctionNat) : Type where
  left : DistinctionNat
  right : DistinctionNat
  product_eq : left * right = n

/-- The positional chart sees only the product of a pair. -/
def factorPairProduct (a b : DistinctionNat) : DistinctionNat :=
  a * b

/-- The Archimedean magnitude displayed by an orbit position. -/
def archimedeanMagnitude (n : DistinctionNat) : Nat :=
  n.toNat

theorem factorPairProduct_toNat (a b : DistinctionNat) :
    (factorPairProduct a b).toNat = a.toNat * b.toNat := by
  unfold factorPairProduct
  exact toNat_mul a b

/-- Same product means same displayed magnitude. This is the cheap chart. -/
theorem same_product_same_magnitude {a b c d : DistinctionNat}
    (h : factorPairProduct a b = factorPairProduct c d) :
    archimedeanMagnitude (factorPairProduct a b) =
      archimedeanMagnitude (factorPairProduct c d) := by
  unfold archimedeanMagnitude
  rw [h]

/-- Concrete ambiguity: `2 * 6` and `3 * 4` are different factor pairs with
the same product. This is the finite obstruction behind "magnitude is not a
factor oracle." -/
theorem two_six_product_eq_three_four :
    factorPairProduct (ofNat 2) (ofNat 6) =
      factorPairProduct (ofNat 3) (ofNat 4) := by
  apply toNat_inj
  simp [factorPairProduct, toNat_mul]

theorem two_ne_three : ofNat 2 ≠ ofNat 3 := by
  intro h
  have hnat := congrArg DistinctionNat.toNat h
  simp at hnat

theorem six_ne_four : ofNat 6 ≠ ofNat 4 := by
  intro h
  have hnat := congrArg DistinctionNat.toNat h
  simp at hnat

/-- Magnitude data cannot identify the left factor in general. -/
theorem magnitude_underdetermines_left_factor :
    factorPairProduct (ofNat 2) (ofNat 6) =
      factorPairProduct (ofNat 3) (ofNat 4) ∧
    ofNat 2 ≠ ofNat 3 := by
  exact ⟨two_six_product_eq_three_four, two_ne_three⟩

/-- Magnitude data cannot identify the right factor in general. -/
theorem magnitude_underdetermines_right_factor :
    factorPairProduct (ofNat 2) (ofNat 6) =
      factorPairProduct (ofNat 3) (ofNat 4) ∧
    ofNat 6 ≠ ofNat 4 := by
  exact ⟨two_six_product_eq_three_four, six_ne_four⟩

/-- A proper nonunit divisor gives a native nontrivial factorization. This is
the reusable endpoint for period-readout factoring: once a period witness gives
a proper gcd divisor, the δ divisibility layer supplies the factorization. -/
theorem nontrivialFactorization_of_proper_divisor {N d : DistinctionNat}
    (hN0 : N ≠ zero)
    (hd0 : d ≠ zero)
    (hdu : ¬ unit d)
    (hdN : d ≠ N)
    (hdiv : divides d N) :
    nontrivialFactorization N := by
  let q := quotient N d hd0
  have hq0 : q ≠ zero :=
    quotient_ne_zero_of_divides (n := N) (d := d) hd0 hdiv hN0
  have hmul_toNat : q.toNat * d.toNat = N.toNat :=
    quotient_mul_divisor_toNat_of_divides (n := N) (d := d) hd0 hdiv
  have hmul : q * d = N := by
    apply toNat_inj
    rw [toNat_mul]
    exact hmul_toNat
  have hqu : ¬ unit q := by
    intro hqUnit
    apply hdN
    unfold unit at hqUnit
    rw [← hmul, hqUnit, one_mul_eq]
  exact ⟨q, d, hq0, hd0, hqu, hdu, hmul⟩

/-- Certificate for the chart-transition obstruction surface. -/
structure ChartTransitionCertificate : Prop where
  product_display :
    ∀ a b : DistinctionNat,
      (factorPairProduct a b).toNat = a.toNat * b.toNat
  same_product_same_magnitude :
    ∀ {a b c d : DistinctionNat},
      factorPairProduct a b = factorPairProduct c d →
        archimedeanMagnitude (factorPairProduct a b) =
          archimedeanMagnitude (factorPairProduct c d)
  explicit_ambiguous_product :
    factorPairProduct (ofNat 2) (ofNat 6) =
      factorPairProduct (ofNat 3) (ofNat 4)
  explicit_left_factor_difference :
    ofNat 2 ≠ ofNat 3
  explicit_right_factor_difference :
    ofNat 6 ≠ ofNat 4
  proper_divisor_to_nontrivial_factorization :
    ∀ {N d : DistinctionNat},
      N ≠ zero → d ≠ zero → ¬ unit d → d ≠ N → divides d N →
        nontrivialFactorization N

theorem chart_transition_certificate : ChartTransitionCertificate where
  product_display := factorPairProduct_toNat
  same_product_same_magnitude := by
    intro a b c d h
    exact same_product_same_magnitude h
  explicit_ambiguous_product := two_six_product_eq_three_four
  explicit_left_factor_difference := two_ne_three
  explicit_right_factor_difference := six_ne_four
  proper_divisor_to_nontrivial_factorization := by
    intro N d hN0 hd0 hdu hdN hdiv
    exact nontrivialFactorization_of_proper_divisor hN0 hd0 hdu hdN hdiv

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
