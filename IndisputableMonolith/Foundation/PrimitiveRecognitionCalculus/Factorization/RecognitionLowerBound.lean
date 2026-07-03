/-
  PrimitiveRecognitionCalculus/Factorization/RecognitionLowerBound.lean

  Door A, first honest theorem layer: magnitude-only observables cannot see
  factor coordinates. This is not a complexity lower bound. It is the formal
  obstruction that kills Archimedean-only/J-cost-magnitude factoring heuristics.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.FiniteMulCharacter

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- A magnitude-only observable factors through the product orbit position. -/
def MagnitudeOnlyObservable
    (F : DistinctionNat → DistinctionNat → Nat) : Prop :=
  ∀ a b c d : DistinctionNat,
    factorPairProduct a b = factorPairProduct c d → F a b = F c d

/-- The displayed product magnitude is magnitude-only. -/
def productMagnitudeObservable (a b : DistinctionNat) : Nat :=
  archimedeanMagnitude (factorPairProduct a b)

theorem productMagnitudeObservable_magnitudeOnly :
    MagnitudeOnlyObservable productMagnitudeObservable := by
  intro a b c d h
  unfold productMagnitudeObservable
  exact same_product_same_magnitude h

/-- A left-factor extractor cannot be magnitude-only: the same product can have
different left coordinates. -/
theorem leftFactorObservable_not_magnitudeOnly :
    ¬ MagnitudeOnlyObservable (fun a _ => a.toNat) := by
  intro h
  have hsame := h (ofNat 2) (ofNat 6) (ofNat 3) (ofNat 4)
    two_six_product_eq_three_four
  simp at hsame

/-- A right-factor extractor cannot be magnitude-only. -/
theorem rightFactorObservable_not_magnitudeOnly :
    ¬ MagnitudeOnlyObservable (fun _ b => b.toNat) := by
  intro h
  have hsame := h (ofNat 2) (ofNat 6) (ofNat 3) (ofNat 4)
    two_six_product_eq_three_four
  simp at hsame

/-- Any observable obtained by applying a scalar post-processing function to
the product magnitude is still magnitude-only. This includes J-cost-style
ratio or magnitude scores unless they are coupled to residue or character data. -/
def productMagnitudePostprocess (φ : Nat → Nat)
    (a b : DistinctionNat) : Nat :=
  φ (productMagnitudeObservable a b)

theorem productMagnitudePostprocess_magnitudeOnly (φ : Nat → Nat) :
    MagnitudeOnlyObservable (productMagnitudePostprocess φ) := by
  intro a b c d h
  unfold productMagnitudePostprocess
  rw [productMagnitudeObservable_magnitudeOnly a b c d h]

/-- No scalar post-processing of product magnitude can equal the left factor
coordinate for all factor pairs. -/
theorem no_productMagnitudePostprocess_extracts_left_factor :
    ¬ ∃ φ : Nat → Nat,
      ∀ a b : DistinctionNat,
        productMagnitudePostprocess φ a b = a.toNat := by
  intro h
  rcases h with ⟨φ, hφ⟩
  have h2 := hφ (ofNat 2) (ofNat 6)
  have h3 := hφ (ofNat 3) (ofNat 4)
  have hsame :
      productMagnitudePostprocess φ (ofNat 2) (ofNat 6) =
        productMagnitudePostprocess φ (ofNat 3) (ofNat 4) :=
    productMagnitudePostprocess_magnitudeOnly φ
      (ofNat 2) (ofNat 6) (ofNat 3) (ofNat 4)
      two_six_product_eq_three_four
  rw [h2, h3] at hsame
  simp at hsame

/-- No scalar post-processing of product magnitude can equal the right factor
coordinate for all factor pairs. -/
theorem no_productMagnitudePostprocess_extracts_right_factor :
    ¬ ∃ φ : Nat → Nat,
      ∀ a b : DistinctionNat,
        productMagnitudePostprocess φ a b = b.toNat := by
  intro h
  rcases h with ⟨φ, hφ⟩
  have h6 := hφ (ofNat 2) (ofNat 6)
  have h4 := hφ (ofNat 3) (ofNat 4)
  have hsame :
      productMagnitudePostprocess φ (ofNat 2) (ofNat 6) =
        productMagnitudePostprocess φ (ofNat 3) (ofNat 4) :=
    productMagnitudePostprocess_magnitudeOnly φ
      (ofNat 2) (ofNat 6) (ofNat 3) (ofNat 4)
      two_six_product_eq_three_four
  rw [h6, h4] at hsame
  simp at hsame

/-- Door A certificate: product magnitude is a real invariant, but coordinate
extraction is not a magnitude-only operation. -/
structure RecognitionLowerBoundCertificate : Prop where
  product_magnitude_is_magnitude_only :
    MagnitudeOnlyObservable productMagnitudeObservable
  left_factor_not_magnitude_only :
    ¬ MagnitudeOnlyObservable (fun a _ => a.toNat)
  right_factor_not_magnitude_only :
    ¬ MagnitudeOnlyObservable (fun _ b => b.toNat)
  product_magnitude_postprocess_is_magnitude_only :
    ∀ φ : Nat → Nat, MagnitudeOnlyObservable (productMagnitudePostprocess φ)
  product_magnitude_postprocess_cannot_extract_left :
    ¬ ∃ φ : Nat → Nat,
      ∀ a b : DistinctionNat,
        productMagnitudePostprocess φ a b = a.toNat
  product_magnitude_postprocess_cannot_extract_right :
    ¬ ∃ φ : Nat → Nat,
      ∀ a b : DistinctionNat,
        productMagnitudePostprocess φ a b = b.toNat

theorem recognition_lower_bound_certificate :
    RecognitionLowerBoundCertificate where
  product_magnitude_is_magnitude_only := productMagnitudeObservable_magnitudeOnly
  left_factor_not_magnitude_only := leftFactorObservable_not_magnitudeOnly
  right_factor_not_magnitude_only := rightFactorObservable_not_magnitudeOnly
  product_magnitude_postprocess_is_magnitude_only :=
    productMagnitudePostprocess_magnitudeOnly
  product_magnitude_postprocess_cannot_extract_left :=
    no_productMagnitudePostprocess_extracts_left_factor
  product_magnitude_postprocess_cannot_extract_right :=
    no_productMagnitudePostprocess_extracts_right_factor

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
