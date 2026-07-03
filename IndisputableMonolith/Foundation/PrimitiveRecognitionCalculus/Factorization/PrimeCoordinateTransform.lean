/-
  PrimitiveRecognitionCalculus/Factorization/PrimeCoordinateTransform.lean

  Final-goal interface for δ-native prime-coordinate data. This module proves
  that once such coordinates are supplied, factor recovery is a projection from
  the data. It does not claim that the transform is already δ-derived.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PhysicalPeriodReadout

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- One prime coordinate: a prime orbit base and a nonzero exponent. -/
structure PrimePowerCoordinate : Type where
  base : DistinctionNat
  exponent : DistinctionNat
  base_prime : primeOrbit base
  exponent_nonzero : exponent ≠ zero

/-- The orbit value of one prime-power coordinate. -/
def primePowerValue (c : PrimePowerCoordinate) : DistinctionNat :=
  orbitPow c.base c.exponent

/-- Product of a list of prime-power coordinates. -/
def primeCoordinateProduct : List PrimePowerCoordinate → DistinctionNat
  | [] => one
  | c :: rest => primePowerValue c * primeCoordinateProduct rest

theorem primeCoordinateProduct_nil :
    primeCoordinateProduct [] = one := rfl

theorem primeCoordinateProduct_cons (c : PrimePowerCoordinate)
    (rest : List PrimePowerCoordinate) :
    primeCoordinateProduct (c :: rest) =
      primePowerValue c * primeCoordinateProduct rest := rfl

/-- Prime-coordinate data for an orbit number `N`. -/
structure PrimeCoordinateData (N : DistinctionNat) : Type where
  coordinates : List PrimePowerCoordinate
  reconstructs : primeCoordinateProduct coordinates = N

theorem primeCoordinateData_reconstructs {N : DistinctionNat}
    (data : PrimeCoordinateData N) :
    primeCoordinateProduct data.coordinates = N :=
  data.reconstructs

theorem primeCoordinateProduct_append
    (xs ys : List PrimePowerCoordinate) :
    primeCoordinateProduct (xs ++ ys) =
      primeCoordinateProduct xs * primeCoordinateProduct ys := by
  induction xs with
  | nil =>
      simp [primeCoordinateProduct, one_mul_eq]
  | cons c rest ih =>
      simp [primeCoordinateProduct, ih]
      rw [mul_assoc]

def singlePrimeCoordinateData {N : DistinctionNat}
    (hp : primeOrbit N) : PrimeCoordinateData N where
  coordinates := [{
    base := N
    exponent := one
    base_prime := hp
    exponent_nonzero := one_ne_zero
  }]
  reconstructs := by
    apply toNat_inj
    simp [primeCoordinateProduct, primePowerValue, orbitPow_toNat,
      one_toNat, toNat_mul]

theorem nontrivialFactorization_of_not_primeOrbit
    {N : DistinctionNat}
    (hN0 : N ≠ zero) (hNunit : ¬ unit N)
    (hnot : ¬ primeOrbit N) :
    nontrivialFactorization N := by
  by_contra hfac
  exact hnot ⟨hN0, hNunit, hfac⟩

theorem toNat_pos_of_ne_zero {N : DistinctionNat} (hN : N ≠ zero) :
    0 < N.toNat := by
  have hne : N.toNat ≠ 0 := by
    intro h
    apply hN
    apply toNat_inj
    rw [h, toNat_zero]
  omega

theorem toNat_ne_one_of_not_unit {N : DistinctionNat}
    (hNunit : ¬ unit N) :
    N.toNat ≠ 1 := by
  intro h
  apply hNunit
  rw [unit_iff_toNat_eq_one]
  exact h

theorem factor_left_toNat_lt_product {a b N : DistinctionNat}
    (ha0 : a ≠ zero) (hb0 : b ≠ zero)
    (hbunit : ¬ unit b) (hmul : a * b = N) :
    a.toNat < N.toNat := by
  have hapos : 0 < a.toNat := toNat_pos_of_ne_zero ha0
  have hbpos : 0 < b.toNat := toNat_pos_of_ne_zero hb0
  have hbne1 : b.toNat ≠ 1 := toNat_ne_one_of_not_unit hbunit
  have hbge2 : 2 ≤ b.toNat := by omega
  have hmulNat : a.toNat * b.toNat = N.toNat := by
    have h := congrArg DistinctionNat.toNat hmul
    simpa [toNat_mul] using h
  nlinarith

theorem factor_right_toNat_lt_product {a b N : DistinctionNat}
    (ha0 : a ≠ zero) (hb0 : b ≠ zero)
    (haunit : ¬ unit a) (hmul : a * b = N) :
    b.toNat < N.toNat := by
  rw [mul_comm] at hmul
  exact factor_left_toNat_lt_product hb0 ha0 haunit hmul

/-- A claimed δ-prime-coordinate transform. This is the bold goal object. -/
def DeltaPrimeCoordinateTransform : Type :=
  ∀ N : DistinctionNat, N ≠ zero → ¬ unit N → PrimeCoordinateData N

/-- A weaker transform that is allowed to rely on a named external readout. -/
structure AssistedPrimeCoordinateTransform : Type where
  commitmentName : String
  transform :
    ∀ N : DistinctionNat, N ≠ zero → ¬ unit N → PrimeCoordinateData N

/-! ## Classical factorization transport back into δ -/

theorem primeOrbit_ofNat_of_natPrime {p : Nat} (hp : Nat.Prime p) :
    primeOrbit (ofNat p) := by
  rw [primeOrbit_iff_toNat_no_nontrivial_factor, toNat_ofNat]
  refine ⟨hp.ne_zero, hp.ne_one, ?_⟩
  rintro ⟨a, b, ha0, _hb0, ha1, hb1, hmul⟩
  have hadvd : a ∣ p := ⟨b, hmul.symm⟩
  rcases hp.eq_one_or_self_of_dvd a hadvd with haeq | haeq
  · exact ha1 haeq
  · have hb : b = 1 := by
      rw [haeq] at hmul
      nlinarith [hmul, hp.pos]
    exact hb1 hb

def primePowerCoordinateOfNatPrime (p : Nat) (hp : Nat.Prime p) :
    PrimePowerCoordinate where
  base := ofNat p
  exponent := one
  base_prime := primeOrbit_ofNat_of_natPrime hp
  exponent_nonzero := one_ne_zero

theorem primePowerValue_of_natPrime_toNat (p : Nat) (hp : Nat.Prime p) :
    (primePowerValue (primePowerCoordinateOfNatPrime p hp)).toNat = p := by
  simp [primePowerValue, primePowerCoordinateOfNatPrime, orbitPow_toNat,
    one_toNat, toNat_ofNat]

def primeCoordinatesFromNatList :
    (L : List Nat) → (∀ p ∈ L, Nat.Prime p) → List PrimePowerCoordinate
  | [], _ => []
  | p :: rest, hprime =>
      primePowerCoordinateOfNatPrime p (hprime p (by simp)) ::
        primeCoordinatesFromNatList rest (by
          intro q hq
          exact hprime q (by simp [hq]))

theorem primeCoordinateProduct_fromNatList_toNat
    (L : List Nat) (hprime : ∀ p ∈ L, Nat.Prime p) :
    (primeCoordinateProduct (primeCoordinatesFromNatList L hprime)).toNat =
      L.prod := by
  induction L with
  | nil =>
      simp [primeCoordinatesFromNatList, primeCoordinateProduct, one_toNat]
  | cons p rest ih =>
      simp [primeCoordinatesFromNatList, primeCoordinateProduct,
        primePowerValue_of_natPrime_toNat, toNat_mul, ih]

def natPrimeFactorCoordinates (n : Nat) : List PrimePowerCoordinate :=
  primeCoordinatesFromNatList n.primeFactorsList (by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp)

theorem primeCoordinateProduct_natPrimeFactorCoordinates_toNat (n : Nat) :
    (primeCoordinateProduct (natPrimeFactorCoordinates n)).toNat =
      n.primeFactorsList.prod := by
  unfold natPrimeFactorCoordinates
  exact primeCoordinateProduct_fromNatList_toNat n.primeFactorsList (by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp)

private theorem toNat_ne_zero_of_ne_zero {N : DistinctionNat} (hN : N ≠ zero) :
    N.toNat ≠ 0 := by
  intro h
  apply hN
  apply toNat_inj
  rw [h, toNat_zero]

/-- A theorem-level δ prime-coordinate transform obtained by transporting
Mathlib's canonical `Nat.primeFactorsList` through the established δ/Nat
display equivalence. This closes the transform as a classical transport
theorem; it is not a new fast factoring algorithm. -/
def deltaPrimeCoordinateTransform_classicalTransport :
    DeltaPrimeCoordinateTransform := by
  intro N hN0 _hNunit
  refine {
    coordinates := natPrimeFactorCoordinates N.toNat
    reconstructs := ?_
  }
  apply toNat_inj
  rw [primeCoordinateProduct_natPrimeFactorCoordinates_toNat]
  exact Nat.prod_primeFactorsList (toNat_ne_zero_of_ne_zero hN0)

theorem deltaPrimeCoordinateTransform_exists :
    Nonempty DeltaPrimeCoordinateTransform :=
  ⟨deltaPrimeCoordinateTransform_classicalTransport⟩

/-! ## Native-choice δ transform by prime/factorization descent -/

theorem nativePrimeCoordinateData_exists :
    ∀ N : DistinctionNat, N ≠ zero → ¬ unit N →
      Nonempty (PrimeCoordinateData N) := by
  have hmain :
      ∀ n : Nat, ∀ N : DistinctionNat,
        N.toNat = n → N ≠ zero → ¬ unit N →
          Nonempty (PrimeCoordinateData N) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N hNnat hN0 hNunit
        by_cases hp : primeOrbit N
        · exact ⟨singlePrimeCoordinateData hp⟩
        · have hfac := nontrivialFactorization_of_not_primeOrbit
            hN0 hNunit hp
          rcases hfac with ⟨a, b, ha0, hb0, haunit, hbunit, hmul⟩
          have ha_lt_n : a.toNat < n := by
            rw [← hNnat]
            exact factor_left_toNat_lt_product ha0 hb0 hbunit hmul
          have hb_lt_n : b.toNat < n := by
            rw [← hNnat]
            exact factor_right_toNat_lt_product ha0 hb0 haunit hmul
          rcases ih a.toNat ha_lt_n a rfl ha0 haunit with ⟨adata⟩
          rcases ih b.toNat hb_lt_n b rfl hb0 hbunit with ⟨bdata⟩
          refine ⟨{
            coordinates := adata.coordinates ++ bdata.coordinates
            reconstructs := ?_
          }⟩
          rw [primeCoordinateProduct_append, adata.reconstructs,
            bdata.reconstructs, hmul]
  intro N hN0 hNunit
  exact hmain N.toNat N rfl hN0 hNunit

/-- Noncomputable native-choice transform: it uses the δ-native
`primeOrbit/nontrivialFactorization` split and well-founded descent. -/
noncomputable def deltaPrimeCoordinateTransform_nativeChoice :
    DeltaPrimeCoordinateTransform := by
  intro N hN0 hNunit
  exact Classical.choice (nativePrimeCoordinateData_exists N hN0 hNunit)

theorem deltaPrimeCoordinateTransform_nativeChoice_exists :
    Nonempty DeltaPrimeCoordinateTransform :=
  ⟨deltaPrimeCoordinateTransform_nativeChoice⟩

theorem primeCoordinateData_nonempty_of_nonunit {N : DistinctionNat}
    (data : PrimeCoordinateData N) (hNunit : ¬ unit N) :
    data.coordinates ≠ [] := by
  intro hnil
  have hN : one = N := by
    simpa [primeCoordinateProduct, hnil] using data.reconstructs
  apply hNunit
  unfold unit
  exact hN.symm

theorem base_divides_orbitPow_of_exponent_nonzero
    (p e : DistinctionNat) (he : e ≠ zero) :
    divides p (orbitPow p e) := by
  cases e with
  | zero =>
      exact False.elim (he rfl)
  | succ k =>
      refine ⟨orbitPow p k, ?_⟩
      rw [orbitPow_succ, mul_comm]

/-- The first coordinate in a coordinate list gives a prime divisor of the
reconstructed number. This is the formal version of "factor recovery is a
coordinate projection." -/
theorem first_coordinate_prime_divisor {N : DistinctionNat}
    (c : PrimePowerCoordinate) (rest : List PrimePowerCoordinate)
    (data : PrimeCoordinateData N)
    (hcoords : data.coordinates = c :: rest) :
    primeOrbit c.base ∧ divides c.base N := by
  constructor
  · exact c.base_prime
  · have hpow : divides c.base (primePowerValue c) :=
      base_divides_orbitPow_of_exponent_nonzero c.base c.exponent
        c.exponent_nonzero
    have hprod : divides (primePowerValue c)
        (primePowerValue c * primeCoordinateProduct rest) :=
      divides_mul_right (primePowerValue c) (primeCoordinateProduct rest)
    have hdivProduct : divides c.base
        (primePowerValue c * primeCoordinateProduct rest) :=
      divides_trans hpow hprod
    rcases hdivProduct with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    rw [← primeCoordinateProduct_cons]
    rw [← hcoords]
    exact data.reconstructs

/-- A δ-prime-coordinate transform makes factor recovery immediate for every
nonzero nonunit orbit number. -/
theorem deltaPrimeCoordinateTransform_recovers_prime_divisor
    (T : DeltaPrimeCoordinateTransform) :
    ∀ N : DistinctionNat, N ≠ zero → ¬ unit N →
      ∃ p : DistinctionNat, primeOrbit p ∧ divides p N := by
  intro N hN0 hNunit
  let data := T N hN0 hNunit
  have hnonempty := primeCoordinateData_nonempty_of_nonunit data hNunit
  cases hcoords : data.coordinates with
  | nil =>
      exact False.elim (hnonempty hcoords)
  | cons c rest =>
      exact ⟨c.base, first_coordinate_prime_divisor c rest data hcoords⟩

/-- Certificate for the prime-coordinate transform interface. -/
structure PrimeCoordinateTransformCertificate : Prop where
  data_reconstructs :
    ∀ {N : DistinctionNat} (data : PrimeCoordinateData N),
      primeCoordinateProduct data.coordinates = N
  classical_transport_exists :
    Nonempty DeltaPrimeCoordinateTransform
  native_choice_exists :
    Nonempty DeltaPrimeCoordinateTransform
  nonunit_data_nonempty :
    ∀ {N : DistinctionNat} (data : PrimeCoordinateData N),
      ¬ unit N → data.coordinates ≠ []
  delta_transform_recovers_prime_divisor :
    DeltaPrimeCoordinateTransform →
      ∀ N : DistinctionNat, N ≠ zero → ¬ unit N →
        ∃ p : DistinctionNat, primeOrbit p ∧ divides p N

theorem prime_coordinate_transform_certificate :
    PrimeCoordinateTransformCertificate where
  data_reconstructs := by
    intro N data
    exact primeCoordinateData_reconstructs data
  classical_transport_exists := deltaPrimeCoordinateTransform_exists
  native_choice_exists := deltaPrimeCoordinateTransform_nativeChoice_exists
  nonunit_data_nonempty := by
    intro N data hNunit
    exact primeCoordinateData_nonempty_of_nonunit data hNunit
  delta_transform_recovers_prime_divisor := by
    intro T N hN0 hNunit
    exact deltaPrimeCoordinateTransform_recovers_prime_divisor T N hN0 hNunit

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
