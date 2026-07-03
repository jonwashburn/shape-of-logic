/-
  PrimitiveRecognitionCalculus/OrbitDivisibility.lean

  Round-trip sources:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html
    δ/PRC_Structural_Brainstorm_20260527.html

  Spec anchors:
    Build Order step 2: divisibility, units, factorization, and primality on
    orbit positions.

  Strength: δ-only for definitions. Nat divisibility and Nat arithmetic appear
  only in verifier transport theorems.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitArithmetic

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DistinctionNat

/-! ## Native divisibility on finite δ-orbit positions -/

/-- The multiplicative unit orbit position. -/
def one : DistinctionNat :=
  succ zero

@[simp] theorem one_toNat :
    one.toNat = 1 := by
  rfl

theorem one_ne_zero :
    one ≠ zero := by
  intro h
  exact zero_ne_succ zero h.symm

theorem mul_one_eq (a : DistinctionNat) :
    a * one = a := by
  unfold one
  rw [mul_succ_eq, mul_zero_eq, zero_add_eq]

theorem one_mul_eq (a : DistinctionNat) :
    one * a = a := by
  rw [mul_comm, mul_one_eq]

theorem mul_assoc (a b c : DistinctionNat) :
    (a * b) * c = a * (b * c) := by
  apply toNat_inj
  rw [toNat_mul, toNat_mul, toNat_mul, toNat_mul]
  exact Nat.mul_assoc a.toNat b.toNat c.toNat

/-- Native orbit divisibility: `a` divides `b` when multiplying `a` by another
orbit position yields `b`. -/
def divides (a b : DistinctionNat) : Prop :=
  ∃ k : DistinctionNat, a * k = b

/-- Native unit predicate. In the finite δ-orbit, the only multiplicative unit
is the one-step orbit. -/
def unit (a : DistinctionNat) : Prop :=
  a = one

/-- Native nontrivial factorization. Both factors must be nonzero and non-unit. -/
def nontrivialFactorization (n : DistinctionNat) : Prop :=
  ∃ a b : DistinctionNat,
    a ≠ zero ∧ b ≠ zero ∧ ¬ unit a ∧ ¬ unit b ∧ a * b = n

/-- Native prime orbit position: nonzero, non-unit, and with no nontrivial
factorization. -/
def primeOrbit (p : DistinctionNat) : Prop :=
  p ≠ zero ∧ ¬ unit p ∧ ¬ nontrivialFactorization p

theorem divides_refl (a : DistinctionNat) :
    divides a a := by
  exact ⟨one, mul_one_eq a⟩

theorem divides_zero (a : DistinctionNat) :
    divides a zero := by
  exact ⟨zero, mul_zero_eq a⟩

theorem one_divides (a : DistinctionNat) :
    divides one a := by
  exact ⟨a, one_mul_eq a⟩

theorem divides_trans {a b c : DistinctionNat}
    (hab : divides a b) (hbc : divides b c) :
    divides a c := by
  rcases hab with ⟨m, hm⟩
  rcases hbc with ⟨n, hn⟩
  refine ⟨m * n, ?_⟩
  rw [← mul_assoc, hm, hn]

theorem divides_mul_right (a b : DistinctionNat) :
    divides a (a * b) := by
  exact ⟨b, rfl⟩

theorem divides_mul_left (a b : DistinctionNat) :
    divides b (a * b) := by
  refine ⟨a, ?_⟩
  rw [mul_comm]

theorem zero_divides_iff_eq_zero (a : DistinctionNat) :
    divides zero a ↔ a = zero := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    rw [zero_mul_eq] at hk
    exact hk.symm
  · intro h
    rw [h]
    exact divides_zero zero

/-- Divisibility is native, but it displays as Nat divisibility. -/
theorem divides_iff_toNat_dvd (a b : DistinctionNat) :
    divides a b ↔ a.toNat ∣ b.toNat := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨k.toNat, ?_⟩
    have hnat := congrArg DistinctionNat.toNat hk
    rw [toNat_mul] at hnat
    exact hnat.symm
  · intro h
    rcases h with ⟨k, hk⟩
    refine ⟨ofNat k, ?_⟩
    apply toNat_inj
    rw [toNat_mul, toNat_ofNat]
    exact hk.symm

theorem unit_iff_toNat_eq_one (a : DistinctionNat) :
    unit a ↔ a.toNat = 1 := by
  constructor
  · intro h
    unfold unit at h
    rw [h, one_toNat]
  · intro h
    unfold unit
    apply toNat_inj
    rw [h, one_toNat]

theorem divides_one_iff_unit (a : DistinctionNat) :
    divides a one ↔ unit a := by
  rw [divides_iff_toNat_dvd, unit_iff_toNat_eq_one, one_toNat]
  exact Nat.dvd_one

theorem unit_of_divides_unit {a b : DistinctionNat}
    (hb : unit b) (hdiv : divides a b) :
    unit a := by
  rw [unit_iff_toNat_eq_one] at hb ⊢
  have hnat := (divides_iff_toNat_dvd a b).mp hdiv
  rw [hb] at hnat
  exact Nat.dvd_one.mp hnat

theorem divides_antisymm {a b : DistinctionNat}
    (hab : divides a b) (hba : divides b a) :
    a = b := by
  apply toNat_inj
  exact Nat.dvd_antisymm
    ((divides_iff_toNat_dvd a b).mp hab)
    ((divides_iff_toNat_dvd b a).mp hba)

private theorem ofNat_ne_zero_of_ne_zero {n : Nat} (h : n ≠ 0) :
    ofNat n ≠ zero := by
  intro hz
  have hnat := congrArg DistinctionNat.toNat hz
  rw [toNat_ofNat, toNat_zero] at hnat
  exact h hnat

private theorem not_unit_ofNat_of_ne_one {n : Nat} (h : n ≠ 1) :
    ¬ unit (ofNat n) := by
  intro hu
  rw [unit_iff_toNat_eq_one] at hu
  rw [toNat_ofNat] at hu
  exact h hu

/-- Native nontrivial factorization displays as ordinary Nat nontrivial
factorization. -/
theorem nontrivialFactorization_iff_toNat (n : DistinctionNat) :
    nontrivialFactorization n ↔
      ∃ a b : Nat,
        a ≠ 0 ∧ b ≠ 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b = n.toNat := by
  constructor
  · intro h
    rcases h with ⟨a, b, ha0, hb0, ha1, hb1, hmul⟩
    refine ⟨a.toNat, b.toNat, ?_, ?_, ?_, ?_, ?_⟩
    · intro hz
      have : a = zero := by
        apply toNat_inj
        rw [hz, toNat_zero]
      exact ha0 this
    · intro hz
      have : b = zero := by
        apply toNat_inj
        rw [hz, toNat_zero]
      exact hb0 this
    · intro h1
      apply ha1
      rw [unit_iff_toNat_eq_one]
      exact h1
    · intro h1
      apply hb1
      rw [unit_iff_toNat_eq_one]
      exact h1
    · have hnat := congrArg DistinctionNat.toNat hmul
      rw [toNat_mul] at hnat
      exact hnat
  · intro h
    rcases h with ⟨a, b, ha0, hb0, ha1, hb1, hmul⟩
    refine ⟨ofNat a, ofNat b, ?_, ?_, ?_, ?_, ?_⟩
    · exact ofNat_ne_zero_of_ne_zero ha0
    · exact ofNat_ne_zero_of_ne_zero hb0
    · exact not_unit_ofNat_of_ne_one ha1
    · exact not_unit_ofNat_of_ne_one hb1
    · apply toNat_inj
      rw [toNat_mul, toNat_ofNat, toNat_ofNat, hmul]

/-- Native prime-orbit predicate displays as the Nat no-nontrivial-factor
predicate, without defining primality by importing Nat prime theory. -/
theorem primeOrbit_iff_toNat_no_nontrivial_factor (p : DistinctionNat) :
    primeOrbit p ↔
      p.toNat ≠ 0 ∧ p.toNat ≠ 1 ∧
        ¬ ∃ a b : Nat,
          a ≠ 0 ∧ b ≠ 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b = p.toNat := by
  unfold primeOrbit
  rw [unit_iff_toNat_eq_one, nontrivialFactorization_iff_toNat]
  constructor
  · intro h
    rcases h with ⟨hp0, hp1, hfac⟩
    refine ⟨?_, hp1, hfac⟩
    intro hz
    have : p = zero := by
      apply toNat_inj
      rw [hz, toNat_zero]
    exact hp0 this
  · intro h
    rcases h with ⟨hp0, hp1, hfac⟩
    refine ⟨?_, hp1, hfac⟩
    intro hz
    exact hp0 (by rw [hz, toNat_zero])

/-- If an orbit is prime, every native factorization has a unit factor. -/
theorem unit_or_unit_of_mul_eq_prime {a b p : DistinctionNat}
    (hp : primeOrbit p) (hmul : a * b = p) :
    unit a ∨ unit b := by
  by_cases ha0 : a = zero
  · exfalso
    rcases hp with ⟨hp0, _, _⟩
    apply hp0
    rw [← hmul, ha0, zero_mul_eq]
  · by_cases hb0 : b = zero
    · exfalso
      rcases hp with ⟨hp0, _, _⟩
      apply hp0
      rw [← hmul, hb0, mul_zero_eq]
    · by_cases ha1 : unit a
      · exact Or.inl ha1
      · by_cases hb1 : unit b
        · exact Or.inr hb1
        · exfalso
          rcases hp with ⟨_, _, hnf⟩
          exact hnf ⟨a, b, ha0, hb0, ha1, hb1, hmul⟩

/-- Converse native factor theorem: if a nonzero non-unit orbit position has
only unit factors, then it is a prime orbit. -/
theorem primeOrbit_of_unit_or_unit
    {p : DistinctionNat}
    (hp0 : p ≠ zero)
    (hp1 : ¬ unit p)
    (hfac : ∀ a b : DistinctionNat, a * b = p → unit a ∨ unit b) :
    primeOrbit p := by
  refine ⟨hp0, hp1, ?_⟩
  intro hnon
  rcases hnon with ⟨a, b, _ha0, _hb0, ha1, hb1, hmul⟩
  rcases hfac a b hmul with ha | hb
  · exact ha1 ha
  · exact hb1 hb

theorem unit_or_eq_of_divides_prime {a p : DistinctionNat}
    (hp : primeOrbit p) (hdiv : divides a p) :
    unit a ∨ a = p := by
  rcases hdiv with ⟨k, hk⟩
  rcases unit_or_unit_of_mul_eq_prime hp hk with ha | hkunit
  · exact Or.inl ha
  · right
    unfold unit at hkunit
    rw [hkunit, mul_one_eq] at hk
    exact hk

/-- Bundling certificate for the native divisibility surface. -/
structure OrbitDivisibilityCertificate : Prop where
  divides_display :
    ∀ a b : DistinctionNat, divides a b ↔ a.toNat ∣ b.toNat
  divides_reflexive :
    ∀ a : DistinctionNat, divides a a
  divides_transitive :
    ∀ {a b c : DistinctionNat}, divides a b → divides b c → divides a c
  divides_mul_right_factor :
    ∀ a b : DistinctionNat, divides a (a * b)
  divides_mul_left_factor :
    ∀ a b : DistinctionNat, divides b (a * b)
  one_divides_all :
    ∀ a : DistinctionNat, divides one a
  zero_divides_only_zero :
    ∀ a : DistinctionNat, divides zero a ↔ a = zero
  unit_display :
    ∀ a : DistinctionNat, unit a ↔ a.toNat = 1
  divides_one_exactly_units :
    ∀ a : DistinctionNat, divides a one ↔ unit a
  divisor_of_unit_is_unit :
    ∀ {a b : DistinctionNat}, unit b → divides a b → unit a
  divides_antisymmetric :
    ∀ {a b : DistinctionNat}, divides a b → divides b a → a = b
  nontrivial_factorization_display :
    ∀ n : DistinctionNat,
      nontrivialFactorization n ↔
        ∃ a b : Nat,
          a ≠ 0 ∧ b ≠ 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b = n.toNat
  prime_orbit_display :
    ∀ p : DistinctionNat,
      primeOrbit p ↔
        p.toNat ≠ 0 ∧ p.toNat ≠ 1 ∧
          ¬ ∃ a b : Nat,
            a ≠ 0 ∧ b ≠ 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b = p.toNat
  prime_factor_property :
    ∀ {a b p : DistinctionNat},
      primeOrbit p → a * b = p → unit a ∨ unit b
  prime_divisor_property :
    ∀ {a p : DistinctionNat}, primeOrbit p → divides a p → unit a ∨ a = p

/-- The native orbit divisibility surface is closed. -/
theorem orbit_divisibility_certificate : OrbitDivisibilityCertificate where
  divides_display := divides_iff_toNat_dvd
  divides_reflexive := divides_refl
  divides_transitive := by
    intro a b c hab hbc
    exact divides_trans hab hbc
  divides_mul_right_factor := divides_mul_right
  divides_mul_left_factor := divides_mul_left
  one_divides_all := one_divides
  zero_divides_only_zero := zero_divides_iff_eq_zero
  unit_display := unit_iff_toNat_eq_one
  divides_one_exactly_units := divides_one_iff_unit
  divisor_of_unit_is_unit := by
    intro a b hb hdiv
    exact unit_of_divides_unit hb hdiv
  divides_antisymmetric := by
    intro a b hab hba
    exact divides_antisymm hab hba
  nontrivial_factorization_display := nontrivialFactorization_iff_toNat
  prime_orbit_display := primeOrbit_iff_toNat_no_nontrivial_factor
  prime_factor_property := by
    intro a b p hp hmul
    exact unit_or_unit_of_mul_eq_prime hp hmul
  prime_divisor_property := by
    intro a p hp hdiv
    exact unit_or_eq_of_divides_prime hp hdiv

end DistinctionNat
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
