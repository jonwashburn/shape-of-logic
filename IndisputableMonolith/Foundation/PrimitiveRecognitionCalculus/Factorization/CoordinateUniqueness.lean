/-
  PrimitiveRecognitionCalculus/Factorization/CoordinateUniqueness.lean

  Fundamental theorem of arithmetic in δ prime coordinates. This module proves
  that the prime-coordinate readout of an orbit number is unique (any two
  reconstructions induce the same Nat factorization), that every coordinate base
  is a genuine prime divisor, and that every prime divisor appears as a
  coordinate base. Together these say factor recovery is list membership on the
  readout, not a search.

  This is theorem content about the structure of the readout. It makes no claim
  about the cost of producing the readout; both transforms in
  `PrimeCoordinateTransform` remain search-grade.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PrimeCoordinateTransform

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-! ## A prime orbit displays as a Nat prime -/

/-- The δ-native `primeOrbit` predicate forces the orbit display to be a genuine
Nat prime. This is the bridge that lets the readout inherit `Nat.factorization`
structure. -/
theorem natPrime_toNat_of_primeOrbit {p : DistinctionNat} (hp : primeOrbit p) :
    Nat.Prime p.toNat := by
  rw [primeOrbit_iff_toNat_no_nontrivial_factor] at hp
  obtain ⟨h0, h1, hnf⟩ := hp
  rw [Nat.prime_def_lt]
  refine ⟨by omega, ?_⟩
  intro m hmlt hmdvd
  rcases hmdvd with ⟨k, hk⟩
  by_contra hm1
  apply hnf
  refine ⟨m, k, ?_, ?_, hm1, ?_, hk.symm⟩
  · intro hm0
    rw [hm0, Nat.zero_mul] at hk
    exact h0 hk
  · intro hk0
    rw [hk0, Nat.mul_zero] at hk
    exact h0 hk
  · intro hk1
    rw [hk1, Nat.mul_one] at hk
    omega

/-- The converse bridge: a Nat prime display lifts back to a δ prime orbit. -/
theorem primeOrbit_of_natPrime_toNat {p : DistinctionNat}
    (h : Nat.Prime p.toNat) : primeOrbit p := by
  have hp := primeOrbit_ofNat_of_natPrime h
  rwa [ofNat_toNat] at hp

/-- δ primality is exactly Nat primality of the display. -/
theorem primeOrbit_iff_natPrime_toNat (p : DistinctionNat) :
    primeOrbit p ↔ Nat.Prime p.toNat :=
  ⟨natPrime_toNat_of_primeOrbit, primeOrbit_of_natPrime_toNat⟩

/-- Consequently `primeOrbit` is decidable: δ primality is machine-checkable. -/
instance : DecidablePred (primeOrbit : DistinctionNat → Prop) := fun p =>
  decidable_of_iff (Nat.Prime p.toNat) (primeOrbit_iff_natPrime_toNat p).symm

/-! ## The induced Nat factorization of a coordinate list -/

/-- The Nat factorization read off a coordinate list: each prime-power
coordinate `base^exponent` contributes `exponent` to the prime `base`. -/
noncomputable def coordinateFactorization
    (coords : List PrimePowerCoordinate) : Nat →₀ Nat :=
  (coords.map fun c => Finsupp.single c.base.toNat c.exponent.toNat).sum

theorem coordinateFactorization_nil :
    coordinateFactorization [] = 0 := by
  simp [coordinateFactorization]

theorem coordinateFactorization_cons (c : PrimePowerCoordinate)
    (rest : List PrimePowerCoordinate) :
    coordinateFactorization (c :: rest) =
      Finsupp.single c.base.toNat c.exponent.toNat +
        coordinateFactorization rest := by
  simp [coordinateFactorization, List.map_cons, List.sum_cons]

theorem primeCoordinateProduct_toNat_ne_zero
    (coords : List PrimePowerCoordinate) :
    (primeCoordinateProduct coords).toNat ≠ 0 := by
  induction coords with
  | nil => simp [primeCoordinateProduct, one_toNat]
  | cons c rest ih =>
      rw [primeCoordinateProduct_cons, toNat_mul]
      have hbpos : 0 < c.base.toNat := (natPrime_toNat_of_primeOrbit c.base_prime).pos
      have hc : (primePowerValue c).toNat ≠ 0 := by
        rw [primePowerValue, orbitPow_toNat]
        exact pow_ne_zero _ hbpos.ne'
      exact Nat.mul_ne_zero hc ih

/-- The factorization read off a coordinate list equals the canonical Nat
factorization of the reconstructed product. -/
theorem coordinateFactorization_eq_factorization_product
    (coords : List PrimePowerCoordinate) :
    coordinateFactorization coords =
      Nat.factorization (primeCoordinateProduct coords).toNat := by
  induction coords with
  | nil =>
      rw [coordinateFactorization_nil, primeCoordinateProduct_nil, one_toNat,
        Nat.factorization_one]
  | cons c rest ih =>
      have hbpos : 0 < c.base.toNat :=
        (natPrime_toNat_of_primeOrbit c.base_prime).pos
      have hc : (primePowerValue c).toNat ≠ 0 := by
        rw [primePowerValue, orbitPow_toNat]
        exact pow_ne_zero _ hbpos.ne'
      have hr : (primeCoordinateProduct rest).toNat ≠ 0 :=
        primeCoordinateProduct_toNat_ne_zero rest
      have hpf : Nat.factorization (primePowerValue c).toNat
          = Finsupp.single c.base.toNat c.exponent.toNat := by
        rw [primePowerValue, orbitPow_toNat, Nat.factorization_pow,
          (natPrime_toNat_of_primeOrbit c.base_prime).factorization,
          Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [coordinateFactorization_cons, ih, primeCoordinateProduct_cons,
        toNat_mul, Nat.factorization_mul hc hr, hpf]

/-- Specialized to reconstruction data: the readout of `N` is exactly the
canonical factorization of `N`'s display. -/
theorem coordinateFactorization_eq_factorization_of_data {N : DistinctionNat}
    (data : PrimeCoordinateData N) :
    coordinateFactorization data.coordinates = Nat.factorization N.toNat := by
  rw [coordinateFactorization_eq_factorization_product, data.reconstructs]

/-- Fundamental theorem of arithmetic in δ coordinates: any two prime-coordinate
reconstructions of the same orbit number induce the same prime factorization.
The readout is unique as a multiset of prime powers. -/
theorem primeCoordinateData_factorization_unique {N : DistinctionNat}
    (d₁ d₂ : PrimeCoordinateData N) :
    coordinateFactorization d₁.coordinates =
      coordinateFactorization d₂.coordinates := by
  rw [coordinateFactorization_eq_factorization_of_data,
    coordinateFactorization_eq_factorization_of_data]

/-! ## Soundness: every coordinate base is a prime divisor -/

theorem mem_coordinate_divides_product (c : PrimePowerCoordinate) :
    ∀ (coords : List PrimePowerCoordinate), c ∈ coords →
      divides (primePowerValue c) (primeCoordinateProduct coords) := by
  intro coords
  induction coords with
  | nil =>
      intro hmem
      simp at hmem
  | cons d rest ih =>
      intro hmem
      rw [primeCoordinateProduct_cons]
      rcases List.mem_cons.mp hmem with h | h
      · subst h
        exact divides_mul_right _ _
      · exact divides_trans (ih h) (divides_mul_left _ _)

/-- Every coordinate base is a prime orbit that divides `N`. Reading a base off
the list is a sound factor projection. -/
theorem coordinate_base_is_prime_divisor {N : DistinctionNat}
    (data : PrimeCoordinateData N) (c : PrimePowerCoordinate)
    (hmem : c ∈ data.coordinates) :
    primeOrbit c.base ∧ divides c.base N := by
  refine ⟨c.base_prime, ?_⟩
  have h1 : divides c.base (primePowerValue c) :=
    base_divides_orbitPow_of_exponent_nonzero c.base c.exponent c.exponent_nonzero
  have h2 : divides (primePowerValue c) (primeCoordinateProduct data.coordinates) :=
    mem_coordinate_divides_product c data.coordinates hmem
  rw [← data.reconstructs]
  exact divides_trans h1 h2

/-! ## Completeness: every prime divisor appears as a coordinate base -/

theorem mem_support_coordinateFactorization :
    ∀ (coords : List PrimePowerCoordinate) {x : Nat},
      x ∈ (coordinateFactorization coords).support →
        ∃ c ∈ coords, c.base.toNat = x := by
  intro coords
  induction coords with
  | nil =>
      intro x hx
      rw [coordinateFactorization_nil] at hx
      simp at hx
  | cons c rest ih =>
      intro x hx
      rw [coordinateFactorization_cons] at hx
      have hsub := Finsupp.support_add hx
      rw [Finset.mem_union] at hsub
      rcases hsub with h | h
      · have hx1 := Finsupp.support_single_subset h
        rw [Finset.mem_singleton] at hx1
        exact ⟨c, List.mem_cons.mpr (Or.inl rfl), hx1.symm⟩
      · rcases ih h with ⟨d, hd, hdx⟩
        exact ⟨d, List.mem_cons.mpr (Or.inr hd), hdx⟩

/-- Every prime orbit dividing `N` appears as a coordinate base. The readout is
a complete factor oracle. -/
theorem prime_divisor_is_coordinate_base {N : DistinctionNat}
    (data : PrimeCoordinateData N) (hN0 : N ≠ zero)
    {q : DistinctionNat} (hq : primeOrbit q) (hdvd : divides q N) :
    ∃ c ∈ data.coordinates, c.base = q := by
  have hqp : Nat.Prime q.toNat := natPrime_toNat_of_primeOrbit hq
  have hdvdNat : q.toNat ∣ N.toNat := (divides_iff_toNat_dvd q N).mp hdvd
  have hN0Nat : N.toNat ≠ 0 := by
    intro h
    apply hN0
    apply toNat_inj
    rw [h, toNat_zero]
  have hmemPF : q.toNat ∈ N.toNat.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hqp, hdvdNat, hN0Nat⟩
  have hsupp : q.toNat ∈ (Nat.factorization N.toNat).support := by
    rwa [Nat.support_factorization]
  rw [← coordinateFactorization_eq_factorization_of_data data] at hsupp
  rcases mem_support_coordinateFactorization data.coordinates hsupp with ⟨c, hc, hcq⟩
  exact ⟨c, hc, toNat_inj hcq⟩

/-- The headline readout equivalence: for a prime orbit `q`, deciding whether
`q` divides `N` is exactly checking whether `q` is one of the coordinate bases.
Factor recovery is list membership on the readout, not a search. -/
theorem primeOrbit_divides_iff_mem_coordinate_bases {N : DistinctionNat}
    (data : PrimeCoordinateData N) (hN0 : N ≠ zero)
    {q : DistinctionNat} (hq : primeOrbit q) :
    divides q N ↔ ∃ c ∈ data.coordinates, c.base = q := by
  constructor
  · intro hdvd
    exact prime_divisor_is_coordinate_base data hN0 hq hdvd
  · rintro ⟨c, hc, hcq⟩
    rw [← hcq]
    exact (coordinate_base_is_prime_divisor data c hc).2

/-! ## The computable transport readout is the canonical factorization -/

/-- The computable classical-transport transform produces, for every nonzero
nonunit orbit number, a readout whose induced factorization is the canonical
`Nat.factorization`. Combined with uniqueness, this is a computable δ transform
whose output is the canonical prime decomposition. -/
theorem classicalTransport_readout_is_canonical
    (N : DistinctionNat) (hN0 : N ≠ zero) (hNunit : ¬ unit N) :
    coordinateFactorization
        (deltaPrimeCoordinateTransform_classicalTransport N hN0 hNunit).coordinates
      = Nat.factorization N.toNat :=
  coordinateFactorization_eq_factorization_of_data _

/-- Certificate for the coordinate-uniqueness layer. -/
structure CoordinateUniquenessCertificate : Prop where
  prime_orbit_displays_natPrime :
    ∀ {p : DistinctionNat}, primeOrbit p → Nat.Prime p.toNat
  prime_orbit_iff_natPrime :
    ∀ p : DistinctionNat, primeOrbit p ↔ Nat.Prime p.toNat
  factorization_of_data :
    ∀ {N : DistinctionNat} (data : PrimeCoordinateData N),
      coordinateFactorization data.coordinates = Nat.factorization N.toNat
  factorization_unique :
    ∀ {N : DistinctionNat} (d₁ d₂ : PrimeCoordinateData N),
      coordinateFactorization d₁.coordinates =
        coordinateFactorization d₂.coordinates
  coordinate_base_sound :
    ∀ {N : DistinctionNat} (data : PrimeCoordinateData N)
      (c : PrimePowerCoordinate),
      c ∈ data.coordinates → primeOrbit c.base ∧ divides c.base N
  readout_complete :
    ∀ {N : DistinctionNat} (data : PrimeCoordinateData N), N ≠ zero →
      ∀ {q : DistinctionNat}, primeOrbit q →
        (divides q N ↔ ∃ c ∈ data.coordinates, c.base = q)

theorem coordinate_uniqueness_certificate : CoordinateUniquenessCertificate where
  prime_orbit_displays_natPrime := by
    intro p hp
    exact natPrime_toNat_of_primeOrbit hp
  prime_orbit_iff_natPrime := primeOrbit_iff_natPrime_toNat
  factorization_of_data := by
    intro N data
    exact coordinateFactorization_eq_factorization_of_data data
  factorization_unique := by
    intro N d₁ d₂
    exact primeCoordinateData_factorization_unique d₁ d₂
  coordinate_base_sound := by
    intro N data c hmem
    exact coordinate_base_is_prime_divisor data c hmem
  readout_complete := by
    intro N data hN0 q hq
    exact primeOrbit_divides_iff_mem_coordinate_bases data hN0 hq

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
