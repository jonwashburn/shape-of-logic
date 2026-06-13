import Mathlib

namespace IndisputableMonolith
namespace Spectral

/-!
# Eight-Tick DFT Backbone (DFT-8)

This module formalizes the 8-point Discrete Fourier Transform as the canonical
unitary basis for the 8-tick recognition cycle.

## Main Definitions

- `omega8`: The primitive 8th root of unity, ω = e^{-2πi/8}
- `dft8_entry`: Entry (t, k) of the DFT-8 matrix: ω^{tk} / √8
- `dft8_matrix`: The full 8×8 unitary DFT matrix
- `cyclic_shift`: The cyclic shift operator on 8-vectors
- `dft8_mode`: The k-th DFT basis vector (column k of dft8_matrix)

## Main Results

- `dft8_unitary`: The DFT-8 matrix is unitary (B^H B = I)
- `dft8_diagonalizes_shift`: DFT diagonalizes the cyclic shift operator
- `shift_eigenvalue`: Eigenvalue of shift on mode k is ω^k
- `dft8_neutral_subspace`: Modes k=1..7 span the neutral (mean-free) subspace

## Physical Motivation

The 8-tick period τ₀ = 2^D (D=3) is forced by Recognition Science axioms.
The DFT-8 basis is the unique (up to permutation/phase) unitary basis that:
1. Diagonalizes the cyclic shift operator (time-translation symmetry)
2. Separates DC (k=0) from neutral modes (k=1..7)
3. Provides φ-lattice quantization via complex exponentials

This makes DFT-8 the canonical spectral basis for the 8-tick cycle.
-/

open Complex

/-- Primitive 8th root of unity: ω = e^{-2πi/8} = e^{-πi/4} -/
noncomputable def omega8 : ℂ := Complex.exp (-Complex.I * Real.pi / 4)

/-- ω^8 = 1 (periodicity) -/
theorem omega8_pow_8 : omega8 ^ 8 = 1 := by
  simp only [omega8]
  rw [← Complex.exp_nat_mul]
  have h : (8 : ℕ) * (-Complex.I * Real.pi / 4) = -(2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- ω^4 = -1 (half-period) -/
theorem omega8_pow_4 : omega8 ^ 4 = -1 := by
  simp only [omega8]
  rw [← Complex.exp_nat_mul]
  have h : (4 : ℕ) * (-Complex.I * Real.pi / 4) = -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg_one]

/-- |ω| = 1 (unit modulus) -/
theorem omega8_abs : ‖omega8‖ = 1 := by
  have h1 : omega8 = Complex.exp ((-Real.pi / 4 : ℝ) * Complex.I) := by
    simp only [omega8]
    congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  rw [h1, Complex.norm_exp_ofReal_mul_I]

/-- DFT-8 matrix entry at position (t, k): ω^{tk} / √8
    t = time index (row), k = frequency index (column) -/
noncomputable def dft8_entry (t k : Fin 8) : ℂ :=
  omega8 ^ (t.val * k.val) / Real.sqrt 8

/-- DFT entries are symmetric in their indices. -/
lemma dft8_entry_sym (t k : Fin 8) :
    dft8_entry t k = dft8_entry k t := by
  unfold dft8_entry
  simp [Nat.mul_comm]

/-- The 8×8 DFT matrix as a function -/
noncomputable def dft8_matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  fun t k => dft8_entry t k

/-- The k-th DFT basis vector (column k of dft8_matrix) -/
noncomputable def dft8_mode (k : Fin 8) : Fin 8 → ℂ :=
  fun t => dft8_entry t k

/-- Cyclic shift operator: shifts indices by 1 mod 8 -/
def cyclic_shift (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun t => v ⟨(t.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- Cyclic shift as a matrix -/
def shift_matrix : Matrix (Fin 8) (Fin 8) ℂ :=
  fun t s => if s.val = (t.val + 1) % 8 then 1 else 0

/-! ## Unitarity of DFT-8 -/

/-- Helper: ω^k ≠ 1 for 0 < k < 8.
    Proof: ω^k = exp(-I * π * k / 4), and exp(z) = 1 iff z = 2πin for some integer n.
    The equation -k/4 = 2n has no integer solutions for 0 < k < 8. -/
theorem omega8_pow_ne_one (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < 8) :
    omega8 ^ k ≠ 1 := by
  simp only [omega8, ← Complex.exp_nat_mul]
  intro h_eq_one
  -- h_eq_one : exp(k * (-I * π / 4)) = 1
  rw [Complex.exp_eq_one_iff] at h_eq_one
  -- h_eq_one : ∃ n : ℤ, k * (-I * π / 4) = n * (2 * π * I)
  obtain ⟨n, h_eq⟩ := h_eq_one
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- h_eq: (k : ℂ) * (-I * π / 4) = n * (2 * π * I)
  -- Simplify: -k / 4 = 2n, so k = -8n
  have h1 : -(k : ℂ) = 8 * n := by
    have h2 : (k : ℂ) * (-Complex.I * Real.pi / 4) =
        ↑n * (2 * Real.pi * Complex.I) := h_eq
    field_simp [hpi, hI] at h2
    have h3 : -(k : ℂ) = 8 * ↑n := by
      have : -(k : ℂ) = 4 * ↑n * 2 := h2
      ring_nf at this ⊢
      exact this
    exact h3
  -- Now -k = 8n as complex numbers, need to derive contradiction
  -- First extract to ℤ: k = -8n
  have h2 : (k : ℤ) = -8 * n := by
    have h1' : (k : ℂ) = -8 * ↑n := by
      calc (k : ℂ) = -(-((k : ℂ))) := by ring
        _ = -(8 * ↑n) := by rw [h1]
        _ = -8 * ↑n := by ring
    have h1'' : ((k : ℕ) : ℂ) = ((-8 * n : ℤ) : ℂ) := by
      simp only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat] at h1' ⊢
      exact h1'
    have : ((k : ℤ) : ℂ) = ((-8 * n : ℤ) : ℂ) := by
      simp only [Int.cast_natCast]
      exact h1''
    exact Int.cast_injective this
  -- k is a natural number with 0 < k < 8, so k ∈ {1,2,3,4,5,6,7}
  -- -8n ∈ {..., -16, -8, 0, 8, 16, ...}
  -- These sets are disjoint, contradiction
  omega

/-- Backward compatibility alias -/
theorem omega8_pow_ne_one_axiom (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < 8) :
    omega8 ^ k ≠ 1 :=
  omega8_pow_ne_one k hk_pos hk_lt

/-- star(ω) = ω^(-1) for the primitive 8th root of unity.
    Since ω = exp(-i π/4), we have conj(ω) = exp(i π/4) = ω^(-1). -/
lemma star_omega8 : star omega8 = omega8⁻¹ := by
  simp only [omega8, Complex.star_def]
  rw [← Complex.exp_conj]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, neg_neg, Complex.conj_ofReal,
    RCLike.conj_ofNat]
  -- Now have: exp(I * π / 4) = exp(-I * π / 4)⁻¹
  -- This is exp(z)⁻¹ = exp(-z)
  rw [← Complex.exp_neg]
  congr 1
  ring

/-- star(ω^n) = ω^(-n) for unit modulus -/
lemma star_omega8_pow (n : ℕ) : star (omega8 ^ n) = omega8⁻¹ ^ n := by
  rw [star_pow, star_omega8]

/-- ω * ω^(-1) = 1 -/
lemma omega8_mul_inv : omega8 * omega8⁻¹ = 1 := mul_inv_cancel₀ (by
  simp only [omega8, ne_eq]
  exact Complex.exp_ne_zero _)

/-- |ω|² = 1, expressed as star(ω) * ω = 1 -/
lemma star_omega8_mul_self : star omega8 * omega8 = 1 := by
  rw [star_omega8, inv_mul_cancel₀]
  simp only [omega8, ne_eq]
  exact Complex.exp_ne_zero _

/-- (star ω)^n * ω^n = 1 -/
lemma star_omega8_pow_mul_self (n : ℕ) : star omega8 ^ n * omega8 ^ n = 1 := by
  rw [← mul_pow, star_omega8_mul_self, one_pow]

/-- ω^{-1} = ω^7 since ω^8 = 1 -/
lemma omega8_inv_eq_pow7 : omega8⁻¹ = omega8 ^ 7 := by
  have h8 : omega8 ^ 8 = 1 := omega8_pow_8
  have h : omega8 ^ 7 * omega8 = 1 := by
    calc
      omega8 ^ 7 * omega8 = omega8 ^ 7 * omega8 ^ 1 := by ring
      _ = omega8 ^ (7 + 1) := by rw [pow_add]
      _ = omega8 ^ 8 := by norm_num
      _ = 1 := h8
  have hne : omega8 ≠ 0 := Complex.exp_ne_zero _
  rw [mul_comm] at h
  exact (eq_inv_of_mul_eq_one_right h).symm

/-- star(ω^n) * ω^m = ω^(7n + m) for n, m : ℕ -/
lemma star_omega8_pow_mul_pow (n m : ℕ) :
    star (omega8 ^ n) * omega8 ^ m = omega8 ^ (7 * n + m) := by
  rw [star_omega8_pow]
  conv_lhs => rw [omega8_inv_eq_pow7]
  rw [← pow_mul, ← pow_add]

/-- Sum over star(ω^{tk}) * ω^{tk'} = sum over ω^{t(7k+k')} -/
lemma sum_star_omega8_pow_prod (k k' : Fin 8) :
    Finset.univ.sum (fun t : Fin 8 => star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k'.val)) =
    Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * (7 * k.val + k'.val))) := by
  congr 1
  ext t
  rw [star_omega8_pow_mul_pow]
  congr 1
  ring

/-- Sum of roots of unity vanishes: ∑_{t=0}^{7} ω^{tk} = 0 for k ≠ 0 mod 8
    Standard result from geometric series. -/
theorem roots_of_unity_sum (k : Fin 8) (hk : k ≠ 0) :
    Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * k.val)) = 0 := by
  -- Let ζ = ω^k, then sum = ∑_{t=0}^{7} ζ^t
  let zeta := omega8 ^ k.val
  have h_sum_eq : Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * k.val))
                = Finset.univ.sum (fun t : Fin 8 => zeta ^ t.val) := by
    congr 1
    ext t
    simp only [zeta, ← pow_mul, mul_comm]
  rw [h_sum_eq]
  have h_zeta8 : zeta ^ 8 = 1 := by
    show (omega8 ^ k.val) ^ 8 = 1
    rw [← pow_mul, mul_comm]
    simp only [pow_mul, omega8_pow_8, one_pow]
  have h_k_pos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
  have h_zeta_ne_one : zeta ≠ 1 := omega8_pow_ne_one_axiom k.val h_k_pos k.isLt
  -- Geometric series: ∑_{t=0}^{7} ζ^t = (ζ^8 - 1) / (ζ - 1)
  -- Since ζ^8 = 1, numerator = 0, so sum = 0
  have h_ne : zeta - 1 ≠ 0 := sub_ne_zero.mpr h_zeta_ne_one
  -- (∑ ζ^t) * (ζ - 1) = ζ^8 - 1 by telescoping
  have h_geom_mul : Finset.univ.sum (fun t : Fin 8 => zeta ^ t.val) * (zeta - 1) = zeta ^ 8 - 1 := by
    have h_expand : Finset.univ.sum (fun t : Fin 8 => zeta ^ t.val) =
                    zeta^0 + zeta^1 + zeta^2 + zeta^3 + zeta^4 + zeta^5 + zeta^6 + zeta^7 := by
      simp only [Fin.sum_univ_eight]
      rfl
    rw [h_expand]
    ring
  rw [h_zeta8, sub_self] at h_geom_mul
  exact (mul_eq_zero.mp h_geom_mul).resolve_right h_ne

/-- Sum of all 8th roots equals 8 when k = 0 -/
lemma roots_of_unity_sum_zero :
    Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * 0)) = 8 := by
  simp [Finset.sum_const]

/-- star(dft8_entry t k) * dft8_entry t k' expressed in terms of omega8 -/
lemma star_dft8_entry_mul (t k k' : Fin 8) :
    star (dft8_entry t k) * dft8_entry t k' =
    star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k'.val) / 8 := by
  simp only [dft8_entry, star_div₀, Complex.star_def, Complex.conj_ofReal]
  have hsqrt8 : (Real.sqrt 8 : ℂ) * Real.sqrt 8 = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_cast
  field_simp
  ring_nf
  rw [sq, hsqrt8]

/-- For k = k', star(ω^{tk}) * ω^{tk} = 1 -/
lemma star_omega8_pow_mul_same (t k : Fin 8) :
    star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k.val) = 1 := by
  rw [star_omega8_pow, ← mul_pow, inv_mul_cancel₀]
  · simp only [one_pow]
  · simp only [omega8, ne_eq]
    exact Complex.exp_ne_zero _

/-- Inner product of DFT columns: ⟨column k, column k'⟩ = δ_{k,k'}
    This is the fundamental orthonormality property of DFT. -/
theorem dft8_column_orthonormal (k k' : Fin 8) :
    Finset.univ.sum (fun t : Fin 8 =>
      star (dft8_entry t k) * dft8_entry t k') =
    if k = k' then 1 else 0 := by
  -- Expand the sum in terms of omega8
  have h_sum : Finset.univ.sum (fun t : Fin 8 => star (dft8_entry t k) * dft8_entry t k') =
               Finset.univ.sum (fun t : Fin 8 => star (omega8 ^ (t.val * k.val)) *
                                                omega8 ^ (t.val * k'.val) / 8) := by
    congr 1
    ext t
    exact star_dft8_entry_mul t k k'
  rw [h_sum]
  -- Factor out the /8
  have h_factor : Finset.univ.sum (fun t : Fin 8 => star (omega8 ^ (t.val * k.val)) *
                                                   omega8 ^ (t.val * k'.val) / 8) =
                  Finset.univ.sum (fun t : Fin 8 => star (omega8 ^ (t.val * k.val)) *
                                                   omega8 ^ (t.val * k'.val)) / 8 := by
    rw [Finset.sum_div]
  rw [h_factor]
  split_ifs with heq
  · -- Case k = k': sum of 1 = 8, divided by 8 = 1
    subst heq
    have h1 : Finset.univ.sum (fun t : Fin 8 => star (omega8 ^ (t.val * k.val)) *
                                               omega8 ^ (t.val * k.val)) = 8 := by
      have h_all_one : ∀ t : Fin 8, star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k.val) = 1 :=
        fun t => star_omega8_pow_mul_same t k
      simp only [h_all_one, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]; norm_cast
    rw [h1]
    norm_num
  · -- Case k ≠ k': use roots_of_unity_sum
    -- By sum_star_omega8_pow_prod: ∑_t star(ω^{tk}) * ω^{tk'} = ∑_t ω^{t(7k+k')}
    rw [sum_star_omega8_pow_prod]
    -- Define the frequency as a Fin 8
    let freq := (7 * k.val + k'.val) % 8
    have h_freq_lt : freq < 8 := Nat.mod_lt _ (by norm_num)
    let freq_fin : Fin 8 := ⟨freq, h_freq_lt⟩
    -- The key: freq_fin ≠ 0 when k ≠ k'
    -- Note: 7k + k' ≡ -k + k' (mod 8), so (7k+k') % 8 = 0 iff k = k'
    have h_freq_ne_zero : freq_fin ≠ 0 := by
      simp only [freq_fin, freq, ne_eq, Fin.ext_iff, Fin.val_zero]
      have hk : k.val < 8 := k.isLt
      have hk' : k'.val < 8 := k'.isLt
      have hne : k.val ≠ k'.val := fun h => heq (Fin.ext h)
      omega
    -- First show ∑_t ω^{t(7k+k')} = ∑_t ω^{t * freq}
    have h_pow_mod : ∀ t : Fin 8, omega8 ^ (t.val * (7 * k.val + k'.val)) =
                                  omega8 ^ (t.val * freq_fin.val) := by
      intro t
      simp only [freq_fin, freq]
      have h8 : omega8 ^ 8 = 1 := omega8_pow_8
      have h_eq : t.val * (7 * k.val + k'.val) % 8 = t.val * ((7 * k.val + k'.val) % 8) % 8 := by
        conv_lhs => rw [Nat.mul_mod]
        conv_rhs => rw [Nat.mul_mod]
        have h_mod_lt : (7 * k.val + k'.val) % 8 < 8 := Nat.mod_lt _ (by norm_num)
        rw [Nat.mod_eq_of_lt h_mod_lt]
      have h_period : ∀ n m : ℕ, n % 8 = m % 8 → omega8 ^ n = omega8 ^ m := by
        intro n m heq
        have hn : n = 8 * (n / 8) + n % 8 := (Nat.div_add_mod n 8).symm
        have hm : m = 8 * (m / 8) + m % 8 := (Nat.div_add_mod m 8).symm
        rw [hn, hm, heq]
        rw [pow_add, pow_add, pow_mul, pow_mul, h8, one_pow, one_pow]
      apply h_period
      exact h_eq
    have h_sum_eq :
        Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * (7 * k.val + k'.val))) =
          Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * freq_fin.val)) := by
      congr 1; ext t; exact h_pow_mod t
    rw [h_sum_eq]
    have h_roots := roots_of_unity_sum freq_fin h_freq_ne_zero
    simp only [div_eq_zero_iff, h_roots, true_or]

/-- DFT-8 matrix is unitary: B^H · B = I -/
theorem dft8_unitary :
    dft8_matrix.conjTranspose * dft8_matrix = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  -- (B^H · B)_{i,j} = ∑_t conj(B_{t,i}) * B_{t,j} = ∑_t conj(dft8_entry t i) * dft8_entry t j
  -- By dft8_column_orthonormal, this equals δ_{i,j}
  convert dft8_column_orthonormal i j using 1

/-- Row orthonormality: Σ_k star(B_sk) * B_tk = δ_{s,t}.
    Follows from column orthonormality via symmetry B_tk = B_kt. -/
theorem dft8_row_orthonormal (s t : Fin 8) :
    Finset.univ.sum (fun k : Fin 8 => star (dft8_entry s k) * dft8_entry t k) =
    if s = t then 1 else 0 := by
  -- Use symmetry: B_sk = B_ks and B_tk = B_kt
  have h_sym : ∀ k, star (dft8_entry s k) * dft8_entry t k =
      star (dft8_entry k s) * dft8_entry k t := fun k => by
    rw [dft8_entry_sym s k, dft8_entry_sym t k]
  simp_rw [h_sym]
  -- Now it's exactly column orthonormality with swapped indices
  exact dft8_column_orthonormal s t

/-! ## Shift Diagonalization -/

/-- The eigenvalue of cyclic shift on mode k is ω^k -/
noncomputable def shift_eigenvalue (k : Fin 8) : ℂ := omega8 ^ k.val

/-- Helper: (t + 1) mod 8 * k ≡ (t + 1) * k mod 8 -/
lemma mod8_mul_eq (t : Fin 8) (k : ℕ) :
    omega8 ^ (((t.val + 1) % 8) * k) = omega8 ^ ((t.val + 1) * k) := by
  -- Since ω^8 = 1, ω^(a mod 8 * k) = ω^(a * k mod 8) = ω^(a * k)
  have h8 : omega8 ^ 8 = 1 := omega8_pow_8
  cases Nat.lt_or_ge (t.val + 1) 8 with
  | inl hlt =>
    -- t.val + 1 < 8, so mod is identity
    simp only [Nat.mod_eq_of_lt hlt]
  | inr hge =>
    -- t.val + 1 ≥ 8, but t.val < 8, so t.val + 1 ∈ [8, 8], i.e., = 8
    have h_eq : t.val + 1 = 8 := by omega
    simp only [h_eq, Nat.mod_self]
    -- Need: ω^(0 * k) = ω^(8 * k)
    simp only [zero_mul, pow_zero]
    -- ω^(8 * k) = (ω^8)^k = 1^k = 1
    rw [pow_mul, h8, one_pow]

/-- DFT mode k is an eigenvector of cyclic shift with eigenvalue ω^k.
    This is the key property: DFT diagonalizes the shift operator. -/
theorem dft8_shift_eigenvector (k : Fin 8) :
    cyclic_shift (dft8_mode k) = (omega8 ^ k.val) • (dft8_mode k) := by
  funext t
  simp only [cyclic_shift, dft8_mode, dft8_entry, Pi.smul_apply, smul_eq_mul]
  -- LHS: ω^{((t+1) % 8)k} / √8, RHS: ω^k * ω^{tk} / √8
  rw [mod8_mul_eq]
  have h_add : (t.val + 1) * k.val = t.val * k.val + k.val := by ring
  rw [h_add, pow_add]
  ring

/-- (S * B)_{t,j} = ω^j * B_{t,j} - the shift on column j equals ω^j times that column entry -/
lemma shift_mul_dft8_entry (t j : Fin 8) :
    (shift_matrix * dft8_matrix) t j = (omega8 ^ j.val) * dft8_matrix t j := by
  -- Use dft8_shift_eigenvector directly
  have h := dft8_shift_eigenvector j
  have h_t := congrFun h t
  simp only [cyclic_shift, dft8_mode, dft8_entry, Pi.smul_apply, smul_eq_mul] at h_t
  simp only [Matrix.mul_apply, shift_matrix, dft8_matrix, dft8_entry]
  -- Convert the sum to a single term using the shift matrix structure
  let idx : Fin 8 := ⟨(t.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩
  have h_fin : idx ∈ Finset.univ := Finset.mem_univ _
  rw [Finset.sum_eq_single idx]
  · -- Main case: s = idx
    have hcond : idx.val = (t.val + 1) % 8 := rfl
    simp only [hcond, ↓reduceIte, one_mul]
    exact h_t
  · -- Other cases: s ≠ idx
    intro s _ hs
    have hne : ¬(s.val = (t.val + 1) % 8) := by
      intro heq
      apply hs
      ext
      simp only [idx]
      exact heq
    simp only [hne, ↓reduceIte, zero_mul]
  · intro h_not_in
    exact absurd h_fin h_not_in

/-- B^H * (S * B) at entry (i, j) equals ω^j * δ_{i,j} -/
lemma conjTranspose_shift_mul (i j : Fin 8) :
    (dft8_matrix.conjTranspose * (shift_matrix * dft8_matrix)) i j =
    (omega8 ^ j.val) * (if i = j then 1 else 0) := by
  have h_expand : (dft8_matrix.conjTranspose * (shift_matrix * dft8_matrix)) i j =
                  ∑ t, star (dft8_matrix t i) * (shift_matrix * dft8_matrix) t j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h_expand]
  -- Use shift_mul_dft8_entry to simplify each term
  have h_simp : ∀ t, star (dft8_matrix t i) * (shift_matrix * dft8_matrix) t j =
                     (omega8 ^ j.val) * (star (dft8_matrix t i) * dft8_matrix t j) := by
    intro t
    rw [shift_mul_dft8_entry]
    ring
  simp only [h_simp, ← Finset.mul_sum]
  -- Now show ∑_t star(B_{t,i}) * B_{t,j} = δ_{i,j}
  have h_ortho := dft8_column_orthonormal i j
  simp only [dft8_matrix, h_ortho, mul_ite, mul_one, mul_zero]

/-- DFT diagonalizes the shift operator:
    B^H · S · B = diag(1, ω, ω², ..., ω⁷) -/
theorem dft8_diagonalizes_shift :
    dft8_matrix.conjTranspose * shift_matrix * dft8_matrix =
    Matrix.diagonal (fun k => shift_eigenvalue k) := by
  ext i j
  rw [Matrix.mul_assoc]
  rw [conjTranspose_shift_mul]
  simp only [Matrix.diagonal, Matrix.of_apply, shift_eigenvalue]
  split_ifs with h
  · subst h; ring
  · ring
/-! ## Neutral Subspace -/

/-- Mode k=0 is the constant (DC) mode -/
lemma dft8_mode_zero_constant :
    ∀ t : Fin 8, dft8_mode 0 t = 1 / Real.sqrt 8 := by
  intro t
  unfold dft8_mode dft8_entry
  simp [mul_zero, pow_zero]

/-- Modes k=1..7 are orthogonal to the constant mode (mean-free) -/
lemma dft8_mode_neutral (k : Fin 8) (hk : k ≠ 0) :
    Finset.univ.sum (dft8_mode k) = 0 := by
  unfold dft8_mode dft8_entry
  -- Sum of ω^{tk} over t = 0 for k ≠ 0 (roots of unity sum)
  have hzero : Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * k.val)) = 0 :=
    roots_of_unity_sum k hk
  have hsum :
      Finset.univ.sum (fun t : Fin 8 =>
          omega8 ^ (t.val * k.val) * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹) =
        (Finset.univ.sum fun t : Fin 8 => omega8 ^ (t.val * k.val)) *
          ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ := by
    simpa using
      (Finset.sum_mul
        (s := (Finset.univ : Finset (Fin 8)))
        (f := fun t : Fin 8 => omega8 ^ (t.val * k.val))
        (((Real.sqrt 8 : ℝ) : ℂ)⁻¹)).symm
  simpa [div_eq_mul_inv, hzero] using hsum

/-! ## Inverse DFT and Neutral Subspace -/

/-- DFT coefficients of a vector v: c_k = ∑_t conj(mode_k(t)) · v(t) -/
noncomputable def dft_coefficients (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun k => Finset.univ.sum (fun t => star (dft8_entry t k) * v t)

/-- The DC coefficient of v is (1/√8) · ∑v -/
lemma dft_coeff_zero (v : Fin 8 → ℂ) :
    dft_coefficients v 0 = (Finset.univ.sum v) / Real.sqrt 8 := by
  unfold dft_coefficients dft8_entry
  simp only [Fin.val_zero, mul_zero, pow_zero, one_div, star_inv₀]
  -- star((√8)⁻¹) * v t = (√8)⁻¹ * v t since √8 is real
  have hsqrt_real : (star ((Real.sqrt 8 : ℝ) : ℂ)) = ((Real.sqrt 8 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have h_factor : ∀ t, (star ((Real.sqrt 8 : ℝ) : ℂ))⁻¹ * v t =
                       ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * v t := by
    intro t; rw [hsqrt_real]
  simp only [h_factor]
  have h_comm : ∀ t, ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * v t = v t * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ := by
    intro t; ring
  simp only [h_comm, ← Finset.sum_mul]
  rfl

/-- If v is neutral (∑v = 0), its DC coefficient is 0 -/
lemma dft_coeff_zero_of_neutral (v : Fin 8 → ℂ) (hv : Finset.univ.sum v = 0) :
    dft_coefficients v 0 = 0 := by
  rw [dft_coeff_zero, hv, zero_div]

/-- Inverse DFT expansion using matrix notation.
    Since DFT is unitary (B^H B = I), we also have B B^H = I.
    Thus v = B · (B^H · v) = ∑_k ⟨mode_k, v⟩ · mode_k. -/
lemma inverse_dft_expansion (v : Fin 8 → ℂ) :
    ∀ t, v t = Finset.univ.sum (fun k => dft_coefficients v k * dft8_entry t k) := by
  intro t
  simp only [dft_coefficients]
  -- v(t) = ∑_k (∑_s conj(B_{s,k}) v(s)) B_{t,k}
  -- Rearrange: = ∑_s v(s) (∑_k conj(B_{s,k}) B_{t,k})
  --           = ∑_s v(s) δ_{s,t}  [by row orthonormality]
  --           = v(t)
  have h_sum : (∑ k : Fin 8, (∑ s : Fin 8, star (dft8_entry s k) * v s) * dft8_entry t k) =
               ∑ s : Fin 8, v s * ∑ k : Fin 8, star (dft8_entry s k) * dft8_entry t k := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    ext s
    congr 1
    ext k
    ring
  rw [h_sum]
  have h_ortho : ∀ s, Finset.univ.sum (fun k => star (dft8_entry s k) * dft8_entry t k) =
                      if s = t then 1 else 0 := fun s => dft8_row_orthonormal s t
  simp only [h_ortho]
  simp [Finset.sum_ite_eq']

/-- The 7 non-DC modes span the neutral subspace.
    Any mean-free vector can be expressed as a linear combination of modes 1..7.

    Proof: Using inverse DFT, v = ∑_k c_k · mode_k. For neutral v, c_0 = 0,
    so v = ∑_{k≠0} c_k · mode_k is in span{mode_1, ..., mode_7}. -/
theorem dft8_neutral_subspace :
    ∀ v : Fin 8 → ℂ,
      Finset.univ.sum v = 0 →
        v ∈ Submodule.span ℂ {m | ∃ k : Fin 8, k ≠ 0 ∧ m = dft8_mode k} := by
  intro v hv
  -- Step 1: DC coefficient is 0 for neutral v
  have h_c0 := dft_coeff_zero_of_neutral v hv
  -- Step 2: Rewrite v using inverse DFT as a sum of smul'd modes
  have h_inv := inverse_dft_expansion v
  have h_eq : v = Finset.univ.sum (fun k => dft_coefficients v k • dft8_mode k) := by
    ext t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dft8_mode]
    exact h_inv t
  rw [h_eq]
  -- Split sum: k=0 contributes 0, rest are in span
  have h_zero_term : dft_coefficients v 0 • dft8_mode 0 = 0 := by simp [h_c0]
  -- Isolate k=0 using Finset manipulation
  have h_mem_univ : (0 : Fin 8) ∈ Finset.univ := Finset.mem_univ 0
  rw [← Finset.insert_erase h_mem_univ, Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
  rw [h_zero_term, zero_add]
  -- Sum over k ≠ 0 is in span
  apply Submodule.sum_mem
  intro k hk
  have hk_ne : k ≠ 0 := Finset.ne_of_mem_erase hk
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨k, hk_ne, rfl⟩

/-- Legacy alias for compatibility. -/
def dft8_neutral_subspace_hypothesis : Prop :=
    ∀ v : Fin 8 → ℂ,
      Finset.univ.sum v = 0 →
        v ∈ Submodule.span ℂ {m | ∃ k : Fin 8, k ≠ 0 ∧ m = dft8_mode k}

/-- The hypothesis is now a theorem. -/
theorem dft8_neutral_subspace_hypothesis_holds : dft8_neutral_subspace_hypothesis :=
  dft8_neutral_subspace

/-! ## Uniqueness (Representation-Theoretic) -/

/-- The DFT-8 basis is unique up to permutation and phase among bases that
    diagonalize the cyclic shift operator.

    This follows from the representation theory of cyclic groups:
    - The cyclic group Z/8Z has exactly 8 one-dimensional irreducible representations
    - The characters are χ_k(g) = ω^{kg} for k = 0, 1, ..., 7
    - Any basis diagonalizing the shift must consist of eigenvectors
    - The eigenvectors are unique up to scalar multiple (one-dimensional eigenspaces)

    Therefore DFT-8 is the canonical choice (with standard normalization).
    Note: This was an axiom but is not used in any proofs. Converted to hypothesis. -/
def dft8_unique_up_to_phase_hypothesis : Prop :=
    ∀ (B : Matrix (Fin 8) (Fin 8) ℂ),
      -- B is unitary
      B.conjTranspose * B = 1 →
      -- B diagonalizes shift
      (∃ D : Fin 8 → ℂ, B.conjTranspose * shift_matrix * B = Matrix.diagonal D) →
      -- Then B differs from dft8_matrix only by a diagonal phase matrix
      ∃ (phases : Fin 8 → ℂ) (perm : Equiv.Perm (Fin 8)),
        (∀ k, ‖phases k‖ = 1) ∧
        ∀ t k, B t k = phases k * dft8_matrix t (perm k)

/-! ## Eight-Tick Basis Type -/

/-- The canonical eight-tick DFT basis as a bundled structure.
    This provides the standard basis for all 8-tick spectral operations. -/
structure EightTickBasis where
  /-- The 8 basis vectors (DFT modes) -/
  modes : Fin 8 → (Fin 8 → ℂ)
  /-- Mode 0 is the DC (constant) mode -/
  mode_zero_dc : ∀ t, modes 0 t = 1 / Real.sqrt 8
  /-- Modes 1..7 are neutral (mean-free) -/
  modes_neutral : ∀ k, k ≠ 0 → Finset.univ.sum (modes k) = 0
  /-- Modes are orthonormal -/
  modes_orthonormal : ∀ k k',
    Finset.univ.sum (fun t => star (modes k t) * modes k' t) =
    if k = k' then 1 else 0

/-- The standard DFT-8 basis instance -/
noncomputable def standardDFT8Basis : EightTickBasis where
  modes := dft8_mode
  mode_zero_dc := dft8_mode_zero_constant
  modes_neutral := dft8_mode_neutral
  modes_orthonormal := dft8_column_orthonormal

/-- Theorem: The standard DFT-8 basis is the unique shift-invariant basis.
    Any other orthonormal basis that diagonalizes cyclic shift is equivalent
    to DFT-8 up to phase and permutation.
    Note: This was an axiom but is not used in any proofs. Converted to hypothesis. -/
def standardDFT8Basis_canonical_hypothesis : Prop :=
    ∀ (B : EightTickBasis),
      (∀ k, ∃ lam : ℂ, cyclic_shift (B.modes k) = lam • B.modes k) →
      ∃ (phases : Fin 8 → ℂ) (perm : Equiv.Perm (Fin 8)),
        (∀ k, ‖phases k‖ = 1) ∧
        ∀ k t, B.modes k t = phases k * standardDFT8Basis.modes (perm k) t

end Spectral
end IndisputableMonolith
