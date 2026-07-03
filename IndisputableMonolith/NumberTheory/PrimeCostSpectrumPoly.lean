import Mathlib
import IndisputableMonolith.Cost

/-!
# The Cost Spectrum on the Polynomial Ring `F[X]`

This module is the function-field analog of
`IndisputableMonolith.NumberTheory.PrimeCostSpectrum`.
For a finite field `F` of cardinality `q`, the polynomial ring `F[X]`
is a unique factorization domain in which every nonzero monic
polynomial factors uniquely into monic irreducibles.

The norm of a monic polynomial `f` is `‖f‖ := q^(deg f)`.
Every monic irreducible `P` of degree `n` has norm `q^n`.
The cost function extends to `F[X]` via

  `c(f) := Σ_{P irreducible} v_P(f) · J(‖P‖)`

where `v_P(f)` is the multiplicity of `P` in the factorization of `f`.

We define `c` for arbitrary nonzero polynomials (not just monic) via
the multiset of normalized factors, which is well-defined in any UFD
via mathlib's `normalizedFactors`.

## Main definitions

* `polyCost q f`         : the cost of a polynomial `f`, computed
                           from `normalizedFactors f`, using `q` as
                           the field cardinality parameter.
* `polyPrimeCost q P`    : the cost of an irreducible factor `P`,
                           equal to `Jcost (q^(deg P) : ℝ)`.

## Main theorems (all 0 sorry, 0 axiom)

* `polyPrimeCost_pos`     : the cost of any irreducible polynomial of
                            positive degree is strictly positive.
* `polyCost_one`          : `c(1) = 0`.
* `polyCost_mul`          : `c(f g) = c(f) + c(g)` for nonzero `f, g`.
* `polyCost_irreducible`  : `c(P) = J(q^(deg P))` for `P` monic
                            irreducible of positive degree.
* `polyCost_pow`          : `c(P^k) = k · J(q^(deg P))`.
* `polyCost_nonneg`       : `c(f) ≥ 0`.
* `cost_spectrum_poly_certificate` : bundled certificate.

## Lean status: 0 sorry
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PrimeCostSpectrumPoly

open Polynomial Cost UniqueFactorizationMonoid

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The norm of a polynomial

The norm of a polynomial of degree `n` over a field of cardinality `q`
is `q^n`.  By convention the norm of the zero polynomial is `0` and the
norm of a unit (degree 0) polynomial is `1`. -/

/-- The norm `q^(deg f)` of a polynomial as a real number, where
    `q := Fintype.card F`. -/
def polyNorm (f : Polynomial F) : ℝ :=
  (Fintype.card F : ℝ) ^ f.natDegree

@[simp] theorem polyNorm_one : polyNorm (1 : Polynomial F) = 1 := by
  unfold polyNorm; simp

theorem polyNorm_pos (f : Polynomial F) : 0 < polyNorm f := by
  unfold polyNorm
  have hq : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact pow_pos hq _

/-! ## Cost spectrum: per-irreducible and total -/

/-- The cost of an irreducible polynomial `P`, equal to `J(‖P‖)`. -/
def polyPrimeCost (P : Polynomial F) : ℝ := Jcost (polyNorm P)

/-- The cost of a polynomial `f`, computed by summing the per-factor
    cost over the multiset of normalized irreducible factors of `f`.
    By convention `polyCost 0 = 0`. -/
def polyCost (f : Polynomial F) : ℝ :=
  ((normalizedFactors f).map polyPrimeCost).sum

/-! ## Elementary properties -/

@[simp] theorem polyCost_zero : polyCost (0 : Polynomial F) = 0 := by
  unfold polyCost
  simp [normalizedFactors_zero]

@[simp] theorem polyCost_one : polyCost (1 : Polynomial F) = 0 := by
  unfold polyCost
  simp [normalizedFactors_one]

/-- The norm of a monic polynomial of positive degree is at least `q ≥ 2`,
    hence at least `2`.  Combined with `Jcost_pos_of_ne_one`, this gives
    `polyPrimeCost P > 0` for any irreducible polynomial of positive degree
    over a field with at least 2 elements. -/
theorem polyPrimeCost_pos {P : Polynomial F} (hP : 0 < P.natDegree)
    (hF : 2 ≤ Fintype.card F) : 0 < polyPrimeCost P := by
  unfold polyPrimeCost
  have hnorm_pos : 0 < polyNorm P := polyNorm_pos P
  have hnorm_ne_one : polyNorm P ≠ 1 := by
    unfold polyNorm
    have hq_real : (1 : ℝ) < (Fintype.card F : ℝ) := by
      exact_mod_cast hF
    have h_pow_gt : 1 < (Fintype.card F : ℝ) ^ P.natDegree :=
      one_lt_pow₀ hq_real (Nat.pos_iff_ne_zero.mp hP)
    exact ne_of_gt h_pow_gt
  exact Jcost_pos_of_ne_one (polyNorm P) hnorm_pos hnorm_ne_one

/-- `polyPrimeCost` is nonnegative on any polynomial (it is always `J`
    of a positive real). -/
theorem polyPrimeCost_nonneg (P : Polynomial F) : 0 ≤ polyPrimeCost P :=
  Jcost_nonneg (polyNorm_pos P)

/-- `polyCost` is nonnegative on any polynomial. -/
theorem polyCost_nonneg (f : Polynomial F) : 0 ≤ polyCost f := by
  unfold polyCost
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨P, _, hP_eq⟩ := Multiset.mem_map.mp hx
  rw [← hP_eq]
  exact polyPrimeCost_nonneg P

/-! ## Multiplicativity over factorization -/

/-- The total cost is additive under multiplication of nonzero polynomials.
    This is the function-field analog of `costSpectrumValue_mul`. -/
theorem polyCost_mul {f g : Polynomial F} (hf : f ≠ 0) (hg : g ≠ 0) :
    polyCost (f * g) = polyCost f + polyCost g := by
  unfold polyCost
  rw [normalizedFactors_mul hf hg]
  rw [Multiset.map_add, Multiset.sum_add]

/-! ## Cost on irreducibles and powers -/

/-- For a monic irreducible polynomial `P`, the cost equals `J(‖P‖)`.
    Mathlib's `normalizedFactors` returns the multiset of monic
    irreducible factors. -/
theorem polyCost_irreducible {P : Polynomial F}
    (hP_irr : Irreducible P) (hP_monic : P.Monic) :
    polyCost P = polyPrimeCost P := by
  unfold polyCost
  rw [normalizedFactors_irreducible hP_irr]
  have hP_ne : P ≠ 0 := hP_irr.ne_zero
  have h_norm : normalize P = P :=
    (normalize_eq_self_iff_monic hP_ne).mpr hP_monic
  rw [h_norm]
  simp

/-- Cost on a power: `c(P^k) = k · c(P)` for any nonzero `P`. -/
theorem polyCost_pow {P : Polynomial F} (hP : P ≠ 0) (k : ℕ) :
    polyCost (P ^ k) = (k : ℝ) * polyCost P := by
  induction k with
  | zero => simp [polyCost_one]
  | succ k ih =>
    have hPk : P ^ k ≠ 0 := pow_ne_zero k hP
    rw [pow_succ, polyCost_mul hPk hP, ih]
    push_cast
    ring

/-- Cost is monotonic under multiplication by nonzero polynomials. -/
theorem polyCost_le_mul {f g : Polynomial F} (hf : f ≠ 0) (hg : g ≠ 0) :
    polyCost f ≤ polyCost (f * g) := by
  rw [polyCost_mul hf hg]
  have := polyCost_nonneg g
  linarith

/-! ## Strict positivity for non-units -/

/-- An irreducible polynomial over a field has positive `natDegree`.
    A polynomial with `natDegree = 0` is either zero or a unit;
    irreducibles are neither. -/
private lemma irreducible_natDegree_pos {P : Polynomial F}
    (hP_irr : Irreducible P) : 0 < P.natDegree := by
  rw [Nat.pos_iff_ne_zero]
  intro h_zero
  have hP_ne : P ≠ 0 := hP_irr.ne_zero
  -- natDegree = 0 ⟹ P = C (coeff P 0).
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h_zero
  -- coeff P 0 ≠ 0 because P ≠ 0.
  have hc_ne : c ≠ 0 := by
    intro h_c_zero
    apply hP_ne
    rw [← hc, h_c_zero]
    simp
  -- A constant polynomial with nonzero constant is a unit in F[X].
  have hP_unit : IsUnit P := by
    rw [← hc]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc_ne)
  exact hP_irr.not_isUnit hP_unit

/-- If `f` is a nonzero non-unit polynomial over a field with `q ≥ 2`,
    then `polyCost f > 0`. -/
theorem polyCost_pos {f : Polynomial F}
    (hf : f ≠ 0) (h_not_unit : ¬ IsUnit f)
    (hF : 2 ≤ Fintype.card F) :
    0 < polyCost f := by
  -- Since f is a nonzero non-unit, normalizedFactors f is nonempty.
  have h_factors_ne : normalizedFactors f ≠ 0 := by
    intro h_empty
    have h_prod : (normalizedFactors f).prod = normalize f :=
      prod_normalizedFactors_eq hf
    rw [h_empty, Multiset.prod_zero] at h_prod
    have h_norm_unit : IsUnit (normalize f) := h_prod ▸ isUnit_one
    have h_f_unit : IsUnit f :=
      (associated_normalize f).symm.isUnit h_norm_unit
    exact h_not_unit h_f_unit
  -- Pick a factor P from normalizedFactors f.
  obtain ⟨P, hP_mem⟩ := Multiset.exists_mem_of_ne_zero h_factors_ne
  have hP_irr : Irreducible P := irreducible_of_normalized_factor P hP_mem
  have hP_deg : 0 < P.natDegree := irreducible_natDegree_pos hP_irr
  have hP_pos : 0 < polyPrimeCost P := polyPrimeCost_pos hP_deg hF
  -- Decompose the multiset sum: P contributes hP_pos, others ≥ 0.
  unfold polyCost
  have h_decomp :
      (normalizedFactors f).map polyPrimeCost
        = polyPrimeCost P ::ₘ ((normalizedFactors f).erase P).map polyPrimeCost := by
    rw [← Multiset.map_cons polyPrimeCost P]
    congr 1
    exact (Multiset.cons_erase hP_mem).symm
  rw [h_decomp, Multiset.sum_cons]
  apply add_pos_of_pos_of_nonneg hP_pos
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨Q, _, hQ_eq⟩ := Multiset.mem_map.mp hx
  rw [← hQ_eq]
  exact polyPrimeCost_nonneg Q

/-! ## Cost spectrum certificate -/

/-- Master certificate: the elementary properties of the polynomial
    cost spectrum.  Mirrors `cost_spectrum_certificate` from the integer
    module.  Used by the companion paper. -/
theorem cost_spectrum_poly_certificate :
    -- (1) Per-irreducible cost is strictly positive (positive degree, q ≥ 2).
    (∀ {P : Polynomial F}, 0 < P.natDegree → 2 ≤ Fintype.card F →
      0 < polyPrimeCost P) ∧
    -- (2) Cost is zero at the unit polynomial 1.
    (polyCost (1 : Polynomial F) = 0) ∧
    -- (3) Cost is nonnegative everywhere.
    (∀ (f : Polynomial F), 0 ≤ polyCost f) ∧
    -- (4) Cost is strictly positive on non-units (q ≥ 2).
    (∀ {f : Polynomial F}, f ≠ 0 → ¬ IsUnit f → 2 ≤ Fintype.card F →
      0 < polyCost f) ∧
    -- (5) Cost is completely additive over nonzero products.
    (∀ {f g : Polynomial F}, f ≠ 0 → g ≠ 0 →
      polyCost (f * g) = polyCost f + polyCost g) ∧
    -- (6) Cost on a monic irreducible equals its prime cost.
    (∀ {P : Polynomial F}, Irreducible P → P.Monic →
      polyCost P = polyPrimeCost P) ∧
    -- (7) Cost on a power: c(P^k) = k · c(P) for any nonzero P.
    (∀ {P : Polynomial F} (_ : P ≠ 0) (k : ℕ),
      polyCost (P ^ k) = (k : ℝ) * polyCost P) :=
  ⟨@polyPrimeCost_pos F _ _ _,
   polyCost_one,
   polyCost_nonneg,
   @polyCost_pos F _ _ _,
   @polyCost_mul F _ _ _,
   @polyCost_irreducible F _ _ _,
   @polyCost_pow F _ _ _⟩

end

end PrimeCostSpectrumPoly
end NumberTheory
end IndisputableMonolith
