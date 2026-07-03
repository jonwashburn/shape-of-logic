import Mathlib

/-!
  HadamardGenusOne.lean

  Concrete analytic substrate for the genus-one Hadamard factorization.

  Mathlib does not currently package the Hadamard factorization theorem for
  entire functions of order ≤ 1. This module proves what is unconditionally
  provable for the genus-one elementary Weierstrass factor
  `E₁(z) = (1 - z) · exp(z)`:

  * the per-factor norm estimate `‖E₁(z) - 1‖ ≤ 3 ‖z‖²` for `‖z‖ ≤ 1`;
  * absolute summability of the corrections `E₁(z_n) - 1` from absolute
    summability of `‖z_n‖²`;
  * Multipliability of the partial products `∏ E₁(z_n)`.

  These are the analytic prerequisites for the Hadamard product. Three named
  pieces remain open:

  1. `XiOrderBound`     : `completedRiemannZeta₀` has order ≤ 1.
  2. `XiZeroSummability`: the inverse-square moduli of its zeros are summable.
  3. `XiHadamardIdentification` : the partial product limit equals
                                   `completedRiemannZeta₀` up to `exp(A+Bs)`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace HadamardGenusOne

open Complex

noncomputable section

/-! ## 1. The genus-one elementary factor -/

/-- The genus-one elementary Weierstrass factor `E₁(z) = (1 - z) · exp(z)`. -/
def E1 (z : ℂ) : ℂ := (1 - z) * Complex.exp z

@[simp] theorem E1_zero : E1 0 = 1 := by simp [E1]

theorem E1_one : E1 1 = 0 := by simp [E1]

/-- Algebraic identity `E₁(z) - 1 = (exp z - 1 - z) - z (exp z - 1)`. -/
theorem E1_sub_one_eq (z : ℂ) :
    E1 z - 1 = (Complex.exp z - 1 - z) - z * (Complex.exp z - 1) := by
  unfold E1
  have hz : Complex.exp z = 1 + (Complex.exp z - 1) := by ring
  conv_lhs => rw [hz]
  ring

/-! ## 2. The per-factor estimate -/

/-- `‖exp z - 1‖ ≤ 2 ‖z‖` for `‖z‖ ≤ 1`. -/
private theorem norm_exp_sub_one_le_two_mul (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  have h1 : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le hz
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ := by
    have := mul_le_mul_of_nonneg_left hz hzn
    have heq : ‖z‖ * ‖z‖ = ‖z‖ ^ 2 := by ring
    rw [heq] at this
    have : ‖z‖ * 1 = ‖z‖ := by ring
    linarith [this]
  calc
    ‖Complex.exp z - 1‖
        = ‖(Complex.exp z - 1 - z) + z‖ := by ring_nf
    _ ≤ ‖Complex.exp z - 1 - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 2 + ‖z‖ := by linarith
    _ ≤ ‖z‖ + ‖z‖ := by linarith
    _ = 2 * ‖z‖ := by ring

/-- The genus-one factor estimate: `‖E₁(z) - 1‖ ≤ 3 ‖z‖²` for `‖z‖ ≤ 1`. -/
theorem norm_E1_sub_one_le (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖E1 z - 1‖ ≤ 3 * ‖z‖ ^ 2 := by
  rw [E1_sub_one_eq]
  have h1 : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le hz
  have hexp : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ :=
    norm_exp_sub_one_le_two_mul z hz
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have h2 : ‖z * (Complex.exp z - 1)‖ ≤ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul]
    calc
      ‖z‖ * ‖Complex.exp z - 1‖
          ≤ ‖z‖ * (2 * ‖z‖) := by
              exact mul_le_mul_of_nonneg_left hexp hzn
      _ = 2 * ‖z‖ ^ 2 := by ring
  calc
    ‖(Complex.exp z - 1 - z) - z * (Complex.exp z - 1)‖
        ≤ ‖Complex.exp z - 1 - z‖ + ‖z * (Complex.exp z - 1)‖ :=
          norm_sub_le _ _
    _ ≤ ‖z‖ ^ 2 + 2 * ‖z‖ ^ 2 := by linarith
    _ = 3 * ‖z‖ ^ 2 := by ring

/-! ## 3. Absolute summability of `E₁` corrections -/

/-- If `‖z_n‖ ≤ 1` for all `n` and `‖z_n‖²` is summable, then `‖E₁(z_n) - 1‖`
is summable. -/
theorem summable_norm_E1_sub_one_of_summable_sq
    (z : ℕ → ℂ) (hbnd : ∀ n, ‖z n‖ ≤ 1)
    (hsum : Summable (fun n => ‖z n‖ ^ 2)) :
    Summable (fun n => ‖E1 (z n) - 1‖) := by
  refine (hsum.mul_left 3).of_norm_bounded ?_
  intro n
  have h := norm_E1_sub_one_le (z n) (hbnd n)
  have hnn : 0 ≤ ‖E1 (z n) - 1‖ := norm_nonneg _
  rw [Real.norm_of_nonneg hnn]
  exact h

/-- The corrections `E₁(z_n) - 1` are themselves summable in `ℂ` under the
square-summable bounded-zero hypothesis. -/
theorem summable_E1_sub_one_of_summable_sq
    (z : ℕ → ℂ) (hbnd : ∀ n, ‖z n‖ ≤ 1)
    (hsum : Summable (fun n => ‖z n‖ ^ 2)) :
    Summable (fun n => E1 (z n) - 1) :=
  (summable_norm_E1_sub_one_of_summable_sq z hbnd hsum).of_norm

/-! ## 4. Multipliability of genus-one products -/

/-- If the per-factor corrections `E₁(z_n) - 1` are summable in `ℂ`, then the
genus-one partial products are multipliable. -/
theorem multipliable_E1_of_summable_sub_one
    (z : ℕ → ℂ)
    (hsum : Summable (fun n => E1 (z n) - 1)) :
    Multipliable (fun n => E1 (z n)) := by
  have h := Complex.multipliable_one_add_of_summable hsum
  have heq : (fun n => 1 + (E1 (z n) - 1)) = (fun n => E1 (z n)) := by
    funext n; ring
  simpa [heq] using h

/-- Combined corollary: from square-summable bounded zeros, the genus-one
product is multipliable. -/
theorem multipliable_E1_of_summable_sq
    (z : ℕ → ℂ) (hbnd : ∀ n, ‖z n‖ ≤ 1)
    (hsum : Summable (fun n => ‖z n‖ ^ 2)) :
    Multipliable (fun n => E1 (z n)) :=
  multipliable_E1_of_summable_sub_one z
    (summable_E1_sub_one_of_summable_sq z hbnd hsum)

/-! ## 5. Uniform-on-disk estimate -/

/-- For zeros at modulus at least `‖s‖` (i.e. `s` inside the closed disk of
radius `‖ρ‖`), each genus-one factor satisfies the per-factor estimate. -/
theorem norm_E1_sub_one_at_quotient_le
    (s : ℂ) (ρ : ℂ) (hρ : ρ ≠ 0) (hbound : ‖s‖ ≤ ‖ρ‖) :
    ‖E1 (s / ρ) - 1‖ ≤ 3 * ‖s‖ ^ 2 / ‖ρ‖ ^ 2 := by
  have hρn : 0 < ‖ρ‖ := by
    have hne : ‖ρ‖ ≠ 0 := fun h => hρ ((norm_eq_zero).1 h)
    exact lt_of_le_of_ne (norm_nonneg ρ) (Ne.symm hne)
  have hquot_norm : ‖s / ρ‖ = ‖s‖ / ‖ρ‖ := norm_div s ρ
  have hbnd : ‖s / ρ‖ ≤ 1 := by
    rw [hquot_norm]
    exact (div_le_one hρn).mpr hbound
  have h := norm_E1_sub_one_le (s / ρ) hbnd
  rw [hquot_norm] at h
  calc
    ‖E1 (s / ρ) - 1‖
        ≤ 3 * (‖s‖ / ‖ρ‖) ^ 2 := h
    _ = 3 * ‖s‖ ^ 2 / ‖ρ‖ ^ 2 := by
          rw [div_pow]; ring

/-! ## 6. Named hypotheses for the missing analytic content -/

/-- `XiOrderBound`: `completedRiemannZeta₀` has order ≤ 1. Standard classical
fact (Stirling on the gamma factor + bounds on ζ in vertical strips), not yet
in Mathlib. -/
def XiOrderBound : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ s : ℂ, K ≤ ‖s‖ →
      ‖completedRiemannZeta₀ s‖ ≤ Real.exp (C * ‖s‖)

/-- `XiZeroSummability`: the inverse-square moduli of zeros of
`completedRiemannZeta₀` are summable (Jensen's formula + counting). Mathlib
has Jensen's formula but the application to ξ₀ is not packaged. -/
def XiZeroSummability : Prop :=
  ∃ ρ : ℕ → ℂ,
    (∀ n, completedRiemannZeta₀ (ρ n) = 0) ∧
    (∀ n, ρ n ≠ 0) ∧
    Summable (fun n => 1 / ‖ρ n‖ ^ 2)

/-- `XiHadamardIdentification`: the genus-one Hadamard factorization of
`completedRiemannZeta₀`.

Once supplied, `ξ₀(s) = exp(A + B s) · ∏ E₁(s/ρ_n)`. The actual analytic
proof of this identification is the classical Hadamard theorem, not yet in
Mathlib. -/
structure XiHadamardIdentification where
  zeros : ℕ → ℂ
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  inv_sq_summable : Summable (fun n => 1 / ‖zeros n‖ ^ 2)
  A : ℂ
  B : ℂ
  identification :
    ∀ s : ℂ,
      completedRiemannZeta₀ s =
        Complex.exp (A + B * s) * ∏' n, E1 (s / zeros n)

/-! ## 7. What the supplied data gives -/

/-- Once `XiHadamardIdentification` is supplied, `completedRiemannZeta₀`
factors as the genus-one product times an exponential. -/
theorem completedRiemannZeta0_genus_one_factorization
    (H : XiHadamardIdentification) (s : ℂ) :
    completedRiemannZeta₀ s =
      Complex.exp (H.A + H.B * s) * ∏' n, E1 (s / H.zeros n) :=
  H.identification s

/-! ## 8. Status -/

/-- Track-D status bundle: per-factor estimate proved, summability proved,
multipliability proved; the order bound, zero-summability, and Hadamard
identification remain open analytic content. -/
structure HadamardGenusOneStatus where
  per_factor_estimate :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖E1 z - 1‖ ≤ 3 * ‖z‖ ^ 2
  summability_from_sq :
    ∀ z : ℕ → ℂ, (∀ n, ‖z n‖ ≤ 1) →
      Summable (fun n => ‖z n‖ ^ 2) →
        Summable (fun n => E1 (z n) - 1)
  multipliability_from_sq :
    ∀ z : ℕ → ℂ, (∀ n, ‖z n‖ ≤ 1) →
      Summable (fun n => ‖z n‖ ^ 2) →
        Multipliable (fun n => E1 (z n))
  open_xi_identification : XiHadamardIdentification → Prop

def hadamardGenusOneStatus : HadamardGenusOneStatus where
  per_factor_estimate := norm_E1_sub_one_le
  summability_from_sq := summable_E1_sub_one_of_summable_sq
  multipliability_from_sq := multipliable_E1_of_summable_sq
  open_xi_identification := fun _ => True

end

end HadamardGenusOne
end NumberTheory
end IndisputableMonolith
