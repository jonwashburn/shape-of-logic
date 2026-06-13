import Mathlib
import Mathlib.NumberTheory.Real.GoldenRatio
import IndisputableMonolith.Constants

/-!
Module: IndisputableMonolith.PhiSupport.Lemmas

Golden-ratio support lemmas used by certificates:
- `φ^2 = φ + 1` (from Mathlib's `Real.goldenRatio_sq`)
- fixed-point identity `φ = 1 + 1/φ`
- uniqueness of the positive root of `x^2 = x + 1`

These depend only on elementary real algebra and Mathlib's goldenRatio facts.
-/

namespace IndisputableMonolith
namespace PhiSupport

open Real

/-- Closed form for φ. -/
lemma phi_def : Constants.phi = Real.goldenRatio := rfl

/-- φ > 1. -/
lemma one_lt_phi : 1 < Constants.phi := by simp [phi_def, Real.one_lt_goldenRatio]

/-- φ ≠ 0. -/
lemma phi_ne_zero : Constants.phi ≠ 0 := by
  -- goldenRatio = (1+√5)/2 ≠ 0
  have : Real.goldenRatio ≠ 0 := by
    have hpos : 0 < Real.goldenRatio := Real.goldenRatio_pos
    exact ne_of_gt hpos
  simpa [phi_def] using this

/-- φ^2 = φ + 1 using the closed form. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  simp [phi_def, Real.goldenRatio_sq]

/-- φ = 1 + 1/φ as an algebraic corollary. -/
theorem phi_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  have h_sq : Constants.phi ^ 2 = Constants.phi + 1 := phi_squared
  have h_ne_zero : Constants.phi ≠ 0 := phi_ne_zero
  calc
    Constants.phi = (Constants.phi ^ 2) / Constants.phi := by
      rw [pow_two, mul_div_cancel_left₀ _ h_ne_zero]
    _ = (Constants.phi + 1) / Constants.phi := by rw [h_sq]
    _ = Constants.phi / Constants.phi + 1 / Constants.phi := by rw [add_div]
    _ = 1 + 1 / Constants.phi := by
      have : Constants.phi / Constants.phi = 1 := div_self h_ne_zero
      rw [this]

/-- Uniqueness: if x > 0 and x² = x + 1, then x = φ. -/
 theorem phi_unique_pos_root (x : ℝ) : (x ^ 2 = x + 1 ∧ 0 < x) ↔ x = Constants.phi := by
  constructor
  · intro hx
    have hx2 : x ^ 2 = x + 1 := hx.left
    -- (2x−1)^2 = 5
    have hquad : (2 * x - 1) ^ 2 = 5 := by
      calc
        (2 * x - 1) ^ 2 = 4 * x ^ 2 - 4 * x + 1 := by ring
        _ = 4 * (x + 1) - 4 * x + 1 := by simpa [hx2]
        _ = 5 := by ring
    -- From x>0 and x(x−1)=1, get x>1 hence 2x−1>0
    have hx_nonzero : x ≠ 0 := ne_of_gt hx.right
    have hx_sub : x ^ 2 - x = 1 := by
      have := congrArg (fun t => t - x) hx.left
      simpa [sub_eq_add_neg] using this
    have hx_mul : x * (x - 1) = 1 := by
      have hfac : x ^ 2 - x = x * (x - 1) := by ring
      simpa [hfac] using hx_sub
    have hx1_pos : 0 < x - 1 := by
      -- divide by positive x
      have := congrArg (fun t : ℝ => t / x) hx_mul
      have hdiv : x - 1 = 1 / x := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hx_nonzero] using this
      simpa [hdiv] using (one_div_pos.mpr hx.right)
    have hx_pos : 0 < 2 * x - 1 := by linarith
    -- Take square root
    have hsqroot : Real.sqrt ((2 * x - 1) ^ 2) = Real.sqrt 5 := by
      simpa [hquad]
    have hsqabs : Real.sqrt ((2 * x - 1) ^ 2) = |2 * x - 1| := by
      exact Real.sqrt_sq_eq_abs (2 * x - 1)
    have habs : |2 * x - 1| = Real.sqrt 5 := by
      -- rewrite the left side of hsqroot via sqrt(sq)=|·|
      simpa [hsqabs] using hsqroot
    have hlin : 2 * x - 1 = Real.sqrt 5 := by
      have hnonneg : 0 ≤ 2 * x - 1 := le_of_lt hx_pos
      have hdrop : |2 * x - 1| = 2 * x - 1 := abs_of_nonneg hnonneg
      simpa [hdrop] using habs
    have h2x : 2 * x = 1 + Real.sqrt 5 := by linarith
    have hx_eq : x = (1 + Real.sqrt 5) / 2 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      -- x = (1+√5)/2  ↔  2*x = 1+√5
      exact (eq_div_iff_mul_eq h2).2 (by simpa [mul_comm] using h2x)
    simpa [Constants.phi] using hx_eq
  · intro hx; subst hx
    exact And.intro phi_squared (lt_trans (by norm_num) one_lt_phi)

/-- **Phase 3 Derivation**: Model-independent exclusivity of φ.
    The golden ratio is the unique positive solution to the self-similarity constraint. -/
theorem exclusivity_model_independent :
    ∀ x : ℝ, x > 0 → (x^2 = x + 1) → x = Constants.phi := by
  intro x hx h_eq
  have h_root := phi_unique_pos_root x
  exact h_root.mp ⟨h_eq, hx⟩

end PhiSupport
end IndisputableMonolith
