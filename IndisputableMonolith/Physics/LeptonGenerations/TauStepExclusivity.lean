import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.AlphaDerivation

/-!
# Tau Step Coefficient Exclusivity: Why (W + D/2) is Forced

This module proves that the coefficient **(W + D/2)** in the tau generation step
is uniquely determined once we state the missing first-principles rule the
reviewer is asking for: an **admissible class** of dimension-dependent
corrections.

## The Question

In the tau generation step formula:
  `step_μ→τ = F - (W + D/2) · α`

Why is the α-correction coefficient **W + D/2** and not:
- W + F/4  (using faces)
- W + E/8  (using edges)
- W + D(D-1)/4  (quadratic in D)
- W + D²/6  (another quadratic)

All these alternatives evaluate to 18.5 in D=3!

## The Answer

The alternatives fall into two categories:

**Category 1: Algebraically Equivalent**
- `F/4 = D/2` (since F = 2D by definition of hypercube faces)
- These are the SAME formula, just different notation.

**Category 2: Numerically Coincident but Algebraically Distinct**
- `E/8`, `D(D-1)/4`, `D²/6` all equal 1.5 in D=3
- But they DIFFER from D/2 in other dimensions.
- They are ruled out once we require **axis additivity** (independent axes contribute
  additively) and **no constant offset**.

## The Exclusivity Principles

1. **Axis Additivity**: If a correction term is a sum of independent per-axis
   contributions, then it must satisfy:

     `f(0)=0` and `f(a+b)=f(a)+f(b)`.

   This makes the correction linear in D (no cross-axis interaction terms).

2. **Calibration at D=3**: The tau step requires the dimension correction to be
   `3/2` when D=3 (i.e., the observed coefficient is `W + 3/2`).

Under (1)+(2), the dimension correction is uniquely `D/2`.
-/

namespace IndisputableMonolith
namespace Physics
namespace LeptonGenerations
namespace TauStepExclusivity

open Real Constants.AlphaDerivation

/-! ## Part 2: The Candidate Correction Terms -/

/-- Candidate 1: D/2 (our claimed formula) -/
noncomputable def correction_D_half (d : ℕ) : ℝ := (d : ℝ) / 2

/-- Candidate 2: F/4 = (2D)/4 = D/2 (algebraically equivalent!) -/
noncomputable def correction_F_quarter (d : ℕ) : ℝ := (cube_faces d : ℝ) / 4

/-- Candidate 3: E/8 (edges divided by 8) -/
noncomputable def correction_E_eighth (d : ℕ) : ℝ := (cube_edges d : ℝ) / 8

/-- Candidate 4: D(D-1)/4 (quadratic) -/
noncomputable def correction_D_quad1 (d : ℕ) : ℝ := (d : ℝ) * ((d : ℝ) - 1) / 4

/-- Candidate 5: D²/6 (another quadratic) -/
noncomputable def correction_D_quad2 (d : ℕ) : ℝ := ((d : ℝ) ^ 2) / 6

/-! ## Part 3: All Candidates Equal 1.5 in D=3 -/

theorem D_half_at_3 : correction_D_half 3 = 3/2 := by
  unfold correction_D_half
  norm_num

theorem F_quarter_at_3 : correction_F_quarter 3 = 3/2 := by
  unfold correction_F_quarter
  simp [cube_faces]
  norm_num

theorem E_eighth_at_3 : correction_E_eighth 3 = 3/2 := by
  unfold correction_E_eighth
  simp [cube_edges]
  norm_num

theorem D_quad1_at_3 : correction_D_quad1 3 = 3/2 := by
  unfold correction_D_quad1
  norm_num

theorem D_quad2_at_3 : correction_D_quad2 3 = 3/2 := by
  unfold correction_D_quad2
  norm_num

/-! ## Part 4: F/4 and D/2 are Algebraically Identical -/

/-- **Key Identity**: F/4 = D/2 for ALL dimensions.
    This is not numerical coincidence—it's algebraic identity. -/
theorem F_quarter_eq_D_half : ∀ d : ℕ, correction_F_quarter d = correction_D_half d := by
  intro d
  unfold correction_F_quarter correction_D_half
  -- (2*d)/4 = d/2
  simp [cube_faces]
  ring

/-- Corollary: F/4 is NOT a distinct alternative; it IS D/2. -/
theorem F_quarter_not_alternative :
    correction_F_quarter = correction_D_half := funext F_quarter_eq_D_half

/-! ## Part 5: Axis-Additive Admissible Class -/

/-! ### Axis additivity -/

/-- Axis additivity: independent axes contribute additively, with no constant offset. -/
def AxisAdditive (f : ℕ → ℝ) : Prop :=
  f 0 = 0 ∧ ∀ a b : ℕ, f (a + b) = f a + f b

/-- Any axis-additive function on ℕ is linear: f(d) = d * f(1). -/
theorem axisAdditive_linear (f : ℕ → ℝ) (h : AxisAdditive f) :
    ∀ d : ℕ, f d = (d : ℝ) * f 1 := by
  rcases h with ⟨h0, hadd⟩
  intro d
  induction d with
  | zero =>
      simp [h0]
  | succ d ih =>
      -- f(d+1) = f(d) + f(1)
      have hstep : f (d + 1) = f d + f 1 := by
        simpa using (hadd d 1)
      -- expand and use IH
      calc
        f (Nat.succ d) = f d + f 1 := by
          simpa [Nat.succ_eq_add_one] using hstep
        _ = ((d : ℝ) * f 1) + f 1 := by simpa [ih]
        _ = ((d : ℝ) + 1) * f 1 := by ring
        _ = ((Nat.succ d : ℝ) * f 1) := by
          simp [Nat.cast_succ, add_comm, add_left_comm, add_assoc]

/-! ### Admissible correction terms -/

/-- Admissible dimension correction: axis-additive and calibrated at D=3. -/
structure AdmissibleCorrection (f : ℕ → ℝ) : Prop where
  axisAdditive : AxisAdditive f
  calib_D3 : f 3 = 3 / 2

/-- Uniqueness: any admissible correction is exactly D/2. -/
theorem admissible_unique (f : ℕ → ℝ) (h : AdmissibleCorrection f) :
    ∀ d : ℕ, f d = (d : ℝ) / 2 := by
  have hlin := axisAdditive_linear f h.axisAdditive
  -- use calibration at d=3 to solve for f(1)
  have h3 : f 3 = (3 : ℝ) * f 1 := hlin 3
  have hf1 : f 1 = (1 : ℝ) / 2 := by
    -- from f3 = 3/2 = 3*f1
    have : (3 : ℝ) * f 1 = (3 : ℝ) / 2 := by
      -- rewrite h3 using calib
      rw [← h3, h.calib_D3]
    -- divide by 3
    have h3ne : (3 : ℝ) ≠ 0 := by norm_num
    -- f1 = (3/2)/3 = 1/2
    field_simp [h3ne] at this
    -- `this` is now: 3 * (2 * f1) = 3  (or equivalent); solve
    nlinarith
  intro d
  have : f d = (d : ℝ) * f 1 := hlin d
  -- substitute f1 = 1/2
  rw [this, hf1]
  ring

/-! ### Instances and exclusions -/

/-- D/2 is admissible. -/
theorem D_half_admissible : AdmissibleCorrection correction_D_half := by
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [correction_D_half], ?_⟩
    intro a b
    simp [correction_D_half, Nat.cast_add, add_div]
  · simpa [correction_D_half]

/-- F/4 is admissible (because it equals D/2). -/
theorem F_quarter_admissible : AdmissibleCorrection correction_F_quarter := by
  -- transport admissibility through definitional equality
  have hEq : correction_F_quarter = correction_D_half := funext F_quarter_eq_D_half
  -- rewrite and reuse
  simpa [hEq] using D_half_admissible

/-! ## Part 6: Excluding Common Alternatives (they violate axis additivity) -/

/-- E/8 is not axis-additive (witness: 2+2). -/
theorem E_eighth_not_axisAdditive : ¬ AxisAdditive correction_E_eighth := by
  intro h
  rcases h with ⟨h0, hadd⟩
  have h22 : correction_E_eighth (2 + 2) = correction_E_eighth 2 + correction_E_eighth 2 := hadd 2 2
  -- compute both sides
  unfold correction_E_eighth at h22
  simp [cube_edges] at h22
  -- LHS = 4, RHS = 1
  norm_num at h22

/-- D(D-1)/4 is not axis-additive (witness: 1+1). -/
theorem D_quad1_not_axisAdditive : ¬ AxisAdditive correction_D_quad1 := by
  intro h
  rcases h with ⟨h0, hadd⟩
  have h11 : correction_D_quad1 (1 + 1) = correction_D_quad1 1 + correction_D_quad1 1 := hadd 1 1
  unfold correction_D_quad1 at h11
  norm_num at h11

/-- D²/6 is not axis-additive (witness: 1+1). -/
theorem D_quad2_not_axisAdditive : ¬ AxisAdditive correction_D_quad2 := by
  intro h
  rcases h with ⟨h0, hadd⟩
  have h11 : correction_D_quad2 (1 + 1) = correction_D_quad2 1 + correction_D_quad2 1 := hadd 1 1
  unfold correction_D_quad2 at h11
  norm_num at h11

/-! ## Part 7: Main statement (uniqueness within the admissible class) -/

/-- **Main theorem**: any admissible correction is exactly `D/2`. -/
theorem tau_correction_unique_admissible (f : ℕ → ℝ) (h : AdmissibleCorrection f) :
    ∀ d : ℕ, f d = correction_D_half d := by
  intro d
  have := admissible_unique f h d
  simpa [correction_D_half] using this

/-! ## Summary

**The Exclusivity Proof**:

1. Among the proposed alternatives {D/2, F/4, E/8, D(D-1)/4, D²/6}:
   - F/4 = D/2 algebraically (not a distinct alternative)
   - E/8, D(D-1)/4, D²/6 violate axis additivity (they are not sums of per-axis contributions)

2. Under the admissible class (axis-additive + calibrated at D=3), the correction term is unique:
   `f(D) = D/2`.

**Conclusion**: the dimension contribution in the tau step coefficient is uniquely `D/2`
within the stated admissible correction class.
-/

end TauStepExclusivity
end LeptonGenerations
end Physics
end IndisputableMonolith
