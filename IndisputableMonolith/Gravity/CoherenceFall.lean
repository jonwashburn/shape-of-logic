/-
  CoherenceFall.lean

  Formalizes the insight: "Falling is Coherence/Synchronization".

  THE KEY INSIGHT:
  In the presence of a gravitational gradient (varying processing density),
  an extended object experiences a "refresh rate mismatch" (decoherence).

  However, in a frame accelerating at `a`, there is an induced inertial potential
  `Φ_acc(z) = a * z` so that the induced inertial force is `F_inertial = -∇Φ_acc = -a`.

  The "Falling Condition" is the choice of acceleration `a` such that
  the total potential `Φ_total = Φ_grav + Φ_acc` is locally constant (flat).

  Flat potential => Uniform refresh rate => Coherence (Zero J-cost).

  Part of: IndisputableMonolith/Gravity/
-/

import Mathlib
-- import IndisputableMonolith.Foundation.RecognitionOperator  -- [not in public release]

noncomputable section

namespace IndisputableMonolith.Gravity

-- (no external Foundation import needed for this self-contained module)

/-! ## The Setup -/

abbrev Position := ℝ

structure ProcessingField where
  /-- Potential function Φ(h) -/
  phi : Position → ℝ

structure ExtendedObject where
  h_cm : Position
  extent : ℝ
  extent_pos : extent > 0

/-! ## Frame Dependent Refresh Rate -/

/-- Total Potential in a frame accelerating with `a` at position `h` (relative to CM).
    Φ_tot(z) ≈ Φ_grav(h_cm + z) + a * z
    (Linear approximation for local frame)
-/
def total_potential_in_frame (field : ProcessingField) (obj : ExtendedObject) (a : ℝ) (z : ℝ) : ℝ :=
  -- Taylor expand phi around h_cm: phi(h_cm) + phi'(h_cm) * z
  let phi_grav := field.phi obj.h_cm + (deriv field.phi obj.h_cm) * z
  -- Inertial potential from acceleration a (pointing up? a is vertical acceleration)
  -- If object accelerates down (a < 0), inertial force is up.
  -- Potential Φ_acc such that F = -∇Φ_acc. F_inertial = -a, hence Φ_acc = a * z.
  let phi_acc := a * z

  phi_grav + phi_acc

/-- Coherence Defect: Variance of the potential across the object.
    If Potential is flat, Defect is 0.
-/
def coherence_defect (field : ProcessingField) (obj : ExtendedObject) (a : ℝ) : ℝ :=
  -- Difference in potential between Head (z = +extent) and Feet (z = -extent)
  let pot_head := total_potential_in_frame field obj a obj.extent
  let pot_feet := total_potential_in_frame field obj a (-obj.extent)
  abs (pot_head - pot_feet)

/-- Helper: expand coherence_defect into explicit arithmetic (no let bindings). -/
private lemma coherence_defect_expand (field : ProcessingField) (obj : ExtendedObject) (a : ℝ) :
    coherence_defect field obj a =
      abs ((field.phi obj.h_cm + deriv field.phi obj.h_cm * obj.extent + a * obj.extent) -
           (field.phi obj.h_cm + deriv field.phi obj.h_cm * (-obj.extent) + a * (-obj.extent))) := by
  rfl

/-- Closed form for the linearized coherence defect:
    `coherence_defect = | 2 * extent * (∂ϕ + a) |`. -/
lemma coherence_defect_simplify (field : ProcessingField) (obj : ExtendedObject) (a : ℝ) :
    coherence_defect field obj a =
      abs (2 * obj.extent * (deriv field.phi obj.h_cm + a)) := by
  rw [coherence_defect_expand]
  congr 1
  ring

/-! ## The Theorem -/

/-- Falling (Acceleration) Restores Coherence.

    Theorem: There exists a unique acceleration `a` that reduces the
    linear Coherence Defect to zero.

    This `a` is exactly the gravitational acceleration `g = -∇Φ`.
-/
theorem falling_restores_coherence (field : ProcessingField) (obj : ExtendedObject) :
    ∃! a : ℝ, coherence_defect field obj a = 0 := by
  -- We want |2 * e * (ϕ' + a)| = 0 ⇒ a = -ϕ' (since e > 0).
  -- This is exactly "Falling with acceleration = -Gradient".
  use -(deriv field.phi obj.h_cm)
  constructor
  · -- Existence
    -- | 2 * e * (ϕ' + (-ϕ')) | = |0| = 0
    simp [coherence_defect_simplify]
  · -- Uniqueness
    intro a' h_zero
    -- Reduce to a product equals zero
    have h0 : 2 * obj.extent * (deriv field.phi obj.h_cm + a') = 0 := by
      simpa [coherence_defect_simplify, abs_eq_zero] using h_zero
    -- From |x| = 0 we get x = 0
    -- Since obj.extent > 0, we have 2 * obj.extent ≠ 0
    have h_extent_pos : (0 : ℝ) < 2 * obj.extent := by
      have htwo : (0 : ℝ) < 2 := by norm_num
      exact mul_pos htwo obj.extent_pos
    have h_extent_ne : 2 * obj.extent ≠ 0 := ne_of_gt h_extent_pos
    -- So (deriv field.phi obj.h_cm + a') = 0
    have h2 : deriv field.phi obj.h_cm + a' = 0 := by
      have := mul_eq_zero.mp h0
      cases this with
      | inl h => exact absurd h h_extent_ne
      | inr h => exact h
    -- Therefore a' = -(deriv field.phi obj.h_cm)
    linarith

/-! ## Interpretation

"Gravity" is the requirement to accelerate in order to maintain
a locally constant processing environment (Coherence).

In this view:
- Standing still (a = 0) in a gravitational field means experiencing a coherence defect
- Free-falling (a = -∇Φ) cancels the defect, restoring coherence
- This is why free fall feels like nothing: you're in the coherent state
-/

end IndisputableMonolith.Gravity
