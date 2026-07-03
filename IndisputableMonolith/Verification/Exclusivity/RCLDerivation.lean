/-
  RCLDerivation.lean — Bridge B2 Scaffold

  This file now contains the honest algebraic adapter for Bridge B2.
  The raw associativity-only scaffold was inconsistent with the proved
  boundary law `f(a,0) = 2a`, so the classification is stated in the
  factorization-gate form used by the forcing chain.

  What is PROVED (zero sorry):
  - The d'Alembert composition rule satisfies the boundary conditions.
  - Boundary condition 1: f(0,0) = 0  (from J(1)=0).
  - Boundary condition 2: f(a,0) = 2a (from y=1 substitution).
  - Associativity of `f` itself contradicts the boundary law.
  - Under the factorization gate, the combiner is forced to the RCL polynomial.

  Still open in the paper sense:
  - derive the factorization gate itself directly from multiplicative
    recognition structure, without packaging right-affine response as a
    separate hypothesis.

  Paper §8.2: Bridge B2.
-/

import Mathlib
import IndisputableMonolith.Foundation.DAlembert.FactorizationForcing
import IndisputableMonolith.Verification.Exclusivity.Framework

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace RCLDerivation

set_option autoImplicit false

open IndisputableMonolith.Foundation.DAlembert.FactorizationForcing

/-- A composition rule: a symmetric binary function on ℝ specifying how
    compound cost values decompose:  J(xy) + J(x/y) = f(J(x), J(y)). -/
structure CompositionRule where
  f         : ℝ → ℝ → ℝ
  symmetric : ∀ a b, f a b = f b a

/-- The d'Alembert composition rule: f(a,b) = 2(a+1)(b+1) - 2.
    Equivalently: f(a,b) = 2ab + 2a + 2b. -/
noncomputable def dAlembertRule : CompositionRule where
  f         := fun a b => 2 * (a + 1) * (b + 1) - 2
  symmetric := by intro a b; ring

/-- Boundary condition 1 (proved): f(0,0) = 0.
    Derivation: set x = y = 1 in J(xy)+J(x/y) = f(J(x),J(y)).
    J(1)+J(1) = f(J(1),J(1)) = f(0,0), so f(0,0) = 0. -/
theorem composition_rule_f00_eq_zero
    (f : CompositionRule) (J : ℝ → ℝ)
    (hJ0   : J 1 = 0)
    (hComp : ∀ x y, 0 < x → 0 < y →
               J (x * y) + J (x / y) = f.f (J x) (J y)) :
    f.f 0 0 = 0 := by
  have h := hComp 1 1 one_pos one_pos
  simp [hJ0] at h
  linarith

/-- Boundary condition 2 (proved): f(a,0) = 2a.
    Derivation: set y = 1.  J(x)+J(x) = f(J(x),0), so f(a,0) = 2a. -/
theorem composition_rule_f_at_zero
    (f : CompositionRule) (J : ℝ → ℝ)
    (hJ0   : J 1 = 0)
    (hComp : ∀ x y, 0 < x → 0 < y →
               J (x * y) + J (x / y) = f.f (J x) (J y))
    (x : ℝ) (hx : 0 < x) :
    f.f (J x) 0 = 2 * J x := by
  have h := hComp x 1 hx one_pos
  simp [hJ0, mul_one, div_one] at h
  linarith

/-- The d'Alembert rule satisfies both boundary conditions. -/
theorem dAlembert_satisfies_boundaries :
    dAlembertRule.f 0 0 = 0 ∧ ∀ a, dAlembertRule.f a 0 = 2 * a :=
  ⟨by simp [dAlembertRule], by intro a; simp [dAlembertRule]; ring⟩

/-- The original associativity-only scaffold is inconsistent with the proved
    boundary law `f(a,0) = 2a`.

    Indeed, symmetry gives `f(0,1) = 2` and `f(0,2) = 4`, while associativity
    at `(0,0,1)` would force `f(0,1) = f(0,2)`. So the old Open Problem B
    statement was malformed: the actual closure step cannot be associativity
    of `f` itself. -/
theorem associativity_contradicts_boundary
    (f        : CompositionRule)
    (h00      : f.f 0 0 = 0)
    (hbdry    : ∀ a, f.f a 0 = 2 * a)
    (h_assoc  : ∀ a b c, f.f (f.f a b) c = f.f a (f.f b c)) :
    False := by
  have h01 : f.f 0 1 = 2 := by
    calc
      f.f 0 1 = f.f 1 0 := f.symmetric 0 1
      _ = 2 * 1 := hbdry 1
      _ = 2 := by norm_num
  have h02 : f.f 0 2 = 4 := by
    calc
      f.f 0 2 = f.f 2 0 := f.symmetric 0 2
      _ = 2 * 2 := hbdry 2
      _ = 4 := by norm_num
  have h_assoc001 := h_assoc 0 0 1
  rw [h00, h01] at h_assoc001
  linarith

/-- Bridge B2 classification in the honest form used by the forcing chain.

    The RS algebraic closure does not use associativity of `f` itself.
    What is actually needed, and already proved elsewhere in the forcing
    chain, is the factorization gate:

    - symmetry,
    - right-affine response in the second argument,
    - the zero-boundary law `f(a,0) = 2a`,
    - and the canonical normalization `f(1,1) = 6`.

    Under those hypotheses the combiner is forced exactly to the RCL
    polynomial. -/
theorem composition_rule_classification
    (f        : CompositionRule)
    (hbdry    : ∀ a, f.f a 0 = 2 * a)
    (hAffine  : ∀ a, ∃ α β, ∀ b, f.f a b = α * b + β)
    (h11      : f.f 1 1 = 6) :
    ∀ a b, f.f a b = 2 * (a + 1) * (b + 1) - 2 := by
  let hGate : FactorizationAssociativityGate f.f :=
    { symmetric := f.symmetric
      rightAffine := hAffine
      zeroBoundary := hbdry
      unitDiagonal := h11 }
  intro a b
  calc
    f.f a b = 2 * a * b + 2 * a + 2 * b := gate_forces_rcl f.f hGate a b
    _ = 2 * (a + 1) * (b + 1) - 2 := by ring

end RCLDerivation
end Exclusivity
end Verification
end IndisputableMonolith
