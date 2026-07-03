import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RSBridge.Anchor

/-!
# AnchorPolicy Model (Lean-native, computable stand-in)

`IndisputableMonolith/Physics/AnchorPolicy.lean` intentionally treats the Standard-Model RG residue
`f_residue` as an **opaque interface** (axiom), because the repo does not currently implement
multi-loop RG kernels + threshold policy + numerical integration inside Lean.

This file provides a **Lean-native model** of the residue whose value is *by definition* the closed
form display function:

  `f_residue_model f μ := gap (ZOf f)`

This is useful for:
- making downstream algebraic consequences executable / #eval-friendly,
- avoiding `axiom` dependencies when you explicitly want to work in the *model* where the anchor
  identity holds by construction.

Important: this is **not** a proof of the SM RG statement; it is a definitional model.
-/

namespace IndisputableMonolith.Physics
namespace AnchorPolicyModel

open IndisputableMonolith.Constants
open IndisputableMonolith.RSBridge

/-! ## Model residue -/

/-- A computable stand-in for the RG residue: constant in scale and equal to the display `gap(Z)`.

This encodes the single-anchor closed form as a *definition* rather than a phenomenology axiom. -/
noncomputable def f_residue_model (f : Fermion) (_mu : ℝ) : ℝ :=
  gap (ZOf f)

@[simp] theorem f_residue_model_at (f : Fermion) (mu : ℝ) :
    f_residue_model f mu = gap (ZOf f) := rfl

/-! ## Consequences (stationarity/robustness become trivial in the model) -/

/-- In the model, the residue is constant in `t`, hence stationary at every point. -/
theorem stationary_at_any (muStar : ℝ) (f : Fermion) :
    deriv (fun t => f_residue_model f (Real.exp t)) (Real.log muStar) = 0 := by
  -- `f_residue_model` ignores its scale argument, so the function of `t` is constant.
  simp [f_residue_model]

/-- In the model, the second derivative is also identically zero, hence bounded. -/
theorem stability_bound_at_any (muStar : ℝ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (f : Fermion),
      |deriv (deriv (fun t => f_residue_model f (Real.exp t))) (Real.log muStar)| < ε := by
  refine ⟨1, by norm_num, ?_⟩
  intro f
  -- Second derivative of a constant is 0.
  simp [f_residue_model]

/-- Equal-Z degeneracy holds by definition in the model. -/
theorem equalZ_at_any {f g : Fermion} (hZ : ZOf f = ZOf g) (mu : ℝ) :
    f_residue_model f mu = f_residue_model g mu := by
  simp [f_residue_model, hZ]

end AnchorPolicyModel
end IndisputableMonolith.Physics
