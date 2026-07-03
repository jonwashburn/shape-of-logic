import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# RRF Theorems: Monotone Transform Invariance

If `g : ℝ → ℝ` is strictly monotone, then `argmin (g ∘ J) = argmin J`.

This is fundamental to RRF: the "meaning" of strain is preserved under any
monotone rescaling. What matters is the ordering, not the absolute values.

## Main Results

- `argmin_comp_strictMono`: argmin is invariant under strictly monotone transforms
- `order_preserving_strictMono`: strict monotonicity preserves all ordering relations
-/


namespace IndisputableMonolith
namespace RRF.Theorems

variable {State : Type*} {J : State → ℝ} {g : ℝ → ℝ}

/-- A state x is an argmin of J if J(x) ≤ J(y) for all y. -/
def isArgmin (J : State → ℝ) (x : State) : Prop :=
  ∀ y : State, J x ≤ J y

/-- Strictly monotone transforms preserve argmin.

If g is strictly monotone and x is an argmin of J,
then x is also an argmin of g ∘ J.
-/
theorem argmin_comp_strictMono
    (hg : StrictMono g)
    (x : State) (hx : isArgmin J x) :
    isArgmin (g ∘ J) x := by
  intro y
  exact hg.monotone (hx y)

/-- Strictly monotone transforms preserve the converse: if x is argmin of g ∘ J, then x is argmin of J (assuming g is onto the relevant range). -/
theorem argmin_of_comp_strictMono
    (hg : StrictMono g)
    (x : State) (hgx : isArgmin (g ∘ J) x) :
    isArgmin J x := by
  intro y
  -- g(J(x)) ≤ g(J(y)) and g strictly mono → J(x) ≤ J(y)
  by_contra h
  push_neg at h
  have : g (J x) > g (J y) := hg h
  have : ¬ (g ∘ J) x ≤ (g ∘ J) y := not_le_of_gt this
  exact this (hgx y)

/-- Strictly monotone transforms preserve strict ordering. -/
theorem strictOrder_comp_strictMono
    (hg : StrictMono g)
    {x y : State} (hxy : J x < J y) :
    (g ∘ J) x < (g ∘ J) y :=
  hg hxy

/-- Monotone transforms preserve weak ordering. -/
theorem weakOrder_comp_mono
    (hg : Monotone g)
    {x y : State} (hxy : J x ≤ J y) :
    (g ∘ J) x ≤ (g ∘ J) y :=
  hg hxy

/-- The key theorem: strictly monotone transforms induce an equivalence on argmin sets. -/
theorem argmin_equiv_strictMono (hg : StrictMono g) (x : State) :
    isArgmin J x ↔ isArgmin (g ∘ J) x :=
  ⟨argmin_comp_strictMono hg x, argmin_of_comp_strictMono hg x⟩

/-- Application: shifting J by a constant preserves argmin. -/
theorem argmin_add_const (c : ℝ) (x : State) :
    isArgmin J x ↔ isArgmin (fun s => J s + c) x := by
  constructor
  · intro h y
    have := h y
    linarith
  · intro h y
    have := h y
    linarith

/-- Application: scaling J by a positive constant preserves argmin. -/
theorem argmin_mul_pos (c : ℝ) (hc : 0 < c) (x : State) :
    isArgmin J x ↔ isArgmin (fun s => c * J s) x := by
  have hg : StrictMono (fun t => c * t) := strictMono_mul_left_of_pos hc
  exact argmin_equiv_strictMono hg x

end RRF.Theorems
end IndisputableMonolith
