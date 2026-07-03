import IndisputableMonolith.Cost.Ndim.Core

/-!
# Uniqueness lift theorem for the n-dimensional extension

This module captures the forcing pattern:
if a candidate factors through the weighted multiplicative aggregate and the
scalar factor is uniquely fixed to `Jcost` on positive reals, then the whole
multi-component functional is forced to be `JcostN`.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

/-- `F` factors through the weighted aggregate via some scalar profile `G`. -/
def FactorsThrough {n : ℕ} (F : Vec n → ℝ) (α : Vec n) : Prop :=
  ∃ G : ℝ → ℝ, ∀ x : Vec n, F x = G (aggregate α x)

/-- Main forcing theorem: scalar uniqueness forces the `n`-dimensional lift. -/
theorem forced_of_scalar_uniqueness {n : ℕ}
    (F : Vec n → ℝ) (α : Vec n) (G : ℝ → ℝ)
    (hfactor : ∀ x : Vec n, F x = G (aggregate α x))
    (hscalar : ∀ {u : ℝ}, 0 < u → G u = Jcost u) :
    ∀ x : Vec n, F x = JcostN α x := by
  intro x
  calc
    F x = G (aggregate α x) := hfactor x
    _ = Jcost (aggregate α x) := hscalar (aggregate_pos α x)
    _ = JcostN α x := by simp [JcostN_eq_Jcost_aggregate]

/-- Existential version of the forcing theorem. -/
theorem forced_of_factorization {n : ℕ}
    (F : Vec n → ℝ) (α : Vec n)
    (hfac : FactorsThrough F α)
    (hscalar_unique : ∀ G : ℝ → ℝ,
      (∀ x : Vec n, F x = G (aggregate α x)) →
      (∀ {u : ℝ}, 0 < u → G u = Jcost u)) :
    ∀ x : Vec n, F x = JcostN α x := by
  rcases hfac with ⟨G, hG⟩
  exact forced_of_scalar_uniqueness F α G hG (hscalar_unique G hG)

end Ndim
end Cost
end IndisputableMonolith
