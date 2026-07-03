import Mathlib

namespace IndisputableMonolith

/-- Locally-finite step relation with bounded out-degree. -/
class BoundedStep (α : Type) (degree_bound : outParam Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

end IndisputableMonolith
