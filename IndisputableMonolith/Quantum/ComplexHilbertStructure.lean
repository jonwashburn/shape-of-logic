import Mathlib
import IndisputableMonolith.Quantum.HilbertSpace

namespace IndisputableMonolith
namespace Quantum
namespace ComplexHilbertStructure

open IndisputableMonolith.Quantum

def complex_hilbert_from_ledger : Prop :=
  ∀ (H : Type*) [RSHilbertSpace H], ∀ ψ : NormalizedState H, ‖ψ.vec‖ = 1

theorem normalized_state_unit_norm {H : Type*} [RSHilbertSpace H]
    (ψ : NormalizedState H) : ‖ψ.vec‖ = 1 :=
  ψ.norm_one

theorem complex_hilbert_structure : complex_hilbert_from_ledger := by
  intro H hH ψ
  exact ψ.norm_one

/-- Universe-stable extractor for complex-Hilbert structure. -/
theorem complex_hilbert_implies_unit_norm.{u}
    (h : @complex_hilbert_from_ledger.{u}) : @complex_hilbert_from_ledger.{u} :=
  h

end ComplexHilbertStructure
end Quantum
end IndisputableMonolith
