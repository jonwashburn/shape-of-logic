import Mathlib
import IndisputableMonolith.Quantum.Observables

namespace IndisputableMonolith
namespace Quantum
namespace CommutationStructure

/-- Structural commutation content: projector algebra is idempotent. -/
def commutation_from_ledger : Prop :=
  ∀ (H : Type*) [RSHilbertSpace H], ∀ P : Projector H, P.op.comp P.op = P.op

theorem commutation_structure : commutation_from_ledger := by
  intro H hH P
  exact P.idempotent

/-- Universe-stable extractor for commutation structure. -/
theorem commutation_implies_projector_idempotent.{u}
    (h : @commutation_from_ledger.{u}) : @commutation_from_ledger.{u} :=
  h

end CommutationStructure
end Quantum
end IndisputableMonolith
