import Mathlib
import IndisputableMonolith.Foundation.RationalsFromLogic
import IndisputableMonolith.NumberTheory.ErdosStrausRCL

/-!
  LogicErdosStrausRCL.lean

  Logic-native Erdős-Straus rational representation adapter.

  The rational layer is stated over `LogicRat`; all algebraic content is
  transported through `LogicRat.toRat` to the existing `ℚ` theorem surface.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace LogicErdosStrausRCL

open Foundation.RationalsFromLogic
open Foundation.RationalsFromLogic.LogicRat

/-- Logic-native Erdős-Straus rational representation. -/
def HasRationalErdosStrausReprLogic (n : LogicRat) : Prop :=
  ErdosStrausRCL.HasRationalErdosStrausRepr (toRat n)

theorem reprLogic_iff_classical (n : LogicRat) :
    HasRationalErdosStrausReprLogic n ↔
      ErdosStrausRCL.HasRationalErdosStrausRepr (toRat n) :=
  Iff.rfl

theorem reprLogic_of_classical {n : LogicRat}
    (h : ErdosStrausRCL.HasRationalErdosStrausRepr (toRat n)) :
    HasRationalErdosStrausReprLogic n :=
  h

theorem classical_of_reprLogic {n : LogicRat}
    (h : HasRationalErdosStrausReprLogic n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (toRat n) :=
  h

/-- Transport a classical rational representation to the recovered rational
whose image is the given classical rational. -/
theorem reprLogic_fromRat_of_classical {n : ℚ}
    (h : ErdosStrausRCL.HasRationalErdosStrausRepr n) :
    HasRationalErdosStrausReprLogic (fromRat n) := by
  simpa [HasRationalErdosStrausReprLogic, toRat_fromRat] using h

end LogicErdosStrausRCL
end NumberTheory
end IndisputableMonolith
