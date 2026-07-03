import IndisputableMonolith.RecogSpec.PhiSelectionCore
import IndisputableMonolith.PhiSupport.Lemmas

namespace IndisputableMonolith
namespace Verification
namespace PhiPinned

/-- Certificate: the RS φ-selection predicate pins a unique real φ. -/
structure PhiPinnedCert where
  deriving Repr

@[simp] def PhiPinnedCert.verified (_c : PhiPinnedCert) : Prop :=
  ∃! φ : ℝ, IndisputableMonolith.RecogSpec.PhiSelection φ

@[simp] theorem PhiPinnedCert.verified_any (c : PhiPinnedCert) :
    PhiPinnedCert.verified c := by
  refine ⟨IndisputableMonolith.Constants.phi, ?_, ?_⟩
  · -- PhiSelection for Constants.phi
    constructor
    · simpa using IndisputableMonolith.PhiSupport.phi_squared
    · exact lt_trans (by norm_num : (0 : ℝ) < 1) IndisputableMonolith.PhiSupport.one_lt_phi
  · intro x hx
    exact (IndisputableMonolith.PhiSupport.phi_unique_pos_root x).mp hx

end PhiPinned
end Verification
end IndisputableMonolith
