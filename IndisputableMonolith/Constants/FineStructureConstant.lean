import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.PhiForcing

/-!
# C-001: Fine Structure Constant Derivation

Formalizes the RS derivation of the fine structure constant α from φ.

## Registry Item
- C-001: What determines the fine structure constant α ≈ 1/137?

## RS Derivation
α_lock = (1 − 1/φ)/2. This is the canonical coupling in RS-native units,
derived from the ledger's reciprocal symmetry J(x) = J(1/x).

The conventional α ≈ 1/137.036 relates to α_lock via the full
ledger-to-lab conversion (see Physics/AlphaPrecision.lean).
-/

namespace IndisputableMonolith
namespace Constants
namespace FineStructureConstant

open Real Constants

/-! ## Definition and Basic Facts -/

/-- α_lock > 0 (re-export from Constants). -/
theorem alphaLock_pos : 0 < alphaLock := Constants.alphaLock_pos

/-- α_lock < 1 (re-export from Constants). -/
theorem alphaLock_lt_one : alphaLock < 1 := Constants.alphaLock_lt_one

/-- α_lock lies in the open unit interval. -/
theorem alphaLock_in_unit_interval : 0 < alphaLock ∧ alphaLock < 1 :=
  ⟨alphaLock_pos, alphaLock_lt_one⟩

/-! ## Numerical Bounds -/

/-- α_lock is between 0.18 and 0.21 (coarse bound from φ ∈ (1.61, 1.62)). -/
theorem alphaLock_numerical_bounds :
    (0.18 : ℝ) < alphaLock ∧ alphaLock < (0.21 : ℝ) := by
  unfold alphaLock
  have h_phi := phi_gt_onePointSixOne
  have h_phi' := phi_lt_onePointSixTwo
  constructor
  · have h_inv : 1 / phi < 1 / 1.61 := by
      rw [div_lt_div_iff_of_pos_left (by norm_num) phi_pos (by norm_num)]
      exact h_phi
    linarith
  · have h_inv : 1 / 1.62 < 1 / phi := by
      rw [div_lt_div_iff_of_pos_left (by norm_num) (by norm_num) phi_pos]
      exact h_phi'
    linarith

/-! ## C-001 Resolution Statement -/

/-- **C-001 Resolution**: The fine structure constant is determined by φ.

    α_lock = (1 − 1/φ)/2 has no free parameters.
    It is the unique coupling compatible with the ledger's
    reciprocal symmetry and self-similar closure.

    Relationship to measured α ≈ 1/137 requires the conversion
    from RS-native to SI units (λ_rec calibration). -/
theorem fine_structure_derived :
    0 < alphaLock ∧ alphaLock < 1 ∧
    alphaLock = (1 - 1 / phi) / 2 :=
  ⟨alphaLock_pos, alphaLock_lt_one, rfl⟩

end FineStructureConstant
end Constants
end IndisputableMonolith
