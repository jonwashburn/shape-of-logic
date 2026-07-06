import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.PhiForcing

/-!
# α_lock: the ILG kernel exponent (NOT the fine-structure constant)

HONEST STATUS (2026-07-06): despite this module's historical name,
`alphaLock = (1 − 1/φ)/2 ≈ 0.19` is the information-limited-gravity
kernel exponent. It is NOT the electromagnetic fine-structure constant
α ≈ 1/137 ≈ 0.0073, and no "ledger-to-lab conversion" connecting the two
exists in this repository. The former claim that it resolves
"C-001: What determines α?" is RETRACTED.

The honest position on the EM α is in `Constants.AlphaGenesis`: the exact
value of α⁻¹(0) is a free boundary datum within RS
(`KappaGammaIrreducibility`), and the first-order construction value is
excluded by measurement (`MeasurementVerdict`).
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

/-! ## Structure statement (formerly mislabeled "C-001 Resolution") -/

/-- α_lock structure: `alphaLock = (1 − 1/φ)/2` with unit-interval bounds.
    This is a φ-structural fact about the ILG kernel exponent. It does NOT
    determine the EM fine-structure constant; see the module header. -/
theorem alphaLock_structure :
    0 < alphaLock ∧ alphaLock < 1 ∧
    alphaLock = (1 - 1 / phi) / 2 :=
  ⟨alphaLock_pos, alphaLock_lt_one, rfl⟩

@[deprecated alphaLock_structure (since := "2026-07-06")]
alias fine_structure_derived := alphaLock_structure

end FineStructureConstant
end Constants
end IndisputableMonolith
