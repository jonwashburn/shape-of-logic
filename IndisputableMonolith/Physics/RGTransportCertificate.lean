import Mathlib
import IndisputableMonolith.RSBridge.Anchor

namespace IndisputableMonolith
namespace Physics
namespace RGTransportCertificate

open RSBridge

/-- Certified SM RG transport exponent f^RG_i(μ*, μ_end) from canonical policy. -/
def f_RG_certified : Fermion → ℚ
  | .e   => 494/10000
  | .mu  => 288/10000
  | .tau => 179/10000
  | .u   => 4822/10000
  | .d   => 4764/10000
  | .s   => 4764/10000
  | .c   => 5470/10000
  | .b   => 3807/10000
  | .t   => 98/10000
  | _    => 0

/-!
NOTE (policy seam):

These values are an **external certificate** produced under a declared RG transport policy
(loop order, thresholds, scheme, integrator). They are not “fit parameters” of the RS model
layer, but they *are* conventions that must be declared whenever used for PDG comparisons.

Source-of-truth for the policy snapshot and floating values:
- `data/certificates/rg_transport/canonical_2025_q4.json`
- `tools/rg_transport_policy.json` + `tools/rg_transport_certify.py`
-/

/-- Tolerance for the certified transport exponents. -/
def f_RG_tolerance : ℚ := 1/10000

/-- Hypothesis that the true f^RG lies within the certified range. -/
def is_certified (f : Fermion) (val : ℝ) : Prop :=
  (f_RG_certified f : ℝ) - (f_RG_tolerance : ℝ) ≤ val ∧
  val ≤ (f_RG_certified f : ℝ) + (f_RG_tolerance : ℝ)

/-- Lower endpoint of the certified enclosure interval. -/
def f_RG_lower (f : Fermion) : ℚ := f_RG_certified f - f_RG_tolerance

/-- Upper endpoint of the certified enclosure interval. -/
def f_RG_upper (f : Fermion) : ℚ := f_RG_certified f + f_RG_tolerance

theorem f_RG_tolerance_nonneg : (0 : ℚ) ≤ f_RG_tolerance := by
  norm_num [f_RG_tolerance]

theorem f_RG_interval_nonempty (f : Fermion) : f_RG_lower f ≤ f_RG_upper f := by
  unfold f_RG_lower f_RG_upper
  nlinarith [f_RG_tolerance_nonneg]

/-- Equivalent absolute-error enclosure form for certified transport values. -/
theorem is_certified_iff_abs_error_le (f : Fermion) (val : ℝ) :
    is_certified f val ↔
      |val - (f_RG_certified f : ℝ)| ≤ (f_RG_tolerance : ℝ) := by
  constructor
  · intro h
    rcases h with ⟨hlo, hhi⟩
    have h1 : -((f_RG_tolerance : ℚ) : ℝ) ≤ val - (f_RG_certified f : ℚ) := by
      linarith
    have h2 : val - (f_RG_certified f : ℚ) ≤ ((f_RG_tolerance : ℚ) : ℝ) := by
      linarith
    exact abs_le.mpr ⟨h1, h2⟩
  · intro h
    have h' := abs_le.mp h
    constructor <;> linarith [h'.1, h'.2]

/-- The certified center value is enclosed for every fermion. -/
theorem certified_center_enclosed (f : Fermion) :
    is_certified f (f_RG_certified f) := by
  unfold is_certified
  have htol_nonneg : (0 : ℝ) ≤ (f_RG_tolerance : ℝ) := by
    exact_mod_cast f_RG_tolerance_nonneg
  constructor
  · exact sub_le_self _ htol_nonneg
  · exact le_add_of_nonneg_right htol_nonneg

end RGTransportCertificate
end Physics
end IndisputableMonolith
