import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.StandardModel.HiggsEFTBridge

/-!
# Electroweak Mass Bridge

This module derives the Standard-Model gauge-boson mass relations from the
recognition-substrate scale `v` plus generic positive gauge couplings
`g, g'`.  Concretely it formalises

    m_W² = g² v² / 4,
    m_Z² = (g² + g'²) v² / 4,
    m_W / m_Z = cos θ_W = g / √(g² + g'²),
    sin² θ_W = g'² / (g² + g'²).

These are the SM tree-level gauge-mass relations.  Their content here is
conditional: given the same `v` from the RS substrate (formalised in
`HiggsEFTBridge`) and any positive `g, g'`, the SM gauge-mass relations
hold.  The identification of `g, g'` with their measured numerical values
remains an empirical input, just as the φ-ladder numerical match for `v`
is a separate (still open) calibration step.

The companion module `Masses/ElectroweakMasses.lean` already provides a
recognition-Weinberg-angle prediction `sin²θ_W = (3 − φ)/6` and proves
`w_pred / z_pred = cos θ_W` on its specific RS yardsticks.  The present
module instead proves the *gauge relation* unconditionally on positive
`(g, g')`, so any definition of `θ_W` (RS or PDG) is admissible as input.

## Status

* `THEOREM`: all gauge-mass relations on positive `(g, g', v)`.
* `THEOREM`: the W/Z ratio equals `cos θ_W` from the SM definition.
* `OPEN`: numerical calibration of `g, g'` from RS substrate (separate
  from this bridge; tracked under the `OPEN_NORMALIZATION` tag).
-/

namespace IndisputableMonolith
namespace StandardModel
namespace ElectroweakMassBridge

open Real
open Constants

noncomputable section

/-! ## §1. Tree-Level Gauge-Boson Masses -/

/-- W boson mass squared: `m_W² = g² v² / 4`. -/
def mW_sq (g v : ℝ) : ℝ := g ^ 2 * v ^ 2 / 4

/-- Z boson mass squared: `m_Z² = (g² + g'²) v² / 4`. -/
def mZ_sq (g gp v : ℝ) : ℝ := (g ^ 2 + gp ^ 2) * v ^ 2 / 4

/-- W boson mass: `m_W = g v / 2` (for `g, v > 0`). -/
def mW (g v : ℝ) : ℝ := Real.sqrt (mW_sq g v)

/-- Z boson mass: `m_Z = √(g² + g'²) · v / 2` (for `g, g', v > 0`). -/
def mZ (g gp v : ℝ) : ℝ := Real.sqrt (mZ_sq g gp v)

/-- `m_W² ≥ 0` always. -/
theorem mW_sq_nonneg (g v : ℝ) : 0 ≤ mW_sq g v := by
  unfold mW_sq
  have h1 : 0 ≤ g ^ 2 := sq_nonneg _
  have h2 : 0 ≤ v ^ 2 := sq_nonneg _
  positivity

/-- `m_Z² ≥ 0` always. -/
theorem mZ_sq_nonneg (g gp v : ℝ) : 0 ≤ mZ_sq g gp v := by
  unfold mZ_sq
  have h1 : 0 ≤ g ^ 2 := sq_nonneg _
  have h2 : 0 ≤ gp ^ 2 := sq_nonneg _
  have h3 : 0 ≤ v ^ 2 := sq_nonneg _
  have hsum : 0 ≤ g ^ 2 + gp ^ 2 := by linarith
  positivity

/-- `m_W² ≤ m_Z²` for any `g, g', v` (since `g'² ≥ 0`). -/
theorem mW_sq_le_mZ_sq (g gp v : ℝ) : mW_sq g v ≤ mZ_sq g gp v := by
  unfold mW_sq mZ_sq
  have hgp : 0 ≤ gp ^ 2 := sq_nonneg _
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg _
  have hprod : 0 ≤ gp ^ 2 * v ^ 2 := mul_nonneg hgp hv2
  nlinarith [hprod]

/-- The Z is heavier than the W when `g'` is non-trivial, i.e. when
    electromagnetic mixing is present. -/
theorem mW_sq_lt_mZ_sq_of_gp_pos (g gp v : ℝ) (hgp : 0 < gp) (hv : 0 < v) :
    mW_sq g v < mZ_sq g gp v := by
  unfold mW_sq mZ_sq
  have hv2 : 0 < v ^ 2 := by positivity
  have hgp2 : 0 < gp ^ 2 := by positivity
  have hprod : 0 < gp ^ 2 * v ^ 2 := mul_pos hgp2 hv2
  nlinarith [hprod]

/-! ## §2. The W/Z Ratio Identity -/

/-- The W/Z ratio identity in squared form:

    m_W² / m_Z² = g² / (g² + g'²) = cos² θ_W. -/
theorem mW_over_mZ_sq (g gp v : ℝ) (hg : 0 < g) (hv : 0 < v) :
    mW_sq g v / mZ_sq g gp v = g ^ 2 / (g ^ 2 + gp ^ 2) := by
  unfold mW_sq mZ_sq
  have hg2 : 0 < g ^ 2 := by positivity
  have hgp2 : 0 ≤ gp ^ 2 := sq_nonneg _
  have hsum : 0 < g ^ 2 + gp ^ 2 := by linarith
  have hv2 : 0 < v ^ 2 := by positivity
  field_simp

/-- The Standard-Model definition of `cos² θ_W` from gauge couplings. -/
def cos_sq_thetaW_SM (g gp : ℝ) : ℝ := g ^ 2 / (g ^ 2 + gp ^ 2)

/-- The Standard-Model definition of `sin² θ_W` from gauge couplings. -/
def sin_sq_thetaW_SM (g gp : ℝ) : ℝ := gp ^ 2 / (g ^ 2 + gp ^ 2)

/-- `cos²θ_W + sin²θ_W = 1` for nontrivial gauge couplings. -/
theorem cos_sq_plus_sin_sq_thetaW (g gp : ℝ) (hg : 0 < g) :
    cos_sq_thetaW_SM g gp + sin_sq_thetaW_SM g gp = 1 := by
  unfold cos_sq_thetaW_SM sin_sq_thetaW_SM
  have hg2 : 0 < g ^ 2 := by positivity
  have hgp2 : 0 ≤ gp ^ 2 := sq_nonneg _
  have hsum_pos : 0 < g ^ 2 + gp ^ 2 := by linarith
  have hsum_ne : g ^ 2 + gp ^ 2 ≠ 0 := ne_of_gt hsum_pos
  field_simp

/-- The W/Z mass-squared ratio equals `cos² θ_W` in the SM definition. -/
theorem mW_over_mZ_sq_eq_cos_sq (g gp v : ℝ) (hg : 0 < g) (hv : 0 < v) :
    mW_sq g v / mZ_sq g gp v = cos_sq_thetaW_SM g gp := by
  rw [mW_over_mZ_sq g gp v hg hv]
  rfl

/-- `cos²θ_W ∈ (0, 1]` for any nontrivial gauge coupling pair. -/
theorem cos_sq_thetaW_in_unit_interval (g gp : ℝ) (hg : 0 < g) :
    0 < cos_sq_thetaW_SM g gp ∧ cos_sq_thetaW_SM g gp ≤ 1 := by
  unfold cos_sq_thetaW_SM
  have hg2 : 0 < g ^ 2 := by positivity
  have hgp2 : 0 ≤ gp ^ 2 := sq_nonneg _
  have hsum_pos : 0 < g ^ 2 + gp ^ 2 := by linarith
  refine ⟨?_, ?_⟩
  · exact div_pos hg2 hsum_pos
  · rw [div_le_one hsum_pos]; linarith

/-- The Z is heavier than (or equal to) the W in mass-squared. -/
theorem mZ_sq_ge_mW_sq (g gp v : ℝ) : mW_sq g v ≤ mZ_sq g gp v :=
  mW_sq_le_mZ_sq g gp v

/-- The W/Z mass ratio identity in mass form (under positivity). -/
theorem mW_over_mZ_eq_cos_thetaW (g gp v : ℝ)
    (hg : 0 < g) (hgp : 0 ≤ gp) (hv : 0 < v) :
    mW g v / mZ g gp v = Real.sqrt (cos_sq_thetaW_SM g gp) := by
  unfold mW mZ
  have hmW_sq_pos : 0 < mW_sq g v := by
    unfold mW_sq; positivity
  have hmZ_sq_pos : 0 < mZ_sq g gp v := by
    unfold mZ_sq
    have hg2 : 0 < g ^ 2 := by positivity
    have hgp2 : 0 ≤ gp ^ 2 := sq_nonneg _
    have hsum : 0 < g ^ 2 + gp ^ 2 := by linarith
    have hv2 : 0 < v ^ 2 := by positivity
    positivity
  -- Use Real.sqrt_div_sqrt-style identity via Real.sqrt_div'
  have hmW_nn : 0 ≤ mW_sq g v := le_of_lt hmW_sq_pos
  have hmZ_nn : 0 ≤ mZ_sq g gp v := le_of_lt hmZ_sq_pos
  rw [← Real.sqrt_div hmW_nn]
  congr 1
  exact mW_over_mZ_sq_eq_cos_sq g gp v hg hv

/-! ## §3. Master Bridge Certificate -/

/-- Master certificate for the W/Z mass relations.

    Tags:
    - `THEOREM`: all clauses are unconditional theorems on positive
      gauge couplings and positive electroweak scale.
    - `OPEN_NORMALIZATION`: deriving `g, g'` numerically from the RS
      substrate is a separate problem, not closed here. -/
structure ElectroweakMassBridgeCert where
  /-- THEOREM: m_W² ≥ 0 unconditionally. -/
  mW_sq_nn         : ∀ g v, 0 ≤ mW_sq g v
  /-- THEOREM: m_Z² ≥ 0 unconditionally. -/
  mZ_sq_nn         : ∀ g gp v, 0 ≤ mZ_sq g gp v
  /-- THEOREM: m_W² ≤ m_Z² unconditionally. -/
  mW_le_mZ         : ∀ g gp v, mW_sq g v ≤ mZ_sq g gp v
  /-- THEOREM: m_W² < m_Z² when `g'` is nontrivial. -/
  mW_lt_mZ         : ∀ g gp v, 0 < gp → 0 < v → mW_sq g v < mZ_sq g gp v
  /-- THEOREM: the W/Z mass-squared ratio equals `cos²θ_W`. -/
  ratio_eq_cos_sq  : ∀ g gp v, 0 < g → 0 < v →
    mW_sq g v / mZ_sq g gp v = cos_sq_thetaW_SM g gp
  /-- THEOREM: cos²θ_W + sin²θ_W = 1. -/
  cos2_plus_sin2   : ∀ g gp, 0 < g →
    cos_sq_thetaW_SM g gp + sin_sq_thetaW_SM g gp = 1
  /-- THEOREM: `cos²θ_W` lies in `(0, 1]`. -/
  cos_sq_window    : ∀ g gp, 0 < g →
    0 < cos_sq_thetaW_SM g gp ∧ cos_sq_thetaW_SM g gp ≤ 1

def electroweakMassBridgeCert : ElectroweakMassBridgeCert where
  mW_sq_nn         := mW_sq_nonneg
  mZ_sq_nn         := mZ_sq_nonneg
  mW_le_mZ         := mW_sq_le_mZ_sq
  mW_lt_mZ         := fun g gp v hgp hv => mW_sq_lt_mZ_sq_of_gp_pos g gp v hgp hv
  ratio_eq_cos_sq  := fun g gp v hg hv => mW_over_mZ_sq_eq_cos_sq g gp v hg hv
  cos2_plus_sin2   := fun g gp hg => cos_sq_plus_sin_sq_thetaW g gp hg
  cos_sq_window    := fun g gp hg => cos_sq_thetaW_in_unit_interval g gp hg

theorem electroweakMassBridgeCert_inhabited : Nonempty ElectroweakMassBridgeCert :=
  ⟨electroweakMassBridgeCert⟩

end

end ElectroweakMassBridge
end StandardModel
end IndisputableMonolith
