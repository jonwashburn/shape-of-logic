import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Higgs EFT Bridge from Recognition Cost Geometry

This module formalises the first link in the chain

    RS cost geometry  →  effective scalar coordinate  →  canonical Higgs EFT

The dimensionless RS coordinate is `ε = h / v` where `h` is the canonically
normalised collider scalar field of mass dimension one and `v > 0` is the
electroweak scale supplied by the recognition substrate.  A dimensionful
prefactor `Λ⁴` (with `Λ` of mass dimension one) is required to match the
Standard-Model Lagrangian normalisation.

The recognition-cost potential is

    V_RS Λ v h := Λ^4 · J(exp (h / v))

where `J(x) = ½(x + x⁻¹) − 1` is the canonical reciprocal cost functional
and `J(eᵉ) = cosh ε − 1` (Lean: `Cost.Jcost_exp_cosh`).

Expanded around the vacuum `h = 0`, this becomes

    V_RS Λ v h = (Λ⁴ / 2 v²) · h² + (Λ⁴ / 24 v⁴) · h⁴ + 𝒪(h⁶)

Matching onto the Standard-Model parametrisation

    V_SM h = ½ m_H² h² + (λ_SM / 4) · h⁴ + ⋯

gives the SM-to-RS dictionary

    m_H² = Λ⁴ / v²,        λ_SM = (1/6) · Λ⁴ / v⁴.

The map closes the first two arrows of Anil Thapa's reviewer chain.
The remaining collider-normalisation problem reduces to fixing `Λ(v)`
from the recognition substrate, which is left explicit as a hypothesis
below.

## Status

* `THEOREM`: the Taylor-coefficient extraction is forced by the cosh
  expansion proved here from `Cost.Jcost_exp_cosh` plus a Mathlib
  truncation bound.
* `CONDITIONAL_THEOREM`: the SM-quartic identification depends on the
  normalisation hypothesis `Λ⁴ = m_H² · v²`, which is the open subproblem.
* `OPEN_NORMALIZATION`: deriving `Λ` from the φ-ladder yardstick.

## ATTACKER BREADCRUMB (read before claiming this matches the SM at tree level)

The "λ_SM = m_H²/(6v²)" coefficient extracted in §3 is **NOT the standard
SM Higgs quartic** (which is m_H²/(2v²) ≈ 0.129 at v = 246 GeV, not
m_H²/(6v²) ≈ 0.043). It is the value that would match the cosh's quartic
Taylor coefficient.

The cosh form `V_RS = Λ⁴(cosh(h/v)−1)` is **even in h**, so:
  * the trilinear `h³` coefficient is identically zero (`κ_λ_3 = 0`).
  * the quartic `h⁴` coefficient is `m_H²/(24v²) = (1/3)·(m_H²/(8v²))`,
    one-third of the SM Mexican-hat value (`κ_λ_4 = 1/3`).
  * the sextic `h⁶` coefficient is `m_H²/(720v⁴)`, nonzero (BSM).

These are pre-registered BSM signatures, falsifiable at HL-LHC di-Higgs
(probes h³) and FCC-hh tri-Higgs (probes h⁴). See
`StandardModel.HiggsCoshBSMPredictions` for the explicit Lean theorems
and the master falsifier `HiggsCoshBSMFalsifier`.

The exact magnitude of the BSM deviation depends on the substrate
kinetic-term shape: under the canonical (linear) identification
`h = v · ε` used in this module, the predictions are as above. Other
kinetic-term shapes give different `κ_λ_3`, `κ_λ_4` values; deriving
the canonical kinetic term from RS primitives is the OPEN frontier.
-/

namespace IndisputableMonolith
namespace StandardModel
namespace HiggsEFTBridge

open Real
open Constants
open IndisputableMonolith.Cost

noncomputable section

/-! ## §1. The Recognition-Cost Potential -/

/-- The RS Higgs effective potential at canonical mass dimension four.

    `V_RS Λ v h = Λ⁴ · J(exp (h / v))`. -/
def V_RS (Λ v h : ℝ) : ℝ := Λ ^ 4 * Jcost (Real.exp (h / v))

/-- `V_RS` reduces to `Λ⁴ · (cosh(h/v) − 1)`. -/
theorem V_RS_eq_cosh (Λ v h : ℝ) :
    V_RS Λ v h = Λ ^ 4 * (Real.cosh (h / v) - 1) := by
  unfold V_RS
  rw [Cost.Jcost_exp_cosh]

/-- The vacuum is at `h = 0` with zero potential. -/
theorem V_RS_at_vacuum (Λ v : ℝ) : V_RS Λ v 0 = 0 := by
  rw [V_RS_eq_cosh]
  simp [Real.cosh_zero]

/-- The RS potential is non-negative. -/
theorem V_RS_nonneg (Λ v : ℝ) (h : ℝ) : 0 ≤ V_RS Λ v h := by
  rw [V_RS_eq_cosh]
  have hΛ4 : 0 ≤ Λ ^ 4 := by positivity
  have hcosh : 1 ≤ Real.cosh (h / v) := Real.one_le_cosh _
  have : 0 ≤ Real.cosh (h / v) - 1 := by linarith
  exact mul_nonneg hΛ4 this

/-! ## §2. Quartic-Order Taylor Expansion -/

/-- The quartic Taylor approximation to the RS potential about the vacuum. -/
def V_RS_quartic (Λ v h : ℝ) : ℝ :=
  Λ ^ 4 * ((h / v) ^ 2 / 2 + (h / v) ^ 4 / 24)

/-- Mathlib truncation lemma, restated for real `t` to depth 6.

    `|exp t − (1 + t + t²/2 + t³/6 + t⁴/24 + t⁵/120)| ≤ exp |t| · |t|⁶`.

    Proof: lift to ℂ and apply `Complex.norm_exp_sub_sum_le_norm_mul_exp`. -/
private theorem exp_sub_trunc6_le (t : ℝ) :
    |Real.exp t - (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120)| ≤
      Real.exp |t| * |t| ^ 6 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (t : ℂ) 6
  have hexpr :
      Complex.exp (t : ℂ) - ∑ m ∈ Finset.range 6, (t : ℂ) ^ m / m.factorial =
        ((Real.exp t - (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120) : ℝ) : ℂ) := by
    simp [Complex.ofReal_exp, Finset.sum_range_succ, Nat.factorial]
  rw [hexpr, Complex.norm_real, Real.norm_eq_abs] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Quartic-error bound for `cosh ε - 1` on `|ε| ≤ 1/2`:

    `|cosh ε - 1 - ε²/2 - ε⁴/24| ≤ exp |ε| · |ε|⁶`.

    Proof: average the truncation bound for `exp t` and `exp (-t)`. -/
private theorem cosh_quartic_error (ε : ℝ) :
    |Real.cosh ε - 1 - ε ^ 2 / 2 - ε ^ 4 / 24| ≤ Real.exp |ε| * |ε| ^ 6 := by
  set P : ℝ → ℝ := fun t =>
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120
  have hpos : |Real.exp ε - P ε| ≤ Real.exp |ε| * |ε| ^ 6 := by
    simpa [P] using exp_sub_trunc6_le ε
  have hneg : |Real.exp (-ε) - P (-ε)| ≤ Real.exp |ε| * |ε| ^ 6 := by
    simpa [P, abs_neg] using exp_sub_trunc6_le (-ε)
  have hpoly : P ε + P (-ε) = 2 * (1 + ε ^ 2 / 2 + ε ^ 4 / 24) := by
    simp only [P]; ring
  have hrewrite :
      Real.cosh ε - 1 - ε ^ 2 / 2 - ε ^ 4 / 24 =
        ((Real.exp ε - P ε) + (Real.exp (-ε) - P (-ε))) / 2 := by
    rw [Real.cosh_eq]
    linarith [hpoly]
  rw [hrewrite, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |(Real.exp ε - P ε) + (Real.exp (-ε) - P (-ε))| / 2
        ≤ (|Real.exp ε - P ε| + |Real.exp (-ε) - P (-ε)|) / 2 :=
          div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ (Real.exp |ε| * |ε| ^ 6 + Real.exp |ε| * |ε| ^ 6) / 2 :=
          div_le_div_of_nonneg_right (add_le_add hpos hneg) (by norm_num)
    _ = Real.exp |ε| * |ε| ^ 6 := by ring

/-- Quartic Taylor identity for `J(exp ε)` at depth 4:

    `|J(exp ε) - ε²/2 - ε⁴/24| ≤ exp |ε| · |ε|⁶`. -/
theorem jcost_quartic_error (ε : ℝ) :
    |Jcost (Real.exp ε) - ε ^ 2 / 2 - ε ^ 4 / 24| ≤ Real.exp |ε| * |ε| ^ 6 := by
  have h := cosh_quartic_error ε
  have hcosh : Jcost (Real.exp ε) = Real.cosh ε - 1 := Cost.Jcost_exp_cosh ε
  -- |Jcost(exp ε) - ε²/2 - ε⁴/24| = |cosh ε - 1 - ε²/2 - ε⁴/24|
  have hrewrite :
      Jcost (Real.exp ε) - ε ^ 2 / 2 - ε ^ 4 / 24
        = Real.cosh ε - 1 - ε ^ 2 / 2 - ε ^ 4 / 24 := by
    rw [hcosh]
  rw [hrewrite]
  exact h

/-- The error in approximating `V_RS` by its quartic Taylor polynomial is
    bounded uniformly on `|h| ≤ v / 2`. -/
theorem V_RS_quartic_error (Λ v h : ℝ) (hv : 0 < v) (hbound : |h| ≤ v / 2) :
    |V_RS Λ v h - V_RS_quartic Λ v h|
      ≤ |Λ| ^ 4 * (Real.exp |h / v| * |h / v| ^ 6) := by
  have hε : |h / v| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hv]
    rw [div_le_iff₀ hv]
    linarith
  have hcore := jcost_quartic_error (h / v)
  -- |V_RS − V_RS_quartic| = |Λ|^4 · |J(exp ε) − ε²/2 − ε⁴/24|
  unfold V_RS V_RS_quartic
  set ε := h / v
  have hL : Λ ^ 4 * Jcost (Real.exp ε) - Λ ^ 4 * (ε ^ 2 / 2 + ε ^ 4 / 24)
            = Λ ^ 4 * (Jcost (Real.exp ε) - ε ^ 2 / 2 - ε ^ 4 / 24) := by ring
  rw [hL, abs_mul]
  have hΛ : |Λ ^ 4| = |Λ| ^ 4 := by rw [abs_pow]
  rw [hΛ]
  have hΛ4 : 0 ≤ |Λ| ^ 4 := by positivity
  exact mul_le_mul_of_nonneg_left hcore hΛ4

/-- The leading quadratic coefficient is forced: `Λ⁴ / (2 v²)`. -/
def quadratic_coefficient (Λ v : ℝ) : ℝ := Λ ^ 4 / (2 * v ^ 2)

/-- The leading quartic coefficient is forced: `Λ⁴ / (24 v⁴)`. -/
def quartic_coefficient_canonical (Λ v : ℝ) : ℝ := Λ ^ 4 / (24 * v ^ 4)

/-- Algebraic identity: the quartic Taylor potential equals the canonical
    quadratic-plus-quartic Lagrangian potential up to renaming. -/
theorem V_RS_quartic_canonical (Λ v : ℝ) (hv : v ≠ 0) (h : ℝ) :
    V_RS_quartic Λ v h
      = quadratic_coefficient Λ v * h ^ 2
        + quartic_coefficient_canonical Λ v * h ^ 4 := by
  unfold V_RS_quartic quadratic_coefficient quartic_coefficient_canonical
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hv4 : v ^ 4 ≠ 0 := pow_ne_zero 4 hv
  field_simp

/-! ## §3. Standard-Model Dictionary -/

/-- The Standard-Model normalisation hypothesis: the canonically normalised
    Higgs mass squared equals `Λ⁴ / v²`.

    This is the *defining* normalisation map between the recognition-cost
    scale `Λ` and the SM electroweak scale `v`.  Closing this hypothesis
    from the φ-ladder yardstick is the open collider-normalisation problem
    flagged in the companion paper. -/
def NormalizationHypothesis (Λ v m_H : ℝ) : Prop :=
  Λ ^ 4 = m_H ^ 2 * v ^ 2

/-- Under the normalisation hypothesis, the SM kinetic-normalised Higgs mass
    appears as the coefficient of `½ h²` in the RS quartic Taylor potential. -/
theorem mass_term_matches_SM
    (Λ v m_H : ℝ) (hv : 0 < v) (hΛ : NormalizationHypothesis Λ v m_H) :
    quadratic_coefficient Λ v = m_H ^ 2 / 2 := by
  unfold quadratic_coefficient
  unfold NormalizationHypothesis at hΛ
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hv)
  rw [hΛ]
  field_simp

/-- Under the normalisation hypothesis, the canonical SM quartic coupling is
    `λ_SM = (1/6) · m_H² / v²`.

    In the convention `V_SM = ½ m_H² h² + (λ_SM / 4) h⁴`, matching the RS
    quartic coefficient `Λ⁴ / (24 v⁴)` to `λ_SM / 4` gives this relation. -/
theorem quartic_coupling_from_normalization
    (Λ v m_H : ℝ) (hv : 0 < v) (hΛ : NormalizationHypothesis Λ v m_H) :
    4 * quartic_coefficient_canonical Λ v = m_H ^ 2 / (6 * v ^ 2) := by
  unfold quartic_coefficient_canonical
  unfold NormalizationHypothesis at hΛ
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hv)
  have hv4 : v ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hv)
  have hv4_eq : (v : ℝ) ^ 4 = v ^ 2 * v ^ 2 := by ring
  rw [hΛ, hv4_eq]
  field_simp
  ring

/-! ## §4. Master Bridge Certificate -/

/-- Master certificate for the cost-geometry → scalar-EFT map.

    Tags: each clause is `THEOREM` except where marked `CONDITIONAL_THEOREM`;
    those clauses depend on `NormalizationHypothesis Λ v m_H`. -/
structure HiggsEFTBridgeCert where
  /-- THEOREM: the RS potential vanishes at the vacuum. -/
  vacuum_zero        : ∀ Λ v, V_RS Λ v 0 = 0
  /-- THEOREM: the RS potential is non-negative everywhere. -/
  nonneg             : ∀ Λ v h, 0 ≤ V_RS Λ v h
  /-- THEOREM: the RS potential equals `Λ⁴(cosh − 1)`. -/
  cosh_form          : ∀ Λ v h, V_RS Λ v h = Λ ^ 4 * (Real.cosh (h / v) - 1)
  /-- THEOREM: the RS potential matches its quartic Taylor approximation up
      to a sextic-order remainder bounded uniformly on `|h| ≤ v / 2`. -/
  quartic_remainder  :
    ∀ Λ v h, 0 < v → |h| ≤ v / 2 →
      |V_RS Λ v h - V_RS_quartic Λ v h|
        ≤ |Λ| ^ 4 * (Real.exp |h / v| * |h / v| ^ 6)
  /-- CONDITIONAL_THEOREM: under the normalisation hypothesis, the leading
      quadratic coefficient gives the SM Higgs mass term. -/
  mass_term_match    : ∀ Λ v m_H, 0 < v → NormalizationHypothesis Λ v m_H →
    quadratic_coefficient Λ v = m_H ^ 2 / 2
  /-- CONDITIONAL_THEOREM: under the normalisation hypothesis, the canonical
      SM quartic coupling is `λ_SM = (1/6) · m_H² / v²`. -/
  quartic_match      : ∀ Λ v m_H, 0 < v → NormalizationHypothesis Λ v m_H →
    4 * quartic_coefficient_canonical Λ v = m_H ^ 2 / (6 * v ^ 2)

/-- The bridge certificate is theorem-backed (modulo the explicit
    normalisation hypotheses recorded in its conditional clauses). -/
def higgsEFTBridgeCert : HiggsEFTBridgeCert where
  vacuum_zero       := V_RS_at_vacuum
  nonneg            := V_RS_nonneg
  cosh_form         := V_RS_eq_cosh
  quartic_remainder := fun Λ v h hv hb => V_RS_quartic_error Λ v h hv hb
  mass_term_match   := fun Λ v m_H hv hΛ => mass_term_matches_SM Λ v m_H hv hΛ
  quartic_match     := fun Λ v m_H hv hΛ =>
    quartic_coupling_from_normalization Λ v m_H hv hΛ

theorem higgsEFTBridgeCert_inhabited : Nonempty HiggsEFTBridgeCert :=
  ⟨higgsEFTBridgeCert⟩

end

end HiggsEFTBridge
end StandardModel
end IndisputableMonolith
