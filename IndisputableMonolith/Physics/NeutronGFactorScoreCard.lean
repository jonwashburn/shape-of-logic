import Mathlib
import IndisputableMonolith.Nuclear.Neutron_Magnetic_Moment_RS

/-!
# Neutron g-Factor Score Card

Phase 1 row **P1-C08** in `planning/PHYSICAL_DERIVATION_PLAN.md`.

## Statement

The current theorem-grade support is structural: the neutron magnetic
moment row has a J-cost-on-ratio certificate, but the codebase does not
yet contain a derived numerical prediction for the neutron `g` factor.

## Measurement target

CODATA / PDG:

`g_n ≈ -3.82608545` (dimensionless), equivalently
`μ_n ≈ -1.91304273 μ_N`.

This module records the CODATA target and proves only the structural
J-cost facts already available. The numerical spin/strong-sector bridge
is named as the residual.

Falsifier: once the neutron spin-sector bridge is stated, CODATA outside
the declared interval falsifies the row; until then, claiming `g_n` is
derived is false.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Physics.NeutronGFactorScoreCard

open IndisputableMonolith.Nuclear.Neutron_Magnetic_Moment_RS

noncomputable section

/-- CODATA/PDG neutron g-factor target. -/
def row_neutron_g_codata : ℝ := -3.82608545

/-- CODATA neutron magnetic moment target in nuclear magnetons. -/
def row_neutron_mu_over_muN_codata : ℝ := -1.91304273

/-- Named residual: derive a neutron spin/strong-sector numerical `g_n`. -/
def NeutronGFactorResidual : Prop :=
  ∃ g_pred : ℝ,
    |g_pred - row_neutron_g_codata| / |row_neutron_g_codata| < (1e-6 : ℝ)

theorem row_neutron_g_codata_negative :
    row_neutron_g_codata < 0 := by
  unfold row_neutron_g_codata
  norm_num

theorem row_neutron_mu_codata_negative :
    row_neutron_mu_over_muN_codata < 0 := by
  unfold row_neutron_mu_over_muN_codata
  norm_num

theorem row_neutron_magnetic_cost_matched (r : ℝ) (h : r ≠ 0) :
    domainCost r r = 0 :=
  domainCost_at_eq r h

theorem row_neutron_magnetic_cost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) :
    0 ≤ domainCost m e :=
  domainCost_nonneg m e hm he

theorem row_neutron_threshold_pos :
    0 < canonicalThreshold :=
  canonicalThreshold_pos

theorem row_neutron_g_residual_named :
    NeutronGFactorResidual = NeutronGFactorResidual := rfl

structure NeutronGFactorScoreCardCert where
  g_target_negative : row_neutron_g_codata < 0
  mu_target_negative : row_neutron_mu_over_muN_codata < 0
  cost_matched : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
  residual_named : NeutronGFactorResidual = NeutronGFactorResidual

theorem neutronGFactorScoreCardCert_holds :
    Nonempty NeutronGFactorScoreCardCert :=
  ⟨{ g_target_negative := row_neutron_g_codata_negative
     mu_target_negative := row_neutron_mu_codata_negative
     cost_matched := row_neutron_magnetic_cost_matched
     cost_nonneg := row_neutron_magnetic_cost_nonneg
     threshold_pos := row_neutron_threshold_pos
     residual_named := row_neutron_g_residual_named }⟩

end

end IndisputableMonolith.Physics.NeutronGFactorScoreCard
