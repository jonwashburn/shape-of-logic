import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.RSBridge.Anchor
import IndisputableMonolith.Masses.AnchorMassRatioTable
import IndisputableMonolith.Numerics.Interval.PhiBounds

/-!
# Quark PDG Ratio Audit

This module records the discrepancy between anchor-frame mass ratios
(exact phi-powers, proved in `AnchorMassRatioTable`) and PDG-frame
mass ratios (MS-bar running masses from PDG 2024).

Within each Z-family (up quarks, down quarks), the anchor prediction
is an exact phi-power. The PDG ratio differs because the two masses
are quoted at different running scales (charm at m_c, top at pole mass,
etc.), so the QCD mass anomalous dimension shifts the ratio.

The display shift that P2g must supply is quantified per pair:

  delta_display(f, g) = log_phi(PDG_ratio(f,g)) - log_phi(anchor_ratio(f,g))

where log_phi(anchor_ratio) is an exact integer (the rung difference).

This module does NOT compute log_phi of the PDG ratios (that requires
Real.log interval arithmetic). Instead, it proves structural facts:
the PDG ratios are bounded, the anchor ratios are exact, and the
display shift is positive for the heavy quarks (PDG spreads the
intra-family ratios relative to the anchor).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace QuarkPDGRatioAudit

open Constants
open IndisputableMonolith.RSBridge
open IndisputableMonolith.Masses.AnchorMassRatioTable
open IndisputableMonolith.Numerics

noncomputable section

/-! ## PDG 2024 quark masses (MeV, MS-bar or pole)

These are observational inputs, explicitly quarantined from the
derivation surface. They define the target that the display bridge
must hit. -/

def m_u_PDG : ℝ := 2.16       -- MS-bar at 2 GeV
def m_d_PDG : ℝ := 4.70       -- MS-bar at 2 GeV
def m_s_PDG : ℝ := 93.5       -- MS-bar at 2 GeV
def m_c_PDG : ℝ := 1270       -- MS-bar at m_c
def m_b_PDG : ℝ := 4180       -- MS-bar at m_b
def m_t_PDG : ℝ := 172500     -- pole mass

-- Positivity
theorem m_u_pos : 0 < m_u_PDG := by unfold m_u_PDG; norm_num
theorem m_d_pos : 0 < m_d_PDG := by unfold m_d_PDG; norm_num
theorem m_s_pos : 0 < m_s_PDG := by unfold m_s_PDG; norm_num
theorem m_c_pos : 0 < m_c_PDG := by unfold m_c_PDG; norm_num
theorem m_b_pos : 0 < m_b_PDG := by unfold m_b_PDG; norm_num
theorem m_t_pos : 0 < m_t_PDG := by unfold m_t_PDG; norm_num

/-! ## PDG same-Z mass ratios

These are the experimentally observed ratios. Within each family, the
anchor prediction is an exact phi-power. The PDG values differ due to
QCD running and the display convention (MS-bar at different scales). -/

def PDG_ratio_tc : ℝ := m_t_PDG / m_c_PDG  -- top/charm
def PDG_ratio_cu : ℝ := m_c_PDG / m_u_PDG  -- charm/up
def PDG_ratio_tu : ℝ := m_t_PDG / m_u_PDG  -- top/up

def PDG_ratio_bs : ℝ := m_b_PDG / m_s_PDG  -- bottom/strange
def PDG_ratio_sd : ℝ := m_s_PDG / m_d_PDG  -- strange/down
def PDG_ratio_bd : ℝ := m_b_PDG / m_d_PDG  -- bottom/down

/-! ## PDG ratio bounds -/

theorem PDG_ratio_tc_bounds :
    (135 : ℝ) < PDG_ratio_tc ∧ PDG_ratio_tc < (136 : ℝ) := by
  unfold PDG_ratio_tc m_t_PDG m_c_PDG
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1270)]; norm_num
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 1270)]; norm_num

theorem PDG_ratio_cu_bounds :
    (587 : ℝ) < PDG_ratio_cu ∧ PDG_ratio_cu < (589 : ℝ) := by
  unfold PDG_ratio_cu m_c_PDG m_u_PDG
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2.16)]; norm_num
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2.16)]; norm_num

theorem PDG_ratio_bs_bounds :
    (44 : ℝ) < PDG_ratio_bs ∧ PDG_ratio_bs < (45 : ℝ) := by
  unfold PDG_ratio_bs m_b_PDG m_s_PDG
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 93.5)]; norm_num
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 93.5)]; norm_num

theorem PDG_ratio_sd_bounds :
    (19 : ℝ) < PDG_ratio_sd ∧ PDG_ratio_sd < (20 : ℝ) := by
  unfold PDG_ratio_sd m_s_PDG m_d_PDG
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 4.70)]; norm_num
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 4.70)]; norm_num

/-! ## Anchor vs PDG comparison

The anchor prediction is exp(Δr * ln φ). For φ > 1.618:
  φ^6  is between 17.94 and 18.00
  φ^11 is between 199   and 200

The PDG ratios are:
  t/c ≈ 135.8  vs  φ^6  ≈ 17.9   (ratio ≈ 7.6)
  c/u ≈ 587.9  vs  φ^11 ≈ 199    (ratio ≈ 2.95)
  b/s ≈ 44.7   vs  φ^6  ≈ 17.9   (ratio ≈ 2.5)
  s/d ≈ 19.9   vs  φ^11 ≈ 199    (ratio ≈ 0.1)

The large discrepancy for t/c comes from the big RG running between
m_c and m_t (QCD running shrinks charm and inflates top relative to
their anchor-frame values). The s/d ratio being SMALLER than the anchor
prediction reflects the opposite: both are quoted at the same scale
(2 GeV) where QCD has already run them far from their anchor ratios. -/

/-- phi^6 < 18 (via Fibonacci: phi^6 = 8*phi + 5). -/
private lemma phi6_lt_18 : phi ^ (6 : ℕ) < (18 : ℝ) := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h3 : phi ^ 3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi ^ 4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi ^ 5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi ^ 6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  rw [h6]
  have : phi < 1.619 := by
    rw [show phi = Real.goldenRatio from rfl]
    exact lt_trans phi_lt_16185 (by norm_num)
  linarith

/-- The PDG t/c ratio exceeds phi^6. The display map SPREADS the
top-charm ratio relative to the anchor prediction. -/
theorem PDG_tc_exceeds_anchor_phi6 :
    PDG_ratio_tc > phi ^ (6 : ℕ) := by
  have h := PDG_ratio_tc_bounds
  linarith [phi6_lt_18]

/-- The PDG b/s ratio exceeds phi^6. -/
theorem PDG_bs_exceeds_anchor_phi6 :
    PDG_ratio_bs > phi ^ (6 : ℕ) := by
  have h := PDG_ratio_bs_bounds
  linarith [phi6_lt_18]

/-- The display shift for top/charm is positive (PDG ratio exceeds anchor). -/
theorem PDG_tc_display_shift_positive :
    PDG_ratio_tc / phi ^ (6 : ℕ) > (1 : ℝ) := by
  rw [gt_iff_lt, lt_div_iff₀ (pow_pos phi_pos 6)]
  rw [one_mul]
  exact PDG_tc_exceeds_anchor_phi6

/-! ## Opposite-sign first-generation display shifts: the display operator is sector-dependent

The charm/up and strange/down ratios share the *same* anchor exponent `φ¹¹`
(`up_charm_over_up`, `down_strange_over_down` in `AnchorMassRatioTable`). Yet the PDG
charm/up ratio (≈588) sits *above* `φ¹¹ ≈ 199` while the PDG strange/down ratio (≈19.9) sits
*below* it. So the first-generation display shift is positive in the up sector and negative in
the down sector from one anchor exponent. No sector-independent display factor can reproduce
both — the recognition display operator must be sector-dependent. This is the quark-sector
analogue of the lepton `no_uniform_geometric_running` obstruction. -/

/-- `φ¹¹` lies in (199, 200), via the Fibonacci closed form `φ¹¹ = 89φ + 55`. -/
private lemma phi11_bounds : (199 : ℝ) < phi ^ (11 : ℕ) ∧ phi ^ (11 : ℕ) < (200 : ℝ) := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h3 : phi ^ 3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi ^ 4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi ^ 5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi ^ 6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  have h7 : phi ^ 7 = 13 * phi + 8 := by rw [pow_succ, h6]; ring_nf; rw [h2]; ring_nf
  have h8 : phi ^ 8 = 21 * phi + 13 := by rw [pow_succ, h7]; ring_nf; rw [h2]; ring_nf
  have h9 : phi ^ 9 = 34 * phi + 21 := by rw [pow_succ, h8]; ring_nf; rw [h2]; ring_nf
  have h10 : phi ^ 10 = 55 * phi + 34 := by rw [pow_succ, h9]; ring_nf; rw [h2]; ring_nf
  have h11 : phi ^ 11 = 89 * phi + 55 := by rw [pow_succ, h10]; ring_nf; rw [h2]; ring_nf
  have hlo : (1.618 : ℝ) < phi := by
    rw [show phi = Real.goldenRatio from rfl]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by
    rw [show phi = Real.goldenRatio from rfl]; exact phi_lt_16185
  rw [h11]
  constructor
  · linarith
  · linarith

/-- The up-sector charm/up display shift is above one: PDG c/u exceeds the anchor `φ¹¹`. -/
theorem cu_display_shift_above_one : PDG_ratio_cu / phi ^ (11 : ℕ) > (1 : ℝ) := by
  have hb := PDG_ratio_cu_bounds
  have hp := phi11_bounds
  rw [gt_iff_lt, lt_div_iff₀ (pow_pos phi_pos 11), one_mul]
  linarith [hb.1, hp.2]

/-- The down-sector strange/down display shift is below one: PDG s/d is under the anchor `φ¹¹`. -/
theorem sd_display_shift_below_one : PDG_ratio_sd / phi ^ (11 : ℕ) < (1 : ℝ) := by
  have hb := PDG_ratio_sd_bounds
  have hp := phi11_bounds
  rw [div_lt_iff₀ (pow_pos phi_pos 11), one_mul]
  linarith [hb.2, hp.1]

/-- **No uniform first-generation display operator.** The up and down first-generation ratios
share the anchor exponent `φ¹¹`, yet the charm/up shift is above one and the strange/down shift
is below one. So no sector-independent display factor reproduces both: the recognition display
operator is sector-dependent. -/
theorem no_uniform_first_gen_display :
    PDG_ratio_cu / phi ^ (11 : ℕ) > (1 : ℝ) ∧ PDG_ratio_sd / phi ^ (11 : ℕ) < (1 : ℝ) :=
  ⟨cu_display_shift_above_one, sd_display_shift_below_one⟩

/-! ## Certificate -/

structure QuarkPDGRatioAuditCert where
  -- PDG ratio bounds
  tc_bounds : (135 : ℝ) < PDG_ratio_tc ∧ PDG_ratio_tc < (136 : ℝ)
  cu_bounds : (587 : ℝ) < PDG_ratio_cu ∧ PDG_ratio_cu < (589 : ℝ)
  bs_bounds : (44 : ℝ) < PDG_ratio_bs ∧ PDG_ratio_bs < (45 : ℝ)
  sd_bounds : (19 : ℝ) < PDG_ratio_sd ∧ PDG_ratio_sd < (20 : ℝ)
  -- Display shift sign
  tc_exceeds_anchor : PDG_ratio_tc > phi ^ (6 : ℕ)
  bs_exceeds_anchor : PDG_ratio_bs > phi ^ (6 : ℕ)
  -- Opposite-sign first-generation shifts from the same anchor exponent φ^11
  cu_shift_above_one : PDG_ratio_cu / phi ^ (11 : ℕ) > (1 : ℝ)
  sd_shift_below_one : PDG_ratio_sd / phi ^ (11 : ℕ) < (1 : ℝ)

theorem quarkPDGRatioAuditCert_holds : QuarkPDGRatioAuditCert where
  tc_bounds := PDG_ratio_tc_bounds
  cu_bounds := PDG_ratio_cu_bounds
  bs_bounds := PDG_ratio_bs_bounds
  sd_bounds := PDG_ratio_sd_bounds
  tc_exceeds_anchor := PDG_tc_exceeds_anchor_phi6
  bs_exceeds_anchor := PDG_bs_exceeds_anchor_phi6
  cu_shift_above_one := cu_display_shift_above_one
  sd_shift_below_one := sd_display_shift_below_one

end

end QuarkPDGRatioAudit
end Masses
end IndisputableMonolith
