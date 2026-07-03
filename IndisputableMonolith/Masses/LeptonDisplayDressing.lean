import IndisputableMonolith.Masses.LeptonPDGRatioAudit

/-!
# Lepton Display Dressing

This module implements the lepton-dressing lane (`U4` / `M4`) of
`Mass_Framework_Total_Closure_Plan_20260530.html`.

Leptons are direct / near-direct observables, so the residual between the
anchor φ-power ratios and the PDG ratios is the cleanest test of the single
display factor isolated in `CrossSectorYardstickCertificate`.

The decisive fact, proved here, is that the two residuals point in **opposite**
directions:

* `μ/e`: the PDG ratio `≈ 206.77` *exceeds* `φ¹¹ ≈ 199.05` (dressing factor `> 1`);
* `τ/μ`: the PDG ratio `≈ 16.82` is *below* `φ⁶ ≈ 17.94` (dressing factor `< 1`).

A single scale-independent multiplicative dressing constant therefore cannot
reconcile both ratios. The dressing must be scale (rung) dependent. That is
exactly the signature of QED + electroweak radiative running. This module
proves the opposite-sign obstruction and names the remaining physical
derivation as `LeptonDressingFromRecognition`.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace LeptonDisplayDressing

open Constants
open LeptonPDGRatioAudit

noncomputable section

/-! ## Dressing factors as exact ratios of observed-over-anchor -/

/-- The dressing factor needed to take the anchor prediction `φ¹¹` to the PDG
`μ/e` ratio. -/
noncomputable def dressing_mu_e : ℝ :=
  PDG_ratio_mu_e / phi ^ (11 : ℕ)

/-- The dressing factor needed to take the anchor prediction `φ⁶` to the PDG
`τ/μ` ratio. -/
noncomputable def dressing_tau_mu : ℝ :=
  PDG_ratio_tau_mu / phi ^ (6 : ℕ)

theorem phi11_pos : 0 < phi ^ (11 : ℕ) := pow_pos phi_pos _
theorem phi6_pos : 0 < phi ^ (6 : ℕ) := pow_pos phi_pos _

/-- The `μ/e` dressing factor exceeds one: the anchor undershoots the data. -/
theorem dressing_mu_e_gt_one : 1 < dressing_mu_e := by
  unfold dressing_mu_e
  rw [lt_div_iff₀ phi11_pos, one_mul]
  exact PDG_mu_e_exceeds_phi11

/-- The `τ/μ` dressing factor is below one: the anchor overshoots the data. -/
theorem dressing_tau_mu_lt_one : dressing_tau_mu < 1 := by
  unfold dressing_tau_mu
  rw [div_lt_iff₀ phi6_pos, one_mul]
  exact PDG_tau_mu_below_phi6

/-- The two dressing factors are different: the `μ/e` factor is above one and the
`τ/μ` factor is below one. -/
theorem dressing_factors_opposite :
    dressing_tau_mu < 1 ∧ 1 < dressing_mu_e :=
  ⟨dressing_tau_mu_lt_one, dressing_mu_e_gt_one⟩

theorem dressing_tau_mu_lt_dressing_mu_e :
    dressing_tau_mu < dressing_mu_e :=
  lt_trans dressing_tau_mu_lt_one dressing_mu_e_gt_one

/-! ## The obstruction: no single scale-independent dressing constant works -/

/-- **OBSTRUCTION.** There is no single multiplicative dressing constant `c` that
reconciles both lepton ratios with the anchor φ-powers. Because the `μ/e`
residual is positive (`> 1`) and the `τ/μ` residual is negative (`< 1`), any
common `c` would have to be simultaneously above and below one. The dressing is
therefore scale dependent, the signature of QED + electroweak running rather than
a uniform normalization. -/
theorem no_uniform_dressing_constant :
    ¬ ∃ c : ℝ, dressing_mu_e = c ∧ dressing_tau_mu = c := by
  rintro ⟨c, hmu, htau⟩
  have : dressing_tau_mu < dressing_mu_e := dressing_tau_mu_lt_dressing_mu_e
  rw [hmu, htau] at this
  exact lt_irrefl c this

/-- **STRONGER OBSTRUCTION.** There is no uniform geometric running rate either: no
single base `ρ > 0` reproduces both lepton dressing factors as `ρ` raised to the
respective rung gaps (`ρ¹¹` for `μ/e`, `ρ⁶` for `τ/μ`). A geometric running would
force `ρ > 1` from the `μ/e` factor and `ρ < 1` from the `τ/μ` factor. The dressing
operator is therefore not a pure exponential running in the rung gap; its log-slope
changes sign between the rung-6 and rung-11 windows. This rules out the single most
natural one-parameter candidate (a constant per-rung anomalous dimension). -/
theorem no_uniform_geometric_running :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧ dressing_mu_e = ρ ^ (11 : ℕ) ∧ dressing_tau_mu = ρ ^ (6 : ℕ) := by
  rintro ⟨ρ, hρ, hmu, htau⟩
  have h1 : 1 < ρ := by
    have hpow : (1 : ℝ) < ρ ^ (11 : ℕ) := hmu ▸ dressing_mu_e_gt_one
    exact (one_lt_pow_iff_of_nonneg hρ.le (by norm_num)).mp hpow
  have h2 : ρ < 1 := by
    have hpow : ρ ^ (6 : ℕ) < 1 := htau ▸ dressing_tau_mu_lt_one
    exact (pow_lt_one_iff_of_nonneg hρ.le (by norm_num)).mp hpow
  linarith

/-! ## Third falsifiable consequence: the τ/e dressing undershoots φ¹⁷ -/

private lemma phi_lo' : (1.618 : ℝ) < phi := by
  rw [show phi = Real.goldenRatio from rfl]; exact IndisputableMonolith.Numerics.phi_gt_1618

/-- `φ¹⁷ = φ¹¹·φ⁶ > 3478`, enough to bracket the PDG `τ/e` ratio (which is below 3478). -/
private lemma phi17_gt_3478 : (3478 : ℝ) < phi ^ (17 : ℕ) := by
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
  have e17 : phi ^ (17 : ℕ) = (89 * phi + 55) * (8 * phi + 5) := by
    rw [show (17 : ℕ) = 11 + 6 from rfl, pow_add, h11, h6]
  rw [e17]; nlinarith [phi_lo']

/-- The `τ/e` dressing factor: PDG `τ/e` ratio over the anchor prediction `φ¹⁷`. -/
noncomputable def dressing_tau_e : ℝ :=
  PDG_ratio_tau_e / phi ^ (17 : ℕ)

theorem phi17_pos : 0 < phi ^ (17 : ℕ) := pow_pos phi_pos _

/-- **Composition law.** The `τ/e` dressing factors as the product of the `μ/e` and
`τ/μ` dressing factors, because the mass ratios are multiplicative and
`φ¹⁷ = φ¹¹·φ⁶`. The lepton dressing respects the rung-additive ladder structure. -/
theorem dressing_tau_e_eq :
    dressing_tau_e = dressing_mu_e * dressing_tau_mu := by
  have hme : m_e_PDG ≠ 0 := ne_of_gt m_e_pos
  have hmmu : m_mu_PDG ≠ 0 := ne_of_gt m_mu_pos
  have h11 : phi ^ (11 : ℕ) ≠ 0 := ne_of_gt phi11_pos
  have h6 : phi ^ (6 : ℕ) ≠ 0 := ne_of_gt phi6_pos
  unfold dressing_tau_e dressing_mu_e dressing_tau_mu PDG_ratio_tau_e PDG_ratio_mu_e
    PDG_ratio_tau_mu
  rw [show (17 : ℕ) = 11 + 6 from rfl, pow_add]
  field_simp

/-- The PDG `τ/e` ratio is below `φ¹⁷`: the anchor prediction overshoots. -/
theorem PDG_tau_e_below_phi17 : PDG_ratio_tau_e < phi ^ (17 : ℕ) := by
  have h := PDG_ratio_tau_e_bounds
  have h17 := phi17_gt_3478
  linarith [h.2]

/-- **THIRD FALSIFIABLE CONSEQUENCE.** The `τ/e` dressing factor is below one: the
`φ¹⁷` anchor prediction overshoots the measured `τ/e` ratio. With `μ/e` overshooting
the data the other way (`dressing_mu_e > 1`) and `τ/μ` undershooting
(`dressing_tau_mu < 1`), the composed `τ/e` residual is the parameter-free prediction
that closes the lepton triangle. -/
theorem dressing_tau_e_lt_one : dressing_tau_e < 1 := by
  unfold dressing_tau_e
  rw [div_lt_iff₀ phi17_pos, one_mul]
  exact PDG_tau_e_below_phi17

/-! ## The remaining physical derivation -/

/-- The remaining physical lepton-dressing closure.

The opposite-sign residual is proved, so the dressing cannot be a constant. What
remains is to derive the scale-dependent dressing operator from recognition
primitives (the recognition analogue of QED + electroweak radiative running)
rather than importing loop factors. The fields are propositions/data so later
work can replace them with concrete primitive content. -/
structure LeptonDressingFromRecognition : Type where
  /-- A scale-dependent dressing operator on rung-indexed ratios. -/
  dressingOperator : ℤ → ℝ
  /-- It reproduces the measured `μ/e` dressing at the `μ/e` rung gap (11). -/
  matches_mu_e : dressingOperator 11 = dressing_mu_e
  /-- It reproduces the measured `τ/μ` dressing at the `τ/μ` rung gap (6). -/
  matches_tau_mu : dressingOperator 6 = dressing_tau_mu
  /-- The operator is derived from a recognition primitive, not imported. -/
  recognition_source : Prop
  recognition_source_holds : recognition_source

/-- Certificate for the theorem-grade part of the lepton dressing lane. -/
structure LeptonDisplayDressingCert where
  audit : LeptonPDGRatioAudit.LeptonPDGRatioAuditCert
  mu_e_dressing_gt_one : 1 < dressing_mu_e
  tau_mu_dressing_lt_one : dressing_tau_mu < 1
  residuals_opposite : dressing_tau_mu < dressing_mu_e
  no_uniform_constant :
    ¬ ∃ c : ℝ, dressing_mu_e = c ∧ dressing_tau_mu = c
  no_uniform_running :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧ dressing_mu_e = ρ ^ (11 : ℕ) ∧ dressing_tau_mu = ρ ^ (6 : ℕ)
  tau_e_composition :
    dressing_tau_e = dressing_mu_e * dressing_tau_mu
  tau_e_dressing_lt_one :
    dressing_tau_e < 1
  remaining_physical_closure : Type

/-- The lepton display dressing certificate holds. The remaining work is the
scale-dependent dressing operator `LeptonDressingFromRecognition`. -/
noncomputable def leptonDisplayDressingCert : LeptonDisplayDressingCert where
  audit := LeptonPDGRatioAudit.leptonPDGRatioAuditCert_holds
  mu_e_dressing_gt_one := dressing_mu_e_gt_one
  tau_mu_dressing_lt_one := dressing_tau_mu_lt_one
  residuals_opposite := dressing_tau_mu_lt_dressing_mu_e
  no_uniform_constant := no_uniform_dressing_constant
  no_uniform_running := no_uniform_geometric_running
  tau_e_composition := dressing_tau_e_eq
  tau_e_dressing_lt_one := dressing_tau_e_lt_one
  remaining_physical_closure := LeptonDressingFromRecognition

end

end LeptonDisplayDressing
end Masses
end IndisputableMonolith
