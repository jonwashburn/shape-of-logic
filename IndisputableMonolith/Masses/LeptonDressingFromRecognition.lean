import Mathlib
import IndisputableMonolith.Masses.LeptonDisplayDressing
import IndisputableMonolith.Masses.LeptonicVacuumPolarizationRunning
import IndisputableMonolith.Numerics.Interval.PhiBounds

/-!
# Lepton Dressing From Recognition: operator surface and screening obstruction

`LeptonDisplayDressing` proves the measured residuals are opposite-signed:

* `μ/e` needs a dressing factor above one;
* `τ/μ` needs a dressing factor below one.

`LeptonicVacuumPolarizationRunning` supplies the real radiative seed: positive leptonic
screening and a coarse percent-scale magnitude. That seed has a fixed sign. This module proves
the next required structural fact: **positive universal screening alone cannot be the lepton
dressing operator**. Any recognition-derived dressing must contain a second, family/torsion term
whose sign changes between the `μ/e` and `τ/μ` windows.

The module deliberately does not guess the torsion dynamics. It turns the remaining problem into
an exact target:

```
dressing(gap) = screening(Δ gap) * torsion(gap)
torsion(6) < 1/screening(6)
screening(Δ) > 1
```

So U4 is no longer "find any scale-dependent factor." It is: derive the compensating torsion
operator from recognition primitives.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith
namespace Masses
namespace LeptonDressingFromRecognition

open LeptonDisplayDressing
open LeptonPDGRatioAudit
open LeptonicVacuumPolarizationRunning
open Constants

noncomputable section

/-- A positive screening shift turns into a multiplicative dressing factor. This is the
standard `α(q) = α(0)/(1-Δ)` form, abstracted away from a specific loop integral. -/
def screeningFactor (Δ : ℝ) : ℝ :=
  1 / (1 - Δ)

/-- A universal screening factor is above one whenever `0 < Δ < 1`. -/
theorem screeningFactor_gt_one {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (1 : ℝ) < screeningFactor Δ := by
  unfold screeningFactor
  have hden : 0 < 1 - Δ := by linarith
  rw [lt_div_iff₀ hden]
  linarith

/-- The reciprocal of a positive screening factor is below one. -/
theorem inv_screeningFactor_lt_one {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (screeningFactor Δ)⁻¹ < (1 : ℝ) := by
  have hs : (1 : ℝ) < screeningFactor Δ := screeningFactor_gt_one hΔ0 hΔ1
  exact inv_lt_one_of_one_lt₀ hs

/-- The two-block recognition dressing ansatz: universal radiative screening times a
family/torsion correction. -/
def recognitionDressing (screening torsion : ℤ → ℝ) (gap : ℤ) : ℝ :=
  screening gap * torsion gap

/-- No positive universal screening-only operator can reproduce the `τ/μ` dressing row. -/
theorem no_positive_screening_only_for_tau_mu {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    screeningFactor Δ ≠ dressing_tau_mu := by
  intro h
  have hs : (1 : ℝ) < screeningFactor Δ := screeningFactor_gt_one hΔ0 hΔ1
  have ht : dressing_tau_mu < (1 : ℝ) := dressing_tau_mu_lt_one
  linarith

/-- If a positive screening factor is used in the `τ/μ` row, the torsion factor must be
strictly below the inverse screening factor, hence below one. This is the precise
sign-changing target left for recognition dynamics. -/
theorem tau_mu_torsion_must_compensate {Δ τ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hmatch : screeningFactor Δ * τ = dressing_tau_mu) :
    τ < (screeningFactor Δ)⁻¹ ∧ τ < (1 : ℝ) := by
  have hs_pos : 0 < screeningFactor Δ := by
    unfold screeningFactor
    have hden : 0 < 1 - Δ := by linarith
    positivity
  have htau : dressing_tau_mu < (1 : ℝ) := dressing_tau_mu_lt_one
  have hτ : τ < (screeningFactor Δ)⁻¹ := by
    have hdiv : (screeningFactor Δ * τ) / screeningFactor Δ <
        (1 : ℝ) / screeningFactor Δ := by
      exact div_lt_div_of_pos_right (by simpa [hmatch] using htau) hs_pos
    have hleft : (screeningFactor Δ * τ) / screeningFactor Δ = τ := by
      field_simp [ne_of_gt hs_pos]
    have hright : (1 : ℝ) / screeningFactor Δ = (screeningFactor Δ)⁻¹ := by
      simp
    simpa [hleft, hright] using hdiv
  have hinv : (screeningFactor Δ)⁻¹ < (1 : ℝ) :=
    inv_screeningFactor_lt_one hΔ0 hΔ1
  exact ⟨hτ, lt_trans hτ hinv⟩

/-- If the torsion term is identically one, positive screening cannot fit both lepton rows. -/
theorem no_unit_torsion_two_row_fit {Δ_mu Δ_tau : ℝ}
    (_hmu0 : 0 < Δ_mu) (_hmu1 : Δ_mu < 1)
    (htau0 : 0 < Δ_tau) (htau1 : Δ_tau < 1) :
    ¬ (screeningFactor Δ_mu * 1 = dressing_mu_e ∧
       screeningFactor Δ_tau * 1 = dressing_tau_mu) := by
  intro h
  have bad := no_positive_screening_only_for_tau_mu htau0 htau1
  exact bad (by simpa using h.2)

/-! ## Quantitative torsion window

The previous theorems force a compensating torsion term qualitatively. The next step is to
bound it. The measured dressing factors are already tightly bracketed from the PDG ratio audit:

* `1.038 < d(μ/e) < 1.040`;
* `0.936 < d(τ/μ) < 0.939`.

If the screening shift lies in the coarse leptonic running band `0.015 < Δ < 0.05`, then the
torsion factor required in the `τ/μ` row is in `(0.889, 0.939)`. This interval is the target
for a future recognition-family/torsion derivation.
-/

private lemma phi_lo : (1.618 : ℝ) < phi := by
  rw [show phi = Real.goldenRatio from rfl]
  exact IndisputableMonolith.Numerics.phi_gt_1618

private lemma phi_hi : phi < (1.6185 : ℝ) := by
  rw [show phi = Real.goldenRatio from rfl]
  exact IndisputableMonolith.Numerics.phi_lt_16185

private lemma phi11_bounds :
    (199.0 : ℝ) < phi ^ (11 : ℕ) ∧ phi ^ (11 : ℕ) < (199.1 : ℝ) := by
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
  rw [h11]
  constructor <;> nlinarith [phi_lo, phi_hi]

private lemma phi6_bounds :
    (17.94 : ℝ) < phi ^ (6 : ℕ) ∧ phi ^ (6 : ℕ) < (17.95 : ℝ) := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h3 : phi ^ 3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi ^ 4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi ^ 5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi ^ 6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  rw [h6]
  constructor <;> nlinarith [phi_lo, phi_hi]

theorem dressing_mu_e_bounds :
    (1.038 : ℝ) < dressing_mu_e ∧ dressing_mu_e < (1.040 : ℝ) := by
  unfold dressing_mu_e
  have hpdg := PDG_ratio_mu_e_bounds
  have hphi := phi11_bounds
  constructor
  · rw [lt_div_iff₀ (by linarith [hphi.1] : (0 : ℝ) < phi ^ (11 : ℕ))]
    nlinarith
  · rw [div_lt_iff₀ (by linarith [hphi.1] : (0 : ℝ) < phi ^ (11 : ℕ))]
    nlinarith

theorem dressing_tau_mu_bounds :
    (0.936 : ℝ) < dressing_tau_mu ∧ dressing_tau_mu < (0.939 : ℝ) := by
  unfold dressing_tau_mu
  have hpdg := PDG_ratio_tau_mu_bounds
  have hphi := phi6_bounds
  constructor
  · rw [lt_div_iff₀ (by linarith [hphi.1] : (0 : ℝ) < phi ^ (6 : ℕ))]
    nlinarith
  · rw [div_lt_iff₀ (by linarith [hphi.1] : (0 : ℝ) < phi ^ (6 : ℕ))]
    nlinarith

/-- If a screening shift in the certified lepton-running band is used for `τ/μ`, the torsion
term is quantitatively forced into a narrow compensating window. -/
theorem tau_mu_torsion_window_for_leptonic_band {Δ τ : ℝ}
    (hΔlo : (0.015 : ℝ) < Δ) (hΔhi : Δ < (0.05 : ℝ))
    (hmatch : screeningFactor Δ * τ = dressing_tau_mu) :
    (0.889 : ℝ) < τ ∧ τ < (0.939 : ℝ) := by
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hΔ1 : Δ < (1 : ℝ) := by linarith
  have hden : 0 < 1 - Δ := by linarith
  have hs_pos : 0 < screeningFactor Δ := by
    unfold screeningFactor
    positivity
  have hτ_eq : τ = dressing_tau_mu * (1 - Δ) := by
    have hdiv : (screeningFactor Δ * τ) / screeningFactor Δ =
        dressing_tau_mu / screeningFactor Δ := by rw [hmatch]
    have hleft : (screeningFactor Δ * τ) / screeningFactor Δ = τ := by
      field_simp [ne_of_gt hs_pos]
    have hright : dressing_tau_mu / screeningFactor Δ = dressing_tau_mu * (1 - Δ) := by
      unfold screeningFactor
      field_simp [ne_of_gt hden]
    linarith
  have hd := dressing_tau_mu_bounds
  constructor
  · rw [hτ_eq]
    have hfactor : (0.95 : ℝ) < 1 - Δ := by linarith
    have hdpos : (0 : ℝ) < dressing_tau_mu := by linarith
    have hmul : (0.936 : ℝ) * 0.95 < dressing_tau_mu * (1 - Δ) :=
      mul_lt_mul hd.1 (le_of_lt hfactor) (by norm_num) (le_of_lt hdpos)
    norm_num at hmul ⊢
    linarith
  · rw [hτ_eq]
    have hfactor : 1 - Δ < (1 : ℝ) := by linarith
    have hfactor_pos : 0 < 1 - Δ := by linarith
    have hmul : dressing_tau_mu * (1 - Δ) < (0.939 : ℝ) * 1 :=
      mul_lt_mul hd.2 (le_of_lt hfactor) hfactor_pos (by norm_num)
    norm_num at hmul ⊢
    linarith

/-- A concrete record for the remaining U4 dynamic target. `screening` may be supplied by a
loop/running theorem such as `LeptonicVacuumPolarizationRunning`; `torsion` is the missing
recognition-family term. -/
structure RecognitionLeptonDressingOperator where
  screening : ℤ → ℝ
  torsion : ℤ → ℝ
  dressingOperator : ℤ → ℝ := recognitionDressing screening torsion
  matches_mu_e : dressingOperator 11 = dressing_mu_e
  matches_tau_mu : dressingOperator 6 = dressing_tau_mu
  screening_positive_shift : Prop
  torsion_source : Prop
  screening_positive_shift_holds : screening_positive_shift
  torsion_source_holds : torsion_source

/-- Certificate for the theorem-grade part of the recognition-dressing surface. -/
structure LeptonDressingFromRecognitionCert where
  screening_above_one :
    ∀ {Δ : ℝ}, 0 < Δ → Δ < 1 → (1 : ℝ) < screeningFactor Δ
  screening_only_tau_forbidden :
    ∀ {Δ : ℝ}, 0 < Δ → Δ < 1 → screeningFactor Δ ≠ dressing_tau_mu
  tau_torsion_compensation :
    ∀ {Δ τ : ℝ}, 0 < Δ → Δ < 1 →
      screeningFactor Δ * τ = dressing_tau_mu →
      τ < (screeningFactor Δ)⁻¹ ∧ τ < (1 : ℝ)
  unit_torsion_forbidden :
    ∀ {Δ_mu Δ_tau : ℝ}, 0 < Δ_mu → Δ_mu < 1 → 0 < Δ_tau → Δ_tau < 1 →
      ¬ (screeningFactor Δ_mu * 1 = dressing_mu_e ∧
         screeningFactor Δ_tau * 1 = dressing_tau_mu)
  dressing_mu_e_band : (1.038 : ℝ) < dressing_mu_e ∧ dressing_mu_e < 1.040
  dressing_tau_mu_band : (0.936 : ℝ) < dressing_tau_mu ∧ dressing_tau_mu < 0.939
  tau_torsion_window :
    ∀ {Δ τ : ℝ}, (0.015 : ℝ) < Δ → Δ < 0.05 →
      screeningFactor Δ * τ = dressing_tau_mu →
      (0.889 : ℝ) < τ ∧ τ < 0.939
  remaining_operator : Type

theorem leptonDressingFromRecognitionCert_holds :
    Nonempty LeptonDressingFromRecognitionCert :=
  ⟨{ screening_above_one := fun h0 h1 => screeningFactor_gt_one h0 h1
     screening_only_tau_forbidden := fun h0 h1 => no_positive_screening_only_for_tau_mu h0 h1
     tau_torsion_compensation := fun h0 h1 hm => tau_mu_torsion_must_compensate h0 h1 hm
     unit_torsion_forbidden := fun hmu0 hmu1 htau0 htau1 =>
       no_unit_torsion_two_row_fit hmu0 hmu1 htau0 htau1
     dressing_mu_e_band := dressing_mu_e_bounds
     dressing_tau_mu_band := dressing_tau_mu_bounds
     tau_torsion_window := fun hlo hhi hm => tau_mu_torsion_window_for_leptonic_band hlo hhi hm
     remaining_operator := RecognitionLeptonDressingOperator }⟩

end

end LeptonDressingFromRecognition
end Masses
end IndisputableMonolith
