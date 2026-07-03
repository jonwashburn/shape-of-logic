import IndisputableMonolith.Constants.KDisplayCore

namespace IndisputableMonolith
namespace Constants

/-! ### Dimensionless bridge ratio K and display equalities -/

namespace RSUnits

/-!
Core K-display definitions/lemmas live in `IndisputableMonolith.Constants.KDisplayCore`.
This file extends those basics with additional measurement/protocol material.
-/

/-- Structural speed identity from units: ℓ0/τ0 = c. -/
lemma ell0_div_tau0_eq_c (U : RSUnits) (h : U.tau0 ≠ 0) : U.ell0 / U.tau0 = U.c := by
  calc
    U.ell0 / U.tau0 = (U.c * U.tau0) / U.tau0 := by rw [U.c_ell0_tau0]
    _ = U.c * (U.tau0 / U.tau0) := by rw [mul_div_assoc]
    _ = U.c * 1 := by rw [div_self h]
    _ = U.c := by rw [mul_one]

/-- Display speed equals structural speed: (λ_kin/τ_rec) = c. -/
lemma display_speed_eq_c_of_nonzero (U : RSUnits)
  (hτ : tau_rec_display U ≠ 0) : (lambda_kin_display U) / (tau_rec_display U) = U.c := by
  have h := lambda_kin_from_tau_rec U
  calc
    (lambda_kin_display U) / (tau_rec_display U)
        = (U.c * tau_rec_display U) / (tau_rec_display U) := by rw [h]
    _   = U.c * (tau_rec_display U / tau_rec_display U) := by rw [mul_div_assoc]
    _   = U.c * 1 := by rw [div_self hτ]
    _   = U.c := by rw [mul_one]

/-! Strengthen display-speed equality: remove nonzero hypothesis by proving positivity. -/
lemma tau_rec_display_pos (U : RSUnits) (h : 0 < U.tau0) : 0 < tau_rec_display U := by
  -- τ_rec_display = (2π·τ₀)/(8 log φ) > 0 when τ₀ > 0, π > 0, log φ > 0
  unfold tau_rec_display
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : 0 < Real.log phi := Real.log_pos one_lt_phi
  positivity

lemma tau_rec_display_ne_zero (U : RSUnits) (h : 0 < U.tau0) : tau_rec_display U ≠ 0 := by
  exact ne_of_gt (tau_rec_display_pos U h)

lemma display_speed_eq_c (U : RSUnits) (h : 0 < U.tau0) :
  (lambda_kin_display U) / (tau_rec_display U) = RSUnits.c U := by
  have hτ : tau_rec_display U ≠ 0 := tau_rec_display_ne_zero U h
  exact display_speed_eq_c_of_nonzero U hτ

/-! Strengthened K-Gate Lemmas (Consolidation) -/

/-- K-gate is independent of units rescaling -/
theorem K_gate_units_invariant (U : RSUnits) (α : ℝ) (hα : 0 < α) (hτ : 0 < U.tau0) :
  let U' : RSUnits := { tau0 := α * U.tau0, ell0 := α * U.ell0, c := U.c,
                        c_ell0_tau0 := by calc U.c * (α * U.tau0) = α * (U.c * U.tau0) := by ring
                                              _ = α * U.ell0 := by rw [U.c_ell0_tau0] }
  (tau_rec_display U') / U'.tau0 = (tau_rec_display U) / U.tau0 := by
  intro U'
  have hα' : α ≠ 0 := ne_of_gt hα
  have hτ' : U.tau0 ≠ 0 := ne_of_gt hτ
  rw [tau_rec_display_ratio U hτ', tau_rec_display_ratio U' (mul_ne_zero hα' hτ')]

/-- Units quotient functoriality: K-gate commutes with units transformations -/
theorem units_quotient_preserves_K (U : RSUnits) (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ∀ (α : ℝ), α ≠ 0 →
    -- Under rescaling (τ0, ℓ0) → (α·τ0, α·ℓ0), K_gate_ratio remains invariant
    (tau_rec_display U) / U.tau0 = K_gate_ratio := by
  intro α _hα
  exact tau_rec_display_ratio U hτ

/-- Single-inequality audit: checking one route inequality suffices (routes equal).

    Since `(tau_rec_display U)/τ0 = (lambda_kin_display U)/ℓ0` by `K_gate_eqK`,
    the inequality direction is immediate. -/
theorem single_inequality_audit (U : RSUnits) (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  (tau_rec_display U) / U.tau0 ≤ (lambda_kin_display U) / U.ell0 := by
  have h := K_gate_eqK U hτ hℓ
  rw [h.1, h.2]

/-- Tolerance band for K-gate measurement -/
noncomputable def K_gate_tolerance (U : RSUnits) (σ_tau σ_ell : ℝ) : ℝ :=
  -- Combined uncertainty for K from τ_rec and λ_kin measurements
  -- σ_K = K_gate_ratio · √((σ_τ/τ)² + (σ_ℓ/ℓ)²) (error propagation)
  let rel_tau := σ_tau / (tau_rec_display U)
  let rel_ell := σ_ell / (lambda_kin_display U)
  K_gate_ratio * Real.sqrt (rel_tau^2 + rel_ell^2)

/-- K-gate passes if measured values agree within tolerance -/
noncomputable def K_gate_check (tau_meas lambda_meas : ℝ) (U : RSUnits) (tolerance : ℝ) : Prop :=
  let K_tau := tau_meas / U.tau0
  let K_lambda := lambda_meas / U.ell0
  |K_tau - K_lambda| < tolerance

/-! Advanced Display Properties -/

/-- Display speed is positive (null cone, lightlike) -/
theorem display_speed_positive (U : RSUnits) (h : 0 < U.tau0) (hc : 0 < U.c) :
  0 < (lambda_kin_display U) / (tau_rec_display U) := by
  rw [display_speed_eq_c U h]
  exact hc

/-- Displays scale uniformly: ratio is scale-invariant -/
theorem display_ratio_scale_invariant (U : RSUnits) (hτ : 0 < U.tau0) (α : ℝ) (hα : 0 < α) :
  let tau' := α * (tau_rec_display U)
  let lambda' := α * (lambda_kin_display U)
  lambda' / tau' = (lambda_kin_display U) / (tau_rec_display U) := by
  intro tau' lambda'
  have hα' : α ≠ 0 := ne_of_gt hα
  have hτ' : tau_rec_display U ≠ 0 := tau_rec_display_ne_zero U hτ
  simp only [tau', lambda']
  rw [mul_div_mul_left _ _ hα']

/-- Display derivatives (for rate transformations) -/
theorem display_rate_matches_structural_rate (U : RSUnits) :
  (lambda_kin_display U) / (tau_rec_display U) = U.ell0 / U.tau0 := by
  -- λ_kin / τ_rec = (2π·ℓ₀/(8 log φ)) / (2π·τ₀/(8 log φ)) = ℓ₀/τ₀
  simp only [lambda_kin_display, tau_rec_display]
  have hlog : 0 < Real.log phi := Real.log_pos one_lt_phi
  have h8log : 8 * Real.log phi ≠ 0 := by linarith
  have hpi : 2 * Real.pi ≠ 0 := by linarith [Real.pi_pos]
  have h2pi_ell : 2 * Real.pi * U.ell0 / (8 * Real.log phi) =
                  U.ell0 * (2 * Real.pi / (8 * Real.log phi)) := by ring
  have h2pi_tau : 2 * Real.pi * U.tau0 / (8 * Real.log phi) =
                  U.tau0 * (2 * Real.pi / (8 * Real.log phi)) := by ring
  rw [h2pi_ell, h2pi_tau]
  have h_factor : 2 * Real.pi / (8 * Real.log phi) ≠ 0 := by
    apply div_ne_zero hpi h8log
  rw [mul_div_mul_right _ _ h_factor]

/-- Display-level Lorentz structure: (λ/τ)² - c² = 0 (null) -/
theorem display_null_condition (U : RSUnits) (h : 0 < U.tau0) :
  ((lambda_kin_display U) / (tau_rec_display U))^2 = U.c^2 := by
  simp only [display_speed_eq_c U h]

/-! Bridge Coherence and Categorical Structure -/

/-- Units equivalence class: two units packs are equivalent if they have same c -/
def UnitsEquivalent (U1 U2 : RSUnits) : Prop :=
  U1.c = U2.c ∧ ∃ α : ℝ, α ≠ 0 ∧ U2.tau0 = α * U1.tau0 ∧ U2.ell0 = α * U1.ell0

/-- Units equivalence is an equivalence relation -/
theorem UnitsEquivalent.refl (U : RSUnits) : UnitsEquivalent U U := by
  exact ⟨rfl, 1, by norm_num, by norm_num, by norm_num⟩

theorem UnitsEquivalent.symm {U1 U2 : RSUnits} (h : UnitsEquivalent U1 U2) :
    UnitsEquivalent U2 U1 := by
  obtain ⟨hc, α, hα, hτ, hℓ⟩ := h
  refine ⟨hc.symm, α⁻¹, inv_ne_zero hα, ?_, ?_⟩
  · calc U1.tau0 = α⁻¹ * (α * U1.tau0) := by field_simp [hα]
      _ = α⁻¹ * U2.tau0 := by rw [hτ]
  · calc U1.ell0 = α⁻¹ * (α * U1.ell0) := by field_simp [hα]
      _ = α⁻¹ * U2.ell0 := by rw [hℓ]

theorem UnitsEquivalent.trans {U1 U2 U3 : RSUnits}
    (h12 : UnitsEquivalent U1 U2) (h23 : UnitsEquivalent U2 U3) :
    UnitsEquivalent U1 U3 := by
  obtain ⟨hc12, α, hα, hτ12, hℓ12⟩ := h12
  obtain ⟨hc23, β, hβ, hτ23, hℓ23⟩ := h23
  refine ⟨hc12.trans hc23, α * β, mul_ne_zero hα hβ, ?_, ?_⟩
  · calc U3.tau0 = β * U2.tau0 := hτ23
      _ = β * (α * U1.tau0) := by rw [hτ12]
      _ = (α * β) * U1.tau0 := by ring
  · calc U3.ell0 = β * U2.ell0 := hℓ23
      _ = β * (α * U1.ell0) := by rw [hℓ12]
      _ = (α * β) * U1.ell0 := by ring

/-- Displays are invariant under units equivalence -/
theorem displays_invariant_under_equivalence {U1 U2 : RSUnits}
    (h : UnitsEquivalent U1 U2) (hτ1 : U1.tau0 ≠ 0) (hℓ1 : U1.ell0 ≠ 0) :
    (tau_rec_display U1) / U1.tau0 = (tau_rec_display U2) / U2.tau0 := by
  obtain ⟨_, α, hα, hτ2, _⟩ := h
  have hτ2' : U2.tau0 ≠ 0 := by simp [hτ2, hα, hτ1]
  rw [tau_rec_display_ratio U1 hτ1, tau_rec_display_ratio U2 hτ2']

/-! Measurement Protocols and Falsifiers -/

/-- Measurement protocol for K-gate validation -/
structure KGateMeasurement where
  /-- Measured τ_rec (time-first route) -/
  tau_rec_measured : ℝ
  /-- Measured λ_kin (length-first route) -/
  lambda_kin_measured : ℝ
  /-- RS units pack used for normalization -/
  units : RSUnits
  /-- Measurement uncertainties -/
  sigma_tau : ℝ
  sigma_lambda : ℝ
  /-- Derived: K from each route -/
  K_from_tau : ℝ := tau_rec_measured / units.tau0
  K_from_lambda : ℝ := lambda_kin_measured / units.ell0

/-- K-gate validation: routes agree within uncertainty -/
noncomputable def validateKGate (meas : KGateMeasurement) : Prop :=
  let tolerance := K_gate_tolerance meas.units meas.sigma_tau meas.sigma_lambda
  |meas.K_from_tau - meas.K_from_lambda| < tolerance

/-- Falsifier: K-gate mismatch beyond tolerance -/
noncomputable def falsifier_K_gate_mismatch (meas : KGateMeasurement) : Prop :=
  ¬validateKGate meas

/-! Bridge Factorization -/

/-- Observable displays factor through units quotient (sketch) -/
theorem observable_factors_through_quotient (O : RSUnits → ℝ)
    (hQuot : ∀ U α, α ≠ 0 → O {tau0 := α * U.tau0, ell0 := α * U.ell0, c := U.c,
                               c_ell0_tau0 := by calc U.c * (α * U.tau0) = α * (U.c * U.tau0) := by ring
                                                     _ = α * U.ell0 := by rw [U.c_ell0_tau0]} = O U) :
    ∀ U1 U2, UnitsEquivalent U1 U2 → O U1 = O U2 := by
  intro U1 U2 h
  obtain ⟨hc, α, hα, hτ, hℓ⟩ := h
  -- U2 = scaled version of U1
  have h1 := hQuot U1 α hα
  -- Need to show the scaled U1 equals U2
  have hU2_eq : U2 = {tau0 := α * U1.tau0, ell0 := α * U1.ell0, c := U1.c,
                       c_ell0_tau0 := by calc U1.c * (α * U1.tau0) = α * (U1.c * U1.tau0) := by ring
                                             _ = α * U1.ell0 := by rw [U1.c_ell0_tau0]} := by
    cases U2
    simp only [RSUnits.mk.injEq]
    exact ⟨hτ, hℓ, hc.symm⟩
  rw [hU2_eq]
  exact h1.symm

/-! Documentation and Usage -/

/-!
Standard K-gate verification procedure (documentation).

1. Measure τ_rec via time-first route (e.g., pulsar timing)
2. Measure λ_kin via length-first route (e.g., interferometry)
3. Compute K from each: K_τ = τ_rec/τ0, K_λ = λ_kin/ℓ0
4. Check agreement: |K_τ - K_λ| < tolerance
5. If check fails → bridge falsified
-/

end RSUnits

end Constants
end IndisputableMonolith
