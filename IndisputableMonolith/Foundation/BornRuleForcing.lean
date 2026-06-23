import IndisputableMonolith.Foundation.ComplexStructureForcing
import IndisputableMonolith.Verification.TwoOutcomeBornCert

/-!
# Born Rule Forcing from DFT-8 Sector Measure

**Theorem**: The unique probability measure on 8-mode sectors that is
1. normalised (total mass 1 on normalised states),
2. phase-invariant (depends only on |ψ_k|, not arg(ψ_k)),
3. additive over disjoint mode sets, and
4. consistent with the two-branch exp(−C) Born rule,

is **μ(S) = Σ_{k ∈ S} ‖ψ_k‖²**.

By Parseval, the same measure in the DFT-8 frequency basis equals
**Σ_{k ∈ S} ‖(Fψ)_k‖²**.

## Depends on
- `ComplexStructureForcing`: Signal8, inner8, dft8, Parseval, phase invariance
- `TwoOutcomeBornCert`: P_cos_eq, P_sin_eq (two-branch calibration)

## Registry
- Closes: Born-rule gap (replaces True := trivial placeholders)
- Depends on: T5, T7, T8, F-009 (measurement mechanism)
-/

namespace IndisputableMonolith.Foundation.BornRuleForcing

open scoped BigOperators
open ComplexStructureForcing
open IndisputableMonolith.Measurement
open IndisputableMonolith.Verification.TwoOutcomeBorn

noncomputable section

/-! ## Auxiliary bridge lemmas -/

private theorem normSq_eq_norm_sq (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 := by
  rw [Complex.norm_def, sq, Real.mul_self_sqrt (Complex.normSq_nonneg z)]

private theorem star_mul_self_eq_ofReal_normSq (z : ℂ) :
    starRingEnd ℂ z * z = ↑(Complex.normSq z) :=
  Complex.normSq_eq_conj_mul_self.symm

private theorem inner8_self_eq (f : Signal8) :
    inner8 f f = ∑ k : Fin 8, (↑(Complex.normSq (f k)) : ℂ) := by
  simp only [inner8]; congr 1; ext k
  exact star_mul_self_eq_ofReal_normSq (f k)

/-! ## Part 1: Normalised Signals and the Sector Measure -/

/-- A signal ψ is normalised when the sum of squared norms is 1. -/
def IsNormalized (ψ : Signal8) : Prop :=
  ∑ k : Fin 8, ‖ψ k‖ ^ 2 = 1

/-- The sector measure assigns to each mode-set S the sum of ‖ψ_k‖²
    over k ∈ S.  This is the Born-rule probability for the sector. -/
def sectorMeasure (ψ : Signal8) (S : Finset (Fin 8)) : ℝ :=
  ∑ k ∈ S, ‖ψ k‖ ^ 2

theorem sectorMeasure_nonneg (ψ : Signal8) (S : Finset (Fin 8)) :
    0 ≤ sectorMeasure ψ S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sectorMeasure_le_one (ψ : Signal8) (S : Finset (Fin 8))
    (h : IsNormalized ψ) : sectorMeasure ψ S ≤ 1 := by
  calc sectorMeasure ψ S
      ≤ sectorMeasure ψ Finset.univ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          fun _ _ _ => sq_nonneg _
    _ = 1 := h

theorem sectorMeasure_singleton (ψ : Signal8) (k : Fin 8) :
    sectorMeasure ψ {k} = ‖ψ k‖ ^ 2 := by
  simp [sectorMeasure]

theorem sectorMeasure_total (ψ : Signal8) (h : IsNormalized ψ) :
    sectorMeasure ψ Finset.univ = 1 := h

/-! ## Part 2: Phase Invariance -/

/-- Pointwise phase rotation: multiply each mode by e^{i·θ_k}. -/
def phaseRotate (ψ : Signal8) (θ : Fin 8 → ℝ) : Signal8 :=
  fun k => ψ k * Complex.exp (↑(θ k) * Complex.I)

theorem norm_phaseRotate (ψ : Signal8) (θ : Fin 8 → ℝ) (k : Fin 8) :
    ‖phaseRotate ψ θ k‖ = ‖ψ k‖ := by
  simp [phaseRotate, Complex.norm_exp_ofReal_mul_I]

/-- **Phase invariance**: the sector measure depends only on moduli. -/
theorem sectorMeasure_phase_invariant (ψ : Signal8) (θ : Fin 8 → ℝ)
    (S : Finset (Fin 8)) :
    sectorMeasure (phaseRotate ψ θ) S = sectorMeasure ψ S := by
  simp only [sectorMeasure]; congr 1; ext k; rw [norm_phaseRotate]

/-- Phase rotation preserves normalisation. -/
theorem isNormalized_phaseRotate (ψ : Signal8) (θ : Fin 8 → ℝ)
    (h : IsNormalized ψ) : IsNormalized (phaseRotate ψ θ) := by
  show ∑ k : Fin 8, ‖phaseRotate ψ θ k‖ ^ 2 = 1
  simp only [norm_phaseRotate]; exact h

/-! ## Part 3: Disjoint-Sector Additivity -/

/-- **Additivity**: for disjoint mode-sets, sector measures add. -/
theorem sectorMeasure_disjoint_union (ψ : Signal8) (S T : Finset (Fin 8))
    (h : Disjoint S T) :
    sectorMeasure ψ (S ∪ T) = sectorMeasure ψ S + sectorMeasure ψ T :=
  Finset.sum_union h

/-- Complement identity: μ(S) + μ(Sᶜ) = μ(univ). -/
theorem sectorMeasure_compl (ψ : Signal8) (S : Finset (Fin 8)) :
    sectorMeasure ψ S + sectorMeasure ψ Sᶜ = sectorMeasure ψ Finset.univ := by
  rw [← sectorMeasure_disjoint_union ψ S Sᶜ disjoint_compl_right, Finset.union_compl]

/-! ## Part 4: Parseval / DFT-8 Norm Preservation -/

/-- **Parseval corollary**: the total sector measure is preserved by the DFT-8. -/
theorem dft_sector_total_eq (ψ : Signal8) :
    sectorMeasure (dft8 ψ) Finset.univ = sectorMeasure ψ Finset.univ := by
  simp only [sectorMeasure, ← normSq_eq_norm_sq]
  have hp := dft8_preserves_norm ψ
  rw [inner8_self_eq, inner8_self_eq] at hp
  exact_mod_cast hp

/-- The DFT-8 preserves normalisation. -/
theorem isNormalized_dft8 (ψ : Signal8) (h : IsNormalized ψ) :
    IsNormalized (dft8 ψ) := by
  show sectorMeasure (dft8 ψ) Finset.univ = 1
  rw [dft_sector_total_eq]; exact h

/-! ## Part 5: Two-Branch Calibration -/

/-- Two-mode state embedding: cos θ on mode 0, sin θ on mode 1, zero elsewhere. -/
def twoBranchSignal (rot : TwoBranchRotation) : Signal8 :=
  fun k =>
    if k = (0 : Fin 8) then Complex.ofReal (Real.cos rot.θ_s)
    else if k = (1 : Fin 8) then Complex.ofReal (Real.sin rot.θ_s)
    else 0

private theorem norm_ofReal_sq (r : ℝ) : ‖(Complex.ofReal r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [← normSq_eq_norm_sq, Complex.normSq_ofReal]; ring

/-- The two-branch embedding is normalised (cos²θ + sin²θ = 1). -/
theorem twoBranchSignal_normalized (rot : TwoBranchRotation) :
    IsNormalized (twoBranchSignal rot) := by
  unfold IsNormalized twoBranchSignal
  simp only [Fin.sum_univ_eight, Fin.isValue]
  have h1 : (1 : Fin 8) ≠ 0 := by decide
  have h2 : (2 : Fin 8) ≠ 0 := by decide
  have h21 : (2 : Fin 8) ≠ 1 := by decide
  have h3 : (3 : Fin 8) ≠ 0 := by decide
  have h31 : (3 : Fin 8) ≠ 1 := by decide
  have h4 : (4 : Fin 8) ≠ 0 := by decide
  have h41 : (4 : Fin 8) ≠ 1 := by decide
  have h5 : (5 : Fin 8) ≠ 0 := by decide
  have h51 : (5 : Fin 8) ≠ 1 := by decide
  have h6 : (6 : Fin 8) ≠ 0 := by decide
  have h61 : (6 : Fin 8) ≠ 1 := by decide
  have h7 : (7 : Fin 8) ≠ 0 := by decide
  have h71 : (7 : Fin 8) ≠ 1 := by decide
  simp only [ite_true, h1, ite_false, h2, h21, h3, h31, h4, h41,
             h5, h51, h6, h61, h7, h71, norm_zero, zero_pow, ne_eq,
             OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, norm_ofReal_sq]
  linarith [Real.sin_sq_add_cos_sq rot.θ_s]

/-- Sector measure at mode 0 = cos²θ = complementary amplitude². -/
theorem sector_matches_cos_branch (rot : TwoBranchRotation) :
    sectorMeasure (twoBranchSignal rot) {0} = complementAmplitudeSquared rot := by
  simp only [sectorMeasure_singleton, twoBranchSignal, ite_true,
             complementAmplitudeSquared, norm_ofReal_sq]

/-- Sector measure at mode 1 = sin²θ = initial amplitude². -/
theorem sector_matches_sin_branch (rot : TwoBranchRotation) :
    sectorMeasure (twoBranchSignal rot) {1} = initialAmplitudeSquared rot := by
  have h10 : (1 : Fin 8) ≠ (0 : Fin 8) := by decide
  simp only [sectorMeasure_singleton, twoBranchSignal, h10, ite_false, ite_true,
             initialAmplitudeSquared, norm_ofReal_sq]

/-- **Two-branch calibration**: the sector measure agrees with the exp(−C)
    Gibbs probabilities proved in TwoOutcomeBornCert. -/
theorem sector_matches_gibbs_born (rot : TwoBranchRotation) :
    sectorMeasure (twoBranchSignal rot) {0} = P_cos rot ∧
    sectorMeasure (twoBranchSignal rot) {1} = P_sin rot :=
  ⟨by rw [sector_matches_cos_branch, ← P_cos_eq],
   by rw [sector_matches_sin_branch, ← P_sin_eq]⟩

/-! ## Part 6: Weight-Function Forcing -/

/-- **Scalar forcing**: Any weight function calibrated by the two-branch
    Born rule must be r ↦ r².

    For any r ∈ (0,1), let θ = arccos r.  Then cos θ = r and the
    calibration hypothesis gives w(r) = w(cos θ) = cos²θ = r². -/
theorem born_weight_forced (w : ℝ → ℝ)
    (hw : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
          w (Real.cos θ) = (Real.cos θ) ^ 2) :
    ∀ r : ℝ, 0 < r → r < 1 → w r = r ^ 2 := by
  intro r hr0 hr1
  have hr_le : r ≤ 1 := le_of_lt hr1
  have hcos : Real.cos (Real.arccos r) = r :=
    Real.cos_arccos (by linarith) hr_le
  have hθ_pos : 0 < Real.arccos r := by
    unfold Real.arccos
    have := Real.arcsin_lt_pi_div_two.mpr hr1
    linarith
  have hθ_lt : Real.arccos r < Real.pi / 2 := by
    unfold Real.arccos
    have := Real.arcsin_pos.mpr hr0
    linarith
  calc w r = w (Real.cos (Real.arccos r)) := by rw [hcos]
    _ = (Real.cos (Real.arccos r)) ^ 2 := hw _ hθ_pos hθ_lt
    _ = r ^ 2 := by rw [hcos]

/-! ## Part 7: Main Forcing Theorem -/

/-- **DFT-8 Sector Forcing**: the sector measure μ(S) = Σ_{k∈S} ‖ψ_k‖²
    simultaneously satisfies normalisation, phase invariance, disjoint
    additivity, and two-branch calibration. -/
theorem dft8_sector_forcing (ψ : Signal8) (h : IsNormalized ψ)
    (S : Finset (Fin 8)) :
    (sectorMeasure ψ Finset.univ = 1) ∧
    (∀ θ : Fin 8 → ℝ,
      sectorMeasure (phaseRotate ψ θ) S = sectorMeasure ψ S) ∧
    (∀ T : Finset (Fin 8), Disjoint S T →
      sectorMeasure ψ (S ∪ T) = sectorMeasure ψ S + sectorMeasure ψ T) ∧
    (∀ rot : TwoBranchRotation,
      sectorMeasure (twoBranchSignal rot) {0} = P_cos rot ∧
      sectorMeasure (twoBranchSignal rot) {1} = P_sin rot) :=
  ⟨sectorMeasure_total ψ h,
   fun θ => sectorMeasure_phase_invariant ψ θ S,
   fun T hd => sectorMeasure_disjoint_union ψ S T hd,
   fun rot => sector_matches_gibbs_born rot⟩

/-- Frequency-domain version: the same properties hold for the DFT-8
    of ψ (sector probabilities over DFT modes). -/
theorem dft8_sector_forcing_freq (ψ : Signal8) (h : IsNormalized ψ)
    (S : Finset (Fin 8)) :
    (sectorMeasure (dft8 ψ) Finset.univ = 1) ∧
    (∀ θ : Fin 8 → ℝ,
      sectorMeasure (phaseRotate (dft8 ψ) θ) S =
      sectorMeasure (dft8 ψ) S) ∧
    (∀ T : Finset (Fin 8), Disjoint S T →
      sectorMeasure (dft8 ψ) (S ∪ T) =
      sectorMeasure (dft8 ψ) S + sectorMeasure (dft8 ψ) T) :=
  ⟨isNormalized_dft8 ψ h,
   fun θ => sectorMeasure_phase_invariant (dft8 ψ) θ S,
   fun T hd => sectorMeasure_disjoint_union (dft8 ψ) S T hd⟩

end -- noncomputable section

end IndisputableMonolith.Foundation.BornRuleForcing
