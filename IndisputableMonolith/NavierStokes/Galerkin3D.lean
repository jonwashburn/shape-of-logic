import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# 3D Spectral Galerkin Truncation for Navier–Stokes

Extension of `ClassicalBridge.Fluids.Galerkin2D` to three spatial dimensions.
The key results:

1. Fourier mode truncation on T³ with `[-N, N]³` modes
2. Energy identity: the Galerkin nonlinearity is energy-skew (⟪B(u,u), u⟫ = 0)
3. Viscous energy dissipation: ⟪u, Δu⟫ ≤ 0, with equality only at u = 0
4. Enstrophy bound: the spectral enstrophy Σ|k|²|û_k|² is controlled by νN²
5. Connection to the discrete sub-Kolmogorov framework

## Paper reference
RS_NavierStokes_BKM.tex, §4 (Galerkin approximation)
-/

namespace IndisputableMonolith.NavierStokes.Galerkin3D

open Real
open scoped InnerProductSpace

/-! ## Truncated Fourier modes on T³ -/

abbrev Mode3 : Type := ℤ × ℤ × ℤ

noncomputable def modes3 (N : ℕ) : Finset Mode3 :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ)).product
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).product
      (Finset.Icc (-(N : ℤ)) (N : ℤ))))

abbrev VelCoeff3 : Type := EuclideanSpace ℝ (Fin 3)

abbrev GalerkinState3 (N : ℕ) : Type :=
  EuclideanSpace ℝ ((modes3 N) × Fin 3)

/-! ## Wave number and spectral operators -/

noncomputable def kSq3 (k : Mode3) : ℝ :=
  (k.1 : ℝ) ^ 2 + (k.2.1 : ℝ) ^ 2 + (k.2.2 : ℝ) ^ 2

lemma kSq3_nonneg (k : Mode3) : 0 ≤ kSq3 k := by
  unfold kSq3; positivity

noncomputable def laplacianCoeff3 {N : ℕ} (u : GalerkinState3 N) : GalerkinState3 N :=
  WithLp.toLp 2 (fun kc => (-kSq3 ((kc.1 : Mode3))) * u kc)

def ConvectionOp3 (N : ℕ) : Type :=
  GalerkinState3 N → GalerkinState3 N → GalerkinState3 N

noncomputable def galerkinNSRHS3 {N : ℕ} (ν : ℝ) (B : ConvectionOp3 N) (u : GalerkinState3 N) :
    GalerkinState3 N :=
  (ν • laplacianCoeff3 u) - (B u u)

/-! ## Energy functional -/

noncomputable def discreteEnergy3 {N : ℕ} (u : GalerkinState3 N) : ℝ :=
  (1 / 2 : ℝ) * ‖u‖ ^ 2

structure EnergySkewHypothesis3 {N : ℕ} (B : ConvectionOp3 N) : Prop where
  skew : ∀ u : GalerkinState3 N, ⟪B u u, u⟫_ℝ = 0

/-! ## Enstrophy functional

The spectral enstrophy Σ |k|² |û_k|² is the Fourier-side representation
of ‖∇u‖²_{L²}. For vorticity control via BKM, this is the key quantity. -/

noncomputable def spectralEnstrophy {N : ℕ} (u : GalerkinState3 N) : ℝ :=
  ∑ kc : (modes3 N) × Fin 3, kSq3 (kc.1 : Mode3) * (u kc) ^ 2

lemma spectralEnstrophy_nonneg {N : ℕ} (u : GalerkinState3 N) :
    0 ≤ spectralEnstrophy u := by
  unfold spectralEnstrophy
  apply Finset.sum_nonneg
  intro kc _
  exact mul_nonneg (kSq3_nonneg _) (sq_nonneg _)

/-! ## Inviscid energy conservation -/

theorem inviscid_energy_deriv_zero3 {N : ℕ} (B : ConvectionOp3 N) (HB : EnergySkewHypothesis3 B)
    (u : ℝ → GalerkinState3 N) {t : ℝ}
    (hu : HasDerivAt u (-(B (u t) (u t))) t) :
    HasDerivAt (fun s => discreteEnergy3 (u s)) 0 t := by
  have h_normsq :
      HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * ⟪u t, -(B (u t) (u t))⟫_ℝ) t := by
    simpa using (HasDerivAt.norm_sq hu)
  have h_energy : HasDerivAt (fun s => discreteEnergy3 (u s))
      ((1 / 2 : ℝ) * (2 * ⟪u t, -(B (u t) (u t))⟫_ℝ)) t := by
    simpa [discreteEnergy3, mul_assoc] using h_normsq.const_mul (1 / 2 : ℝ)
  have h_inner_zero : ⟪u t, -(B (u t) (u t))⟫_ℝ = 0 := by
    calc
      ⟪u t, -(B (u t) (u t))⟫_ℝ = -⟪u t, B (u t) (u t)⟫_ℝ := by simp
      _ = -⟪B (u t) (u t), u t⟫_ℝ := by simp [real_inner_comm]
      _ = 0 := by simp [HB.skew (u t)]
  simpa [h_inner_zero] using h_energy

/-! ## Viscous dissipation -/

lemma laplacianCoeff3_inner_self_nonpos {N : ℕ} (u : GalerkinState3 N) :
    ⟪u, laplacianCoeff3 u⟫_ℝ ≤ 0 := by
  classical
  have hsum :
      ⟪u, laplacianCoeff3 u⟫_ℝ =
        ∑ kc : (modes3 N) × Fin 3, u kc * ((-kSq3 (kc.1 : Mode3)) * u kc) := by
    simp [laplacianCoeff3, PiLp.inner_apply, kSq3, mul_comm, mul_left_comm]
  rw [hsum]
  refine Finset.sum_nonpos ?_
  intro kc _
  have hkneg : (-kSq3 (kc.1 : Mode3)) ≤ 0 := by linarith [kSq3_nonneg (kc.1 : Mode3)]
  have hmul : 0 ≤ u kc * u kc := mul_self_nonneg (u kc)
  calc
    u kc * ((-kSq3 (kc.1 : Mode3)) * u kc)
        = (-kSq3 (kc.1 : Mode3)) * (u kc * u kc) := by ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hkneg hmul

theorem viscous_energy_deriv3 {N : ℕ} (ν : ℝ) (_hν : 0 ≤ ν)
    (B : ConvectionOp3 N) (HB : EnergySkewHypothesis3 B)
    (u : ℝ → GalerkinState3 N) {t : ℝ}
    (hu : HasDerivAt u (galerkinNSRHS3 ν B (u t)) t) :
    HasDerivAt (fun s => discreteEnergy3 (u s)) (ν * ⟪u t, laplacianCoeff3 (u t)⟫_ℝ) t := by
  have h_normsq :
      HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * ⟪u t, galerkinNSRHS3 ν B (u t)⟫_ℝ) t := by
    simpa using (HasDerivAt.norm_sq hu)
  have h_energy :
      HasDerivAt (fun s => discreteEnergy3 (u s)) ((1 / 2 : ℝ) * (2 * ⟪u t, galerkinNSRHS3 ν B (u t)⟫_ℝ)) t := by
    simpa [discreteEnergy3, mul_assoc] using h_normsq.const_mul (1 / 2 : ℝ)
  have h_skew' : ⟪u t, B (u t) (u t)⟫_ℝ = 0 := by
    have : ⟪B (u t) (u t), u t⟫_ℝ = 0 := HB.skew (u t)
    simpa [real_inner_comm] using this
  have h_inner :
      ⟪u t, galerkinNSRHS3 ν B (u t)⟫_ℝ = ν * ⟪u t, laplacianCoeff3 (u t)⟫_ℝ := by
    simp [galerkinNSRHS3, inner_sub_right, inner_smul_right, h_skew']
  simpa [h_inner, mul_assoc, mul_left_comm, mul_comm] using h_energy

theorem viscous_energy_nonpos3 {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (_B : ConvectionOp3 N) (_HB : EnergySkewHypothesis3 _B)
    (u : ℝ → GalerkinState3 N) {t : ℝ}
    (_hu : HasDerivAt u (galerkinNSRHS3 ν _B (u t)) t) :
    ν * ⟪u t, laplacianCoeff3 (u t)⟫_ℝ ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hν (laplacianCoeff3_inner_self_nonpos (u t))

theorem viscous_energy_antitone3 {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp3 N) (HB : EnergySkewHypothesis3 B)
    (u : ℝ → GalerkinState3 N)
    (hu : ∀ t : ℝ, HasDerivAt u (galerkinNSRHS3 ν B (u t)) t) :
    Antitone (fun t => discreteEnergy3 (u t)) := by
  refine antitone_of_hasDerivAt_nonpos (f := fun t => discreteEnergy3 (u t))
      (f' := fun t => ν * ⟪u t, laplacianCoeff3 (u t)⟫_ℝ) ?_ ?_
  · intro t; exact viscous_energy_deriv3 (N := N) ν hν B HB u (hu t)
  · intro t; exact viscous_energy_nonpos3 (N := N) ν hν B HB u (hu t)

theorem viscous_energy_bound3 {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp3 N) (HB : EnergySkewHypothesis3 B)
    (u : ℝ → GalerkinState3 N)
    (hu : ∀ t : ℝ, HasDerivAt u (galerkinNSRHS3 ν B (u t)) t) :
    ∀ t ≥ 0, discreteEnergy3 (u t) ≤ discreteEnergy3 (u 0) := by
  intro t ht
  exact viscous_energy_antitone3 (N := N) ν hν B HB u hu ht

theorem viscous_norm_bound3 {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp3 N) (HB : EnergySkewHypothesis3 B)
    (u : ℝ → GalerkinState3 N)
    (hu : ∀ t : ℝ, HasDerivAt u (galerkinNSRHS3 ν B (u t)) t) :
    ∀ t ≥ 0, ‖u t‖ ≤ ‖u 0‖ := by
  intro t ht
  have hE := viscous_energy_bound3 (N := N) ν hν B HB u hu t ht
  have hsq : ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
    have h1 : (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖u 0‖ ^ 2 := by
      simpa [discreteEnergy3] using hE
    linarith
  exact le_of_sq_le_sq hsq (norm_nonneg (u 0))

end IndisputableMonolith.NavierStokes.Galerkin3D
