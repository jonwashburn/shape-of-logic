import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Galerkin2D (Milestone M1)

This file introduces a **finite-dimensional** (Fourier-mode truncated) model for 2D incompressible
Navier–Stokes on the torus.  The goal of M1 is *not* the continuum limit yet — it is to get a
concrete discrete state space and the basic algebraic energy identity for the inviscid case.

Design choices (Lean-friendly):
- We represent the truncated Fourier modes as a `Finset` and then use the coercion
  `((modes N : Finset Mode) : Type*)` as the finite index type of coefficients.
- The nonlinear term is modeled as an abstract bilinear operator `B` together with the single
  algebraic property needed for inviscid energy conservation: `⟪B u u, u⟫ = 0`.

This keeps the file executable/compilable while making the analytic content explicit for later
work (Milestones M2+).
-/

namespace IndisputableMonolith.ClassicalBridge.Fluids

open Real
open scoped InnerProductSpace

/-!
## Truncated Fourier modes on 𝕋²
-/

/-- A 2D Fourier mode (k₁, k₂). -/
abbrev Mode2 : Type := ℤ × ℤ

/-- Truncation predicate: max(|k₁|,|k₂|) ≤ N. -/
def modeTrunc (N : ℕ) (k : Mode2) : Prop :=
  max k.1.natAbs k.2.natAbs ≤ N

/-- The finite set of truncated modes. -/
noncomputable def modes (N : ℕ) : Finset Mode2 :=
  ((Finset.Icc (-((N : ℤ))) (N : ℤ)).product (Finset.Icc (-((N : ℤ))) (N : ℤ)))

lemma mem_modes_iff {N : ℕ} {k : Mode2} :
    k ∈ modes N ↔ k.1 ∈ Finset.Icc (-((N : ℤ))) (N : ℤ) ∧ k.2 ∈ Finset.Icc (-((N : ℤ))) (N : ℤ) := by
  simp [modes, and_left_comm, and_assoc, and_comm]

/-!
## Galerkin state space
-/

-- We use Euclidean (L²) norms/inner products for energy identities, so we model coefficients
-- in `EuclideanSpace`, not plain Pi types (which carry the sup norm).

/-- Velocity Fourier coefficient at a mode: a Euclidean real 2-vector (û₁, û₂). -/
abbrev VelCoeff : Type := EuclideanSpace ℝ (Fin 2)

/-- The Galerkin state: velocity coefficients for each truncated mode and each component. -/
abbrev GalerkinState (N : ℕ) : Type :=
  EuclideanSpace ℝ ((modes N) × Fin 2)

/-!
## Discrete dynamics
-/

/-- Squared wave number \( |k|^2 \) as a real number. -/
noncomputable def kSq (k : Mode2) : ℝ :=
  (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2

/-- Fourier Laplacian on coefficients: (Δ û)(k) = -|k|² û(k). -/
noncomputable def laplacianCoeff {N : ℕ} (u : GalerkinState N) : GalerkinState N :=
  WithLp.toLp 2 (fun kc => (-kSq ((kc.1 : Mode2))) * u kc)

/-- Abstract Galerkin convection operator (projected nonlinearity).

Later we will replace this with the explicit Fourier convolution + Leray projection. -/
def ConvectionOp (N : ℕ) : Type :=
  GalerkinState N → GalerkinState N → GalerkinState N

/-- Discrete Navier–Stokes RHS: u' = νΔu - B(u,u). -/
noncomputable def galerkinNSRHS {N : ℕ} (ν : ℝ) (B : ConvectionOp N) (u : GalerkinState N) :
    GalerkinState N :=
  (ν • laplacianCoeff u) - (B u u)

/-!
## Energy functional and inviscid conservation
-/

/-- Discrete kinetic energy: \(E(u)=\frac12 \|u\|^2\). -/
noncomputable def discreteEnergy {N : ℕ} (u : GalerkinState N) : ℝ :=
  (1 / 2 : ℝ) * ‖u‖ ^ 2

/-- Algebraic hypothesis capturing the skew-symmetry of the Galerkin nonlinearity in L²:
\( \langle B(u,u), u \rangle = 0 \). -/
structure EnergySkewHypothesis {N : ℕ} (B : ConvectionOp N) : Prop where
  skew : ∀ u : GalerkinState N, ⟪B u u, u⟫_ℝ = 0

/-- Energy conservation for the inviscid Galerkin system (ν = 0), stated at a point.

If `u` solves `u' = -B(u,u)` and the nonlinearity is energy-skew, then the derivative of the
discrete energy is zero.
-/
theorem inviscid_energy_deriv_zero {N : ℕ} (B : ConvectionOp N) (HB : EnergySkewHypothesis B)
    (u : ℝ → GalerkinState N) {t : ℝ}
    (hu : HasDerivAt u (-(B (u t) (u t))) t) :
    HasDerivAt (fun s => discreteEnergy (u s)) 0 t := by
  -- Use the chain rule for `‖u‖^2` in an inner product space.
  -- d/dt (1/2 * ‖u‖^2) = ⟪u', u⟫.
  have h_normsq :
      HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * ⟪u t, -(B (u t) (u t))⟫_ℝ) t := by
    -- `HasDerivAt.norm_sq` gives: derivative of `‖u‖^2` is `2 * ⟪u, u'⟫`.
    simpa using (HasDerivAt.norm_sq hu)
  have h_energy : HasDerivAt (fun s => discreteEnergy (u s))
      ((1 / 2 : ℝ) * (2 * ⟪u t, -(B (u t) (u t))⟫_ℝ)) t := by
    -- Multiply the norm-square derivative by 1/2
    simpa [discreteEnergy, mul_assoc] using h_normsq.const_mul (1 / 2 : ℝ)
  -- Now simplify using skew-symmetry: ⟪-B(u,u), u⟫ = -⟪B(u,u),u⟫ = 0
  have h_inner_zero : ⟪u t, -(B (u t) (u t))⟫_ℝ = 0 := by
    calc
      ⟪u t, -(B (u t) (u t))⟫_ℝ = -⟪u t, B (u t) (u t)⟫_ℝ := by simp
      _ = -⟪B (u t) (u t), u t⟫_ℝ := by simp [real_inner_comm]
      _ = 0 := by simp [HB.skew (u t)]
  -- Conclude derivative is zero.
  simpa [h_inner_zero] using h_energy

/-!
## Viscous energy dissipation (discrete Laplacian)

For the 2D Galerkin system, the (Fourier) Laplacian is diagonal and dissipative:
`⟪u, Δu⟫ ≤ 0`.  This is the algebraic input behind uniform energy bounds.
-/

lemma laplacianCoeff_inner_self_nonpos {N : ℕ} (u : GalerkinState N) :
    ⟪u, laplacianCoeff u⟫_ℝ ≤ 0 := by
  classical
  -- Expand the inner product as a finite sum over coordinates.
  -- For each coordinate `kc`, the contribution is `u kc * ((-kSq kc.1) * u kc)`,
  -- which is nonpositive since `kSq ≥ 0` and `u kc * u kc ≥ 0`.
  have hsum :
      ⟪u, laplacianCoeff u⟫_ℝ =
        ∑ kc : (modes N) × Fin 2, u kc * ((-kSq (kc.1 : Mode2)) * u kc) := by
    -- `PiLp.inner_apply` expands the inner product; `laplacianCoeff` is defined via `WithLp.toLp`.
    -- The evaluation lemma `PiLp.toLp_apply` is `rfl`, so `simp` reduces the application.
    simp [laplacianCoeff, PiLp.inner_apply, kSq, mul_comm, mul_left_comm]
  -- Reduce to a sum of nonpositive terms.
  rw [hsum]
  refine Finset.sum_nonpos ?_
  intro kc _hkc
  have hkSq : 0 ≤ kSq (kc.1 : Mode2) := by
    -- kSq = k₁² + k₂²
    simp [kSq, add_nonneg, sq_nonneg]
  have hkneg : (-kSq (kc.1 : Mode2)) ≤ 0 := by linarith
  have hmul : 0 ≤ u kc * u kc := mul_self_nonneg (u kc)
  calc
    u kc * ((-kSq (kc.1 : Mode2)) * u kc)
        = (-kSq (kc.1 : Mode2)) * (u kc * u kc) := by ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hkneg hmul

theorem viscous_energy_deriv_le_zero {N : ℕ} (ν : ℝ) (_hν : 0 ≤ ν)
    (B : ConvectionOp N) (HB : EnergySkewHypothesis B)
    (u : ℝ → GalerkinState N) {t : ℝ}
    (hu : HasDerivAt u (galerkinNSRHS ν B (u t)) t) :
    HasDerivAt (fun s => discreteEnergy (u s)) (ν * ⟪u t, laplacianCoeff (u t)⟫_ℝ) t := by
  -- Differentiate `E(u)=1/2‖u‖^2` using `HasDerivAt.norm_sq`, then expand the RHS.
  have h_normsq :
      HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * ⟪u t, galerkinNSRHS ν B (u t)⟫_ℝ) t := by
    simpa using (HasDerivAt.norm_sq hu)
  have h_energy :
      HasDerivAt (fun s => discreteEnergy (u s)) ((1 / 2 : ℝ) * (2 * ⟪u t, galerkinNSRHS ν B (u t)⟫_ℝ)) t := by
    simpa [discreteEnergy, mul_assoc] using h_normsq.const_mul (1 / 2 : ℝ)
  -- Now simplify the inner product with `galerkinNSRHS`.
  -- `⟪u, νΔu - B(u,u)⟫ = ν⟪u,Δu⟫ - ⟪u,B(u,u)⟫` and skew gives the second term is 0.
  have h_skew' : ⟪u t, B (u t) (u t)⟫_ℝ = 0 := by
    -- Convert `⟪B u u, u⟫ = 0` to `⟪u, B u u⟫ = 0` using symmetry.
    have : ⟪B (u t) (u t), u t⟫_ℝ = 0 := HB.skew (u t)
    simpa [real_inner_comm] using this
  have h_inner :
      ⟪u t, galerkinNSRHS ν B (u t)⟫_ℝ = ν * ⟪u t, laplacianCoeff (u t)⟫_ℝ := by
    simp [galerkinNSRHS, inner_sub_right, inner_smul_right, h_skew']
  -- Finish by rewriting.
  simpa [h_inner, mul_assoc, mul_left_comm, mul_comm] using h_energy

theorem viscous_energy_deriv_nonpos {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp N) (HB : EnergySkewHypothesis B)
    (u : ℝ → GalerkinState N) {t : ℝ}
    (hu : HasDerivAt u (galerkinNSRHS ν B (u t)) t) :
    HasDerivAt (fun s => discreteEnergy (u s)) (ν * ⟪u t, laplacianCoeff (u t)⟫_ℝ) t ∧
      ν * ⟪u t, laplacianCoeff (u t)⟫_ℝ ≤ 0 := by
  refine ⟨viscous_energy_deriv_le_zero (N := N) ν hν B HB u hu, ?_⟩
  have hL : ⟪u t, laplacianCoeff (u t)⟫_ℝ ≤ 0 := laplacianCoeff_inner_self_nonpos (u := u t)
  exact mul_nonpos_of_nonneg_of_nonpos hν hL

theorem viscous_energy_antitone {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp N) (HB : EnergySkewHypothesis B)
    (u : ℝ → GalerkinState N)
    (hu : ∀ t : ℝ, HasDerivAt u (galerkinNSRHS ν B (u t)) t) :
    Antitone (fun t => discreteEnergy (u t)) := by
  -- Use the calculus lemma `antitone_of_hasDerivAt_nonpos`.
  refine antitone_of_hasDerivAt_nonpos (f := fun t => discreteEnergy (u t))
      (f' := fun t => ν * ⟪u t, laplacianCoeff (u t)⟫_ℝ) ?_ ?_
  · intro t
    exact viscous_energy_deriv_le_zero (N := N) ν hν B HB u (hu t)
  · intro t
    have hL : ⟪u t, laplacianCoeff (u t)⟫_ℝ ≤ 0 :=
      laplacianCoeff_inner_self_nonpos (u := u t)
    exact mul_nonpos_of_nonneg_of_nonpos hν hL

theorem viscous_energy_bound_from_initial {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp N) (HB : EnergySkewHypothesis B)
    (u : ℝ → GalerkinState N)
    (hu : ∀ t : ℝ, HasDerivAt u (galerkinNSRHS ν B (u t)) t) :
    ∀ t ≥ 0, discreteEnergy (u t) ≤ discreteEnergy (u 0) := by
  intro t ht
  have hAnti : Antitone (fun s => discreteEnergy (u s)) :=
    viscous_energy_antitone (N := N) ν hν B HB u hu
  -- Antitone: s₁ ≤ s₂ → f s₂ ≤ f s₁
  have : discreteEnergy (u t) ≤ discreteEnergy (u 0) := hAnti ht
  simpa using this

theorem viscous_norm_bound_from_initial {N : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (B : ConvectionOp N) (HB : EnergySkewHypothesis B)
    (u : ℝ → GalerkinState N)
    (hu : ∀ t : ℝ, HasDerivAt u (galerkinNSRHS ν B (u t)) t) :
    ∀ t ≥ 0, ‖u t‖ ≤ ‖u 0‖ := by
  intro t ht
  have hE : discreteEnergy (u t) ≤ discreteEnergy (u 0) :=
    viscous_energy_bound_from_initial (N := N) ν hν B HB u hu t ht
  have hE' : (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖u 0‖ ^ 2 := by
    simpa [discreteEnergy] using hE
  -- Multiply both sides by `2` to cancel the `1/2`.
  have hsq : ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hE' (by norm_num : (0 : ℝ) ≤ 2)
    -- `2 * (1/2) = 1`
    simpa [mul_assoc] using hmul
  -- Convert the square inequality to a norm inequality (norms are nonnegative).
  exact le_of_sq_le_sq hsq (norm_nonneg (u 0))

end IndisputableMonolith.ClassicalBridge.Fluids
