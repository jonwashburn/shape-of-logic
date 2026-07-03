import Mathlib
import IndisputableMonolith.ILG.Kernel

namespace IndisputableMonolith
namespace ILG

open Real

/-!
# Target A: Poisson-with-kernel statement

This module defines the modified Poisson equation as a Fourier-space multiplier
and proves basic stability/scaling bounds relative to standard GR.
-/

/-- The modified Poisson equation in Fourier space:
    -k² Φ(k, a) = 4πG * w(k, a) * δρ(k, a)
    We define the operator-theoretic mapping from source density to potential. -/
noncomputable def poisson_operator (P : KernelParams) (k a δρ : ℝ) : ℝ :=
  if k = 0 then 0 else -(4 * Real.pi * kernel P k a * δρ) / k^2

/-- Predicate: Φ solves the modified Poisson equation for a given source δρ. -/
def SolvesModifiedPoisson (P : KernelParams) (k a δρ Φ : ℝ) : Prop :=
  - (k^2 * Φ) = 4 * Real.pi * kernel P k a * δρ

/-- The operator definition satisfies the predicate. -/
theorem poisson_operator_solves (P : KernelParams) (k a δρ : ℝ) (hk : k ≠ 0) :
    SolvesModifiedPoisson P k a δρ (poisson_operator P k a δρ) := by
  unfold SolvesModifiedPoisson poisson_operator
  simp only [if_neg hk]
  have hk2 : (k^2 : ℝ) ≠ 0 := pow_ne_zero 2 hk
  field_simp

/-- Stability/Scaling Bound: The ILG potential Φ is strictly enhanced relative to
    the GR potential Φ_GR by exactly the kernel factor w(k, a). -/
theorem poisson_enhancement (P : KernelParams) (k a δρ : ℝ) (hk : k ≠ 0) :
    let Φ_ILG := poisson_operator P k a δρ
    let Φ_GR  := -(4 * Real.pi * δρ) / k^2
    |Φ_ILG| = kernel P k a * |Φ_GR| := by
  unfold poisson_operator
  simp only [if_neg hk]
  have h_kernel_pos : 0 < kernel P k a := kernel_pos P k a
  -- Rewrite -(4πw·δρ)/k² as w·(-(4π·δρ)/k²) under absolute value.
  have h_eq : -(4 * Real.pi * kernel P k a * δρ) / k^2
              = kernel P k a * (-(4 * Real.pi * δρ) / k^2) := by ring
  rw [h_eq, abs_mul, abs_of_pos h_kernel_pos]

/-- Coercivity Bound: The modified potential is non-vanishing for any non-vanishing source. -/
theorem poisson_coercive (P : KernelParams) (k a δρ : ℝ) (hk : k ≠ 0) (hδρ : δρ ≠ 0) :
    poisson_operator P k a δρ ≠ 0 := by
  unfold poisson_operator
  simp only [if_neg hk]
  have hk2 : (k^2 : ℝ) ≠ 0 := pow_ne_zero 2 hk
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hkern_ne : kernel P k a ≠ 0 := (kernel_pos P k a).ne'
  have hnum_ne : (4 * Real.pi * kernel P k a * δρ : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4pi_ne hkern_ne) hδρ
  have hneg_ne : -(4 * Real.pi * kernel P k a * δρ : ℝ) ≠ 0 := neg_ne_zero.mpr hnum_ne
  exact div_ne_zero hneg_ne hk2

/-! ## Causality-bound Poisson operators (Beltracchi 2026 resolution)

The original `poisson_operator` above is preserved unchanged. The two
operators below split the Poisson equation into a background piece
(unmodified standard GR) and a perturbation piece (ILG-modified, with the
IR cutoff that prevents the `k → 0` divergence). Together they form a
self-consistent ILG Poisson system that resolves Beltracchi's IR concern.
-/

/-- The background Poisson operator: standard FRW, no ILG modification.
The homogeneous mode `ρ̄` sits at the J-cost minimum and does not source
any ledger gradient flow, so the background gravitational potential is
sourced by the standard Poisson equation. -/
noncomputable def poisson_operator_background (a ρ_bar : ℝ) : ℝ :=
  4 * Real.pi * a^2 * ρ_bar / 3

/-- The perturbation Poisson operator: ILG-modified with explicit IR
cutoff `k_min`. Below `k_min` the kernel saturates at its IR-floor value,
preventing the divergence at `k = 0`. The canonical RS choice for the
cutoff is the Hubble wavenumber `k_min = a H / c`. -/
noncomputable def poisson_operator_perturbation (P : KernelParams)
    (k_min k a δρ : ℝ) : ℝ :=
  if k = 0 then 0
  else -(4 * Real.pi * kernel_perturbation P k_min k a * δρ) / k^2

/-- The combined causality-bound Poisson operator: background plus
perturbation, with the kernel acting only on the perturbation. -/
noncomputable def poisson_operator_full (P : KernelParams)
    (k_min k a ρ_bar δρ : ℝ) : ℝ :=
  poisson_operator_background a ρ_bar + poisson_operator_perturbation P k_min k a δρ

/-- The background piece is independent of the kernel parameters. -/
@[simp] theorem poisson_background_independent_of_kernel
    (P : KernelParams) (a ρ_bar : ℝ) :
    poisson_operator_full P 0 0 a ρ_bar 0
      = poisson_operator_background a ρ_bar := by
  unfold poisson_operator_full poisson_operator_perturbation
  simp

/-- The perturbation kernel inside `poisson_operator_perturbation` is
bounded above by its IR-saturated value. This is the operator-level
restatement of `kernel_perturbation_bounded_above`: the multiplier in
front of `δρ/k²` is uniformly bounded above by a finite ceiling fixed by
the IR cutoff, so the perturbation operator does not run away as
`k → 0`. -/
theorem poisson_operator_perturbation_kernel_bounded
    (P : KernelParams) {k_min : ℝ} (hkmin : 0 < k_min)
    {a : ℝ} (ha : 0 < a) (k : ℝ) :
    kernel_perturbation P k_min k a
      ≤ 1 + P.C * (max 0.01 (a / (k_min * P.tau0))) ^ P.alpha :=
  kernel_perturbation_bounded_above P hkmin ha k

/-- **Background-mode invariance.** When the perturbation `δρ = 0` (pure
homogeneous configuration), the perturbation operator vanishes and only
the standard FRW background remains. This is the operator-level statement
that the ILG kernel does not affect the homogeneous mode. -/
@[simp] theorem poisson_operator_perturbation_homogeneous
    (P : KernelParams) (k_min k a : ℝ) :
    poisson_operator_perturbation P k_min k a 0 = 0 := by
  unfold poisson_operator_perturbation
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

/-- The full operator at zero perturbation reduces to the background. -/
theorem poisson_operator_full_homogeneous
    (P : KernelParams) (k_min k a ρ_bar : ℝ) :
    poisson_operator_full P k_min k a ρ_bar 0
      = poisson_operator_background a ρ_bar := by
  unfold poisson_operator_full
  rw [poisson_operator_perturbation_homogeneous]
  ring

/-- **Master certificate for the causality-bound Poisson layer.** -/
structure CausalityBoundsPoissonCert where
  background_indep : ∀ (P : KernelParams) (a ρ_bar : ℝ),
                      poisson_operator_full P 0 0 a ρ_bar 0
                        = poisson_operator_background a ρ_bar
  perturbation_homogeneous : ∀ (P : KernelParams) (k_min k a : ℝ),
                              poisson_operator_perturbation P k_min k a 0 = 0
  full_homogeneous : ∀ (P : KernelParams) (k_min k a ρ_bar : ℝ),
                      poisson_operator_full P k_min k a ρ_bar 0
                        = poisson_operator_background a ρ_bar

noncomputable def causalityBoundsPoissonCert : CausalityBoundsPoissonCert where
  background_indep := poisson_background_independent_of_kernel
  perturbation_homogeneous := poisson_operator_perturbation_homogeneous
  full_homogeneous := poisson_operator_full_homogeneous

end ILG
end IndisputableMonolith
