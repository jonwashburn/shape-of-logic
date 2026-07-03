import Mathlib
import IndisputableMonolith.Constants

/-!
# BIT Kernel Families for w(z) Forecasting

Three kernel-family models for the BIT cosmic-Z-aging amplitude
`δw(z) = δw_0 · K(z)`:

  K1: K(z) = 1                 (constant)
  K2: K(z) = 1 / (1 + z)       (canonical RS arc-11 kernel)
  K3: K(z) = exp(-z / z_0)     (exponential)

Each kernel is bounded in `[0, 1]` on `z ≥ 0`, and the maximum
amplitude `δw_0 ∈ [0, J(φ)]` from the BIT theorem (§XXIV).

Used by `scripts/analysis/desi_y3_wz_forecast.py` for the DESI Y3
forecast.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace BITKernelFamilies

open IndisputableMonolith.Constants

noncomputable section

/-- Kernel family tag. -/
inductive KernelFamily where
  | constant_kernel
  | inv_one_plus_z
  | exponential
  deriving DecidableEq, Inhabited

namespace KernelFamily

def name : KernelFamily → String
  | constant_kernel  => "K1 (constant)"
  | inv_one_plus_z   => "K2 (1/(1+z))"
  | exponential      => "K3 (exp(-z/z0))"

end KernelFamily

/-- The BIT kernel function. -/
def kernel (k : KernelFamily) (z : ℝ) (z0 : ℝ := 1) : ℝ :=
  match k with
  | KernelFamily.constant_kernel  => 1
  | KernelFamily.inv_one_plus_z   => 1 / (1 + z)
  | KernelFamily.exponential      => Real.exp (- z / z0)

/-- All three kernels equal 1 at `z = 0`. -/
theorem kernel_at_zero (k : KernelFamily) (z0 : ℝ) :
    kernel k 0 z0 = 1 := by
  cases k <;> simp [kernel]

/-- The constant kernel is `1` everywhere. -/
theorem constant_kernel_eq_one (z z0 : ℝ) :
    kernel KernelFamily.constant_kernel z z0 = 1 := rfl

/-- The 1/(1+z) kernel is positive for `z > -1`. -/
theorem inv_one_plus_z_pos (z : ℝ) (h : -1 < z) (z0 : ℝ) :
    0 < kernel KernelFamily.inv_one_plus_z z z0 := by
  unfold kernel
  exact div_pos one_pos (by linarith)

/-- The exponential kernel is positive everywhere. -/
theorem exp_kernel_pos (z z0 : ℝ) :
    0 < kernel KernelFamily.exponential z z0 := by
  unfold kernel
  exact Real.exp_pos _

/-- The maximum BIT amplitude is `J(φ) = φ - 3/2 ≈ 0.118`. -/
def delta_w0_max : ℝ := phi - 3 / 2

theorem delta_w0_max_pos : 0 < delta_w0_max := by
  unfold delta_w0_max
  have := phi_gt_onePointFive
  linarith

theorem delta_w0_max_lt_one : delta_w0_max < 1 := by
  unfold delta_w0_max
  have := phi_lt_two
  linarith

/-- The effective equation of state under BIT. -/
def w_eff (k : KernelFamily) (z delta_w0 : ℝ) (z0 : ℝ := 1) : ℝ :=
  -1 + delta_w0 * kernel k z z0

/-- At `z = 0`, `w_eff = -1 + δw_0` for any kernel. -/
theorem w_eff_at_zero (k : KernelFamily) (delta_w0 z0 : ℝ) :
    w_eff k 0 delta_w0 z0 = -1 + delta_w0 := by
  unfold w_eff
  rw [kernel_at_zero]
  ring

/-! ## Master certificate -/

/-- **BIT KERNEL FAMILIES MASTER CERTIFICATE.** -/
structure BITKernelFamiliesCert where
  kernel_at_zero_one :
    ∀ k : KernelFamily, ∀ z0 : ℝ, kernel k 0 z0 = 1
  delta_w0_max_pos :
    0 < delta_w0_max
  delta_w0_max_lt_one :
    delta_w0_max < 1
  w_eff_at_zero :
    ∀ k : KernelFamily, ∀ (delta_w0 z0 : ℝ),
      w_eff k 0 delta_w0 z0 = -1 + delta_w0

/-- The master certificate is inhabited. -/
def bitKernelFamiliesCert : BITKernelFamiliesCert where
  kernel_at_zero_one := kernel_at_zero
  delta_w0_max_pos := delta_w0_max_pos
  delta_w0_max_lt_one := delta_w0_max_lt_one
  w_eff_at_zero := w_eff_at_zero

end

end BITKernelFamilies
end Cosmology
end IndisputableMonolith
