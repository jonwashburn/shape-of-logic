import Mathlib
import IndisputableMonolith.Constants

/-!
# Radial Acceleration Relation (RAR) Emergence from ILG

This module proves that the Radial Acceleration Relation (RAR) emerges
as a mathematical consequence of the ILG weight function.

## The RAR

The empirical RAR states that observed acceleration \(a_{\rm obs}\) correlates
tightly with baryonic acceleration \(a_{\rm baryon}\) across all galaxies:

  \(a_{\rm obs} = f(a_{\rm baryon})\)

with intrinsic scatter ≈ 0.1 dex.

## ILG Prediction

The ILG/causal-response model has:

  \(a_{\rm obs}(r) = w(r) \cdot a_{\rm baryon}(r)\)

where the weight function scales as:

  \(w(r) \propto (a_0 / a_{\rm baryon})^{\alpha/2}\)

The acceleration-space exponent is \(\alpha/2\) where \(\alpha\) is the
dynamical-time exponent. Under RS parameter locks, \(\alpha = \text{alphaLock} \approx 0.191\).

## Main Result

**Theorem (RAR Emergence):**
Given the ILG weight \(w = C \cdot (a_0/a)^{\alpha/2}\), the RAR takes the form:

  \(a_{\rm obs} = C \cdot a_0^{\alpha/2} \cdot a_{\rm baryon}^{1 - \alpha/2}\)

This is a power-law RAR with exponent \(1 - \alpha/2 \approx 0.8\) for \(\alpha = 0.389\).

-/

namespace IndisputableMonolith
namespace Gravity
namespace RAREmergence

open Real
open Constants

noncomputable section

/-! ## ILG Weight Function -/

/-- The ILG weight function (acceleration parameterization).
    \(w(a) = C \cdot (a_0/a)^{\alpha/2}\) for baryonic acceleration \(a\).

    Parameters:
    - \(a_0\): characteristic acceleration scale
    - \(\alpha\): dynamical-time exponent (RS: alphaLock ≈ 0.191)
    - The factor 1/2 comes from the acceleration↔time bridge -/
def w_accel (a₀ a α : ℝ) : ℝ := (a₀ / a) ^ (α / 2)

/-- The observed (effective) acceleration from ILG.
    \(a_{\rm obs} = w(a_{\rm baryon}) \cdot a_{\rm baryon}\) -/
def a_obs_ilg (a₀ a_baryon α : ℝ) : ℝ :=
  w_accel a₀ a_baryon α * a_baryon

/-! ## RAR Emergence Theorem -/

/-- **RAR Emergence Theorem (exact form):**
    The observed acceleration is a power-law function of baryonic acceleration:

    \(a_{\rm obs} = a_0^{\alpha/2} \cdot a_{\rm baryon}^{1 - \alpha/2}\)

    This is the RAR with exponent \(1 - \alpha/2\).
-/
theorem rar_power_law (a₀ a_baryon α : ℝ) (ha0 : 0 < a₀) (ha : 0 < a_baryon) :
    a_obs_ilg a₀ a_baryon α = a₀ ^ (α / 2) * a_baryon ^ (1 - α / 2) := by
  unfold a_obs_ilg w_accel
  -- (a₀/a)^(α/2) * a = a₀^(α/2) * a^(-α/2) * a = a₀^(α/2) * a^(1 - α/2)
  -- This is straightforward algebra using rpow identities
  have ha0' : 0 ≤ a₀ := le_of_lt ha0
  have ha' : 0 ≤ a_baryon := le_of_lt ha
  -- Split the ratio power: (a₀/a)^(α/2) = a₀^(α/2) / a^(α/2)
  rw [Real.div_rpow ha0' ha' (α / 2)]
  -- Convert a / a^(α/2) into a^(1-α/2)
  have hsub : a_baryon ^ (1 - α / 2) = a_baryon ^ (1 : ℝ) / a_baryon ^ (α / 2) := by
    simpa using (Real.rpow_sub ha (1 : ℝ) (α / 2))
  -- Finish by reassociation.
  calc
    (a₀ ^ (α / 2) / a_baryon ^ (α / 2)) * a_baryon
        = a₀ ^ (α / 2) * (a_baryon / a_baryon ^ (α / 2)) := by ring
    _ = a₀ ^ (α / 2) * (a_baryon ^ (1 : ℝ) / a_baryon ^ (α / 2)) := by
          simp [Real.rpow_one]
    _ = a₀ ^ (α / 2) * a_baryon ^ (1 - α / 2) := by
          -- rewrite the right factor using `hsub`
          simp [hsub]

/-- Same result as `rar_power_law`, but stated directly as an algebraic identity
    in the "weight times baryonic acceleration" form. -/
theorem rar_power_law_emergence
    (a₀ a_baryon α : ℝ) (ha0 : 0 < a₀) (ha : 0 < a_baryon) :
    (a₀ / a_baryon) ^ (α / 2) * a_baryon = a₀ ^ (α / 2) * a_baryon ^ (1 - α / 2) := by
  simpa [a_obs_ilg, w_accel] using (rar_power_law a₀ a_baryon α ha0 ha)

/-- Alias for the main RAR emergence statement, kept for stable downstream references. -/
theorem rar_emergence_direct
    (a₀ a_baryon α : ℝ) (ha0 : 0 < a₀) (ha : 0 < a_baryon) :
    a_obs_ilg a₀ a_baryon α = a₀ ^ (α / 2) * a_baryon ^ (1 - α / 2) :=
  rar_power_law a₀ a_baryon α ha0 ha

/-- **RAR slope (log-log):**
    In log-log space, the RAR has slope \(d(\log a_{\rm obs})/d(\log a_{\rm baryon}) = 1 - \alpha/2\).

    For \(\alpha = 0.389\): slope ≈ 0.8055
    For MOND-like (\(\alpha \to 1\)): slope → 0.5 (deep MOND)
-/
def rar_log_slope (α : ℝ) : ℝ := 1 - α / 2

/-- The RS-derived value of the RAR slope.
    Using \(\alpha_{\rm RS} = (1 - 1/\varphi)/2\) as the acceleration exponent:

    slope = 1 - α_RS/2 = 1 - (1 - 1/φ)/4
-/
def rar_slope_rs : ℝ := 1 - alphaLock / 2

theorem rar_slope_rs_value : rar_slope_rs = 1 - (1 - 1/phi) / 4 := by
  unfold rar_slope_rs alphaLock
  ring

/-- RAR slope for a specific α value (for numerical comparison).
    Example: α = 0.389 → slope = 1 - 0.389/2 ≈ 0.8055
-/
def rar_slope_at (α : ℝ) : ℝ := 1 - α / 2

/-! ## Universality of the RAR

The key feature of the RAR is its **universality**: the same function \(f\)
works for all galaxies despite their different masses, sizes, and morphologies.

In the ILG model, universality follows from:
1. The weight function \(w(a)\) depends only on the local acceleration ratio \(a_0/a\)
2. The parameters \((a_0, \alpha)\) are global constants shared by all galaxies
3. The morphology factor \(\xi(f_{\rm gas})\) provides only modest modulation

**Note**: The scatter in the RAR (≈ 0.1 dex empirically) arises from:
- Observational errors
- Variations in \(\xi\) with morphology
- Deviations from steady-state circular orbits
-/

/-- The RAR is universal (same function for all galaxies) when α and a₀ are global. -/
theorem rar_is_universal
    (a₀ α : ℝ) (ha0 : 0 < a₀)
    (galaxy1_a_baryon galaxy2_a_baryon : ℝ)
    (h1 : 0 < galaxy1_a_baryon) (h2 : 0 < galaxy2_a_baryon) :
    -- The ratio of observed accelerations equals the ratio of baryonic accelerations
    -- raised to the power (1 - α/2)
    a_obs_ilg a₀ galaxy1_a_baryon α / a_obs_ilg a₀ galaxy2_a_baryon α =
    (galaxy1_a_baryon / galaxy2_a_baryon) ^ (1 - α / 2) := by
  rw [rar_power_law a₀ galaxy1_a_baryon α ha0 h1]
  rw [rar_power_law a₀ galaxy2_a_baryon α ha0 h2]
  -- The a₀^(α/2) factors cancel, leaving (a1/a2)^(1-α/2)
  set p : ℝ := 1 - α / 2
  have ha0_ne : (a₀ ^ (α / 2)) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos ha0 (α / 2))
  have hcancel :
      (a₀ ^ (α / 2) * galaxy1_a_baryon ^ p) / (a₀ ^ (α / 2) * galaxy2_a_baryon ^ p)
        = (galaxy1_a_baryon ^ p) / (galaxy2_a_baryon ^ p) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_div_mul_left (galaxy1_a_baryon ^ p) (galaxy2_a_baryon ^ p) ha0_ne)
  rw [hcancel]
  have h1' : 0 ≤ galaxy1_a_baryon := le_of_lt h1
  have h2' : 0 ≤ galaxy2_a_baryon := le_of_lt h2
  have hdiv : (galaxy1_a_baryon / galaxy2_a_baryon) ^ p =
      galaxy1_a_baryon ^ p / galaxy2_a_baryon ^ p := by
    simpa [p] using (Real.div_rpow h1' h2' p)
  -- Rewrite the RHS using `hdiv`.
  simp [hdiv]

end

end RAREmergence
end Gravity
end IndisputableMonolith
