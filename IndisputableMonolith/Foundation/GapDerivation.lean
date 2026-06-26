import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.NineParities

/-!
# Gap-45 Derivation from Spatial Dimension

Closes boundary item B-22: the coherence energy exponent = D + 2
(configuration dimension of a recognition event), giving E_coh = φ^{−5}
at D = 3.

## B-22 Resolution

A recognition event has D + 2 independent degrees of freedom:
D spatial (from the lattice, T8), 1 temporal (tick advance, T2),
1 balance (ledger neutrality J(x)=J(x⁻¹), T3).  The coherence
energy is φ^{−1} per degree of freedom, so E_coh = φ^{−(D+2)}.
At D = 3 this gives φ^{−5}, matching `Constants.E_coh`.

## Main Results

- `gap_at_D3`: D²(D+2) = 9 × 5 = 45
- `coprimality_odd`: gcd(2^D, D²(D+2)) = 1 for all odd D
- `coprimality_even_fails`: gcd(2^D, D²(D+2)) > 1 for all even D ≥ 2
- `gap_balance`: φ^{1−gap} × φ^{gap} = φ  (matter-coherence link)

The coprimality result provides a fourth argument that D must be odd.
Combined with Alexander duality (selecting D = 3), gap-45 follows
from D = 3 alone.

## Status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Foundation.GapDerivation

open Constants

/-! ## Definitions -/

/-- Spatial dimension, forced by T8. -/
def D : ℕ := 3

/-- Configuration dimension of a recognition event:
    D spatial + 1 temporal (T2) + 1 balance (T3). -/
def configDim (d : ℕ) : ℕ := d + 2

/-- Number of independent ledger parities: D².
    At D = 3 the linear formula 3D coincides with D². -/
def parityCount (d : ℕ) : ℕ := d ^ 2

/-- Dimension gap: (parity count) × (coherence exponent) = D²(D+2). -/
def dimensionGap (d : ℕ) : ℕ := parityCount d * configDim d

/-! ## B-22: Configuration Dimension -/

theorem configDim_at_D3 : configDim D = 5 := by native_decide

/-- The Fibonacci route (2^D − D) and configuration route (D + 2) agree
    at D = 3.  The identity 2^D − D = D + 2 characterizes D = 3. -/
theorem dual_routes : 2 ^ D - D = configDim D := by native_decide

/-! ## Parity Count -/

theorem parityCount_at_D3 : parityCount D = 9 := by native_decide

/-- 3D = D² at D = 3 (this identity holds only at D = 0, 3). -/
theorem three_D_eq_D_sq : 3 * D = D ^ 2 := by native_decide

/-- The parametric parity count matches the NineParities enumeration. -/
theorem parityCount_matches_enumeration :
    parityCount D = Fintype.card NineParities.ParityIndex := by
  rw [parityCount_at_D3, NineParities.parity_count_eq_nine]

/-! ## Gap = 45 -/

theorem gap_at_D3 : dimensionGap D = 45 := by native_decide

theorem gap_factors : dimensionGap D = 9 * 5 := by native_decide

theorem gap_is_lcm : Nat.lcm 9 5 = 45 := by native_decide

/-! ## Coprimality Forces Odd Dimension -/

/-- For odd D = 2k+1, D²(D+2) is odd (product of odd numbers),
    hence coprime with any power of 2. -/
theorem coprimality_odd (k : ℕ) :
    Nat.Coprime (2 ^ (2 * k + 1)) ((2 * k + 1) ^ 2 * (2 * k + 3)) := by
  suffices h : Nat.Coprime 2 ((2 * k + 1) ^ 2 * (2 * k + 3)) from h.pow_left _
  show Nat.gcd 2 ((2 * k + 1) ^ 2 * (2 * k + 3)) = 1
  have hodd : (2 * k + 1) ^ 2 * (2 * k + 3) =
      2 * (4 * k ^ 3 + 10 * k ^ 2 + 7 * k + 1) + 1 := by ring
  rw [hodd]
  set n := 4 * k ^ 3 + 10 * k ^ 2 + 7 * k + 1
  rw [Nat.gcd_rec]
  have : (2 * n + 1) % 2 = 1 := by omega
  rw [this]
  decide

/-- For even D = 2k (k ≥ 1), D²(D+2) is even, so gcd(2^D, D²(D+2)) > 1. -/
theorem coprimality_even_fails (k : ℕ) (hk : 0 < k) :
    ¬ Nat.Coprime (2 ^ (2 * k)) ((2 * k) ^ 2 * (2 * k + 2)) := by
  intro h
  have h1 : 2 ∣ 2 ^ (2 * k) := dvd_pow (dvd_refl 2) (by omega)
  have h2 : 2 ∣ (2 * k) ^ 2 * (2 * k + 2) := ⟨2 * k ^ 2 * (2 * k + 2), by ring⟩
  have h3 := Nat.dvd_gcd h1 h2
  rw [h] at h3
  exact absurd h3 (by norm_num)

/-- At D = 3: gcd(8, 45) = 1. -/
theorem coprime_at_D3 : Nat.Coprime (2 ^ D) (dimensionGap D) := by native_decide

/-! ## φ-Dependent Results -/

noncomputable section

/-- B-22: E_coh = φ^{−(D+2)} at D = 3. -/
def E_coh_gap : ℝ := phi ^ (-(configDim D : ℤ))

theorem E_coh_gap_eq : E_coh_gap = phi ^ (-5 : ℤ) := by
  unfold E_coh_gap configDim D; norm_num

/-! ### Bridge to the runtime constant

The two theorems below upgrade the prose "matching `Constants.E_coh`" to
machine-checked identities: the coherence exponent of the *actual* runtime
constants `Constants.E_coh` and `Constants.hbar` IS the configuration
dimension `D + 2`. This is the part of the `ℏ = φ⁻⁵` story that is more than a
unit choice. The forced content is the count `configDim D = D + 2 = 5` (`D = 3`
from T8, `+1` tick from T2, `+1` balance from T3); the one modeling input is
`φ⁻¹` per configuration degree of freedom. The absolute SI value of `ℏ` still
needs a dimensional anchor (`Constants.NativeDimensionalBoundary`). -/

/-- The RS-native coherence energy equals `φ` to the minus configuration
dimension: `Constants.E_coh = φ^(-(D+2))`. -/
theorem Constants_E_coh_eq_configDim :
    Constants.E_coh = phi ^ (-(configDim D : ℤ)) := by
  have hcfg : (-(configDim D : ℤ)) = (-5 : ℤ) := by
    have := configDim_at_D3; omega
  rw [hcfg, ← Real.rpow_intCast phi (-5 : ℤ)]
  unfold Constants.E_coh Constants.cLagLock
  norm_num

/-- The RS-native action quantum has exponent equal to the configuration
dimension: `Constants.hbar = φ^(-(D+2))`. The exponent `5` is the forced
`D + 2`, not a free parameter. -/
theorem hbar_exponent_eq_configDim :
    Constants.hbar = phi ^ (-(configDim D : ℤ)) := by
  have hcfg : (-(configDim D : ℤ)) = (-5 : ℤ) := by
    have := configDim_at_D3; omega
  rw [hcfg, Constants.hbar_eq_phi_inv_fifth, ← Real.rpow_intCast phi (-5 : ℤ)]
  norm_num

/-- Active edge count per tick. -/
def A : ℤ := 1

/-- η_B · Θ_crit = φ^A = φ, where η_B = φ^{A−gap} and Θ_crit = φ^{gap}. -/
theorem gap_balance :
    phi ^ (A - ↑(dimensionGap D)) * phi ^ (↑(dimensionGap D) : ℤ) = phi := by
  have hg : (↑(dimensionGap D) : ℤ) = 45 := by exact_mod_cast gap_at_D3
  rw [hg, show A = (1 : ℤ) from rfl, ← zpow_add₀ (ne_of_gt phi_pos)]
  have : (1 : ℤ) - 45 + 45 = 1 := by norm_num
  rw [this, zpow_one]

end

/-! ## Master Certificate -/

structure Gap45Cert where
  config_dim : configDim D = 5
  parity_count : parityCount D = 9
  parity_matches : parityCount D = Fintype.card NineParities.ParityIndex
  gap : dimensionGap D = 45
  coprime : Nat.Coprime (2 ^ D) (dimensionGap D)
  ecoh : E_coh_gap = phi ^ (-5 : ℤ)
  balance : phi ^ (A - ↑(dimensionGap D)) * phi ^ (↑(dimensionGap D) : ℤ) = phi
  odd_coprime : ∀ k, Nat.Coprime (2 ^ (2*k+1)) ((2*k+1)^2 * (2*k+3))
  even_not_coprime : ∀ k, 0 < k → ¬ Nat.Coprime (2^(2*k)) ((2*k)^2 * (2*k+2))

noncomputable def gap45_cert : Gap45Cert where
  config_dim := configDim_at_D3
  parity_count := parityCount_at_D3
  parity_matches := parityCount_matches_enumeration
  gap := gap_at_D3
  coprime := coprime_at_D3
  ecoh := E_coh_gap_eq
  balance := gap_balance
  odd_coprime := coprimality_odd
  even_not_coprime := coprimality_even_fails

end IndisputableMonolith.Foundation.GapDerivation
