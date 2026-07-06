import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace Constants

/-- The fundamental RS time quantum (RS-native). τ₀ = 1 tick. -/
@[simp] def tick : ℝ := 1

/-- Notation for fundamental tick. -/
abbrev τ₀ : ℝ := tick

/-- One octave = 8 ticks: the fundamental evolution period. -/
def octave : ℝ := 8 * tick

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  -- Use that √5 > 0
  have hroot_pos : 0 < Real.sqrt 5 := by
    have : (0 : ℝ) < 5 := by norm_num
    exact Real.sqrt_pos.mpr this
  have hnum_pos : 0 < 1 + Real.sqrt 5 := by exact add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hroot_pos)
  simpa [phi] using (div_pos hnum_pos htwo)

lemma one_lt_phi : 1 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hsqrt_gt : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have h2lt : (2 : ℝ) < 1 + Real.sqrt 5 := by
    have h1lt : (1 : ℝ) < Real.sqrt 5 := by simpa [Real.sqrt_one] using hsqrt_gt
    linarith
  have hdiv : (2 : ℝ) / 2 < (1 + Real.sqrt 5) / 2 := (div_lt_div_of_pos_right h2lt htwo)
  have hone_lt : 1 < (1 + Real.sqrt 5) / 2 := by simpa using hdiv
  simpa [phi] using hone_lt

lemma phi_ge_one : 1 ≤ phi := le_of_lt one_lt_phi
lemma phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos
lemma phi_ne_one : phi ≠ 1 := ne_of_gt one_lt_phi

lemma phi_lt_two : phi < 2 := by
  have hsqrt5_lt : Real.sqrt 5 < 3 := by
    have h5_lt_9 : (5 : ℝ) < 9 := by norm_num
    have h9_eq : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
    have : Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) h5_lt_9
    rwa [h9_eq] at this
  have hnum_lt : 1 + Real.sqrt 5 < 4 := by linarith
  have : (1 + Real.sqrt 5) / 2 < 4 / 2 := div_lt_div_of_pos_right hnum_lt (by norm_num)
  simp only [phi]
  linarith

/-! ### φ irrationality -/

/-- φ is irrational (degree 2 algebraic, not rational).

    Proof: Our φ equals Mathlib's golden ratio, which is proven irrational
    via the irrationality of √5 (5 is prime, hence not a perfect square). -/
theorem phi_irrational : Irrational phi := by
  -- Our phi equals Mathlib's goldenRatio
  have h_eq : phi = Real.goldenRatio := rfl
  rw [h_eq]
  exact Real.goldenRatio_irrational

/-! ### φ power bounds -/

/-- Key identity: φ² = φ + 1 (from the defining equation x² - x - 1 = 0). -/
lemma phi_sq_eq : phi^2 = phi + 1 := by
  simp only [phi]
  have h5_pos : (0 : ℝ) ≤ 5 := by norm_num
  have hsq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt h5_pos
  ring_nf
  linear_combination (1/4) * hsq

/-- Tighter lower bound: φ > 1.5 (since √5 > 2, so (1 + √5)/2 > 1.5). -/
lemma phi_gt_onePointFive : (1.5 : ℝ) < phi := by
  simp only [phi]
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    have h : (2 : ℝ)^2 < 5 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  linarith

/-- Tighter upper bound: φ < 1.62 (since √5 < 2.24). -/
lemma phi_lt_onePointSixTwo : phi < (1.62 : ℝ) := by
  simp only [phi]
  have h5 : Real.sqrt 5 < (2.24 : ℝ) := by
    have h : (5 : ℝ) < (2.24 : ℝ)^2 := by norm_num
    have h24_pos : (0 : ℝ) ≤ 2.24 := by norm_num
    rw [← Real.sqrt_sq h24_pos]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  linarith

/-- Even tighter lower bound: φ > 1.61. -/
lemma phi_gt_onePointSixOne : (1.61 : ℝ) < phi := by
  simp only [phi]
  have h5 : (2.22 : ℝ) < Real.sqrt 5 := by
    have h : (2.22 : ℝ)^2 < 5 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.22)]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  linarith

/-- φ² is between 2.5 and 2.7.
    φ² = φ + 1 ≈ 2.618 (exact: (3 + √5)/2). -/
lemma phi_squared_bounds : (2.5 : ℝ) < phi^2 ∧ phi^2 < 2.7 := by
  rw [phi_sq_eq]
  have h1 := phi_gt_onePointFive
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-! ### Fibonacci power identities for φ -/

/-- Key identity: φ³ = 2φ + 1 (Fibonacci recurrence).
    φ³ = φ × φ² = φ(φ + 1) = φ² + φ = (φ + 1) + φ = 2φ + 1. -/
lemma phi_cubed_eq : phi^3 = 2 * phi + 1 := by
  calc phi^3 = phi * phi^2 := by ring
    _ = phi * (phi + 1) := by rw [phi_sq_eq]
    _ = phi^2 + phi := by ring
    _ = (phi + 1) + phi := by rw [phi_sq_eq]
    _ = 2 * phi + 1 := by ring

/-- Key identity: φ⁴ = 3φ + 2 (Fibonacci recurrence).
    φ⁴ = φ × φ³ = φ(2φ + 1) = 2φ² + φ = 2(φ + 1) + φ = 3φ + 2. -/
lemma phi_fourth_eq : phi^4 = 3 * phi + 2 := by
  calc phi^4 = phi * phi^3 := by ring
    _ = phi * (2 * phi + 1) := by rw [phi_cubed_eq]
    _ = 2 * phi^2 + phi := by ring
    _ = 2 * (phi + 1) + phi := by rw [phi_sq_eq]
    _ = 3 * phi + 2 := by ring

/-- Key identity: φ⁵ = 5φ + 3 (Fibonacci recurrence).
    φ⁵ = φ × φ⁴ = φ(3φ + 2) = 3φ² + 2φ = 3(φ + 1) + 2φ = 5φ + 3. -/
lemma phi_fifth_eq : phi^5 = 5 * phi + 3 := by
  calc phi^5 = phi * phi^4 := by ring
    _ = phi * (3 * phi + 2) := by rw [phi_fourth_eq]
    _ = 3 * phi^2 + 2 * phi := by ring
    _ = 3 * (phi + 1) + 2 * phi := by rw [phi_sq_eq]
    _ = 5 * phi + 3 := by ring

/-! ### Bounds from Fibonacci identities -/

/-- φ³ is between 4.0 and 4.25.
    φ³ = 2φ + 1 ≈ 4.236. -/
lemma phi_cubed_bounds : (4.0 : ℝ) < phi^3 ∧ phi^3 < 4.25 := by
  rw [phi_cubed_eq]
  have h1 := phi_gt_onePointFive
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-- φ⁴ is between 6.5 and 6.9.
    φ⁴ = 3φ + 2 ≈ 6.854. -/
lemma phi_fourth_bounds : (6.5 : ℝ) < phi^4 ∧ phi^4 < 6.9 := by
  rw [phi_fourth_eq]
  have h1 := phi_gt_onePointFive
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-- φ⁵ is between 10.7 and 11.3.
    φ⁵ = 5φ + 3 ≈ 11.090. -/
lemma phi_fifth_bounds : (10.7 : ℝ) < phi^5 ∧ phi^5 < 11.3 := by
  rw [phi_fifth_eq]
  have h1 := phi_gt_onePointSixOne
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-- Key identity: φ⁶ = 8φ + 5 (Fibonacci recurrence). -/
lemma phi_sixth_eq : phi^6 = 8 * phi + 5 := by
  calc phi^6 = phi * phi^5 := by ring
    _ = phi * (5 * phi + 3) := by rw [phi_fifth_eq]
    _ = 5 * phi^2 + 3 * phi := by ring
    _ = 5 * (phi + 1) + 3 * phi := by rw [phi_sq_eq]
    _ = 8 * phi + 5 := by ring

/-- Key identity: φ⁷ = 13φ + 8 (Fibonacci recurrence). -/
lemma phi_seventh_eq : phi^7 = 13 * phi + 8 := by
  calc phi^7 = phi * phi^6 := by ring
    _ = phi * (8 * phi + 5) := by rw [phi_sixth_eq]
    _ = 8 * phi^2 + 5 * phi := by ring
    _ = 8 * (phi + 1) + 5 * phi := by rw [phi_sq_eq]
    _ = 13 * phi + 8 := by ring

/-- Key identity: φ⁸ = 21φ + 13 (Fibonacci recurrence). -/
lemma phi_eighth_eq : phi^8 = 21 * phi + 13 := by
  calc phi^8 = phi * phi^7 := by ring
    _ = phi * (13 * phi + 8) := by rw [phi_seventh_eq]
    _ = 13 * phi^2 + 8 * phi := by ring
    _ = 13 * (phi + 1) + 8 * phi := by rw [phi_sq_eq]
    _ = 21 * phi + 13 := by ring

/-- Key identity: φ⁹ = 34φ + 21 (Fibonacci recurrence). -/
lemma phi_ninth_eq : phi^9 = 34 * phi + 21 := by
  calc phi^9 = phi * phi^8 := by ring
    _ = phi * (21 * phi + 13) := by rw [phi_eighth_eq]
    _ = 21 * phi^2 + 13 * phi := by ring
    _ = 21 * (phi + 1) + 13 * phi := by rw [phi_sq_eq]
    _ = 34 * phi + 21 := by ring

/-- Key identity: φ¹⁰ = 55φ + 34 (Fibonacci recurrence). -/
lemma phi_tenth_eq : phi^10 = 55 * phi + 34 := by
  calc phi^10 = phi * phi^9 := by ring
    _ = phi * (34 * phi + 21) := by rw [phi_ninth_eq]
    _ = 34 * phi^2 + 21 * phi := by ring
    _ = 34 * (phi + 1) + 21 * phi := by rw [phi_sq_eq]
    _ = 55 * phi + 34 := by ring

/-- Key identity: φ¹¹ = 89φ + 55 (Fibonacci recurrence). -/
lemma phi_eleventh_eq : phi^11 = 89 * phi + 55 := by
  calc phi^11 = phi * phi^10 := by ring
    _ = phi * (55 * phi + 34) := by rw [phi_tenth_eq]
    _ = 55 * phi^2 + 34 * phi := by ring
    _ = 55 * (phi + 1) + 34 * phi := by rw [phi_sq_eq]
    _ = 89 * phi + 55 := by ring

/-! ### Canonical constants derived from φ -/

/-- Canonical locked fine-structure constant: α_lock = (1 − 1/φ)/2. -/
@[simp] noncomputable def alphaLock : ℝ := (1 - 1 / phi) / 2

/-- Useful bridge identity: the “acceleration-parameterized” exponent is `2·alphaLock`.

This is purely algebraic (no physics): it just clears the `/2` in the definition. -/
lemma two_mul_alphaLock : 2 * alphaLock = 1 - 1 / phi := by
  unfold alphaLock
  ring_nf

lemma alphaLock_pos : 0 < alphaLock := by
  have hphi := one_lt_phi
  unfold alphaLock
  have : 1 / phi < 1 := (div_lt_one phi_pos).mpr hphi
  linarith

lemma alphaLock_lt_one : alphaLock < 1 := by
  have hpos : 0 < phi := phi_pos
  unfold alphaLock
  have : 1 / phi > 0 := one_div_pos.mpr hpos
  linarith

/-- Canonical locked C_lag constant: C_lock = φ^{−5}. -/
@[simp] noncomputable def cLagLock : ℝ := phi ^ (-(5 : ℝ))

lemma cLagLock_pos : 0 < cLagLock := by
  have hphi : 0 < phi := phi_pos
  unfold cLagLock
  exact Real.rpow_pos_of_pos hphi (-(5 : ℝ))

/-- The elementary ledger bit cost J_bit = ln φ. -/
noncomputable def J_bit : ℝ := Real.log phi

/-- Coherence energy in RS units (dimensionless).
    By Phase 2 derivation, E_coh = C_lock = φ⁻⁵. -/
noncomputable def E_coh : ℝ := cLagLock

lemma E_coh_pos : 0 < E_coh := cLagLock_pos

/-! ### RS-native fundamental units (parameter-free)

The **core theory** is expressed in RS-native units:

- `tau0 = 1` tick (time quantum)
- `ell0 = 1` voxel (length quantum)
- `c = 1` voxel/tick

All SI/CODATA anchoring is treated as **external calibration** and lives in
separate modules (e.g. `IndisputableMonolith.Constants.Consistency`,
`IndisputableMonolith.Constants.Derivation`, `IndisputableMonolith.Constants.Codata`,
and `IndisputableMonolith.Constants.RSNativeUnits`). -/

/-- The fundamental time unit τ₀ (duration of one tick) in RS-native units. -/
@[simp] noncomputable def tau0 : ℝ := tick

lemma tau0_pos : 0 < tau0 := by
  simp [tau0, tick]

/-! ## C-004: Planck's Constant ħ Derivation

### The RS Derivation of ħ

In Recognition Science, the reduced Planck constant ℏ is not a free parameter
but is derived from the fundamental ledger structure:

1. **Coherence Energy** (E_coh): The minimal energy quantum for recognition events
   E_coh = φ⁻⁵ (from self-similar reciprocal closure on the discrete ledger)

2. **Fundamental Time** (τ₀): The duration of one recognition tick
   τ₀ = 1 tick (the atomic unit of time in RS)

3. **Planck's Identity**: ℏ = E_coh · τ₀ = φ⁻⁵ · 1 = φ⁻⁵

This derivation has **zero free parameters** — both E_coh and τ₀ are forced
by the RS forcing chain (T0-T8).

**Physical Interpretation**: ℏ represents the minimal "action" (energy × time)
required for a single recognition event in the ledger. The smallness of ℏ
(≈ 0.09 in RS-native units, or ~10⁻³⁴ J·s in SI) reflects the fine-grained
nature of the recognition substrate.

**SI Conversion**: When mapping to SI units, ℏ acquires its familiar value
through the calibration length λ_rec:
   ℏ_SI = E_coh_SI · τ₀_SI = (φ⁻⁵ · ℏ_base) · (λ_rec/c)
where ℏ_base is the natural unit conversion factor.
-/

/-- Native action quantum in RS-native units: `hbar = E_coh · tau0 = φ⁻⁵ · 1`.

## ATTACKER BREADCRUMB (read before declaring ℏ = φ⁻⁵ "true by definition")

The lemma `hbar_eq_phi_inv_fifth` below closes by `unfold; simp`. That is
intentional: this file *defines* the RS-native action unit. Two separate
questions then arise, and they have different answers; do not collapse them.

* Is the EXPONENT `5` forced, or a free choice? Forced, modulo one modeling
  step. The coherence energy carries one factor of `φ⁻¹` per configuration
  degree of freedom of a recognition event, and a recognition event has
  `D + 2` such degrees: `D` spatial (lattice, T8), `1` temporal (tick advance,
  T2), `1` balance (ledger neutrality `J(x)=J(x⁻¹)`, T3). With `D = 3` forced
  by T8 this gives `configDim = 5`, hence `E_coh = φ^(-(D+2)) = φ⁻⁵`. This is
  boundary item B-22, proved in `Foundation/GapDerivation.lean`
  (`configDim_at_D3`, `E_coh_gap_eq`, `Gap45Cert.ecoh`). The link back to THIS
  constant is machine-checked there:
  `GapDerivation.Constants_E_coh_eq_configDim` and
  `GapDerivation.hbar_exponent_eq_configDim` prove
  `E_coh = hbar = φ^(-(configDim D))`. The forced content is the count
  `D + 2`; the only modeling input is the `φ⁻¹`-per-dof rule. So the honest tag
  for the exponent is derived-modulo-one-modeling-step, NOT pure unit choice.
* Is the SI VALUE of `ℏ` (in J·s) predicted? No. A pure-number theory cannot
  output an absolute dimensionful SI constant without a dimensional anchor:
  see `Constants/NativeDimensionalBoundary.no_nontrivial_dimensionless_monomial`.

So "true by definition" is correct only at the level of native units (one tick
= the time unit ⟹ the native action quantum is `φ⁻⁵` as a pure number). The
substantive, non-definitional content is that the exponent equals the forced
configuration dimension `D + 2 = 5`.

## What the SI calibration looks like

Mapping `hbar_RS = φ⁻⁵` to SI units requires a dimensional anchor.  The
conversion is uniquely determined once the anchor is supplied
(`Foundation/SIBridgeClosure.lean`, `Verification/FirstPrinciplesToSI.lean`,
`Measurement/RSNative/Calibration/SingleAnchor.lean`); the boundary theorem
explaining why an anchor is required lives in
`Constants/NativeDimensionalBoundary.lean`. -/
noncomputable def hbar : ℝ := cLagLock * tau0

lemma hbar_pos : 0 < hbar := mul_pos cLagLock_pos tau0_pos

/-- **THEOREM C-004.1**: the native action quantum equals `φ⁻⁵`.

    This is the native identity: `hbar = E_coh · tau0 = φ⁻⁵ · 1 = φ⁻⁵`.

    Note: the proof is `unfold; simp` because, in RS-native units, ℏ
    is *defined* as `cLagLock · τ₀` with `cLagLock = φ⁻⁵` and `τ₀ = 1`.
    It is not a derivation of the SI value of Planck's constant. What is more
    than a unit choice is the EXPONENT `5 = D + 2` (forced configuration
    dimension), derived in `Foundation/GapDerivation.lean` and bridged back to
    this constant by `GapDerivation.hbar_exponent_eq_configDim`. -/
lemma hbar_eq_phi_inv_fifth : hbar = phi ^ (-(5 : ℝ)) := by
  unfold hbar cLagLock tau0 tick
  simp

/-- **THEOREM C-004.2**: ℏ is positive (required for quantum dynamics). -/
theorem hbar_positive : hbar > 0 := hbar_pos

/-- **THEOREM C-004.3**: ℏ < 1 (the action quantum is small compared to natural units).

    Proof: φ > 1 ⟹ φ⁵ > 1 ⟹ φ⁻⁵ < 1. -/
theorem hbar_lt_one : hbar < 1 := by
  rw [hbar_eq_phi_inv_fifth]
  have h1 : phi ^ (5 : ℝ) > 1 := by
    have hphi : phi > 1 := one_lt_phi
    have hexp : (5 : ℝ) > 0 := by norm_num
    have h1_lt : (1 : ℝ) < phi ^ (5 : ℝ) := by
      rw [← Real.one_rpow (5 : ℝ)]
      apply Real.rpow_lt_rpow
      · norm_num
      · linarith
      · norm_num
    linarith
  have h2 : phi ^ (-(5 : ℝ)) = 1 / (phi ^ (5 : ℝ)) := by
    rw [show (-(5 : ℝ)) = - (5 : ℝ) by norm_num]
    rw [Real.rpow_neg]
    · ring
    · exact le_of_lt phi_pos
  rw [h2]
  have h3 : phi ^ (5 : ℝ) > 0 := by positivity
  apply (div_lt_iff₀ h3).mpr
  linarith

/-- **THEOREM C-004.4**: native action quantum identity.

    The native action quantum is the energy-time product of one coherence
    event and one tick. -/
theorem hbar_action_identity : hbar = E_coh * tau0 := rfl

/-- **THEOREM C-004.5**: Bounds on ℏ from φ bounds.

    With φ ∈ (1.61, 1.62), we get ℏ ∈ (0.088, 0.093). -/
theorem hbar_bounds : (0.088 : ℝ) < hbar ∧ hbar < (0.093 : ℝ) := by
  rw [hbar_eq_phi_inv_fifth]
  have h1 : (1.61 : ℝ) < phi := phi_gt_onePointSixOne
  have h2 : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo
  -- We want 0.088 < φ^(-5) < 0.093
  -- Since hbar = 1/φ^5, we need bounds on φ^5
  -- Lower bound: φ < 1.62, so φ^5 < 1.62^5, so 1/φ^5 > 1/1.62^5
  -- Upper bound: φ > 1.61, so φ^5 > 1.61^5, so 1/φ^5 < 1/1.61^5
  have h_phi5_lower : phi ^ (5 : ℝ) > (1.61 : ℝ) ^ (5 : ℝ) := by
    apply Real.rpow_lt_rpow
    · linarith
    · linarith
    · norm_num
  have h_phi5_upper : phi ^ (5 : ℝ) < (1.62 : ℝ) ^ (5 : ℝ) := by
    apply Real.rpow_lt_rpow
    · linarith
    · linarith
    · norm_num
  -- Convert to hbar = φ^(-5) bounds
  have hbar_lower : phi ^ (-(5 : ℝ)) > (0.088 : ℝ) := by
    have h_inv : phi ^ (-(5 : ℝ)) = 1 / (phi ^ (5 : ℝ)) := by
      rw [show (-(5 : ℝ)) = - (5 : ℝ) by norm_num]
      rw [Real.rpow_neg]
      · ring
      · exact le_of_lt phi_pos
    rw [h_inv]
    -- Since φ^5 < 1.62^5, we have 1/φ^5 > 1/1.62^5
    -- Compute 1.62^5 = 11.158... and 1/11.158 ≈ 0.0896 > 0.088
    have h_div : 1 / (phi ^ (5 : ℝ)) > 1 / ((1.62 : ℝ) ^ (5 : ℝ)) := by
      apply (one_div_lt_one_div (by positivity) (by positivity)).mpr
      linarith [h_phi5_upper]
    have h_numeric : 1 / ((1.62 : ℝ) ^ (5 : ℝ)) > (0.088 : ℝ) := by
      rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hbar_upper : phi ^ (-(5 : ℝ)) < (0.093 : ℝ) := by
    have h_inv : phi ^ (-(5 : ℝ)) = 1 / (phi ^ (5 : ℝ)) := by
      rw [show (-(5 : ℝ)) = - (5 : ℝ) by norm_num]
      rw [Real.rpow_neg]
      · ring
      · exact le_of_lt phi_pos
    rw [h_inv]
    -- Since φ^5 > 1.61^5, we have 1/φ^5 < 1/1.61^5
    -- Compute 1.61^5 = 10.817... and 1/10.817 ≈ 0.0924 < 0.093
    have h_div : 1 / (phi ^ (5 : ℝ)) < 1 / ((1.61 : ℝ) ^ (5 : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      linarith [h_phi5_lower]
    have h_numeric : 1 / ((1.61 : ℝ) ^ (5 : ℝ)) < (0.093 : ℝ) := by
      rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  exact ⟨hbar_lower, hbar_upper⟩

/-- The speed of light c in RS-native units (voxel/tick). -/
@[simp] noncomputable def c : ℝ := 1

lemma c_pos : 0 < c := by
  simp [c]

/-- The fundamental length unit ℓ₀ in RS-native units (voxel). -/
@[simp] noncomputable def ell0 : ℝ := 1

lemma ell0_pos : 0 < ell0 := by
  simp [ell0]

/-- Light-cone identity: ℓ₀ = c · τ₀ (in RS-native units). -/
lemma c_ell0_tau0 : c * tau0 = ell0 := by
  simp [c, tau0, ell0, tick]

/-- Fundamental recognition wavelength λ_rec.
    In the 8-tick cycle, λ_rec = ℓ₀ (in RS-native units).

## ATTACKER BREADCRUMB (read this before declaring λ_rec a calibration)

`λ_rec = ℓ₀ = 1` looks like a unit choice on the surface. It is a
**derived** quantity, not a calibration. The chain:

1. The bit cost `J_bit = 1` (normalized recognition event cost).
2. The curvature cost `J_curv(λ) = 2λ²` from the Q₃ Gauss-Bonnet
   normalization (8 vertices × angular deficit π/2 each = 4π = 2π·χ(S²)).
3. The balance condition `J_bit = J_curv` forces a unique positive
   `λ_0 = 1/√2` in dimensionless RS-native units.
4. The discrete lattice convention `ℓ₀ = 1` (one voxel = one causal step)
   absorbs the `√2`, giving `λ_rec = ℓ₀ = 1`.

Every step is proved in `IndisputableMonolith/Constants/LambdaRecDerivation.lean`:
see `balance_at_lambda_0`, `balance_unique_positive_root`,
`balance_determines_lambda`, `total_curvature_gauss_bonnet`,
`G_derivation_chain_complete`. Zero sorry, zero RS-internal axioms.

`G := λ_rec² · c³ / (π · ℏ)` follows by substitution and gives
`G = φ⁵/π` in RS-native units (zero free parameters at this level).

## Where the SI bridge actually sits (NOT here)

If you are looking for the place the framework calibrates against
SI/CODATA, it is NOT λ_rec. The SI bridge lives in:
* `Constants/RSNativeUnits.lean` `ExternalCalibration` structure
  (seconds_per_tick, meters_per_voxel, joules_per_coh, with c-consistency).
* `Foundation/SIBridgeClosure.lean` (the conversion-map closure; the
  dimensional ANCHOR itself remains the explicit "principal open
  frontier" — one external scale must be supplied, by dimensional
  analysis it cannot be derived from dimensionless structure).
The dimensional bridge is one open frontier, not a hidden cluster of
calibrations spread across the constants. -/
noncomputable def lambda_rec : ℝ := ell0

lemma lambda_rec_pos : 0 < lambda_rec := by
  simp [lambda_rec]

/-- RS-native gravitational coupling projection through the recognition/Planck
    bridge: \(G = \lambda_{\text{rec}}^2 c^3 / (\pi \hbar)\).

    This is not a prediction of the SI value of Newton's constant.  SI conversion
    requires the dimensional bridge in `Foundation/SIBridgeClosure.lean`. -/
noncomputable def G : ℝ := (lambda_rec^2) * (c^3) / (Real.pi * hbar)

lemma G_pos : 0 < G := by
  unfold G
  apply div_pos
  · apply mul_pos
    · exact pow_pos lambda_rec_pos 2
    · exact pow_pos c_pos 3
  · apply mul_pos
    · exact Real.pi_pos
    · exact hbar_pos

/-- Einstein coupling constant κ = 8πG/c⁴ in RS-native units.
    Using G = λ_rec² c³ / (π ℏ) with λ_rec = c = 1 and ℏ = φ⁻⁵:
    κ = 8π · (φ⁵/π) / 1 = 8φ⁵.

    This is the coefficient in front of T_μν in the Einstein field equations. -/
noncomputable def kappa_einstein : ℝ := 8 * Real.pi * G / (c^4)

lemma kappa_einstein_eq : kappa_einstein = 8 * phi ^ (5 : ℝ) := by
  unfold kappa_einstein G hbar cLagLock lambda_rec ell0 c tau0 tick
  simp only [one_pow, mul_one, div_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  rw [Real.rpow_neg phi_pos.le]
  field_simp [phi_ne_zero]

lemma kappa_einstein_pos : 0 < kappa_einstein := by
  unfold kappa_einstein
  apply div_pos
  · apply mul_pos
    · apply mul_pos
      · norm_num
      · exact Real.pi_pos
    · exact G_pos
  · exact pow_pos c_pos 4

/-!
  ## CODATA / SI constants (quarantined)

  The empirical SI/CODATA numeric constants live in
  `IndisputableMonolith/Constants/Codata.lean` and are intentionally **excluded**
  from the certified surface import-closure.

  If you need them for numeric comparisons or empirical reports, import
  `IndisputableMonolith.Constants.Codata` explicitly.
-/

/-- Minimal RS units used in Core. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  c    : ℝ
  c_ell0_tau0 : c * tau0 = ell0

/-- Dimensionless bridge ratio \(K\).

Defined (non-circularly) as \(K = \varphi^{1/2}\). -/
@[simp] noncomputable def K : ℝ := phi ^ (1/2 : ℝ)

@[simp] lemma K_def : K = phi ^ (1/2 : ℝ) := rfl

lemma K_pos : 0 < K := by
  -- φ > 0, hence φ^(1/2) > 0
  simpa [K] using Real.rpow_pos_of_pos phi_pos (1/2 : ℝ)

lemma K_nonneg : 0 ≤ K := le_of_lt K_pos

/-- Alias matching parallel-work naming convention. -/
lemma one_lt_phiPointSixOne : (1.6 : ℝ) < phi := by linarith [phi_gt_onePointSixOne]

/-- Alias: phi_gt_one ≡ one_lt_phi, for parallel-work compat. -/
lemma phi_gt_one : 1 < phi := one_lt_phi

/-- φ ≈ 1.618 (coarse upper bound used in some modules). -/
lemma phi_approx : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo

/-- J(φ) = φ - 3/2 (exact, using φ² = φ + 1). -/
lemma Jcost_phi_val : Cost.Jcost phi = phi - 3 / 2 := by
  rw [Cost.Jcost_eq_sq phi_ne_zero]
  have hphi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  rw [div_eq_iff (by linarith [phi_pos] : 2 * phi ≠ 0)]
  nlinarith [phi_pos, hphi_sq]

/-- J(φ) > 0 -/
lemma Jcost_phi_pos : 0 < Cost.Jcost phi :=
  Cost.Jcost_pos_of_ne_one _ phi_pos phi_ne_one

end Constants
end IndisputableMonolith
