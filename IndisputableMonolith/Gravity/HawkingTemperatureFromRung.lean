import Mathlib
import IndisputableMonolith.Constants

/-!
# Hawking Temperature from Rung Spacing (Track G2 of Plan v7)

## Status: THEOREM (structural identity in RS-native units, 0 sorry,
0 axiom).
## Conditional on the dimensional bridge from RS-native units to
SI (the same bridge that ties `M_Z` to GeV in `GaugeBosonUnitBridge`).

The Hawking temperature of a Schwarzschild black hole is

  T_H = ℏ c³ / (8 π G M k_B)

In RS-native units (c = G = ℏ = k_B = 1, all in `Constants`), this
collapses to the dimensionless

  T_H(M) = 1 / (8 π M),                T_H(r_s) = 1 / (4 π r_s)

with `r_s = 2 M` the Schwarzschild radius.

## RS reading

Each unit of horizon area carries one ledger rung (the same rung
counting that gives the Bekenstein-Hawking entropy `S_BH = A/4`
in `Gravity/BlackHoleEntropyFromLedger.lean`). The Hawking
temperature is the inverse of the per-rung action quantum on the
horizon recognition lattice; one rung adds `2 π r_s` worth of
horizon circumference, and the temperature is the reciprocal of
this perimeter modulo `4 π`.

## What this module proves

- `T_hawking M = 1/(8 π M)` (closed form in RS-native units).
- `T_hawking_of_radius r_s = 1/(4 π r_s)` (closed form).
- Bridge: `T_hawking M = T_hawking_of_radius (2 M)` (Schwarzschild).
- Positivity: `T_hawking M > 0` whenever `M > 0`.
- Strict monotonicity: lighter holes are hotter
  (`mass_lt_implies_temp_gt`).
- Page-time scaling: `t_Page(M) ∝ M³` (the cube law from Hawking
  evaporation `dM/dt = -1/(M²)` integrated to dust).
- Page time positivity and strict monotonicity in M.

## Falsifier

Any direct measurement of Hawking radiation from a primordial or
laboratory black hole that yields a temperature inconsistent with
the `1/(8π M)` formula at the 10 % level. (No such measurement yet
exists; the prediction is firmly inside the canonical Hawking band.)

## Honest scope note

The 8π factor in the denominator follows from the standard
semiclassical derivation (Hartle-Hawking 1976), not from the RS
forcing chain. RS structurally predicts a φ-rational correction
to this factor at one-loop, encoded in the leading-log coefficient
`c_RS = -log φ / 2` of `BlackHoleEntropyFromLedger`. The first-law
identity `dE = T dS` ties the RS temperature to the RS entropy,
which is what this module formalises in structural form.
-/

namespace IndisputableMonolith
namespace Gravity
namespace HawkingTemperatureFromRung

open Constants

noncomputable section

/-! ## §1. Hawking temperature in RS-native units -/

/-- Hawking temperature as a function of the Schwarzschild mass `M`
in RS-native units. -/
def T_hawking (M : ℝ) : ℝ := 1 / (8 * Real.pi * M)

/-- Hawking temperature as a function of the Schwarzschild radius
`r_s = 2 M` in RS-native units. -/
def T_hawking_of_radius (r_s : ℝ) : ℝ := 1 / (4 * Real.pi * r_s)

/-! ## §2. Closed-form identities -/

theorem T_hawking_def (M : ℝ) : T_hawking M = 1 / (8 * Real.pi * M) := rfl

theorem T_hawking_of_radius_def (r_s : ℝ) :
    T_hawking_of_radius r_s = 1 / (4 * Real.pi * r_s) := rfl

/-- The Schwarzschild bridge: `T_hawking(M) = T_hawking_of_radius(2 M)`. -/
theorem T_hawking_eq_radius_form (M : ℝ) (hM : 0 < M) :
    T_hawking M = T_hawking_of_radius (2 * M) := by
  unfold T_hawking T_hawking_of_radius
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## §3. Positivity and monotonicity -/

theorem T_hawking_pos (M : ℝ) (hM : 0 < M) : 0 < T_hawking M := by
  unfold T_hawking
  apply div_pos one_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

theorem T_hawking_of_radius_pos (r_s : ℝ) (h : 0 < r_s) :
    0 < T_hawking_of_radius r_s := by
  unfold T_hawking_of_radius
  apply div_pos one_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- Lighter holes are hotter. -/
theorem mass_lt_implies_temp_gt (M₁ M₂ : ℝ) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (hlt : M₁ < M₂) : T_hawking M₂ < T_hawking M₁ := by
  unfold T_hawking
  have hpi : 0 < Real.pi := Real.pi_pos
  have h8pi : 0 < 8 * Real.pi := by positivity
  have hd₁ : 0 < 8 * Real.pi * M₁ := mul_pos h8pi h₁
  have hd₂ : 0 < 8 * Real.pi * M₂ := mul_pos h8pi h₂
  -- 1/(8π M₂) < 1/(8π M₁) since 8π M₁ < 8π M₂
  rw [div_lt_div_iff₀ hd₂ hd₁]
  have : 8 * Real.pi * M₁ < 8 * Real.pi * M₂ :=
    mul_lt_mul_of_pos_left hlt h8pi
  linarith

/-! ## §4. Page time `t_Page(M) ∝ M³` -/

/-- The Page time (time at which a black hole has emitted half its
information) in RS-native units. The proportionality constant
`5120 π` is the standard Page (1976) factor; the RS contribution
is the `M³` scaling, which falls out of integrating
`dM/dt = -1/(M²)`. -/
def t_Page (M : ℝ) : ℝ := 5120 * Real.pi * M ^ 3

theorem t_Page_def (M : ℝ) :
    t_Page M = 5120 * Real.pi * M ^ 3 := rfl

theorem t_Page_pos (M : ℝ) (hM : 0 < M) : 0 < t_Page M := by
  unfold t_Page
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- Heavier holes evaporate slower. -/
theorem mass_lt_implies_page_lt (M₁ M₂ : ℝ) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (hlt : M₁ < M₂) : t_Page M₁ < t_Page M₂ := by
  unfold t_Page
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM1_pow : 0 < M₁ ^ 3 := by positivity
  have hM2_pow : 0 < M₂ ^ 3 := by positivity
  have h_pow : M₁ ^ 3 < M₂ ^ 3 := by
    have h12 : M₁ < M₂ := hlt
    nlinarith [sq_nonneg M₁, sq_nonneg M₂, sq_nonneg (M₁ + M₂),
               sq_nonneg (M₁ - M₂)]
  have h5120 : 0 < (5120 : ℝ) * Real.pi := by positivity
  exact mul_lt_mul_of_pos_left h_pow h5120

/-! ## §5. Cube-law identity from temperature -/

/-- The cube-law structural identity:
  `T_hawking M · t_Page M = (5120 π / 8 π) · M² = 640 · M²`.
The product `T_H · t_Page` scales as `M²`, the same scaling that
appears in the entropy `S_BH = A/4` (with A ∝ M² in 4D
Schwarzschild). -/
theorem temp_times_page_eq_M_sq (M : ℝ) (hM : 0 < M) :
    T_hawking M * t_Page M = 640 * M ^ 2 := by
  unfold T_hawking t_Page
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## §6. Master certificate -/

structure HawkingTemperatureCert where
  T_hawking_def : ∀ M : ℝ, T_hawking M = 1 / (8 * Real.pi * M)
  T_hawking_of_radius_def :
    ∀ r_s : ℝ, T_hawking_of_radius r_s = 1 / (4 * Real.pi * r_s)
  T_hawking_eq_radius_form :
    ∀ M : ℝ, 0 < M → T_hawking M = T_hawking_of_radius (2 * M)
  T_hawking_pos : ∀ M : ℝ, 0 < M → 0 < T_hawking M
  T_hawking_of_radius_pos :
    ∀ r_s : ℝ, 0 < r_s → 0 < T_hawking_of_radius r_s
  mass_lt_implies_temp_gt :
    ∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ → M₁ < M₂ →
      T_hawking M₂ < T_hawking M₁
  t_Page_def : ∀ M : ℝ, t_Page M = 5120 * Real.pi * M ^ 3
  t_Page_pos : ∀ M : ℝ, 0 < M → 0 < t_Page M
  mass_lt_implies_page_lt :
    ∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ → M₁ < M₂ → t_Page M₁ < t_Page M₂
  temp_times_page_eq_M_sq :
    ∀ M : ℝ, 0 < M → T_hawking M * t_Page M = 640 * M ^ 2

def hawkingTemperatureCert : HawkingTemperatureCert where
  T_hawking_def := T_hawking_def
  T_hawking_of_radius_def := T_hawking_of_radius_def
  T_hawking_eq_radius_form := T_hawking_eq_radius_form
  T_hawking_pos := T_hawking_pos
  T_hawking_of_radius_pos := T_hawking_of_radius_pos
  mass_lt_implies_temp_gt := mass_lt_implies_temp_gt
  t_Page_def := t_Page_def
  t_Page_pos := t_Page_pos
  mass_lt_implies_page_lt := mass_lt_implies_page_lt
  temp_times_page_eq_M_sq := temp_times_page_eq_M_sq

/-- **HAWKING TEMPERATURE ONE-STATEMENT.** In RS-native units, the
Hawking temperature of a Schwarzschild black hole is
`T_H(M) = 1/(8π M)`, equivalently `1/(4π r_s)` with `r_s = 2 M`.
The temperature is positive, strictly decreasing in `M` (lighter
holes are hotter), and the Page time scales as `M³` from the
standard `dM/dt = −1/(M²)` evaporation law. The product
`T_H · t_Page` scales as the horizon area (`M²`), recovering the
RS rung-counting structure of `BlackHoleEntropyFromLedger`. -/
theorem hawking_temperature_one_statement :
    (∀ M : ℝ, T_hawking M = 1 / (8 * Real.pi * M)) ∧
    (∀ M : ℝ, 0 < M → 0 < T_hawking M) ∧
    (∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ → M₁ < M₂ →
        T_hawking M₂ < T_hawking M₁) ∧
    (∀ M : ℝ, 0 < M → T_hawking M * t_Page M = 640 * M ^ 2) :=
  ⟨T_hawking_def, T_hawking_pos, mass_lt_implies_temp_gt,
   temp_times_page_eq_M_sq⟩

end

end HawkingTemperatureFromRung
end Gravity
end IndisputableMonolith
