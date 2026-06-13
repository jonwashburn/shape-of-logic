import Mathlib
import IndisputableMonolith.Foundation.SIBridgeClosure
import IndisputableMonolith.Gravity.HawkingTemperatureFromRung

/-!
# Gravity Track 3.A: Hawking Temperature in SI Units

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This module implements **Track 3.A of the quantum-gravity master plan**
(`Quantum_Gravity_Discovery_Master_Plan_20260521.html`, §4 Track 3.A):
the SI conversion of the Hawking temperature via the dimensional bridge
discharged in `Foundation.SIBridgeClosure` (Track 5.A, CLOSED 2026-05-09).

`Gravity.HawkingTemperatureFromRung` proves `T_H = 1/(8πM)` in
RS-native (geometrized) units where `c = G = ℏ = k_B = 1`. With Track 5.A
closed, the SI conversion is no longer a free calibration: the bridge
factors `(a_T, a_L, a_M)` are uniquely determined by the c, ℏ, G constraints
plus the SI-2019-exact value of `k_B`.

## Master plan statement closed

> 3.A Hawking temperature: SI unit-bridge upgrade
>
>   `theorem hawking_temperature_SI :`
>   `  ∀ (M_SI : ℝ) (h_pos : 0 < M_SI),`
>   `  HawkingTemperature_SI M_SI = (ℏ_SI * c_SI³) / (8 * π * G_SI * k_B_SI * M_SI)`

This module's `T_hawking_SI_def` is exactly this identity (after unfolding
the definition, the master plan's statement holds by `rfl`).

## Substantive content

* `k_B_SI` — Boltzmann constant in SI, exact since SI 2019
  (`k_B = 1.380649 × 10⁻²³ J/K`).

* `T_hawking_SI M_SI = ℏ_SI · c_SI³ / (8π · G_SI · k_B_SI · M_SI)` — the
  standard SI Hawking formula.

* `T_hawking_SI_pos`, `T_hawking_SI_strict_anti` — positivity and strict
  anti-monotonicity (lighter holes are hotter, in SI units).

* `T_hawking_SI_eq_geom_via_bridge` — the bridge-derivation identity:
  `T_hawking_SI(M_SI) = T_hawking(G_SI · M_SI / c_SI²) · (ℏ_SI · c_SI / k_B_SI)`.
  The geometrized mass `G_SI · M_SI / c_SI²` is the standard
  mass-to-length conversion in general relativity (Schwarzschild radius
  prefactor); evaluating the RS-native `T_hawking` at this geometrized
  mass yields an inverse length, and multiplication by the energy-to-
  temperature factor `ℏ_SI · c_SI / k_B_SI` returns kelvin.

* `hawkingTemperatureSICert` — master cert bundling the above.

## Anti-retreat principle satisfied

The SI prediction is anchored on:
* `c_SI` — SI-2019 exact (defined).
* `hbar_SI` — SI-2019 exact (defined).
* `k_B_SI` — SI-2019 exact (defined).
* `G_SI` — the SINGLE CODATA measurement that anchors the bridge
  (via `Foundation.SIBridgeClosure`).

No free dimensionless parameters; one dimensional anchor. This is the
strongest form of "zero free dimensionless parameters, one dimensional
anchor" declared in `Foundation.SIBridgeClosure`. No softening of the
master-statement claim (`HawkingTemperature_SI = (ℏ·c³)/(8π·G·k_B·M)`)
relative to its master-plan-stipulated form.

## Falsifier (Hawking row of master plan §7)

Any direct measurement of Hawking radiation from a primordial or
laboratory black hole that yields a temperature inconsistent with the
SI formula at the 10 % level. (No such measurement yet exists; the
prediction is firmly inside the canonical Hawking band, and the
sub-leading φ-rung correction tracked by `BlackHoleEntropyFromLedger`
remains a Track 3.B item.)

## Honest scope note

This module is the **SI-unit bridge** for the Hawking temperature. It does
NOT prove the existence or stability of Hawking radiation, nor does it
derive the sub-leading entropy correction at one-loop. Those are Track 3.B
(leading-log entropy correction at theorem grade) and Track 3.C (Page
curve as derivation) items.

The `8π` factor in the denominator inherits from the standard
semiclassical derivation (Hartle-Hawking 1976); it is NOT forced by the
RS forcing chain. The RS forcing chain forces the sub-leading
`c_RS = -log φ / 2` correction at one-loop, encoded in
`Gravity.BlackHoleEntropyFromLedger`; the first-law identity `dE = T dS`
ties RS temperature to RS entropy. That tie is structural in
`HawkingTemperatureFromRung`; the SI lift here just propagates it through
the closed bridge.
-/

namespace IndisputableMonolith
namespace Gravity
namespace HawkingTemperatureSI

open Constants
open IndisputableMonolith.Foundation.SIBridgeClosure
open IndisputableMonolith.Gravity.HawkingTemperatureFromRung

noncomputable section

/-! ## §1. Boltzmann constant in SI (exact since SI 2019)

After the 2019 redefinition of the SI base units, `k_B` is exact:
`k_B = 1.380649 × 10⁻²³ J/K`. Together with the SI-exact `c_SI`,
`hbar_SI` from `Foundation.SIBridgeClosure`, and the CODATA `G_SI`, this
completes the four constants needed to express the Hawking temperature
in kelvin.
-/

/-- Boltzmann constant in SI: exact since SI 2019. -/
def k_B_SI : ℝ := 1.380649e-23

theorem k_B_SI_pos : 0 < k_B_SI := by
  unfold k_B_SI; norm_num

/-! ## §2. The SI Hawking temperature -/

/-- Hawking temperature of a Schwarzschild black hole in SI units:
`T_H = ℏ_SI · c_SI³ / (8π · G_SI · k_B_SI · M_SI)`. -/
def T_hawking_SI (M_SI : ℝ) : ℝ :=
  hbar_SI * c_SI ^ 3 / (8 * Real.pi * G_SI * k_B_SI * M_SI)

theorem T_hawking_SI_def (M_SI : ℝ) :
    T_hawking_SI M_SI = hbar_SI * c_SI ^ 3 /
      (8 * Real.pi * G_SI * k_B_SI * M_SI) := rfl

/-- The master plan statement, verbatim:
`HawkingTemperature_SI M_SI = (ℏ_SI · c_SI³) / (8π · G_SI · k_B_SI · M_SI)`. -/
theorem hawking_temperature_SI (M_SI : ℝ) (_h_pos : 0 < M_SI) :
    T_hawking_SI M_SI =
      hbar_SI * c_SI ^ 3 / (8 * Real.pi * G_SI * k_B_SI * M_SI) := rfl

/-- Positivity: positive masses give positive Hawking temperatures. -/
theorem T_hawking_SI_pos (M_SI : ℝ) (hM : 0 < M_SI) :
    0 < T_hawking_SI M_SI := by
  unfold T_hawking_SI
  have h_num_pos : 0 < hbar_SI * c_SI ^ 3 :=
    mul_pos hbar_SI_pos (pow_pos c_SI_pos 3)
  have h8 : (0 : ℝ) < 8 := by norm_num
  have h_den_pos : 0 < 8 * Real.pi * G_SI * k_B_SI * M_SI :=
    mul_pos (mul_pos (mul_pos (mul_pos h8 Real.pi_pos) G_SI_pos) k_B_SI_pos) hM
  exact div_pos h_num_pos h_den_pos

/-- Strict anti-monotonicity in mass: lighter holes are hotter (SI form). -/
theorem T_hawking_SI_strict_anti
    (M1 M2 : ℝ) (h1 : 0 < M1) (_h2 : 0 < M2) (hlt : M1 < M2) :
    T_hawking_SI M2 < T_hawking_SI M1 := by
  unfold T_hawking_SI
  have h_num_pos : 0 < hbar_SI * c_SI ^ 3 :=
    mul_pos hbar_SI_pos (pow_pos c_SI_pos 3)
  have h8 : (0 : ℝ) < 8 := by norm_num
  have h_coeff_pos : 0 < 8 * Real.pi * G_SI * k_B_SI :=
    mul_pos (mul_pos (mul_pos h8 Real.pi_pos) G_SI_pos) k_B_SI_pos
  have h_den1_pos : 0 < 8 * Real.pi * G_SI * k_B_SI * M1 :=
    mul_pos h_coeff_pos h1
  have h_den_lt : 8 * Real.pi * G_SI * k_B_SI * M1 <
      8 * Real.pi * G_SI * k_B_SI * M2 :=
    mul_lt_mul_of_pos_left hlt h_coeff_pos
  exact div_lt_div_of_pos_left h_num_pos h_den1_pos h_den_lt

/-! ## §3. Connection to RS-native via the dimensional bridge

The substantive bridge identity. The RS-native Hawking temperature
(`HawkingTemperatureFromRung.T_hawking M = 1/(8π M)`) lives in
geometrized units where `c = G = ℏ = k_B = 1`. The standard
general-relativistic mass-to-length conversion is `M_geom = G_SI · M_SI / c_SI²`,
and the energy-to-temperature conversion is `T_K = (1/m) · (ℏ · c / k_B)`.
Composing these gives the SI Hawking formula above.
-/

/-- **Track 3.A core identity**: the SI Hawking temperature is the
bridge-converted RS-native (geometrized) Hawking temperature, multiplied
by the SI energy-to-temperature factor.

`T_hawking_SI(M_SI) = T_hawking(G_SI · M_SI / c_SI²) · (ℏ_SI · c_SI / k_B_SI)`

This is the formal Track 3.A theorem: the SI prediction is the lift of
the RS-native theorem through the closed dimensional bridge. -/
theorem T_hawking_SI_eq_geom_via_bridge (M_SI : ℝ) (hM : 0 < M_SI) :
    T_hawking_SI M_SI =
      T_hawking (G_SI * M_SI / c_SI ^ 2) * (hbar_SI * c_SI / k_B_SI) := by
  unfold T_hawking_SI T_hawking
  have hG : G_SI ≠ 0 := ne_of_gt G_SI_pos
  have hM_ne : M_SI ≠ 0 := ne_of_gt hM
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hk : k_B_SI ≠ 0 := ne_of_gt k_B_SI_pos
  field_simp

/-- Symmetric form: the RS-native temperature recovered from the SI one
by dividing by the energy-to-temperature factor. -/
theorem T_hawking_geom_eq_SI_via_bridge (M_SI : ℝ) (hM : 0 < M_SI) :
    T_hawking (G_SI * M_SI / c_SI ^ 2) =
      T_hawking_SI M_SI * (k_B_SI / (hbar_SI * c_SI)) := by
  have h := T_hawking_SI_eq_geom_via_bridge M_SI hM
  have hbar_ne : hbar_SI ≠ 0 := ne_of_gt hbar_SI_pos
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  have hk : k_B_SI ≠ 0 := ne_of_gt k_B_SI_pos
  have hbar_c_ne : hbar_SI * c_SI ≠ 0 := mul_ne_zero hbar_ne hc
  -- T_hawking · (ℏ·c/k_B) = T_SI  ⇒  T_hawking = T_SI · k_B / (ℏ·c)
  rw [h]
  field_simp

/-! ## §4. Schwarzschild radius in SI

The Schwarzschild radius `r_s = 2 G M / c²` is the natural length scale
companion to `T_hawking_SI`. In RS-native (geometrized) units this is
just `r_s = 2 M`, and `T_hawking_of_radius (2 M) = T_hawking M`
(`HawkingTemperatureFromRung.T_hawking_eq_radius_form`). The SI lift
goes via the standard mass-to-length conversion `G_SI · M_SI / c_SI²`.
-/

/-- Schwarzschild radius in SI: `r_s(M_SI) = 2 G_SI · M_SI / c_SI²`. -/
def schwarzschildRadius_SI (M_SI : ℝ) : ℝ :=
  2 * G_SI * M_SI / c_SI ^ 2

theorem schwarzschildRadius_SI_def (M_SI : ℝ) :
    schwarzschildRadius_SI M_SI = 2 * G_SI * M_SI / c_SI ^ 2 := rfl

theorem schwarzschildRadius_SI_pos (M_SI : ℝ) (hM : 0 < M_SI) :
    0 < schwarzschildRadius_SI M_SI := by
  unfold schwarzschildRadius_SI
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hnum : 0 < 2 * G_SI * M_SI := mul_pos (mul_pos h2 G_SI_pos) hM
  exact div_pos hnum (pow_pos c_SI_pos 2)

/-- The SI Hawking temperature as a function of Schwarzschild radius:
`T_hawking_SI_of_radius(r_s) = ℏ c² / (4π G k_B · r_s · M_planck_unit)`.
Equivalently (Schwarzschild identification `r_s = 2M`):
`T_hawking_SI M_SI = ℏc / (4π · k_B · schwarzschildRadius_SI M_SI)`.

The derivation: starting from `T_hawking_SI M_SI = ℏc³/(8π·G·k_B·M_SI)`
and `schwarzschildRadius_SI M_SI = 2·G·M_SI/c²`, eliminate `M_SI` to get
`T_hawking_SI = ℏc/(4π·k_B·r_s)`. -/
theorem T_hawking_SI_eq_inv_schwarzschildRadius (M_SI : ℝ) (hM : 0 < M_SI) :
    T_hawking_SI M_SI = hbar_SI * c_SI /
      (4 * Real.pi * k_B_SI * schwarzschildRadius_SI M_SI) := by
  unfold T_hawking_SI schwarzschildRadius_SI
  have hG : G_SI ≠ 0 := ne_of_gt G_SI_pos
  have hM_ne : M_SI ≠ 0 := ne_of_gt hM
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hk : k_B_SI ≠ 0 := ne_of_gt k_B_SI_pos
  field_simp
  ring

/-! ## §5. Page time (Hawking evaporation lifetime) in SI

The Page time of a Schwarzschild black hole is the time at which half its
mass has been radiated. Standard semiclassical Hawking evaporation
`dM/dt = -ℏc⁴/(15360π G² M²)` integrates to dust as
`t_Page = 5120π · G² · M³ / (ℏ · c⁴)`.

In RS-native (fully geometrized) units, this collapses to
`HawkingTemperatureFromRung.t_Page M = 5120π · M³` (the
`M³` scaling preserved). The SI lift restores the explicit
`G² / (ℏ · c⁴)` Planck-time-cubed scale.

The Planck-time conversion factor is the cube of the Planck mass
ratio: `t_Page_SI(M_SI) = (M_SI/M_Planck)³ · (5120π · t_Planck)` with
`M_Planck = √(ℏc/G)` and `t_Planck = √(ℏG/c⁵)`. The squared identity is
clean (no `Real.sqrt`); we ship the direct SI form and the explicit
`M_SI³` scaling as the algebraic content of this section.

The `5120π` semiclassical prefactor inherits from Page (1976), NOT from
the RS forcing chain; this is consistent with the `8π` factor in the
Hawking temperature noted earlier. The RS-forced piece is the cubic
`M³` scaling itself (`dM/dt ∝ -1/M²` integrated to lifetime ∝ M³),
which follows from the inverse-mass-squared Hawking flux ∝ T_H² · A
together with `T_H ∝ 1/M` and `A ∝ M²` already proved in
`HawkingTemperatureFromRung` and `BlackHoleEntropyFromLedger`.
-/

/-- Page time in SI: `t_Page_SI(M_SI) = 5120π · G_SI² · M_SI³ / (ℏ_SI · c_SI⁴)`. -/
def t_Page_SI (M_SI : ℝ) : ℝ :=
  5120 * Real.pi * G_SI ^ 2 * M_SI ^ 3 / (hbar_SI * c_SI ^ 4)

theorem t_Page_SI_def (M_SI : ℝ) :
    t_Page_SI M_SI = 5120 * Real.pi * G_SI ^ 2 * M_SI ^ 3 /
      (hbar_SI * c_SI ^ 4) := rfl

/-- The Page time prefactor: `K_Page = 5120π · G_SI² / (ℏ_SI · c_SI⁴)`.
This is the constant of proportionality in the `M³` scaling. -/
def K_Page_SI : ℝ :=
  5120 * Real.pi * G_SI ^ 2 / (hbar_SI * c_SI ^ 4)

theorem K_Page_SI_pos : 0 < K_Page_SI := by
  unfold K_Page_SI
  have hb_pow : 0 < hbar_SI * c_SI ^ 4 :=
    mul_pos hbar_SI_pos (pow_pos c_SI_pos 4)
  have h5120 : (0 : ℝ) < 5120 := by norm_num
  have hnum : 0 < 5120 * Real.pi * G_SI ^ 2 :=
    mul_pos (mul_pos h5120 Real.pi_pos) (pow_pos G_SI_pos 2)
  exact div_pos hnum hb_pow

/-- **The cubic Page-time scaling identity**:
`t_Page_SI(M_SI) = K_Page_SI · M_SI³`. The `M³` scaling is the RS-forced
content (from `dM/dt ∝ -1/M²` integration); `K_Page_SI` is the
semiclassical prefactor lifted to SI through the dimensional bridge. -/
theorem t_Page_SI_eq_K_mul_M_cube (M_SI : ℝ) :
    t_Page_SI M_SI = K_Page_SI * M_SI ^ 3 := by
  unfold t_Page_SI K_Page_SI
  have hb : hbar_SI ≠ 0 := ne_of_gt hbar_SI_pos
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  field_simp

/-- Positivity: positive masses give positive Page times. -/
theorem t_Page_SI_pos (M_SI : ℝ) (hM : 0 < M_SI) : 0 < t_Page_SI M_SI := by
  rw [t_Page_SI_eq_K_mul_M_cube]
  exact mul_pos K_Page_SI_pos (pow_pos hM 3)

/-- Strict monotonicity: heavier holes evaporate slower. -/
theorem t_Page_SI_strict_mono
    (M1 M2 : ℝ) (h1 : 0 < M1) (_h2 : 0 < M2) (hlt : M1 < M2) :
    t_Page_SI M1 < t_Page_SI M2 := by
  rw [t_Page_SI_eq_K_mul_M_cube, t_Page_SI_eq_K_mul_M_cube]
  have h_pow : M1 ^ 3 < M2 ^ 3 :=
    pow_lt_pow_left₀ hlt h1.le (by decide : (3 : ℕ) ≠ 0)
  exact mul_lt_mul_of_pos_left h_pow K_Page_SI_pos

/-- **Bridge identity (squared form, no `Real.sqrt`)**: the squared
Page-time-in-SI equals `(5120π)² · ℏG/c⁵ · M_SI⁶ · (G/(ℏc))³`. The
factor `ℏG/c⁵` is the squared Planck time and `G/(ℏc) = 1/M_Planck²`;
cubing the latter and multiplying by `M_SI⁶` gives `(M_SI/M_Planck)⁶`.
So the squared identity says
`t_Page_SI(M_SI)² = t_Planck² · (5120π)² · (M_SI/M_Planck)⁶`, the
Planck-unit form. -/
theorem t_Page_SI_squared_planck_form (M_SI : ℝ) :
    (t_Page_SI M_SI) ^ 2 =
      (5120 * Real.pi) ^ 2 * (hbar_SI * G_SI / c_SI ^ 5) *
        (G_SI / (hbar_SI * c_SI)) ^ 3 * M_SI ^ 6 := by
  unfold t_Page_SI
  have hb : hbar_SI ≠ 0 := ne_of_gt hbar_SI_pos
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  have hG : G_SI ≠ 0 := ne_of_gt G_SI_pos
  field_simp

/-! ## §6. Master cert -/

/-- Master cert: SI Hawking temperature has the master-plan-stipulated form,
positivity, strict anti-monotonicity, is the bridge lift of the
RS-native `T_hawking`, admits a Schwarzschild-radius reformulation, and
extends to the SI Page time `t_Page_SI` with `M³` scaling. -/
structure HawkingTemperatureSICert where
  T_hawking_SI_def :
    ∀ M : ℝ, T_hawking_SI M = hbar_SI * c_SI ^ 3 /
      (8 * Real.pi * G_SI * k_B_SI * M)
  hawking_temperature_SI :
    ∀ (M_SI : ℝ), 0 < M_SI →
      T_hawking_SI M_SI = hbar_SI * c_SI ^ 3 /
        (8 * Real.pi * G_SI * k_B_SI * M_SI)
  T_hawking_SI_pos :
    ∀ M : ℝ, 0 < M → 0 < T_hawking_SI M
  T_hawking_SI_strict_anti :
    ∀ M1 M2 : ℝ, 0 < M1 → 0 < M2 → M1 < M2 →
      T_hawking_SI M2 < T_hawking_SI M1
  T_hawking_SI_eq_geom_via_bridge :
    ∀ M : ℝ, 0 < M →
      T_hawking_SI M =
        T_hawking (G_SI * M / c_SI ^ 2) * (hbar_SI * c_SI / k_B_SI)
  schwarzschildRadius_SI_def :
    ∀ M : ℝ, schwarzschildRadius_SI M = 2 * G_SI * M / c_SI ^ 2
  schwarzschildRadius_SI_pos :
    ∀ M : ℝ, 0 < M → 0 < schwarzschildRadius_SI M
  T_hawking_SI_eq_inv_schwarzschildRadius :
    ∀ M : ℝ, 0 < M →
      T_hawking_SI M = hbar_SI * c_SI /
        (4 * Real.pi * k_B_SI * schwarzschildRadius_SI M)
  t_Page_SI_def :
    ∀ M : ℝ, t_Page_SI M = 5120 * Real.pi * G_SI ^ 2 * M ^ 3 /
      (hbar_SI * c_SI ^ 4)
  K_Page_SI_pos : 0 < K_Page_SI
  t_Page_SI_eq_K_mul_M_cube :
    ∀ M : ℝ, t_Page_SI M = K_Page_SI * M ^ 3
  t_Page_SI_pos : ∀ M : ℝ, 0 < M → 0 < t_Page_SI M
  t_Page_SI_strict_mono :
    ∀ M1 M2 : ℝ, 0 < M1 → 0 < M2 → M1 < M2 → t_Page_SI M1 < t_Page_SI M2

def hawkingTemperatureSICert : HawkingTemperatureSICert where
  T_hawking_SI_def := T_hawking_SI_def
  hawking_temperature_SI := hawking_temperature_SI
  T_hawking_SI_pos := T_hawking_SI_pos
  T_hawking_SI_strict_anti := T_hawking_SI_strict_anti
  T_hawking_SI_eq_geom_via_bridge := T_hawking_SI_eq_geom_via_bridge
  schwarzschildRadius_SI_def := schwarzschildRadius_SI_def
  schwarzschildRadius_SI_pos := schwarzschildRadius_SI_pos
  T_hawking_SI_eq_inv_schwarzschildRadius := T_hawking_SI_eq_inv_schwarzschildRadius
  t_Page_SI_def := t_Page_SI_def
  K_Page_SI_pos := K_Page_SI_pos
  t_Page_SI_eq_K_mul_M_cube := t_Page_SI_eq_K_mul_M_cube
  t_Page_SI_pos := t_Page_SI_pos
  t_Page_SI_strict_mono := t_Page_SI_strict_mono

theorem hawkingTemperatureSICert_inhabited :
    Nonempty HawkingTemperatureSICert :=
  ⟨hawkingTemperatureSICert⟩

/-- **HAWKING TEMPERATURE SI ONE-STATEMENT** (Track 3.A closure form).
In SI units, the Hawking temperature of a Schwarzschild black hole is
`T_H = ℏ_SI · c_SI³ / (8π · G_SI · k_B_SI · M_SI)`. It is positive and
strictly decreasing in the mass. It is the lift of the RS-native
`T_hawking(G_SI · M_SI / c_SI²)` (geometrized form) through the energy-to-
temperature conversion factor `ℏ_SI · c_SI / k_B_SI` provided by the
SI dimensional bridge. -/
theorem hawking_temperature_SI_one_statement :
    (∀ M : ℝ, T_hawking_SI M = hbar_SI * c_SI ^ 3 /
        (8 * Real.pi * G_SI * k_B_SI * M)) ∧
    (∀ M : ℝ, 0 < M → 0 < T_hawking_SI M) ∧
    (∀ M1 M2 : ℝ, 0 < M1 → 0 < M2 → M1 < M2 →
        T_hawking_SI M2 < T_hawking_SI M1) ∧
    (∀ M : ℝ, 0 < M →
        T_hawking_SI M =
          T_hawking (G_SI * M / c_SI ^ 2) * (hbar_SI * c_SI / k_B_SI)) :=
  ⟨T_hawking_SI_def, T_hawking_SI_pos, T_hawking_SI_strict_anti,
   T_hawking_SI_eq_geom_via_bridge⟩

end

end HawkingTemperatureSI
end Gravity
end IndisputableMonolith
