import Mathlib
import IndisputableMonolith.Foundation.SIBridgeClosure
import IndisputableMonolith.Gravity.BlackHoleEntropyFromLedger
import IndisputableMonolith.Gravity.HawkingTemperatureSI

/-!
# Gravity Track 3.B (partial closure): Black-Hole Entropy in SI Units
plus sharper discriminator margins against LQG and string-theory

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This module implements two pieces of **Track 3.B of the quantum-gravity
master plan** (`Quantum_Gravity_Discovery_Master_Plan_20260521.html`, §4
Track 3.B):

1. **SI lift of the Bekenstein-Hawking leading-order entropy**
   `S_BH^SI(A_SI) = k_B_SI · A_SI · c_SI³ / (4 · G_SI · ℏ_SI)`,
   plus the mass-parametric form
   `S_BH^SI_mass(M_SI) = 4π · k_B_SI · G_SI · M_SI² / (ℏ_SI · c_SI)`,
   anchored on the dimensional bridge closed in
   `Foundation.SIBridgeClosure` (Track 5.A, closed 2026-05-09). The
   substantive bridge identity is
   `S_BH_SI(A_SI) = k_B_SI · S_lead(A_SI · c_SI³ / (G_SI · ℏ_SI))`,
   i.e. compute the RS-native dimensionless `S_lead` at the
   Planck-normalised dimensionless area and multiply by `k_B_SI` for SI
   units of J/K.

2. **Sharper discriminator certificates against LQG and string-theory
   leading-log canonical values.** Existing
   `Gravity.BlackHoleEntropyFromLedger` proves only the strict
   inequalities `c_RS ≠ -1/2` and `c_RS ≠ -3/2`. The theorem-grade
   observational channel requires a *margin*: an explicit lower bound on
   `|c_RS - c_LQG|` and `|c_RS - c_string|`, so that an experimental
   sensitivity smaller than the margin closes the falsification gap.

   Concretely:

   * `log_phi_lt_half : Real.log φ < 1/2` (sharper than the existing
     private `log φ < 1`). Proof uses `φ² = φ + 1 < 2.62 < exp 1` and
     monotonicity of `log`.
   * `c_RS_LQG_margin : c_RS - (-1/2) > 1/4` (margin > 0.25 on the leading-
     log coefficient distinguishes RS from LQG).
   * `c_RS_string_margin : c_RS - (-3/2) > 5/4` (margin > 1.25 on the
     leading-log coefficient distinguishes RS from string-theory canonical).

Together the SI lift and the discriminator margins make the
`c_RS = -log φ / 2 ≈ -0.241` prediction theorem-grade *with* an
explicit observational sensitivity threshold. The remaining Track 3.B
work is attaching a specific dataset (LIGO/Virgo QNM ringdown amplitude
spectroscopy, sensitivity in the relevant band) for the falsifier
register row.

## Anti-retreat principle satisfied

The SI entropy is anchored on:
* `k_B_SI` (SI-2019 exact, from `Gravity.HawkingTemperatureSI`).
* `c_SI`, `hbar_SI` (SI-2019 exact, from `Foundation.SIBridgeClosure`).
* `G_SI` (single CODATA measurement, the dimensional anchor).

No free dimensionless parameters; one dimensional anchor. The
discriminator margins are pure-mathematical: they depend only on the
identity `φ² = φ + 1`, the bound `φ < 1.62` (from
`Constants.phi_lt_onePointSixTwo`), and `Real.exp_one_gt_d9`. No
CODATA injection, no soft equality-only inequalities; both margins are
strict numerical lower bounds.

The `1/4` factor in `4 G ℏ` of the Bekenstein-Hawking formula inherits
from the semiclassical derivation (Bekenstein 1973, Hawking 1975), not
from the RS forcing chain. The RS-forced piece is the *coefficient* of
the leading log correction, `c_RS = -log φ / 2`, which is the
discriminator handle established in
`Gravity.BlackHoleEntropyFromLedger`.

## Falsifier (master plan §7 "Leading-log entropy" row)

`c_RS = -log φ / 2 ≈ -0.241` distinct from LQG `-1/2` and string `-3/2`
by margins `> 1/4` and `> 5/4` respectively. An observational
measurement of the leading-log coefficient of black-hole entropy with
absolute sensitivity better than `0.10` (well inside the LQG margin)
that lies outside the band `[-log φ/2 - 0.05, -log φ/2 + 0.05]` would
falsify the framework on this row.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace BlackHoleEntropySI

open Constants
open IndisputableMonolith.Foundation.SIBridgeClosure
open IndisputableMonolith.Gravity.BlackHoleEntropyFromLedger
open IndisputableMonolith.Gravity.HawkingTemperatureSI

/-- Disambiguate: `c_RS` here always refers to the leading-log
coefficient `-log φ / 2` from `Gravity.BlackHoleEntropyFromLedger`, NOT
the RS-native speed-of-light constant `c_RS = 1` from
`Foundation.SIBridgeClosure`. The latter is still accessible via its
qualified name `IndisputableMonolith.Foundation.SIBridgeClosure.c_RS`
or `_root_.IndisputableMonolith.Foundation.SIBridgeClosure.c_RS`. -/
local notation "c_RS" =>
  IndisputableMonolith.Gravity.BlackHoleEntropyFromLedger.c_RS

noncomputable section

/-! ## §1. The SI Bekenstein-Hawking leading-order entropy -/

/-- Bekenstein-Hawking entropy in SI as a function of area:
`S_BH^SI(A_SI) = k_B_SI · A_SI · c_SI³ / (4 · G_SI · ℏ_SI)`. -/
def S_BH_SI (A_SI : ℝ) : ℝ :=
  k_B_SI * A_SI * c_SI ^ 3 / (4 * G_SI * hbar_SI)

theorem S_BH_SI_def (A_SI : ℝ) :
    S_BH_SI A_SI = k_B_SI * A_SI * c_SI ^ 3 /
      (4 * G_SI * hbar_SI) := rfl

/-- Positivity: positive area gives positive entropy. -/
theorem S_BH_SI_pos (A_SI : ℝ) (hA : 0 < A_SI) : 0 < S_BH_SI A_SI := by
  unfold S_BH_SI
  have hnum : 0 < k_B_SI * A_SI * c_SI ^ 3 :=
    mul_pos (mul_pos k_B_SI_pos hA) (pow_pos c_SI_pos 3)
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hden : 0 < 4 * G_SI * hbar_SI :=
    mul_pos (mul_pos h4 G_SI_pos) hbar_SI_pos
  exact div_pos hnum hden

/-- **Track 3.B bridge identity.** The SI Bekenstein-Hawking entropy is
the bridge-converted RS-native `S_lead` evaluated at the dimensionless
area (in Planck units), multiplied by `k_B_SI` for SI units of J/K.

`S_BH_SI(A_SI) = k_B_SI · S_lead(A_SI · c_SI³ / (G_SI · ℏ_SI))`

The argument of `S_lead` is the dimensionless area `A_SI / ℓ_P²` with
`ℓ_P² = G_SI · ℏ_SI / c_SI³` the Planck area in SI. -/
theorem S_BH_SI_eq_S_lead_via_bridge (A_SI : ℝ) (hA : 0 < A_SI) :
    S_BH_SI A_SI = k_B_SI * S_lead (A_SI * c_SI ^ 3 / (G_SI * hbar_SI)) := by
  unfold S_BH_SI S_lead
  have hG : G_SI ≠ 0 := ne_of_gt G_SI_pos
  have hA_ne : A_SI ≠ 0 := ne_of_gt hA
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  have hb : hbar_SI ≠ 0 := ne_of_gt hbar_SI_pos
  have hk : k_B_SI ≠ 0 := ne_of_gt k_B_SI_pos
  field_simp

/-! ## §2. Schwarzschild mass-parametric form -/

/-- Bekenstein-Hawking SI entropy of a Schwarzschild black hole of
SI mass `M_SI`:
`S_BH^SI_mass(M_SI) = 4π · k_B_SI · G_SI · M_SI² / (ℏ_SI · c_SI)`. -/
def S_BH_SI_mass (M_SI : ℝ) : ℝ :=
  4 * Real.pi * k_B_SI * G_SI * M_SI ^ 2 / (hbar_SI * c_SI)

theorem S_BH_SI_mass_def (M_SI : ℝ) :
    S_BH_SI_mass M_SI =
      4 * Real.pi * k_B_SI * G_SI * M_SI ^ 2 / (hbar_SI * c_SI) := rfl

theorem S_BH_SI_mass_pos (M_SI : ℝ) (hM : 0 < M_SI) :
    0 < S_BH_SI_mass M_SI := by
  unfold S_BH_SI_mass
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hnum : 0 < 4 * Real.pi * k_B_SI * G_SI * M_SI ^ 2 :=
    mul_pos (mul_pos (mul_pos (mul_pos h4 Real.pi_pos) k_B_SI_pos) G_SI_pos)
      (pow_pos hM 2)
  exact div_pos hnum (mul_pos hbar_SI_pos c_SI_pos)

/-- Schwarzschild bridge: the mass-parametric form arises from
substituting `A_SI = 16π · G_SI² · M_SI² / c_SI⁴` into `S_BH_SI`. -/
theorem S_BH_SI_mass_eq_S_BH_SI (M_SI : ℝ) (hM : 0 < M_SI) :
    S_BH_SI_mass M_SI =
      S_BH_SI (16 * Real.pi * G_SI ^ 2 * M_SI ^ 2 / c_SI ^ 4) := by
  unfold S_BH_SI S_BH_SI_mass
  have hG : G_SI ≠ 0 := ne_of_gt G_SI_pos
  have hM_ne : M_SI ≠ 0 := ne_of_gt hM
  have hc : c_SI ≠ 0 := ne_of_gt c_SI_pos
  have hb : hbar_SI ≠ 0 := ne_of_gt hbar_SI_pos
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

/-! ## §3. The RS-corrected SI entropy (leading + log) -/

/-- The full RS entropy in SI: leading Bekenstein-Hawking plus the RS
leading-log correction `c_RS · log(A/ℓ_P²)`, then unit-converted by
`k_B_SI` to J/K. -/
def S_RS_SI (A_SI : ℝ) : ℝ :=
  S_BH_SI A_SI + k_B_SI * c_RS * Real.log (A_SI * c_SI ^ 3 / (G_SI * hbar_SI))

theorem S_RS_SI_def (A_SI : ℝ) :
    S_RS_SI A_SI =
      S_BH_SI A_SI + k_B_SI * c_RS *
        Real.log (A_SI * c_SI ^ 3 / (G_SI * hbar_SI)) := rfl

/-! ## §4. Sharper discriminator: `log φ < 1/2`

The existing private lemma in `BlackHoleEntropyFromLedger` only gives
`log φ < 1`. The theorem-grade observational channel needs an explicit
margin on `|c_RS - c_LQG|` and `|c_RS - c_string|`. Both follow from a
sharper bound `log φ < 1/2`, proved via `φ² = φ + 1 < 2.62 < exp 1`.
-/

/-- **Sharper bound on `log φ`**: `log φ < 1/2`, hence
`c_RS = -log φ / 2 > -1/4`. Proof: `φ² = φ + 1`, and `φ < 1.62` gives
`φ² < 2.62 < exp 1`, so `2 · log φ < 1`. -/
theorem log_phi_lt_half : Real.log Constants.phi < (1 : ℝ) / 2 := by
  have h_phi_pos : 0 < Constants.phi := Constants.phi_pos
  have h_phi_sq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have h_phi_lt : Constants.phi < 1.62 := Constants.phi_lt_onePointSixTwo
  have h_phi_sq_lt : Constants.phi ^ 2 < 2.62 := by
    rw [h_phi_sq]; linarith
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_phi_sq_lt_e : Constants.phi ^ 2 < Real.exp 1 := by linarith
  have h_phi_sq_pos : 0 < Constants.phi ^ 2 := pow_pos h_phi_pos 2
  have h_log_lt : Real.log (Constants.phi ^ 2) < Real.log (Real.exp 1) :=
    Real.log_lt_log h_phi_sq_pos h_phi_sq_lt_e
  rw [Real.log_exp, Real.log_pow] at h_log_lt
  -- h_log_lt : ↑2 * Real.log Constants.phi < 1
  push_cast at h_log_lt
  linarith

/-- The RS leading-log coefficient `c_RS` is strictly greater than `-1/4`.
Direct corollary of `log_phi_lt_half`. -/
theorem c_RS_gt_neg_quarter : c_RS > -1 / 4 := by
  unfold BlackHoleEntropyFromLedger.c_RS
  have h := log_phi_lt_half
  linarith

/-! ## §5. Discriminator margins (theorem-grade observational thresholds) -/

/-- **Discriminator margin vs LQG canonical `-1/2`.** Strict lower bound
on `c_RS - (-1/2)`: the RS coefficient sits at least `1/4` above the
LQG prediction. Any experimental sensitivity finer than `1/4` on the
leading-log coefficient distinguishes RS from LQG. -/
theorem c_RS_LQG_margin : c_RS - (-1 / 2) > 1 / 4 := by
  -- c_RS - (-1/2) = (1 - log φ) / 2.  log φ < 1/2 ⇒ (1 - log φ)/2 > 1/4.
  have h := log_phi_lt_half
  unfold BlackHoleEntropyFromLedger.c_RS
  linarith

/-- **Discriminator margin vs string-theory canonical `-3/2`.** Strict
lower bound on `c_RS - (-3/2)`: the RS coefficient sits at least `5/4`
above the string-theory prediction. Any experimental sensitivity finer
than `5/4` distinguishes RS from string. -/
theorem c_RS_string_margin : c_RS - (-3 / 2) > 5 / 4 := by
  -- c_RS - (-3/2) = (3 - log φ) / 2.  log φ < 1/2 ⇒ (3 - log φ)/2 > 5/4.
  have h := log_phi_lt_half
  unfold BlackHoleEntropyFromLedger.c_RS
  linarith

/-- Absolute-value form (LQG): `|c_RS - (-1/2)| > 1/4`. -/
theorem c_RS_LQG_margin_abs : |c_RS - (-1 / 2)| > 1 / 4 := by
  have h := c_RS_LQG_margin
  have h_pos : c_RS - (-1 / 2) > 0 := by linarith
  rw [abs_of_pos h_pos]
  exact h

/-- Absolute-value form (string): `|c_RS - (-3/2)| > 5/4`. -/
theorem c_RS_string_margin_abs : |c_RS - (-3 / 2)| > 5 / 4 := by
  have h := c_RS_string_margin
  have h_pos : c_RS - (-3 / 2) > 0 := by linarith
  rw [abs_of_pos h_pos]
  exact h

/-! ## §6. Master cert -/

/-- Master cert for Track 3.B partial closure: SI lift of leading entropy
plus sharper discriminator margins against LQG and string. -/
structure BlackHoleEntropySICert where
  S_BH_SI_def :
    ∀ A : ℝ, S_BH_SI A = k_B_SI * A * c_SI ^ 3 / (4 * G_SI * hbar_SI)
  S_BH_SI_pos :
    ∀ A : ℝ, 0 < A → 0 < S_BH_SI A
  S_BH_SI_eq_S_lead_via_bridge :
    ∀ A : ℝ, 0 < A →
      S_BH_SI A = k_B_SI * S_lead (A * c_SI ^ 3 / (G_SI * hbar_SI))
  S_BH_SI_mass_def :
    ∀ M : ℝ, S_BH_SI_mass M =
      4 * Real.pi * k_B_SI * G_SI * M ^ 2 / (hbar_SI * c_SI)
  S_BH_SI_mass_pos :
    ∀ M : ℝ, 0 < M → 0 < S_BH_SI_mass M
  S_BH_SI_mass_eq_S_BH_SI :
    ∀ M : ℝ, 0 < M →
      S_BH_SI_mass M = S_BH_SI (16 * Real.pi * G_SI ^ 2 * M ^ 2 / c_SI ^ 4)
  S_RS_SI_def :
    ∀ A : ℝ, S_RS_SI A =
      S_BH_SI A + k_B_SI * c_RS * Real.log (A * c_SI ^ 3 / (G_SI * hbar_SI))
  log_phi_lt_half : Real.log Constants.phi < (1 : ℝ) / 2
  c_RS_gt_neg_quarter : c_RS > -1 / 4
  c_RS_LQG_margin : c_RS - (-1 / 2) > 1 / 4
  c_RS_string_margin : c_RS - (-3 / 2) > 5 / 4
  c_RS_LQG_margin_abs : |c_RS - (-1 / 2)| > 1 / 4
  c_RS_string_margin_abs : |c_RS - (-3 / 2)| > 5 / 4

def blackHoleEntropySICert : BlackHoleEntropySICert where
  S_BH_SI_def := S_BH_SI_def
  S_BH_SI_pos := S_BH_SI_pos
  S_BH_SI_eq_S_lead_via_bridge := S_BH_SI_eq_S_lead_via_bridge
  S_BH_SI_mass_def := S_BH_SI_mass_def
  S_BH_SI_mass_pos := S_BH_SI_mass_pos
  S_BH_SI_mass_eq_S_BH_SI := S_BH_SI_mass_eq_S_BH_SI
  S_RS_SI_def := S_RS_SI_def
  log_phi_lt_half := log_phi_lt_half
  c_RS_gt_neg_quarter := c_RS_gt_neg_quarter
  c_RS_LQG_margin := c_RS_LQG_margin
  c_RS_string_margin := c_RS_string_margin
  c_RS_LQG_margin_abs := c_RS_LQG_margin_abs
  c_RS_string_margin_abs := c_RS_string_margin_abs

theorem blackHoleEntropySICert_inhabited :
    Nonempty BlackHoleEntropySICert :=
  ⟨blackHoleEntropySICert⟩

/-- **BLACK-HOLE ENTROPY SI ONE-STATEMENT** (Track 3.B partial closure form).
The SI Bekenstein-Hawking leading-order entropy is the bridge lift of
the RS-native `S_lead` (`= A/4`) through the energy-to-entropy
conversion factor `k_B_SI`. The RS leading-log coefficient
`c_RS = -log φ / 2` sits at least `1/4` above the LQG canonical `-1/2`
and at least `5/4` above the string-theory canonical `-3/2`. -/
theorem black_hole_entropy_SI_one_statement :
    (∀ A : ℝ, S_BH_SI A = k_B_SI * A * c_SI ^ 3 / (4 * G_SI * hbar_SI)) ∧
    (∀ A : ℝ, 0 < A → 0 < S_BH_SI A) ∧
    (∀ A : ℝ, 0 < A →
        S_BH_SI A = k_B_SI * S_lead (A * c_SI ^ 3 / (G_SI * hbar_SI))) ∧
    (c_RS - (-1 / 2) > 1 / 4) ∧
    (c_RS - (-3 / 2) > 5 / 4) :=
  ⟨S_BH_SI_def, S_BH_SI_pos, S_BH_SI_eq_S_lead_via_bridge,
   c_RS_LQG_margin, c_RS_string_margin⟩

end

end BlackHoleEntropySI
end Gravity
end IndisputableMonolith
