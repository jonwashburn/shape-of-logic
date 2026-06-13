import Mathlib

/-!
# Quantum Gravity Falsifier Register Dataset Attachments

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module attaches concrete named datasets and numerical sensitivity
records to every row of the quantum-gravity master plan §7 falsifier
register.

The records are deliberately conservative. A row is **attached** when it
has:

* a named observational channel or dataset;
* a numerical sensitivity scale;
* an RS target scale or band to compare against;
* an honest flag saying whether current data are already sensitive to
  the RS target.

The purpose is falsifiability accounting, not empirical confirmation.
The records below do not claim that any dataset has confirmed RS. They
only make explicit which experiment tests which prediction, and at what
reported precision.

Anchor examples:

* Planck 2018: `Ω_Λ = 0.6889 ± 0.0056`.
* Planck+BAO+SNe: `w₀ = -1.03 ± 0.03` (constant-w extension).
* Cassini Shapiro delay: `γ - 1 = (2.1 ± 2.3)×10⁻⁵`.
* EHT M87*: ring diameter `42 ± 3 μas`, shadow-size Kerr consistency
  at roughly 17%, circularity deviation ≤10%.
* GRAVITY S2: Schwarzschild-precession factor `f_SP = 1.10 ± 0.19`.
* NANOGrav 15-year: Hellings-Downs correlated stochastic background,
  68 pulsars, 15 yr baseline, power-law spectrum compatible with the
  SMBHB reference slope `γ = 13/3`.
* EPTA DR2: CRS/GWB spectral-index record around `γ ≈ 3.83` and
  `log10 A ≈ -14.32` in the relevant analysis.
* GWTC-3 tests of GR: no significant deviations from GR, no
  post-merger echoes in analyzed events, graviton-mass bound
  `m_g ≤ 2.42×10⁻²³ eV/c²`.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset attachment record -/

/-- Dataset attachment for a falsifier-register row.

`sensitivity` and `rsTargetScale` are dimensionless unless the field
`units` says otherwise. `currentlySensitive` records whether the named
dataset can already reach the RS target scale. For several future rows
this is honestly `false`: the dataset is named, but it is not yet
sensitive enough to test the φ-suppressed target. -/
structure DatasetAttachment where
  sector : String
  dataset : String
  units : String
  sensitivity : ℝ
  rsTargetScale : ℝ
  currentlySensitive : Bool

/-- Positive numerical sensitivity requirement. -/
def HasPositiveSensitivity (D : DatasetAttachment) : Prop :=
  0 < D.sensitivity

/-- Positive RS target scale requirement. -/
def HasPositiveTargetScale (D : DatasetAttachment) : Prop :=
  0 < D.rsTargetScale

/-! ## §2. Named dataset records -/

/-- BMV tabletop / MAQRO-class phase-rate row.

Target band from the master plan and `papers/reproducibility/bmv_phase_rate.py`:
`[4.77, 5.04]×10⁻⁷ rad/s`. Current MAQRO-class experiment is a future
channel, so the row is attached but not yet currently sensitive. -/
def bmvAttachment : DatasetAttachment where
  sector := "BMV phase-rate sign and magnitude"
  dataset := "MAQRO-class tabletop BMV entanglement-generation experiment"
  units := "rad/s"
  sensitivity := 5.04e-7 - 4.77e-7
  rsTargetScale := (4.77e-7 + 5.04e-7) / 2
  currentlySensitive := false

/-- Hawking temperature row.

The falsifier threshold is 10% on the leading Hawking temperature formula.
The row is attached to future analog-gravity / primordial-BH searches. -/
def hawkingTemperatureAttachment : DatasetAttachment where
  sector := "Hawking temperature"
  dataset := "Future analog-gravity or primordial-BH temperature measurement"
  units := "fractional T_H"
  sensitivity := 0.10
  rsTargetScale := 1.0
  currentlySensitive := false

/-- Leading-log entropy coefficient row.

Target coefficient `c_RS = -log φ / 2 ≈ -0.2406`; falsifier sensitivity
0.10 safely distinguishes RS from LQG's `-1/2` margin (`>0.25`). -/
def leadingLogEntropyAttachment : DatasetAttachment where
  sector := "Leading-log entropy coefficient"
  dataset := "LIGO/Virgo ringdown and future LISA/Einstein Telescope QNM spectroscopy"
  units := "coefficient"
  sensitivity := 0.10
  rsTargetScale := 0.05
  currentlySensitive := false

/-- Page curve row.

Structural row: future analog-gravity experiment must distinguish the
triangular Page curve from monotone Hawking entropy increase. -/
def pageCurveAttachment : DatasetAttachment where
  sector := "Page curve"
  dataset := "Future analog-gravity Page-curve experiment"
  units := "shape discriminator"
  sensitivity := 1.0
  rsTargetScale := 1.0
  currentlySensitive := false

/-- Echo phenomenology row.

GWTC-3 tests of GR report no post-merger echoes in the analyzed events.
RS echo damping target is the dimensionless amplitude ratio `1/φ ≈ 0.618`. -/
def echoAttachment : DatasetAttachment where
  sector := "Black-hole echo phenomenology"
  dataset := "LIGO/Virgo/KAGRA GWTC-3 tests of GR ringdown / post-merger echo search"
  units := "echo amplitude ratio"
  sensitivity := 0.10
  rsTargetScale := 0.618
  currentlySensitive := false

/-- Cosmological constant row.

Planck 2018 base-ΛCDM record: `Ω_Λ = 0.6889 ± 0.0056`; RS band
`Ω_Λ ∈ (0.683, 0.686)` is close enough for a two-sigma consistency check. -/
def omegaLambdaAttachment : DatasetAttachment where
  sector := "Cosmological constant ΩΛ"
  dataset := "Planck 2018 TT,TE,EE+lowE+lensing"
  units := "ΩΛ"
  sensitivity := 0.0056
  rsTargetScale := 0.686 - 0.683
  currentlySensitive := true

/-- Dark-energy equation-of-state row.

Planck+BAO+SNe gives a constant-w example `w₀ = -1.03 ± 0.03`.
DESI DR1/DR2 gives the modern dynamic-w channel. The structural RS target
scale `φ⁻⁴⁴ z` is about `6.38×10⁻¹⁰` at z=1, far below current
cosmological equation-of-state precision. -/
def darkEnergyWAttachment : DatasetAttachment where
  sector := "Dark-energy equation of state w(z)"
  dataset := "DESI BAO + Planck CMB + supernovae w0-wa analyses"
  units := "w"
  sensitivity := 0.03
  rsTargetScale := 6.376e-10
  currentlySensitive := false

/-- QNM discriminator row.

GWTC-3 tests of GR report remnant consistency and no significant QNM
deviation; future LISA/ET supply the high-precision row. The numerical
sensitivity here stores the current graviton-mass bound as the concrete
GWTC-3 scale reported in the tests-of-GR abstract. -/
def qnmAttachment : DatasetAttachment where
  sector := "Quasinormal-mode / ringdown discriminator"
  dataset := "LIGO/Virgo/KAGRA GWTC-3 tests of GR; future LISA/Einstein Telescope"
  units := "eV/c^2 graviton-mass bound"
  sensitivity := 2.42e-23
  rsTargetScale := 0.2406
  currentlySensitive := false

/-- PTA stochastic background row.

NANOGrav 15-year: 68 pulsars over 15 years, Hellings-Downs correlated
background, power-law spectrum compatible with the SMBHB reference slope
`γ = 13/3`. The RS structural target uses `log φ ≈ 0.481` as a positive
φ-rational signature; this row is attached, but not yet dynamically
matched to the full spectrum. -/
def ptaAttachment : DatasetAttachment where
  sector := "PTA stochastic gravitational-wave background"
  dataset := "NANOGrav 15-year + EPTA DR2 nanohertz stochastic background"
  units := "spectral-index scale"
  sensitivity := 0.80
  rsTargetScale := 0.481
  currentlySensitive := false

/-- Strong-field row: EHT / GRAVITY / Cassini.

This row stores Cassini's PPN-γ precision as the most precise current
solar-system strong/weak-field number, while the dataset string records
the full strong-field channel list. -/
def strongFieldAttachment : DatasetAttachment where
  sector := "Strong-field / precision-GR tests"
  dataset := "Cassini Shapiro delay; GRAVITY S2 precession; EHT M87* shadow"
  units := "fractional metric-deviation scale"
  sensitivity := 2.3e-5
  rsTargetScale := 6.376e-10
  currentlySensitive := false

/-! ## §3. Positivity lemmas for each record -/

theorem bmv_sensitivity_pos : HasPositiveSensitivity bmvAttachment := by
  unfold HasPositiveSensitivity bmvAttachment
  norm_num

theorem hawking_sensitivity_pos :
    HasPositiveSensitivity hawkingTemperatureAttachment := by
  unfold HasPositiveSensitivity hawkingTemperatureAttachment
  norm_num

theorem leadingLog_sensitivity_pos :
    HasPositiveSensitivity leadingLogEntropyAttachment := by
  unfold HasPositiveSensitivity leadingLogEntropyAttachment
  norm_num

theorem pageCurve_sensitivity_pos :
    HasPositiveSensitivity pageCurveAttachment := by
  unfold HasPositiveSensitivity pageCurveAttachment
  norm_num

theorem echo_sensitivity_pos : HasPositiveSensitivity echoAttachment := by
  unfold HasPositiveSensitivity echoAttachment
  norm_num

theorem omegaLambda_sensitivity_pos :
    HasPositiveSensitivity omegaLambdaAttachment := by
  unfold HasPositiveSensitivity omegaLambdaAttachment
  norm_num

theorem darkEnergyW_sensitivity_pos :
    HasPositiveSensitivity darkEnergyWAttachment := by
  unfold HasPositiveSensitivity darkEnergyWAttachment
  norm_num

theorem qnm_sensitivity_pos : HasPositiveSensitivity qnmAttachment := by
  unfold HasPositiveSensitivity qnmAttachment
  norm_num

theorem pta_sensitivity_pos : HasPositiveSensitivity ptaAttachment := by
  unfold HasPositiveSensitivity ptaAttachment
  norm_num

theorem strongField_sensitivity_pos :
    HasPositiveSensitivity strongFieldAttachment := by
  unfold HasPositiveSensitivity strongFieldAttachment
  norm_num

/-! ## §4. Target-scale positivity -/

theorem bmv_target_pos : HasPositiveTargetScale bmvAttachment := by
  unfold HasPositiveTargetScale bmvAttachment
  norm_num

theorem hawking_target_pos :
    HasPositiveTargetScale hawkingTemperatureAttachment := by
  unfold HasPositiveTargetScale hawkingTemperatureAttachment
  norm_num

theorem leadingLog_target_pos :
    HasPositiveTargetScale leadingLogEntropyAttachment := by
  unfold HasPositiveTargetScale leadingLogEntropyAttachment
  norm_num

theorem pageCurve_target_pos :
    HasPositiveTargetScale pageCurveAttachment := by
  unfold HasPositiveTargetScale pageCurveAttachment
  norm_num

theorem echo_target_pos : HasPositiveTargetScale echoAttachment := by
  unfold HasPositiveTargetScale echoAttachment
  norm_num

theorem omegaLambda_target_pos :
    HasPositiveTargetScale omegaLambdaAttachment := by
  unfold HasPositiveTargetScale omegaLambdaAttachment
  norm_num

theorem darkEnergyW_target_pos :
    HasPositiveTargetScale darkEnergyWAttachment := by
  unfold HasPositiveTargetScale darkEnergyWAttachment
  norm_num

theorem qnm_target_pos : HasPositiveTargetScale qnmAttachment := by
  unfold HasPositiveTargetScale qnmAttachment
  norm_num

theorem pta_target_pos : HasPositiveTargetScale ptaAttachment := by
  unfold HasPositiveTargetScale ptaAttachment
  norm_num

theorem strongField_target_pos :
    HasPositiveTargetScale strongFieldAttachment := by
  unfold HasPositiveTargetScale strongFieldAttachment
  norm_num

/-! ## §5. Master certificate -/

/-- Master certificate: every §7 falsifier-register row has a named
dataset, a positive numerical sensitivity scale, and a positive RS target
scale. -/
structure FalsifierDatasetRegisterCert where
  bmv_sensitivity : HasPositiveSensitivity bmvAttachment
  bmv_target : HasPositiveTargetScale bmvAttachment
  hawking_sensitivity : HasPositiveSensitivity hawkingTemperatureAttachment
  hawking_target : HasPositiveTargetScale hawkingTemperatureAttachment
  leadingLog_sensitivity : HasPositiveSensitivity leadingLogEntropyAttachment
  leadingLog_target : HasPositiveTargetScale leadingLogEntropyAttachment
  pageCurve_sensitivity : HasPositiveSensitivity pageCurveAttachment
  pageCurve_target : HasPositiveTargetScale pageCurveAttachment
  echo_sensitivity : HasPositiveSensitivity echoAttachment
  echo_target : HasPositiveTargetScale echoAttachment
  omegaLambda_sensitivity : HasPositiveSensitivity omegaLambdaAttachment
  omegaLambda_target : HasPositiveTargetScale omegaLambdaAttachment
  darkEnergyW_sensitivity : HasPositiveSensitivity darkEnergyWAttachment
  darkEnergyW_target : HasPositiveTargetScale darkEnergyWAttachment
  qnm_sensitivity : HasPositiveSensitivity qnmAttachment
  qnm_target : HasPositiveTargetScale qnmAttachment
  pta_sensitivity : HasPositiveSensitivity ptaAttachment
  pta_target : HasPositiveTargetScale ptaAttachment
  strongField_sensitivity : HasPositiveSensitivity strongFieldAttachment
  strongField_target : HasPositiveTargetScale strongFieldAttachment

def falsifierDatasetRegisterCert : FalsifierDatasetRegisterCert where
  bmv_sensitivity := bmv_sensitivity_pos
  bmv_target := bmv_target_pos
  hawking_sensitivity := hawking_sensitivity_pos
  hawking_target := hawking_target_pos
  leadingLog_sensitivity := leadingLog_sensitivity_pos
  leadingLog_target := leadingLog_target_pos
  pageCurve_sensitivity := pageCurve_sensitivity_pos
  pageCurve_target := pageCurve_target_pos
  echo_sensitivity := echo_sensitivity_pos
  echo_target := echo_target_pos
  omegaLambda_sensitivity := omegaLambda_sensitivity_pos
  omegaLambda_target := omegaLambda_target_pos
  darkEnergyW_sensitivity := darkEnergyW_sensitivity_pos
  darkEnergyW_target := darkEnergyW_target_pos
  qnm_sensitivity := qnm_sensitivity_pos
  qnm_target := qnm_target_pos
  pta_sensitivity := pta_sensitivity_pos
  pta_target := pta_target_pos
  strongField_sensitivity := strongField_sensitivity_pos
  strongField_target := strongField_target_pos

theorem falsifierDatasetRegisterCert_inhabited :
    Nonempty FalsifierDatasetRegisterCert :=
  ⟨falsifierDatasetRegisterCert⟩

/-- One-statement form: all falsifier-register rows have positive
dataset sensitivities and positive RS target scales. -/
theorem falsifier_dataset_register_one_statement :
    HasPositiveSensitivity bmvAttachment ∧
    HasPositiveSensitivity hawkingTemperatureAttachment ∧
    HasPositiveSensitivity leadingLogEntropyAttachment ∧
    HasPositiveSensitivity pageCurveAttachment ∧
    HasPositiveSensitivity echoAttachment ∧
    HasPositiveSensitivity omegaLambdaAttachment ∧
    HasPositiveSensitivity darkEnergyWAttachment ∧
    HasPositiveSensitivity qnmAttachment ∧
    HasPositiveSensitivity ptaAttachment ∧
    HasPositiveSensitivity strongFieldAttachment ∧
    Nonempty FalsifierDatasetRegisterCert :=
  ⟨bmv_sensitivity_pos,
   hawking_sensitivity_pos,
   leadingLog_sensitivity_pos,
   pageCurve_sensitivity_pos,
   echo_sensitivity_pos,
   omegaLambda_sensitivity_pos,
   darkEnergyW_sensitivity_pos,
   qnm_sensitivity_pos,
   pta_sensitivity_pos,
   strongField_sensitivity_pos,
   falsifierDatasetRegisterCert_inhabited⟩

end

end FalsifierRegisterDatasets
end Verification
end IndisputableMonolith
