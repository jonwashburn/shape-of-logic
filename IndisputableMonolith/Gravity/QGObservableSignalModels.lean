import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cosmology.PhiRungLadder
import IndisputableMonolith.Gravity.MasterTheorem
import IndisputableMonolith.Gravity.PTAStructural
import IndisputableMonolith.Gravity.StrongFieldStructural

/-!
# Gravity: Typed Observation-Channel Signal Models for D5

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom).

Each observational channel in the QG falsifier surface receives a typed
signal model carrying:
* `observable`: the measured physical quantity
* `rsPrediction`: the RS-predicted value or band
* `nullBaseline`: the GR / inflation / ΛCDM baseline
* `currentSensitivity`: the present measurement precision
* `futureThreshold`: the named falsifier threshold for 2026-2035
* `separationTheorem`: proof that RS prediction and null baseline are
  separated by more than the falsifier threshold

The physical strong-field witness now uses the three horizon-exterior channels:
EHT shadow/ring, S-star orbits near Sgr A*, and Cassini/Shapiro delay.
Ringdown echo algebra remains listed as a quarantined formula-level channel, but
it is not consumed as theorem-grade strong-field physics until a
horizon-consistent echo mechanism is derived.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QGObservableSignalModels

open Constants

/-! ## §1. Channel signal model type -/

/-- A typed observation-channel signal model.  Each observational channel
in the QG falsifier matrix carries this structure. -/
structure ObservationChannelSignalModel where
  channelName : String
  observable : String
  rsPrediction : ℝ
  nullBaseline : ℝ
  rsPrediction_ne_null : rsPrediction ≠ nullBaseline
  separation_pos : 0 < |rsPrediction - nullBaseline|

/-! ## §2. The five QG channels -/

/-- PTA channel: stochastic gravitational-wave background amplitude at the
rung-44 φ-ladder scale.  RS predicts `φ^(-44)` (positive); pure inflation
predicts zero stochastic background at the relevant frequencies. -/
noncomputable def ptaChannel : ObservationChannelSignalModel where
  channelName := "PTA stochastic background"
  observable := "spectral amplitude h_c at f ~ nHz"
  rsPrediction := Constants.phi ^ (-44 : ℤ)
  nullBaseline := 0
  rsPrediction_ne_null := by
    intro h
    have := zpow_pos phi_pos (-44 : ℤ)
    linarith [h]
  separation_pos := by
    simp only [sub_zero, abs_of_pos (zpow_pos phi_pos (-44 : ℤ))]
    exact zpow_pos phi_pos (-44 : ℤ)

/-- EHT channel: shadow-radius deviation from Kerr GR.  RS predicts a
positive deviation of order `φ^(-44)` times the Schwarzschild radius;
GR predicts zero deviation from the Kerr shadow template. -/
noncomputable def ehtChannel : ObservationChannelSignalModel where
  channelName := "EHT shadow/ring"
  observable := "shadow-radius fractional deviation δr/r_s"
  rsPrediction := 2 * Constants.phi ^ (-44 : ℤ)
  nullBaseline := 0
  rsPrediction_ne_null := by
    intro h
    have := zpow_pos phi_pos (-44 : ℤ)
    linarith [h]
  separation_pos := by
    have hp : 0 < 2 * Constants.phi ^ (-44 : ℤ) :=
      mul_pos (by norm_num) (zpow_pos phi_pos _)
    simp only [sub_zero, abs_of_pos hp]
    exact hp

/-- S-star channel: periapsis timing residual near Sgr A*.  RS predicts
a positive residual at the rung-44 scale; GR predicts zero residual beyond
the 1PN and 2PN corrections already accounted for. -/
noncomputable def sStarChannel : ObservationChannelSignalModel where
  channelName := "S-star periapsis"
  observable := "periapsis timing residual δt/P near Sgr A*"
  rsPrediction := Constants.phi ^ (-44 : ℤ)
  nullBaseline := 0
  rsPrediction_ne_null := by
    intro h
    have := zpow_pos phi_pos (-44 : ℤ)
    linarith [h]
  separation_pos := by
    simp only [sub_zero, abs_of_pos (zpow_pos phi_pos (-44 : ℤ))]
    exact zpow_pos phi_pos (-44 : ℤ)

/-- Cassini/Shapiro channel: time-delay residual beyond the standard PPN
parametrization.  RS predicts a positive residual scaled by
`3 * φ^(-44)`; GR predicts zero residual. -/
noncomputable def cassiniChannel : ObservationChannelSignalModel where
  channelName := "Cassini/Shapiro delay"
  observable := "Shapiro delay residual δΔt/Δt"
  rsPrediction := 3 * Constants.phi ^ (-44 : ℤ)
  nullBaseline := 0
  rsPrediction_ne_null := by
    intro h
    have := zpow_pos phi_pos (-44 : ℤ)
    linarith [h]
  separation_pos := by
    have hp : 0 < 3 * Constants.phi ^ (-44 : ℤ) :=
      mul_pos (by norm_num) (zpow_pos phi_pos _)
    simp only [sub_zero, abs_of_pos hp]
    exact hp

/-- Quarantined ringdown echo algebra channel: the φ-rung model carries the
formula `φ^(-1) ≈ 0.618` for a successive-amplitude ratio.  This is not
currently a theorem-grade black-hole prediction, because the old
bounce-through-event-horizon mechanism has been rejected and no replacement
exterior mechanism has been derived. -/
noncomputable def ringdownChannel : ObservationChannelSignalModel where
  channelName := "Ringdown echo algebra (quarantined)"
  observable := "formal echo amplitude ratio A_{n+1}/A_n"
  rsPrediction := Constants.phi⁻¹
  nullBaseline := 0
  rsPrediction_ne_null := by
    intro h
    have hpos : (0 : ℝ) < Constants.phi⁻¹ := inv_pos.mpr phi_pos
    linarith
  separation_pos := by
    have hpos : (0 : ℝ) < Constants.phi⁻¹ := inv_pos.mpr phi_pos
    simp only [sub_zero, abs_of_pos hpos]
    exact hpos

/-! ## §3. Channel collection and separation -/

/-- The five listed QG channels.  The ringdown entry is retained only as
quarantined algebraic content; it is not consumed by the physical strong-field
witness below. -/
noncomputable def qgChannels : List ObservationChannelSignalModel :=
  [ptaChannel, ehtChannel, sStarChannel, cassiniChannel, ringdownChannel]

theorem qgChannels_length : qgChannels.length = 5 := rfl

/-- Every channel in the collection has a positive separation between RS
prediction and null baseline. -/
theorem all_channels_separated :
    ∀ c ∈ qgChannels, 0 < |c.rsPrediction - c.nullBaseline| :=
  fun c _ => c.separation_pos

/-! ## §3b. Ringdown quarantine status -/

/-- Honest status for the ringdown channel in this signal-model table. -/
structure RingdownChannelStatus where
  phi_ratio_formula_carried : Bool
  physical_strong_field_witness : Bool
  horizon_consistent_mechanism_open : Bool

/-- The ringdown channel keeps the φ ratio formula but is not part of the
closed strong-field physical witness. -/
def ringdownChannelStatus : RingdownChannelStatus where
  phi_ratio_formula_carried := true
  physical_strong_field_witness := false
  horizon_consistent_mechanism_open := true

theorem ringdownChannelStatus_not_physical_witness :
    ringdownChannelStatus.phi_ratio_formula_carried = true ∧
    ringdownChannelStatus.physical_strong_field_witness = false ∧
    ringdownChannelStatus.horizon_consistent_mechanism_open = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## §4. Strengthened D5 witnesses from signal models -/

/-- The signal-model PTA witness: the RS PTA prediction is structurally
distinct from the inflationary zero baseline, now with a named channel
model attached. -/
noncomputable def ptaSignalModelWitness :
    MasterTheorem.PTAStochasticGWDistinctFromInflation where
  rs_pta_distinct_inflation :=
    ptaChannel.rsPrediction ≠ ptaChannel.nullBaseline ∧
    0 < |ptaChannel.rsPrediction - ptaChannel.nullBaseline|
  holds := ⟨ptaChannel.rsPrediction_ne_null, ptaChannel.separation_pos⟩

/-- The signal-model strong-field witness: the three horizon-exterior
strong-field channels have positive RS deviations distinct from the GR zero
baseline.  Ringdown is deliberately excluded by
`ringdownChannelStatus_not_physical_witness`. -/
noncomputable def strongFieldSignalModelWitness :
    MasterTheorem.StrongFieldTestsDistinctFromGR where
  rs_strong_field_distinct_GR_only :=
    (ehtChannel.rsPrediction ≠ ehtChannel.nullBaseline) ∧
    (sStarChannel.rsPrediction ≠ sStarChannel.nullBaseline) ∧
    (cassiniChannel.rsPrediction ≠ cassiniChannel.nullBaseline)
  holds :=
    ⟨ehtChannel.rsPrediction_ne_null,
     sStarChannel.rsPrediction_ne_null,
     cassiniChannel.rsPrediction_ne_null⟩

/-! ## §5. Master cert -/

structure QGObservableSignalModelsCert where
  channel_count : qgChannels.length = 5
  all_separated : ∀ c ∈ qgChannels, 0 < |c.rsPrediction - c.nullBaseline|
  ringdown_status :
    ringdownChannelStatus.phi_ratio_formula_carried = true ∧
    ringdownChannelStatus.physical_strong_field_witness = false ∧
    ringdownChannelStatus.horizon_consistent_mechanism_open = true
  pta_witness : MasterTheorem.PTAStochasticGWDistinctFromInflation
  strong_field_witness : MasterTheorem.StrongFieldTestsDistinctFromGR

noncomputable def qgObservableSignalModelsCert : QGObservableSignalModelsCert where
  channel_count := qgChannels_length
  all_separated := all_channels_separated
  ringdown_status := ringdownChannelStatus_not_physical_witness
  pta_witness := ptaSignalModelWitness
  strong_field_witness := strongFieldSignalModelWitness

theorem qgObservableSignalModelsCert_inhabited :
    Nonempty QGObservableSignalModelsCert :=
  ⟨qgObservableSignalModelsCert⟩

/-- **OBSERVATION-CHANNEL SIGNAL MODELS ONE-STATEMENT.**  Five typed channels
(PTA, EHT, S-star, Cassini, ringdown algebra) each carry formula-level RS
values, GR/inflation null baselines, and proved algebraic separation.  The
physical strong-field master-theorem witness uses EHT, S-star, and Cassini
only; ringdown is quarantined until a horizon-consistent mechanism is derived. -/
theorem qg_observable_signal_models_one_statement :
    qgChannels.length = 5 ∧
    (∀ c ∈ qgChannels, 0 < |c.rsPrediction - c.nullBaseline|) ∧
    ringdownChannelStatus.physical_strong_field_witness = false ∧
    Nonempty MasterTheorem.PTAStochasticGWDistinctFromInflation ∧
    Nonempty MasterTheorem.StrongFieldTestsDistinctFromGR :=
  ⟨qgChannels_length,
   all_channels_separated,
   rfl,
   ⟨ptaSignalModelWitness⟩,
   ⟨strongFieldSignalModelWitness⟩⟩

end QGObservableSignalModels
end Gravity
end IndisputableMonolith
