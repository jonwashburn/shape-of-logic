import Mathlib
import IndisputableMonolith.Physics.NeutrinoSector

/-!
# Neutrino Baseline Choice-Set Enumeration (O5 Progress)

This module adds a finite-search closure step for the neutrino absolute baseline
question:

- Parameterize the lightest neutrino rung by a quarter-rung numerator `r1_num`.
- Enforce the structural gap profile (`+2`, then `+7/2`) in numerator form.
- Impose a deep-atmospheric window for `r3` and the canonical `-1/4` phase class.

Under these constraints, the admissible baseline set collapses to a singleton
`r1 = -239/4`.
-/

namespace IndisputableMonolith
namespace Verification
namespace NeutrinoBaselineChoiceSet

open Physics.NeutrinoSector

/-- Candidate encoded by the quarter-rung numerator for `r1 = r1_num / 4`. -/
structure BaselineCandidate where
  r1_num : ℤ
  deriving Repr, DecidableEq

/-- Numerator of `r2`, using the structural `r2 - r1 = 2` gap (`= 8/4`). -/
def r2_num (c : BaselineCandidate) : ℤ := c.r1_num + 8

/-- Numerator of `r3`, using `r3 - r2 = 7/2` (`= 14/4`). -/
def r3_num (c : BaselineCandidate) : ℤ := c.r1_num + 22

/-- Convert a quarter-rung numerator to a rational rung value. -/
def quarterRung (n : ℤ) : ℚ := (n : ℚ) / 4

def r1 (c : BaselineCandidate) : ℚ := quarterRung c.r1_num
def r2 (c : BaselineCandidate) : ℚ := quarterRung (r2_num c)
def r3 (c : BaselineCandidate) : ℚ := quarterRung (r3_num c)

/-- Canonical baseline candidate from the current neutrino construction. -/
def canonicalCandidate : BaselineCandidate := { r1_num := -239 }

/-- Finite search window for deep-ladder baselines (contains the canonical value). -/
def candidatePool : List BaselineCandidate :=
  (List.range 121).map (fun n => { r1_num := (n : ℤ) - 300 })

/-- Atmospheric rung must lie in the deep window `(-55, -54)`, i.e. `(-220, -216)/4`. -/
def deepAtmosphericWindow (c : BaselineCandidate) : Bool :=
  decide ((-220 : ℤ) < r3_num c ∧ r3_num c < (-216 : ℤ))

/-- Canonical 8-tick phase class: atmospheric rung is at `integer - 1/4`. -/
def quarterPhaseClass (c : BaselineCandidate) : Bool :=
  decide (((r3_num c + 1) % 4) = (0 : ℤ))

/-- Structural gap profile in doubled/quarter coordinates. -/
def structuralGapProfile (c : BaselineCandidate) : Bool :=
  decide (r2_num c - c.r1_num = 8 ∧ r3_num c - r2_num c = 14)

/-- Combined admissibility filter for the baseline search. -/
def admissible (c : BaselineCandidate) : Bool :=
  deepAtmosphericWindow c && quarterPhaseClass c && structuralGapProfile c

def validCandidates : List BaselineCandidate :=
  candidatePool.filter admissible

/-- "Deepest edge-only sublattice" condition for atmospheric numerators:
in the deep window and in the canonical `-1/4` phase class. -/
def deepestEdgeOnlyAtmospheric (n : ℤ) : Prop :=
  ((-220 : ℤ) < n ∧ n < (-216 : ℤ)) ∧ (((n + 1) % 4) = (0 : ℤ))

theorem candidate_pool_count : candidatePool.length = 121 := by
  native_decide

theorem structural_gap_profile_holds (c : BaselineCandidate) :
    structuralGapProfile c = true := by
  simp [structuralGapProfile, r2_num, r3_num]

/-- Structural atmospheric numerator from deepest edge level (`rung_nu3 = -54`)
and quarter-phase offset (`-1/4`): `4*(-54) - 1 = -217`. -/
theorem deepest_edge_atmospheric_num_eq :
    (4 * rung_nu3 - 1 : ℤ) = -217 := by
  norm_num [rung_nu3]

/-- Deep-window filter is forced once the atmospheric numerator is fixed by
edge confinement to `4*rung_nu3 - 1`. -/
theorem deep_window_forced_from_edge_confinement (c : BaselineCandidate)
    (hdeep : r3_num c = (4 * rung_nu3 - 1 : ℤ)) :
    deepAtmosphericWindow c = true := by
  have hr3 : r3_num c = -217 := by
    simpa [deepest_edge_atmospheric_num_eq] using hdeep
  simp [deepAtmosphericWindow, hr3]

/-- Quarter-phase (`-1/4`) class is forced by the same deepest-edge atmospheric
numerator, via 8-tick modular arithmetic. -/
theorem quarter_phase_forced_from_eight_tick_offset (c : BaselineCandidate)
    (hdeep : r3_num c = (4 * rung_nu3 - 1 : ℤ)) :
    quarterPhaseClass c = true := by
  have hr3 : r3_num c = -217 := by
    simpa [deepest_edge_atmospheric_num_eq] using hdeep
  simp [quarterPhaseClass, hr3]

/-- The deep-window and quarter-phase filters are jointly forced by the
edge-confinement atmospheric numerator. -/
theorem filter_pair_forced_from_edge_confinement (c : BaselineCandidate)
    (hdeep : r3_num c = (4 * rung_nu3 - 1 : ℤ)) :
    deepAtmosphericWindow c = true ∧ quarterPhaseClass c = true := by
  exact ⟨deep_window_forced_from_edge_confinement c hdeep,
    quarter_phase_forced_from_eight_tick_offset c hdeep⟩

/-- Within the deep window, the `-1/4` phase class picks a unique atmospheric numerator. -/
theorem deepest_edge_only_forces_atmospheric_num (n : ℤ)
    (h : deepestEdgeOnlyAtmospheric n) :
    n = -217 := by
  rcases h with ⟨hwin, hphase⟩
  have hdiv : (4 : ℤ) ∣ (n + 1) := (Int.dvd_iff_emod_eq_zero).2 hphase
  rcases hdiv with ⟨k, hk⟩
  omega

/-- The deep-atmospheric window plus quarter-phase class force `r3_num = -217`. -/
theorem deep_window_phase_forces_r3_num (c : BaselineCandidate)
    (hwin : deepAtmosphericWindow c = true)
    (hphase : quarterPhaseClass c = true) :
    r3_num c = -217 := by
  have hwin' : (-220 : ℤ) < r3_num c ∧ r3_num c < (-216 : ℤ) := by
    exact decide_eq_true_eq.mp (by simpa [deepAtmosphericWindow] using hwin)
  have hphase' : ((r3_num c + 1) % 4) = (0 : ℤ) := by
    exact decide_eq_true_eq.mp (by simpa [quarterPhaseClass] using hphase)
  exact deepest_edge_only_forces_atmospheric_num (r3_num c) ⟨hwin', hphase'⟩

/-- Under the same filters, the atmospheric rung value is uniquely `-217/4`. -/
theorem deep_window_phase_forces_r3_value (c : BaselineCandidate)
    (hwin : deepAtmosphericWindow c = true)
    (hphase : quarterPhaseClass c = true) :
    r3 c = (-217 : ℚ) / 4 := by
  have hr3 : r3_num c = -217 := deep_window_phase_forces_r3_num c hwin hphase
  simp [r3, quarterRung, hr3]

/-- With fixed spacing (`r3_num = r1_num + 22`), the same filters force `r1_num = -239`. -/
theorem deep_window_phase_forces_r1_num (c : BaselineCandidate)
    (hwin : deepAtmosphericWindow c = true)
    (hphase : quarterPhaseClass c = true) :
    c.r1_num = -239 := by
  have hr3 : r3_num c = -217 := deep_window_phase_forces_r3_num c hwin hphase
  have hr3' : c.r1_num + 22 = (-217 : ℤ) := by simpa [r3_num] using hr3
  omega

/-- Corresponding forced baseline rung value. -/
theorem deep_window_phase_forces_r1_value (c : BaselineCandidate)
    (hwin : deepAtmosphericWindow c = true)
    (hphase : quarterPhaseClass c = true) :
    r1 c = (-239 : ℚ) / 4 := by
  have hr1 : c.r1_num = -239 := deep_window_phase_forces_r1_num c hwin hphase
  simp [r1, quarterRung, hr1]

/-- Deep-window forcing aligns exactly with the canonical atmospheric rung `res_nu3`. -/
theorem deep_window_phase_forces_res_nu3 (c : BaselineCandidate)
    (hwin : deepAtmosphericWindow c = true)
    (hphase : quarterPhaseClass c = true) :
    r3 c = res_nu3 := by
  calc
    r3 c = (-217 : ℚ) / 4 := deep_window_phase_forces_r3_value c hwin hphase
    _ = res_nu3 := by simpa using res_nu3_simp.symm

/-- With built-in spacing, the same forcing aligns with the canonical baseline `res_nu1`. -/
theorem deep_window_phase_forces_res_nu1 (c : BaselineCandidate)
    (hwin : deepAtmosphericWindow c = true)
    (hphase : quarterPhaseClass c = true) :
    r1 c = res_nu1 := by
  calc
    r1 c = (-239 : ℚ) / 4 := deep_window_phase_forces_r1_value c hwin hphase
    _ = res_nu1 := by simpa using res_nu1_simp.symm

/-- Full baseline forcing from edge-confinement atmospheric level:
filters are forced, then `r3`/`r1` collapse to canonical `res_nu3`/`res_nu1`. -/
theorem edge_confinement_forces_canonical_baseline (c : BaselineCandidate)
    (hdeep : r3_num c = (4 * rung_nu3 - 1 : ℤ)) :
    r3 c = res_nu3 ∧ r1 c = res_nu1 := by
  have hpair : deepAtmosphericWindow c = true ∧ quarterPhaseClass c = true :=
    filter_pair_forced_from_edge_confinement c hdeep
  exact ⟨deep_window_phase_forces_res_nu3 c hpair.1 hpair.2,
    deep_window_phase_forces_res_nu1 c hpair.1 hpair.2⟩

/-- Absolute baseline numerator forced from deep-ladder atmospheric confinement
plus fixed structural spacing `r3_num = r1_num + 22`. -/
theorem absolute_baseline_num_forced_from_deep_ladder (c : BaselineCandidate)
    (hdeep : r3_num c = (4 * rung_nu3 - 1 : ℤ)) :
    c.r1_num = (4 * rung_nu3 - 1 : ℤ) - 22 := by
  have hr3 : c.r1_num + 22 = (4 * rung_nu3 - 1 : ℤ) := by
    simpa [r3_num] using hdeep
  omega

/-- Numeric form of the same forced baseline numerator at `D=3`: `r1_num = -239`. -/
theorem absolute_baseline_num_forced_eq_neg239 (c : BaselineCandidate)
    (hdeep : r3_num c = (4 * rung_nu3 - 1 : ℤ)) :
    c.r1_num = -239 := by
  calc
    c.r1_num = (4 * rung_nu3 - 1 : ℤ) - 22 :=
      absolute_baseline_num_forced_from_deep_ladder c hdeep
    _ = -239 := by norm_num [rung_nu3]

/-- O5' iff surface: deep-ladder atmospheric confinement is equivalent to the
canonical baseline candidate (single-field structure). -/
theorem deep_ladder_constraint_iff_canonical_candidate (c : BaselineCandidate) :
    (r3_num c = (4 * rung_nu3 - 1 : ℤ)) ↔ c = canonicalCandidate := by
  constructor
  · intro hdeep
    have hr1 : c.r1_num = -239 := absolute_baseline_num_forced_eq_neg239 c hdeep
    cases c
    simp [canonicalCandidate] at hr1 ⊢
    simpa using hr1
  · intro hc
    subst hc
    simp [canonicalCandidate, r3_num, rung_nu3]

/-- Baseline candidate forced directly by deep-ladder atmospheric geometry:
`r3_num = 4 * rung_nu3 - 1` and fixed spacing `r3_num = r1_num + 22`. -/
def deepLadderForcedCandidate : BaselineCandidate where
  r1_num := (4 * rung_nu3 - 1 : ℤ) - 22

/-- The deep-ladder forced candidate is exactly the canonical one. -/
theorem deep_ladder_forced_candidate_eq_canonical :
    deepLadderForcedCandidate = canonicalCandidate := by
  simp [deepLadderForcedCandidate, canonicalCandidate, rung_nu3]

/-- The deep-ladder forced candidate reproduces canonical `res_nu3`/`res_nu1`
without any extra filter assumptions. -/
theorem deep_ladder_geometry_forces_canonical_baseline :
    r3 deepLadderForcedCandidate = res_nu3 ∧
    r1 deepLadderForcedCandidate = res_nu1 := by
  have hdeep : r3_num deepLadderForcedCandidate = (4 * rung_nu3 - 1 : ℤ) := by
    simp [r3_num, deepLadderForcedCandidate]
  simpa using edge_confinement_forces_canonical_baseline deepLadderForcedCandidate hdeep

theorem valid_candidate_count : validCandidates.length = 1 := by
  native_decide

theorem valid_candidates_singleton :
    validCandidates = [canonicalCandidate] := by
  native_decide

theorem canonical_is_valid :
    canonicalCandidate ∈ validCandidates := by
  rw [valid_candidates_singleton]
  simp

theorem unique_valid_candidate (c : BaselineCandidate) (hc : c ∈ validCandidates) :
    c = canonicalCandidate := by
  rw [valid_candidates_singleton] at hc
  simpa using hc

/-- The singleton baseline agrees with the neutrino module baseline rung. -/
theorem canonical_r1_matches_res_nu1 :
    r1 canonicalCandidate = res_nu1 := by
  simpa [r1, quarterRung, canonicalCandidate] using res_nu1_simp.symm

/-- The induced atmospheric rung from the singleton baseline matches `res_nu3`. -/
theorem canonical_r3_matches_res_nu3 :
    r3 canonicalCandidate = res_nu3 := by
  have h : r3 canonicalCandidate = (-217 : ℚ) / 4 := by
    norm_num [r3, quarterRung, r3_num, canonicalCandidate]
  calc
    r3 canonicalCandidate = (-217 : ℚ) / 4 := h
    _ = res_nu3 := by simpa using res_nu3_simp.symm

/-- Enumerated-choice closure summary for O5 under the current filter set. -/
theorem baseline_choice_set_collapsed :
    validCandidates = [canonicalCandidate] := valid_candidates_singleton

/-- Any admissible baseline reproduces the current `res_nu1` value. -/
theorem admissible_baselines_match_res_nu1 (c : BaselineCandidate) (hc : c ∈ validCandidates) :
    r1 c = res_nu1 := by
  have huniq : c = canonicalCandidate := unique_valid_candidate c hc
  simpa [huniq] using canonical_r1_matches_res_nu1

end NeutrinoBaselineChoiceSet
end Verification
end IndisputableMonolith
