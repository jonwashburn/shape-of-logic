import Mathlib
import IndisputableMonolith.Cost

/-!
# Null Recognition Mode

The null recognition mode (NRM) is the upstream recognition-theoretic
object: the unique zero-cost propagating mode of the eight-tick recognition
cycle, up to ratio-gauge equivalence.

This module deliberately does **not** call the mode a photon and does not
attach physical labels such as spin, polarization, or lightlike propagation.
Those belong in `Physics.PhotonAsZeroCostMode`.
-/

namespace IndisputableMonolith
namespace Physics
namespace NullRecognitionMode

open Cost

noncomputable section

/-! ## Propagating modes on the eight-tick cycle -/

/-- A carrier event at one tick: a positive recognition ratio. -/
structure CarrierEvent where
  ratio : ℝ
  ratio_pos : 0 < ratio

/-- A propagating recognition mode assigns a carrier event to each tick of
the eight-tick recognition cycle. -/
structure PropagatingMode where
  event : Fin 8 → CarrierEvent

/-- Per-tick reciprocal recognition cost of a propagating mode. -/
def perTickCost (M : PropagatingMode) (i : Fin 8) : ℝ :=
  Jcost ((M.event i).ratio)

/-- Total recognition cost across the eight-tick cycle. -/
def totalModeCost (M : PropagatingMode) : ℝ :=
  ∑ i : Fin 8, perTickCost M i

/-- Gauge equivalence at the NRM level: two modes are equivalent if they
have the same recognition ratio at every tick. -/
def GaugeEquivalent (M N : PropagatingMode) : Prop :=
  ∀ i : Fin 8, (M.event i).ratio = (N.event i).ratio

/-- The canonical null recognition mode: identity ratio at every tick. -/
def canonicalNRM : PropagatingMode where
  event := fun _ => ⟨1, by norm_num⟩

/-- Backward-compatible short name for the canonical NRM. -/
abbrev zeroMode : PropagatingMode := canonicalNRM

@[simp] theorem canonicalNRM_ratio (i : Fin 8) :
    (canonicalNRM.event i).ratio = 1 := rfl

@[simp] theorem zeroMode_ratio (i : Fin 8) :
    (zeroMode.event i).ratio = 1 := rfl

/-- The canonical NRM has zero per-tick recognition cost. -/
theorem canonicalNRM_perTickCost (i : Fin 8) :
    perTickCost canonicalNRM i = 0 := by
  simp [perTickCost]
  exact Jcost_unit0

/-- The canonical NRM has total recognition cost zero. -/
theorem nrm_totalCost_zero : totalModeCost canonicalNRM = 0 := by
  unfold totalModeCost
  apply Finset.sum_eq_zero
  intro i _
  exact canonicalNRM_perTickCost i

/-- Backward-compatible theorem name for the canonical zero-mode cost. -/
theorem zeroMode_totalCost : totalModeCost zeroMode = 0 :=
  nrm_totalCost_zero

/-- A null recognition mode exists. -/
theorem nullRecognitionMode_nonempty :
    ∃ M : PropagatingMode, totalModeCost M = 0 :=
  ⟨canonicalNRM, nrm_totalCost_zero⟩

/-- Backward-compatible existence theorem. -/
theorem zeroCostMode_nonempty :
    ∃ M : PropagatingMode, totalModeCost M = 0 :=
  nullRecognitionMode_nonempty

/-! ## Uniqueness up to gauge -/

/-- Per-tick costs are nonnegative. -/
theorem perTickCost_nonneg (M : PropagatingMode) (i : Fin 8) :
    0 ≤ perTickCost M i := by
  unfold perTickCost
  exact Jcost_nonneg ((M.event i).ratio_pos)

/-- If total mode cost vanishes, then every per-tick cost vanishes. -/
theorem perTickCost_zero_of_total_zero
    (M : PropagatingMode) (h : totalModeCost M = 0) (i : Fin 8) :
    perTickCost M i = 0 := by
  have hsum : ∑ j : Fin 8, perTickCost M j = 0 := h
  have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 8)), 0 ≤ perTickCost M j := by
    intro j _
    exact perTickCost_nonneg M j
  have h_all := Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp hsum
  exact h_all i (Finset.mem_univ i)

/-- If total mode cost vanishes, then every tick is at the identity ratio. -/
theorem ratio_eq_one_of_total_zero
    (M : PropagatingMode) (h : totalModeCost M = 0) (i : Fin 8) :
    (M.event i).ratio = 1 := by
  have hz := perTickCost_zero_of_total_zero M h i
  unfold perTickCost at hz
  exact (Jcost_eq_zero_iff (M.event i).ratio (M.event i).ratio_pos).mp hz

/-- Any zero-cost propagating mode is gauge-equivalent to the canonical NRM. -/
theorem zeroCostMode_unique_up_to_gauge
    (M : PropagatingMode) (h : totalModeCost M = 0) :
    GaugeEquivalent M canonicalNRM := by
  intro i
  exact ratio_eq_one_of_total_zero M h i

/-! ## Certificate -/

structure NullRecognitionModeCert where
  exists_nrm : ∃ M : PropagatingMode, totalModeCost M = 0
  canonical_zero_cost : totalModeCost canonicalNRM = 0
  unique_up_to_gauge :
    ∀ M : PropagatingMode, totalModeCost M = 0 → GaugeEquivalent M canonicalNRM

def nullRecognitionModeCert : NullRecognitionModeCert where
  exists_nrm := nullRecognitionMode_nonempty
  canonical_zero_cost := nrm_totalCost_zero
  unique_up_to_gauge := zeroCostMode_unique_up_to_gauge

theorem nullRecognitionModeCert_inhabited :
    Nonempty NullRecognitionModeCert :=
  ⟨nullRecognitionModeCert⟩

end
end NullRecognitionMode
end Physics
end IndisputableMonolith
