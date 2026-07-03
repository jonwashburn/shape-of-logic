import Mathlib

/-!
# Recognition work per cycle is bounded by the cadence, independent of the population

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

This module formalizes the Phase-11 result behind
`scripts/cosmogenesis/driven_forward.py`: when the open-system (expanding) dynamics drives the
scale-adaptive cell engine over a GROWING world, the recognition cost per cadence cycle stays
bounded while the world grows linearly, so the engine cost localizes to a sub-extensive interface.

The forced law posts at most one recognition event per tick (the cadence, T-7,
`Cosmology.FirstTick.cosmogenesisCadence = 8`). Model a cycle as `T` ticks, with at most one resolved
edge per tick: `res : Fin T → Option (ι × ι)` over an arbitrary region-index type `ι`. Each resolved
edge activates its two endpoints (a double-entry posting), so a tick contributes at most two
region-activations and, when each endpoint costs at most `P` forced postings to expand, at most
`2 * P` units of recognition work.

The theorems below bound the per-cycle activations by `2 * T` and the per-cycle recognition work by
`2 * P * T`. Crucially the bounds mention only the tick count `T` (the cadence) and the per-region
cost ceiling `P`, never the number of regions: the type `ι` can be arbitrarily large and does not
enter. So recognition cost per cycle does not grow with the world. Composed with a world that grows
by a fixed number of regions per cycle (the conjugate births of `expanding_dynamics.py`), this is the
formal core of "the recognition-active fraction falls toward zero and the engine never expands the
locked interior": the numerator (recognition work) is capped while the denominator (volume) grows.

This sits beside the schedule-independence corollary
(`Cosmology.ScaleAdaptiveSchedule.engine_run_literal_under_any_schedule`, which gives that the engine
stays literal under any schedule, hence the emergent open-system one) and the conjugate-birth charge
conservation (`Cosmology.RecognitionEquilibrium.manyBirths_chargeSum`, which gives sigma = 0 through
every birth). Together those three say: the driven engine is literal, conserves sigma through growth,
and pays a per-cycle recognition cost bounded by the cadence regardless of how large reality grows.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RecognitionWorkBound

variable {ι : Type*}

/-- The recognition work a single tick contributes, given a per-region forced-posting cost. A tick
that resolves nothing costs `0`; a tick that resolves an edge `(a, b)` costs `cost a + cost b` (its
two endpoints are expanded). At most one edge is resolved per tick, the forced cadence law. -/
def tickWork (e : Option (ι × ι)) (cost : ι → ℕ) : ℕ :=
  match e with
  | none => 0
  | some (a, b) => cost a + cost b

/-- The number of region-activations a single tick contributes: `0` if it resolves nothing, `2` if it
resolves an edge (its two endpoints). It is `tickWork` with the unit cost. -/
def tickActivations (e : Option (ι × ι)) : ℕ := tickWork e (fun _ => 1)

/-- A tick costs at most `2 * P` recognition work when every endpoint costs at most `P` to expand. -/
theorem tickWork_le (e : Option (ι × ι)) (P : ℕ) (cost : ι → ℕ) (hcost : ∀ i, cost i ≤ P) :
    tickWork e cost ≤ 2 * P := by
  cases e with
  | none => simp [tickWork]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    calc tickWork (some (a, b)) cost = cost a + cost b := rfl
      _ ≤ P + P := Nat.add_le_add (hcost a) (hcost b)
      _ = 2 * P := (two_mul P).symm

/-- A tick contributes at most `2` region-activations. -/
theorem tickActivations_le_two (e : Option (ι × ι)) : tickActivations e ≤ 2 := by
  simpa using tickWork_le e 1 (fun _ => 1) (fun _ => le_rfl)

/-- **Recognition work per cycle is bounded by the cadence, independent of the population.** Over a
cycle of `T` ticks with at most one resolved edge per tick and per-region expansion cost at most `P`,
the engine's total recognition work in the cycle is at most `2 * P * T`. The bound mentions only the
tick count `T` and the per-region ceiling `P`; the region-index type `ι` (the population) does not
appear, so the per-cycle recognition cost does not grow with the world. -/
theorem cycle_work_le (T : ℕ) (res : Fin T → Option (ι × ι)) (P : ℕ)
    (cost : ι → ℕ) (hcost : ∀ i, cost i ≤ P) :
    (∑ t, tickWork (res t) cost) ≤ 2 * P * T := by
  have h : (∑ t : Fin T, tickWork (res t) cost) ≤ ∑ _t : Fin T, 2 * P :=
    Finset.sum_le_sum (fun t _ => tickWork_le (res t) P cost hcost)
  have hconst : (∑ _t : Fin T, 2 * P) = 2 * P * T := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  exact h.trans (le_of_eq hconst)

/-- **Region-activations per cycle are bounded by twice the cadence, independent of the population.**
A specialization of `cycle_work_le` with unit cost: at most `2 * T` region-activations occur in a
`T`-tick cycle, regardless of the number of regions. -/
theorem cycle_activations_le (T : ℕ) (res : Fin T → Option (ι × ι)) :
    (∑ t, tickActivations (res t)) ≤ 2 * T := by
  have := cycle_work_le T res 1 (fun _ => 1) (fun _ => le_rfl)
  simpa [tickActivations] using this

/-- **Phase-11 cost-localization headline.** In a `T`-tick cadence cycle with at most one forced
resolution per tick, the engine's recognition work is at most `2 * P * T` and the region-activations
are at most `2 * T`, both independent of the population `ι`. So when the world grows by a fixed number
of regions per cycle, the recognition-cost numerator is capped while the volume denominator grows: the
recognition-active fraction falls toward zero and the cost localizes to a sub-extensive interface. -/
theorem recognition_work_localizes (T : ℕ) (res : Fin T → Option (ι × ι)) (P : ℕ)
    (cost : ι → ℕ) (hcost : ∀ i, cost i ≤ P) :
    (∑ t, tickWork (res t) cost) ≤ 2 * P * T
    ∧ (∑ t, tickActivations (res t)) ≤ 2 * T :=
  ⟨cycle_work_le T res P cost hcost, cycle_activations_le T res⟩

end RecognitionWorkBound
end Cosmology
end IndisputableMonolith
