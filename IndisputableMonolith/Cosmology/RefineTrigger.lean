import Mathlib
import IndisputableMonolith.Cosmology.RungCoarsen

/-!
# T-3: the refinement trigger is law-derived (threshold = 0, no knob)

This is the Lean statement of theorem T-3 of the scale-adaptive Cosmogenesis engine
(`plans/Cosmogenesis_North_Star_Reality_Simulation_Plan_20260602.html`,
`simulation/manifest.json` `build_spine.T3_law_derived_refinement`). The Python side
(`scripts/cosmogenesis/refine_trigger.py`) discharged it numerically; this module
discharges the statement itself. It builds on the T-1 cell model in
`Cosmology.RungCoarsen` (`Event`, `internalOf`, `crossOf`, `cost`, `cross_add_internal`).

## The knob risk and how it is removed

A naive refiner descends wherever some scalar exceeds a tuned tolerance `ε`. That `ε`
is exactly the free parameter the north star forbids. Sigma is identically zero at
every rung (double-entry), so a sigma imbalance is never the trigger. What forces a
descent is a posted distinction inside a block. The block's recognition demand is the
J-cost of its forced internal postings, and the law-given rule is:

  descend a block iff recognition_demand(block) > 0,

i.e. descend exactly where a distinction is forced. The threshold is structurally
zero, read off the ledger. There is no `ε` to choose.

## The content of T-3

* **the threshold is forced to zero** (`lossless_iff`): reconstructing while refining
  only the blocks in a decision `D` is lossless if and only if `D` covers every block
  that carries an internal posting. There is no freedom: lossless forces you to descend
  exactly the active blocks.
* **the law-given rule is lossless and minimal** (`lossless_law`,
  `descendLaw_necessary`): descend iff the block carries an internal posting; this is
  lossless, and any lossless decision must contain it.
* **no positive threshold is safe** (`jcost_arbitrarily_small_positive`,
  `epsilon_unsafe`): a forced posting can have arbitrarily small positive J-cost (ratio
  near one), so for every `ε > 0` there is a cell with an active block of demand below
  `ε` that the `ε`-rule skips, breaking losslessness. Zero is the unique law-given
  threshold.

## Status

Theorem-backed by `lawGivenTrigger` / `t3_law_derived_refinement`. The cost / demand is
the explicit RS recognition cost `Jcost x = (x + x⁻¹)/2 - 1`. Zero `sorry`, zero new
`axiom`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RefineTrigger

open RungCoarsen

open scoped Classical

/-- Reconstruct the fine cell while refining only the blocks the decision `D` selects:
keep all cross-block events, but expand a block's internal postings only if `D` holds
of that block. A block left coarse contributes none of its internal postings. -/
def reconstructUnder (block : ℕ → ℕ) (D : ℕ → Prop) [DecidablePred D]
    (m : Multiset Event) : Multiset Event :=
  crossOf block m + (internalOf block m).filter (fun e => D (block e.source))

/-! ## §1. The threshold is forced to zero -/

/-- **The descent set is forced.** Refining only the blocks in `D` is lossless if and
only if `D` covers every block that carries an internal posting. There is no tunable
slack: lossless reconstruction requires descending exactly the active blocks. -/
theorem lossless_iff (block : ℕ → ℕ) (D : ℕ → Prop) [DecidablePred D] (m : Multiset Event) :
    reconstructUnder block D m = m ↔ ∀ e ∈ internalOf block m, D (block e.source) := by
  unfold reconstructUnder
  rw [← Multiset.filter_eq_self]
  constructor
  · intro h
    have h2 : crossOf block m + (internalOf block m).filter (fun e => D (block e.source))
            = crossOf block m + internalOf block m := by
      rw [h]; exact (cross_add_internal block m).symm
    exact add_left_cancel h2
  · intro h
    rw [h]
    exact cross_add_internal block m

/-! ## §2. The law-given rule is lossless and minimal -/

/-- The law-given descent predicate: descend a block iff it carries an internal
posting (positive recognition activity). -/
def descendLaw (block : ℕ → ℕ) (m : Multiset Event) (b : ℕ) : Prop :=
  b ∈ (internalOf block m).map (fun e => block e.source)

/-- **The law-given rule is lossless.** Descending exactly the active blocks
reconstructs the cell with zero loss. -/
theorem lossless_law (block : ℕ → ℕ) (m : Multiset Event) :
    reconstructUnder block (descendLaw block m) m = m := by
  rw [lossless_iff]
  intro e he
  exact Multiset.mem_map.mpr ⟨e, he, rfl⟩

/-- **The law-given rule is minimal.** Any lossless decision must descend every active
block; you cannot skip a block that carries a posting. -/
theorem descendLaw_necessary (block : ℕ → ℕ) (D : ℕ → Prop) [DecidablePred D]
    (m : Multiset Event) (h : reconstructUnder block D m = m) :
    ∀ b, descendLaw block m b → D b := by
  intro b hb
  obtain ⟨e, he, hbe⟩ := Multiset.mem_map.mp hb
  have hD := (lossless_iff block D m).mp h e he
  rwa [hbe] at hD

/-! ## §3. The recognition cost and demand -/

/-- The RS recognition cost of a positive ratio. -/
noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

/-- A genuine distinction (ratio not one) has strictly positive cost. -/
theorem jcost_pos {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) : 0 < Jcost x := by
  have hx0 : x ≠ 0 := hx.ne'
  have key : Jcost x = (x - 1) ^ 2 / (2 * x) := by
    unfold Jcost; field_simp; ring
  rw [key]
  have hsq : 0 < (x - 1) ^ 2 := by
    have hne' : x - 1 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hden : 0 < 2 * x := by linarith
  exact div_pos hsq hden

/-- **Forced postings have arbitrarily small positive cost.** For every `ε > 0` there is
a ratio above one whose recognition cost is positive but below `ε`. This is why no
positive threshold is safe: a forced distinction can sit just under any `ε`. -/
theorem jcost_arbitrarily_small_positive (ε : ℝ) (hε : 0 < ε) :
    ∃ x : ℝ, 1 < x ∧ 0 < Jcost x ∧ Jcost x < ε := by
  have hδpos : 0 < min 1 ε := lt_min (by norm_num) hε
  have hδ1 : min 1 ε ≤ 1 := min_le_left _ _
  have hδε : min 1 ε ≤ ε := min_le_right _ _
  have hx1 : (1 : ℝ) < 1 + min 1 ε := by linarith
  have hpos : (0 : ℝ) < 1 + min 1 ε := by linarith
  have hne0 : (1 + min 1 ε) ≠ 0 := hpos.ne'
  refine ⟨1 + min 1 ε, hx1, jcost_pos hpos hx1.ne', ?_⟩
  have key : Jcost (1 + min 1 ε) = (min 1 ε) ^ 2 / (2 * (1 + min 1 ε)) := by
    unfold Jcost; field_simp; ring
  rw [key, div_lt_iff₀ (by nlinarith : (0 : ℝ) < 2 * (1 + min 1 ε))]
  nlinarith [hδpos, hδ1, hδε, hε,
    mul_nonneg hδpos.le (by linarith : (0 : ℝ) ≤ 1 - min 1 ε), mul_pos hε hδpos]

/-- Per-block recognition demand: the recognition cost of the block's internal
postings, the quantity the law-given rule reads. -/
noncomputable def demand (block : ℕ → ℕ) (m : Multiset Event) (b : ℕ) : ℝ :=
  cost Jcost ((internalOf block m).filter (fun e => block e.source = b))

/-! ## §4. No positive threshold is safe -/

/-- A two-site block map: sites `0,1` to coarse block `0`, everything else to block `1`. -/
def b01 : ℕ → ℕ := fun s => if s ≤ 1 then 0 else 1

@[simp] theorem b01_zero : b01 0 = 0 := by simp [b01]
@[simp] theorem b01_one : b01 1 = 0 := by simp [b01]

theorem cost_singleton (wr : ℝ → ℝ) (e : Event) : cost wr {e} = wr e.ratio := by
  unfold cost; simp

/-- **No positive threshold is safe.** For every `ε > 0` there is a cell with a single
internal posting whose demand is positive but below `ε`. The threshold rule "descend
iff demand exceeds `ε`" therefore skips that active block, and the reconstruction is
lossy. Only the zero threshold (descend iff a distinction is forced) is law-given. -/
theorem epsilon_unsafe (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : Multiset Event) (b : ℕ),
      0 < demand b01 m b ∧ demand b01 m b < ε
      ∧ reconstructUnder b01 (fun c => ε < demand b01 m c) m ≠ m := by
  obtain ⟨r, hr1, hrpos, hrlt⟩ := jcost_arbitrarily_small_positive ε hε
  refine ⟨{(⟨0, 1, r⟩ : Event)}, 0, ?_, ?_, ?_⟩
  · -- demand b01 {⟨0,1,r⟩} 0 = Jcost r
    have hd : demand b01 {(⟨0, 1, r⟩ : Event)} 0 = Jcost r := by
      unfold demand internalOf
      simp [sameBlock, b01, Multiset.filter_singleton, cost_singleton]
    rw [hd]; exact hrpos
  · have hd : demand b01 {(⟨0, 1, r⟩ : Event)} 0 = Jcost r := by
      unfold demand internalOf
      simp [sameBlock, b01, Multiset.filter_singleton, cost_singleton]
    rw [hd]; exact hrlt
  · -- the epsilon-rule skips block 0, so reconstruction drops the only posting
    have hd : demand b01 {(⟨0, 1, r⟩ : Event)} 0 = Jcost r := by
      unfold demand internalOf
      simp [sameBlock, b01, Multiset.filter_singleton, cost_singleton]
    have hnotsel : ¬ (ε < demand b01 {(⟨0, 1, r⟩ : Event)} 0) := by rw [hd]; linarith
    -- reconstructUnder = crossOf (empty) + internal filtered by a false predicate = 0
    have hrecon : reconstructUnder b01 (fun c => ε < demand b01 {(⟨0, 1, r⟩ : Event)} c)
        {(⟨0, 1, r⟩ : Event)} = 0 := by
      unfold reconstructUnder crossOf internalOf
      simp [sameBlock, b01, Multiset.filter_singleton, hnotsel]
    rw [hrecon]
    -- 0 ≠ {⟨0,1,r⟩}
    intro hcontra
    have : Multiset.card (0 : Multiset Event) = Multiset.card {(⟨0, 1, r⟩ : Event)} :=
      congrArg Multiset.card hcontra
    simp at this

/-! ## §5. The T-3 model as one object -/

/-- **Law-Given Trigger (T-3).** One named record collecting the refinement-trigger
guarantees:

* lossless reconstruction forces the descent set to be exactly the active blocks
  (`lossless_iff`);
* the law-given rule (descend iff a posting is forced) is lossless and minimal;
* no positive threshold is safe: a forced posting can have demand below any `ε > 0`.

Zero `sorry`, zero new `axiom`. -/
structure LawGivenTrigger (block : ℕ → ℕ) (m : Multiset Event) : Prop where
  threshold_forced : ∀ (D : ℕ → Prop) [DecidablePred D],
    reconstructUnder block D m = m ↔ ∀ e ∈ internalOf block m, D (block e.source)
  law_lossless : reconstructUnder block (descendLaw block m) m = m
  law_minimal : ∀ (D : ℕ → Prop) [DecidablePred D],
    reconstructUnder block D m = m → ∀ b, descendLaw block m b → D b

/-- **The law-given trigger model holds for every cell and block map.** -/
theorem lawGivenTrigger (block : ℕ → ℕ) (m : Multiset Event) : LawGivenTrigger block m where
  threshold_forced := fun D => lossless_iff block D m
  law_lossless := lossless_law block m
  law_minimal := fun D => descendLaw_necessary block D m

/-! ## §6. The headline -/

/-- **T-3 headline.** Lossless reconstruction forces the descent set to be exactly the
blocks that carry a forced posting (`lossless_iff`), the law-given rule realizing that
set is itself lossless (`lossless_law`), and no positive tolerance is safe because a
forced posting can have arbitrarily small positive cost (`epsilon_unsafe`). The
refinement threshold is therefore structurally zero, read off the ledger, with no knob
to choose. -/
theorem t3_law_derived_refinement (block : ℕ → ℕ) (m : Multiset Event) :
    (∀ (D : ℕ → Prop) [DecidablePred D],
        reconstructUnder block D m = m ↔ ∀ e ∈ internalOf block m, D (block e.source))
    ∧ (reconstructUnder block (descendLaw block m) m = m)
    ∧ (∀ ε : ℝ, 0 < ε → ∃ (m' : Multiset Event) (b : ℕ),
        0 < demand b01 m' b ∧ demand b01 m' b < ε
        ∧ reconstructUnder b01 (fun c => ε < demand b01 m' c) m' ≠ m') :=
  ⟨fun D => lossless_iff block D m, lossless_law block m,
   fun ε hε => epsilon_unsafe ε hε⟩

end RefineTrigger
end Cosmology
end IndisputableMonolith
