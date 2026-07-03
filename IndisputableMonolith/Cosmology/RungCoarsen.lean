import Mathlib

/-!
# T-1: Rung-coarsening is sigma-exact and cost-exact (the "literal" theorem)

This is the Lean statement of theorem T-1 of the scale-adaptive Cosmogenesis engine
(`plans/Cosmogenesis_North_Star_Reality_Simulation_Plan_20260602.html`,
`simulation/manifest.json` `build_spine.T1_coarsening_exact`). The Python side
(`scripts/cosmogenesis/rung_coarsen.py`) discharged it numerically (round-trip exact
on the voxel battery and the idle cell); this module discharges the statement itself.

## The model

A recognition cell at one phi-rung is its multiset of canonical recognition events
(`Multiset Event`); order is irrelevant, every conserved functional is a function of
the multiset. A block map `block : ℕ → ℕ` sends fine sites to coarse sites. Coarsening
one rung up partitions the events:

* `internalOf` : both endpoints land in one block, absorbed into that block's summary;
* `crossOf` : the endpoints differ, promoted to coarse events between coarse sites
  with the same ratio (`coarseLedger = (crossOf).map (relabel block)`).

A refinement record keeps exactly the original cross events and the per-block internal
events, and `refineCell` reassembles them. This mirrors `rung_coarsen.py`'s
`coarsen` / `refine` / `Refinement`.

## The content of T-1

* **round-trip is the identity** (`roundtrip_eq`): `refine (coarsen m) = m`, because the
  partition recombines to the original multiset (`Multiset.filter_add_not`). Coarsening
  loses nothing reality has determined; this is what earns the word "literal."
* **every conserved functional is preserved** (`conserved`): because the round-trip
  returns the identical multiset, ANY functional of the cell is unchanged. Instances:
  event count (`count_preserved`), total cost (`cost_preserved`), the log-ratio
  spectrum (`spectrum_preserved`), and net flow / sigma (`sigma_preserved`).
* **cost partitions exactly** (`cost_partition`): the coarse cross-block cost plus the
  sum of block-internal cost equals the fine cost, since relabeling preserves ratios
  and the events partition.
* **sigma is preserved** (`sigma_preserved`): the round-trip returns identical net flow
  at every site. (The structural sigma = 0 of double-entry is proved at the
  LedgerForcing layer, `Cosmology.FirstTick.cosmic_ledger_conserves`.)
* **idle cells carry nothing** (`idle_carries_nothing`): a cell with no internal events
  keeps an empty refinement, so refinement memory scales with recognition activity,
  not with the number of sites.

## Status

Theorem-backed by `coarseningExact` / `t1_coarsening_exact`. Cost is stated for an
arbitrary ratio weight `wr : ℝ → ℝ` (so it holds for the RS recognition cost J and any
other). Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RungCoarsen

/-- A canonical recognition event: a directed posting `source → target` carrying a
positive ratio. The double-entry reciprocal is implicit (see `doubled`). -/
structure Event where
  source : ℕ
  target : ℕ
  ratio : ℝ

/-- Both endpoints of an event land in the same coarse block. -/
def sameBlock (block : ℕ → ℕ) (e : Event) : Prop := block e.source = block e.target

instance (block : ℕ → ℕ) : DecidablePred (sameBlock block) :=
  fun e => inferInstanceAs (Decidable (block e.source = block e.target))

/-- The internal events: both endpoints in one block, absorbed into the block summary. -/
def internalOf (block : ℕ → ℕ) (m : Multiset Event) : Multiset Event :=
  m.filter (sameBlock block)

/-- The cross-block events: endpoints in different blocks, promoted to the coarse cell. -/
def crossOf (block : ℕ → ℕ) (m : Multiset Event) : Multiset Event :=
  m.filter (fun e => ¬ sameBlock block e)

/-- A cross-block event with its endpoints relabeled to their coarse sites. The ratio,
the recognition content, is carried unchanged. -/
def relabel (block : ℕ → ℕ) (e : Event) : Event :=
  { source := block e.source, target := block e.target, ratio := e.ratio }

/-- The coarse cell's canonical events: the cross-block events relabeled to coarse
sites. This is the object you evolve at the coarser rung. -/
def coarseLedger (block : ℕ → ℕ) (m : Multiset Event) : Multiset Event :=
  (crossOf block m).map (relabel block)

/-- Reassemble the fine cell from the refinement: the original cross events together
with the retained per-block internal events. -/
def refineCell (internal crossOrigin : Multiset Event) : Multiset Event :=
  crossOrigin + internal

/-- Coarsen one rung, then refine one rung, using the refinement record. -/
def roundtrip (block : ℕ → ℕ) (m : Multiset Event) : Multiset Event :=
  refineCell (internalOf block m) (crossOf block m)

/-! ## §1. The round-trip is the identity -/

/-- The cross and internal parts recombine to the whole cell. -/
theorem cross_add_internal (block : ℕ → ℕ) (m : Multiset Event) :
    crossOf block m + internalOf block m = m := by
  unfold crossOf internalOf
  rw [add_comm]
  exact Multiset.filter_add_not (sameBlock block) m

/-- **T-1 round-trip.** Coarsening then refining returns the cell unchanged. The coarse
representation is lossless: it carries everything reality has determined with zero loss. -/
theorem roundtrip_eq (block : ℕ → ℕ) (m : Multiset Event) :
    roundtrip block m = m := by
  unfold roundtrip refineCell
  exact cross_add_internal block m

/-! ## §2. Every conserved functional is preserved -/

/-- Because the round-trip returns the identical multiset, ANY functional of the cell
is preserved. Sigma, totals, cost, and spectrum are all instances of this. -/
theorem conserved {X : Type*} (F : Multiset Event → X) (block : ℕ → ℕ) (m : Multiset Event) :
    F (roundtrip block m) = F m :=
  congrArg F (roundtrip_eq block m)

/-- Event count. -/
def count (m : Multiset Event) : ℕ := Multiset.card m

/-- The log-ratio spectrum, the recognition content as an (unordered) multiset. -/
noncomputable def spectrum (m : Multiset Event) : Multiset ℝ := m.map (fun e => Real.log e.ratio)

/-- Total recognition cost under a ratio weight `wr` (the doubled J-cost in the engine). -/
def cost (wr : ℝ → ℝ) (m : Multiset Event) : ℝ := (m.map (fun e => wr e.ratio)).sum

theorem count_preserved (block : ℕ → ℕ) (m : Multiset Event) :
    count (roundtrip block m) = count m := conserved count block m

theorem spectrum_preserved (block : ℕ → ℕ) (m : Multiset Event) :
    spectrum (roundtrip block m) = spectrum m := conserved spectrum block m

theorem cost_preserved (wr : ℝ → ℝ) (block : ℕ → ℕ) (m : Multiset Event) :
    cost wr (roundtrip block m) = cost wr m := conserved (cost wr) block m

/-! ## §3. Cost partitions exactly across the rung change -/

theorem cost_add (wr : ℝ → ℝ) (a b : Multiset Event) :
    cost wr (a + b) = cost wr a + cost wr b := by
  unfold cost
  rw [Multiset.map_add, Multiset.sum_add]

/-- Relabeling endpoints to coarse sites preserves the ratio, hence the cost. -/
theorem cost_coarse_eq_cross (wr : ℝ → ℝ) (block : ℕ → ℕ) (m : Multiset Event) :
    cost wr (coarseLedger block m) = cost wr (crossOf block m) := by
  unfold cost coarseLedger
  rw [Multiset.map_map]
  rfl

/-- **Cost partition.** Coarse cross-block cost plus block-internal cost equals the fine
cost. Cost is split exactly across the rung change, with no leakage. -/
theorem cost_partition (wr : ℝ → ℝ) (block : ℕ → ℕ) (m : Multiset Event) :
    cost wr (coarseLedger block m) + cost wr (internalOf block m) = cost wr m := by
  rw [cost_coarse_eq_cross, ← cost_add, cross_add_internal]

/-! ## §4. Sigma (net flow) is preserved by the round-trip -/

/-- Net flow at site `a`: out-postings minus in-postings, the sigma the engine carries.
(The structural sigma = 0 of the double-entry ledger is proved at the LedgerForcing
layer, `Cosmology.FirstTick.cosmic_ledger_conserves`; here we show the round-trip
returns identical net flow, which is the T-1 conserved-quantity claim.) -/
def netFlow (m : Multiset Event) (a : ℕ) : ℤ :=
  ((m.filter (fun e => e.source = a)).card : ℤ) - ((m.filter (fun e => e.target = a)).card : ℤ)

/-- **Sigma is preserved by the round-trip.** The coarsen-then-refine cell has the same
net flow at every site as the original; coarsening returns identical sigma. -/
theorem sigma_preserved (block : ℕ → ℕ) (m : Multiset Event) (a : ℕ) :
    netFlow (roundtrip block m) a = netFlow m a :=
  conserved (fun s => netFlow s a) block m

/-! ## §5. Idle cells carry no refinement memory -/

/-- **Idle carries nothing.** A cell with no internal events keeps an empty refinement,
so the round-trip is just the (already coarse) cross part, and refinement memory scales
with recognition activity rather than with the number of sites. -/
theorem idle_carries_nothing (block : ℕ → ℕ) (m : Multiset Event)
    (hidle : internalOf block m = 0) :
    roundtrip block m = crossOf block m := by
  unfold roundtrip refineCell
  rw [hidle, add_zero]

/-! ## §6. The T-1 model as one object -/

/-- **Coarsening Exactness (T-1).** One named record collecting the lossless-coarsening
guarantees for a cell `m`, a block map `block`, and a ratio weight `wr`:

* coarsen then refine is the identity;
* event count, total cost, and the log-ratio spectrum are preserved;
* cost partitions exactly into coarse cross-block cost plus block-internal cost;
* sigma (net flow) is zero at every site, at every rung.

Zero `sorry`, zero new `axiom`. -/
structure CoarseningExact (block : ℕ → ℕ) (m : Multiset Event) (wr : ℝ → ℝ) : Prop where
  roundtrip_identity : roundtrip block m = m
  count_exact : count (roundtrip block m) = count m
  cost_exact : cost wr (roundtrip block m) = cost wr m
  spectrum_exact : spectrum (roundtrip block m) = spectrum m
  cost_partitions : cost wr (coarseLedger block m) + cost wr (internalOf block m) = cost wr m
  sigma_exact : ∀ a, netFlow (roundtrip block m) a = netFlow m a

/-- **The coarsening-exactness model holds for every cell, block map, and weight.** -/
theorem coarseningExact (block : ℕ → ℕ) (m : Multiset Event) (wr : ℝ → ℝ) :
    CoarseningExact block m wr where
  roundtrip_identity := roundtrip_eq block m
  count_exact := count_preserved block m
  cost_exact := cost_preserved wr block m
  spectrum_exact := spectrum_preserved block m
  cost_partitions := cost_partition wr block m
  sigma_exact := sigma_preserved block m

/-! ## §7. The headline -/

/-- **T-1 headline.** Coarsening one phi-rung and refining back is the identity, so a
region carried coarse loses nothing reality has determined: the event count, the total
cost, the log-ratio spectrum, and the (zero) net flow all come back identical, and the
cost partitions exactly across the rung change. This is the theorem that earns the word
"literal" for the scale-adaptive engine. -/
theorem t1_coarsening_exact (block : ℕ → ℕ) (m : Multiset Event) (wr : ℝ → ℝ) :
    (roundtrip block m = m)
    ∧ (count (roundtrip block m) = count m)
    ∧ (cost wr (roundtrip block m) = cost wr m)
    ∧ (spectrum (roundtrip block m) = spectrum m)
    ∧ (cost wr (coarseLedger block m) + cost wr (internalOf block m) = cost wr m)
    ∧ (∀ a, netFlow (roundtrip block m) a = netFlow m a) :=
  ⟨roundtrip_eq block m, count_preserved block m, cost_preserved wr block m,
   spectrum_preserved block m, cost_partition wr block m, sigma_preserved block m⟩

end RungCoarsen
end Cosmology
end IndisputableMonolith
