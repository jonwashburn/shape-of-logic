import IndisputableMonolith.Gravity.SevenGaps.Gap2JDiamondRank
import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingDerivation

/-!
# Gap 2 / C14: the LedgerGenerated fork gate

Pre-registered TRUE/FALSE measurement that decides the tilt fork for flag 8
(`gap2_measure_derived`).  A1.7 (`Gap2LetterCostDichotomy`) closed the bulk-
cancelling fixed-kind-totals class; its escape class is where a nonzero
history cost can still live.  This module asks whether the canonical
recognition cost `jCost` is ledger-generated in the sense frozen below.  The
enumeration harness and SJ spectra are those of C15
(`Gap2JDiamondRank`, `scripts/qg/qg_j_diamond_rank_20260730.py`, receipt
`scripts/qg/out/j_diamond_rank_20260730.json`: 437 classes at cap 4).

## PRE-REGISTERED PREDICATE (MODEL, frozen before enumeration)

**Definition (`LedgerGenerated`).** A letter cost `c` is *ledger-generated*
iff there exist a vertex charge `fV : ℤ → ℝ` and constants `cE cT : ℝ` such
that for every size cap `B`, every bounded complex `K`, and every letter of
`K`:

* a vertex letter `v` is charged `fV (vertexImbalance K v)`, where
  `vertexImbalance K v = indeg K v - outdeg K v` is that letter's own
  double-entry posting row (debits minus credits);
* every edge letter is charged the constant `cE`;
* every top-cell letter is charged the constant `cT`.

In particular the charge of a letter is computed from that letter's own
posting-row data alone.  Forbidden inputs: orbit sums, isomorphism-class
data, and any global census of `K` beyond the letter's own row.  Edge and
top-cell letters are not accounts; their posting row is empty and the charge
is therefore a constant (the null-row value).

This definition is a MODEL choice: it is the gate's admissibility class, not
a derived theorem.  The cap-1-3 decisions below are MEASURED /
kernel-certified against it.

## Decision procedure and outcomes

Kernel-decide `LedgerGenerated (jCost κ)` (any `κ ≠ 0`) and the finite
restrictions `LedgerGeneratedAt cap (jCost 1)` at caps 1, 2, 3.  Tabulate
`historyCost (jCost 1)` on the C15 isomorphism classes at those caps
(exact rationals `SJ / 2`, since `historyCost = imbalanceSq / (2κ)` at
`κ = 1`).

Outcome reading (bank only; do not act beyond this module):

* `FALSE`: `jCost` outside the ledger-conservation class; μ-form closure
  lives; week-two primary becomes C18.
* `TRUE` with `historyCost` identically zero at all three caps: conservation
  forces numerator unity on the ledger class.
* `TRUE` with nonzero `historyCost` at any cap: **C27 hard stop** (the fork
  condition is measured true; the choice itself is reserved for Jon).
  Escalate to Jon.  No tilt construction, no flag move, no launch.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`, with
`native_decide` certificates disclosed as carrying
`Lean.ofReduceBool` / `Lean.trustCompiler`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LedgerGenerated

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation
open Gap2JEhrhartSpan Gap2JDiamondRank Gap2GluingDerivation

variable {B : ℕ}

/-! ## §1. The pre-registered predicate -/

/-- **PRE-REGISTERED (MODEL).**  A letter cost is ledger-generated when each
letter's charge is a fixed function of that letter's own double-entry posting
row (debits minus credits on the letter's account), with edge and top-cell
letters carrying constant null-row values.  No orbit sums, no
isomorphism-class data, no global census. -/
def LedgerGenerated (c : LetterCost) : Prop :=
  ∃ (fV : ℤ → ℝ) (cE cT : ℝ),
    (∀ (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV),
      c B K (Sum.inl v) = fV (vertexImbalance K v))
    ∧ (∀ (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE),
      c B K (Sum.inr (Sum.inl e)) = cE)
    ∧ (∀ (B : ℕ) (K : BoundedComplex B) (t : Fin K.nT),
      c B K (Sum.inr (Sum.inr t)) = cT)

/-- Finite restriction of `LedgerGenerated` to complexes whose three counts
are at most `cap`.  This is the per-cap decision the gate asks for. -/
def LedgerGeneratedAt (cap : ℕ) (c : LetterCost) : Prop :=
  ∃ (fV : ℤ → ℝ) (cE cT : ℝ),
    ∀ (B : ℕ) (K : BoundedComplex B),
      K.nV ≤ cap → K.nE ≤ cap → K.nT ≤ cap →
        (∀ v : Fin K.nV, c B K (Sum.inl v) = fV (vertexImbalance K v))
        ∧ (∀ e : Fin K.nE, c B K (Sum.inr (Sum.inl e)) = cE)
        ∧ (∀ t : Fin K.nT, c B K (Sum.inr (Sum.inr t)) = cT)

theorem LedgerGenerated_implies_at {c : LetterCost} (h : LedgerGenerated c)
    (cap : ℕ) : LedgerGeneratedAt cap c := by
  obtain ⟨fV, cE, cT, hV, hE, hT⟩ := h
  exact ⟨fV, cE, cT, fun B K _ _ _ => ⟨hV B K, hE B K, hT B K⟩⟩

/-! ## §2. Kernel decision: `jCost` is ledger-generated -/

noncomputable section

/-- The vertex charge of `jCost κ`: square of the posting-row net over twice
the Casimir. -/
def jCostVertexCharge (kappa : ℝ) (m : ℤ) : ℝ :=
  (m : ℝ) ^ 2 / (2 * kappa)

/-- **MEASURED / kernel-certified: `LedgerGenerated (jCost κ)` is TRUE** for
every nonzero Casimir.  The witnessing `fV` is `m ↦ m² / (2κ)`; edge and
top-cell null-row values are zero. -/
theorem jCost_ledgerGenerated {kappa : ℝ} (_hk : kappa ≠ 0) :
    LedgerGenerated (jCost kappa) :=
  ⟨jCostVertexCharge kappa, 0, 0, by
    refine ⟨?_, ?_, ?_⟩
    · intro B K v
      simp only [jCost_inl, jCostVertexCharge]
    · intro B K e
      simp only [jCost_edge]
    · intro B K t
      simp only [jCost_tet]⟩

/-- Per-cap decisions at caps 1, 2, 3: all TRUE, by the global certificate. -/
theorem jCost_ledgerGenerated_cap1 :
    LedgerGeneratedAt 1 (jCost 1) :=
  LedgerGenerated_implies_at (jCost_ledgerGenerated (by norm_num : (1 : ℝ) ≠ 0)) 1

theorem jCost_ledgerGenerated_cap2 :
    LedgerGeneratedAt 2 (jCost 1) :=
  LedgerGenerated_implies_at (jCost_ledgerGenerated (by norm_num : (1 : ℝ) ≠ 0)) 2

theorem jCost_ledgerGenerated_cap3 :
    LedgerGeneratedAt 3 (jCost 1) :=
  LedgerGenerated_implies_at (jCost_ledgerGenerated (by norm_num : (1 : ℝ) ≠ 0)) 3

/-- Boolean mirrors of the per-cap decisions (TRUE at every named cap). -/
def jCost_ledgerGenerated_decision_cap1 : Bool := true
def jCost_ledgerGenerated_decision_cap2 : Bool := true
def jCost_ledgerGenerated_decision_cap3 : Bool := true

theorem jCost_ledgerGenerated_decision_cap1_eq :
    jCost_ledgerGenerated_decision_cap1 = true := rfl
theorem jCost_ledgerGenerated_decision_cap2_eq :
    jCost_ledgerGenerated_decision_cap2 = true := rfl
theorem jCost_ledgerGenerated_decision_cap3_eq :
    jCost_ledgerGenerated_decision_cap3 = true := rfl

/-! ## §3. Decoy: a global-census cost is not ledger-generated

A gate that only ever returns TRUE has not been tested.  Charging every vertex
the ambient vertex count reads a global census, so equal posting rows at
different sizes disagree. -/

/-- Decoy cost: every vertex letter is charged the complex's vertex census. -/
def censusVertexCost : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => (K.nV : ℝ)
  | Sum.inr _ => 0

/-- **The predicate discriminates.**  `censusVertexCost` is not ledger-generated:
the point and the two-point dust both have imbalance zero at every vertex, but
they charge 1 and 2 respectively. -/
theorem censusVertexCost_not_ledgerGenerated :
    ¬ LedgerGenerated censusVertexCost := by
  rintro ⟨fV, cE, cT, hV, hE, hT⟩
  have h1 := hV 1 (dust 1) ⟨0, by decide⟩
  have h2 := hV 2 (dust 2) ⟨0, by decide⟩
  have m1 : vertexImbalance (dust 1) (⟨0, by decide⟩ : Fin 1) = 0 := by decide
  have m2 : vertexImbalance (dust 2) (⟨0, by decide⟩ : Fin 2) = 0 := by decide
  simp only [censusVertexCost, dust_nV] at h1 h2
  have eq1 : (1 : ℝ) = fV 0 := by simpa [m1] using h1
  have eq2 : (2 : ℝ) = fV 0 := by simpa [m2] using h2
  linarith

/-! ## §4. historyCost table for `jCost 1` at caps 1–3

`historyCost (jCost 1) B K = (imbalanceSq K : ℝ) / 2`, so the exact rational
is `SJ / 2` with `SJ = imbalanceSq K ∈ ℤ`.  Provenance of the class census:
C15 receipt `scripts/qg/out/j_diamond_rank_20260730.json`. -/

theorem historyCost_jCost_one (B : ℕ) (K : BoundedComplex B) :
    historyCost (jCost 1) B K = (imbalanceSq K : ℝ) / 2 := by
  rw [historyCost_jCost_eq]
  norm_num

/-- Cap-1 loop: the only edge is a self-loop on one vertex. -/
def loop1Complex : BoundedComplex 1 where
  nV := 1
  nE := 1
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun _ => (0, 0)
  tetVerts := fun t => t.elim0

theorem imbalanceSq_point : imbalanceSq pointComplex = 0 := by decide
theorem imbalanceSq_edge : imbalanceSq edgeComplex = 2 := by decide
theorem imbalanceSq_path : imbalanceSq pathComplex = 2 := by decide
theorem imbalanceSq_loop1 : imbalanceSq loop1Complex = 0 := by decide
theorem imbalanceSq_empty_cap1 : imbalanceSq (emptyComplex 1) = 0 := by decide

/-- Native-decide certificates for the integer charges used in the table.
Disclosed axiom footprint on these: `Lean.ofReduceBool`, `Lean.trustCompiler`
on top of the base triple. -/
theorem imbalanceSq_edge_native : imbalanceSq edgeComplex = 2 := by native_decide
theorem imbalanceSq_path_native : imbalanceSq pathComplex = 2 := by native_decide
theorem imbalanceSq_loop1_native : imbalanceSq loop1Complex = 0 := by native_decide
theorem imbalanceSq_loopPoint_native : imbalanceSq loopPointComplex = 0 := by
  native_decide
theorem imbalanceSq_fork_native : imbalanceSq forkComplex = 6 := by native_decide

theorem historyCost_jCost_one_edge :
    historyCost (jCost 1) 4 edgeComplex = (1 : ℝ) := by
  rw [historyCost_edge (1 : ℝ) (by norm_num)]
  norm_num

theorem historyCost_jCost_one_point :
    historyCost (jCost 1) 4 pointComplex = (0 : ℝ) :=
  historyCost_point 1

theorem historyCost_jCost_one_path :
    historyCost (jCost 1) 4 pathComplex = (1 : ℝ) := by
  rw [historyCost_path (1 : ℝ) (by norm_num)]
  norm_num

theorem historyCost_jCost_one_loopPoint :
    historyCost (jCost 1) 4 loopPointComplex = (0 : ℝ) :=
  historyCost_loopPoint 1

theorem historyCost_jCost_one_fork :
    historyCost (jCost 1) 4 forkComplex = (3 : ℝ) := by
  rw [historyCost_fork (1 : ℝ) (by norm_num)]
  norm_num

theorem historyCost_loop1 :
    historyCost (jCost 1) 1 loop1Complex = 0 := by
  rw [historyCost_jCost_one, imbalanceSq_loop1]
  norm_num

theorem historyCost_empty_cap1 :
    historyCost (jCost 1) 1 (emptyComplex 1) = 0 := by
  rw [historyCost_jCost_one, imbalanceSq_empty_cap1]
  norm_num

/-- **Cap 1 historyCost table (exact rationals).**  Every C15 class at cap 1
has `SJ = 0`, hence `historyCost (jCost 1) = 0`. -/
theorem historyCost_table_cap1 :
    historyCost (jCost 1) 1 (emptyComplex 1) = 0
      ∧ historyCost (jCost 1) 4 pointComplex = 0
      ∧ historyCost (jCost 1) 1 loop1Complex = 0 :=
  ⟨historyCost_empty_cap1, historyCost_jCost_one_point, historyCost_loop1⟩

def historyCost_identically_zero_decision_cap1 : Bool := true
theorem historyCost_identically_zero_decision_cap1_eq :
    historyCost_identically_zero_decision_cap1 = true := rfl

/-- **Cap 2: historyCost is NOT identically zero.**  The proper edge has
`historyCost (jCost 1) = 1`. -/
theorem historyCost_not_identically_zero_cap2 :
    historyCost (jCost 1) 4 edgeComplex ≠ 0 := by
  rw [historyCost_jCost_one_edge]
  norm_num

def historyCost_identically_zero_decision_cap2 : Bool := false
theorem historyCost_identically_zero_decision_cap2_eq :
    historyCost_identically_zero_decision_cap2 = false := rfl

/-- **Cap 3: historyCost is NOT identically zero.** -/
theorem historyCost_not_identically_zero_cap3 :
    historyCost (jCost 1) 4 edgeComplex ≠ 0
      ∧ historyCost (jCost 1) 4 pathComplex ≠ 0
      ∧ historyCost (jCost 1) 4 forkComplex ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [historyCost_jCost_one_edge]; norm_num
  · rw [historyCost_jCost_one_path]; norm_num
  · rw [historyCost_jCost_one_fork]; norm_num

def historyCost_identically_zero_decision_cap3 : Bool := false
theorem historyCost_identically_zero_decision_cap3_eq :
    historyCost_identically_zero_decision_cap3 = false := rfl

/-! ## §5. Exact rational historyCost table (witness rows)

Rows are `(nV, nE, SJ, historyCost = SJ/2)` for the named seed complexes that
live at caps ≤ 3.  Full per-class tables at caps 1–3 are MEASURED by
`scripts/qg/qg_ledger_generated_20260730.py` and recorded in
`scripts/qg/out/ledger_generated_20260730.json`. -/

/-- Exact rational history cost of `jCost 1` as `SJ / 2`. -/
def historyCostRational (sj : ℤ) : ℚ := (sj : ℚ) / 2

theorem historyCostRational_edge : historyCostRational 2 = (1 : ℚ) := by
  norm_num [historyCostRational]
theorem historyCostRational_fork : historyCostRational 6 = (3 : ℚ) := by
  norm_num [historyCostRational]
theorem historyCostRational_zero : historyCostRational 0 = (0 : ℚ) := by
  norm_num [historyCostRational]

/-- Seed table: `(nV, nE, SJ, historyCostRational SJ)`. -/
def historyCostSeedTable : List (ℕ × ℕ × ℤ × ℚ) :=
  [(0, 0, 0, 0),
    (1, 0, 0, 0),
    (1, 1, 0, 0),
    (2, 1, 2, 1),
    (2, 1, 0, 0),
    (3, 2, 2, 1),
    (3, 2, 6, 3)]

theorem historyCostSeedTable_length : historyCostSeedTable.length = 7 := rfl

theorem historyCostSeedTable_edge_row :
    (2, 1, 2, (1 : ℚ)) ∈ historyCostSeedTable := by decide

theorem historyCostSeedTable_edge_row_native :
    (2, 1, 2, (1 : ℚ)) ∈ historyCostSeedTable := by native_decide

/-- MEASURED tallies (C15 harness, caps 1–3).  Provenance:
`scripts/qg/out/ledger_generated_20260730.json`. -/
structure CapHistoryTally where
  classes : ℕ
  sjAllZero : Bool
  maxAbsSJ : ℤ
  ledgerGeneratedDecision : Bool

def measuredHistoryCaps : Fin 3 → CapHistoryTally :=
  ![{ classes := 3, sjAllZero := true, maxAbsSJ := 0,
      ledgerGeneratedDecision := true },
    { classes := 13, sjAllZero := false, maxAbsSJ := 8,
      ledgerGeneratedDecision := true },
    { classes := 68, sjAllZero := false, maxAbsSJ := 18,
      ledgerGeneratedDecision := true }]

theorem measured_cap1_zero :
    (measuredHistoryCaps 0).sjAllZero = true
      ∧ (measuredHistoryCaps 0).ledgerGeneratedDecision = true := ⟨rfl, rfl⟩

theorem measured_cap2_nonzero :
    (measuredHistoryCaps 1).sjAllZero = false
      ∧ (measuredHistoryCaps 1).ledgerGeneratedDecision = true := ⟨rfl, rfl⟩

theorem measured_cap3_nonzero :
    (measuredHistoryCaps 2).sjAllZero = false
      ∧ (measuredHistoryCaps 2).ledgerGeneratedDecision = true := ⟨rfl, rfl⟩

/-! ## §6. C27 hard-stop trigger

Pre-registered: TRUE with nonzero historyCost at any cap arms C27. -/

/-- **C27 trigger predicate.**  Ledger-generated at the cap, and history cost
not identically zero there. -/
def C27TriggerAt (cap : ℕ) (c : LetterCost) : Prop :=
  LedgerGeneratedAt cap c
    ∧ ∃ (B : ℕ) (K : BoundedComplex B),
        K.nV ≤ cap ∧ K.nE ≤ cap ∧ K.nT ≤ cap ∧ historyCost c B K ≠ 0

theorem edgeComplex_fits_cap2 :
    edgeComplex.nV ≤ 2 ∧ edgeComplex.nE ≤ 2 ∧ edgeComplex.nT ≤ 2 := by
  native_decide

theorem edgeComplex_fits_cap3 :
    edgeComplex.nV ≤ 3 ∧ edgeComplex.nE ≤ 3 ∧ edgeComplex.nT ≤ 3 := by
  native_decide

/-- **C27 trigger armed at cap 2.** -/
theorem C27_trigger_armed_cap2 : C27TriggerAt 2 (jCost 1) := by
  refine ⟨jCost_ledgerGenerated_cap2, ?_⟩
  refine ⟨4, edgeComplex, edgeComplex_fits_cap2.1, edgeComplex_fits_cap2.2.1,
    edgeComplex_fits_cap2.2.2, historyCost_not_identically_zero_cap2⟩

/-- **C27 trigger armed at cap 3.** -/
theorem C27_trigger_armed_cap3 : C27TriggerAt 3 (jCost 1) := by
  refine ⟨jCost_ledgerGenerated_cap3, ?_⟩
  refine ⟨4, edgeComplex, edgeComplex_fits_cap3.1, edgeComplex_fits_cap3.2.1,
    edgeComplex_fits_cap3.2.2, historyCost_not_identically_zero_cap2⟩

/-- Boolean: C27 hard stop is armed. -/
def C27_hard_stop_armed : Bool := true
theorem C27_hard_stop_armed_eq : C27_hard_stop_armed = true := rfl

/-- Cap 1 seeds do not alone arm C27: ledger-generated, history zero. -/
theorem C27_not_armed_by_cap1_seeds :
    LedgerGeneratedAt 1 (jCost 1)
      ∧ historyCost (jCost 1) 1 (emptyComplex 1) = 0
      ∧ historyCost (jCost 1) 4 pointComplex = 0
      ∧ historyCost (jCost 1) 1 loop1Complex = 0 :=
  ⟨jCost_ledgerGenerated_cap1, historyCost_empty_cap1,
    historyCost_jCost_one_point, historyCost_loop1⟩

/-! ## §7. Verdict -/

/-- **The C14 LedgerGenerated fork verdict.** -/
structure LedgerGeneratedVerdict : Prop where
  predicate_is_model : True
  jCost_is_ledgerGenerated : ∀ kappa : ℝ, kappa ≠ 0 → LedgerGenerated (jCost kappa)
  decisions_cap1_2_3 :
    LedgerGeneratedAt 1 (jCost 1)
      ∧ LedgerGeneratedAt 2 (jCost 1)
      ∧ LedgerGeneratedAt 3 (jCost 1)
  decoy_discriminates : ¬ LedgerGenerated censusVertexCost
  history_cap1_zero :
    historyCost (jCost 1) 1 (emptyComplex 1) = 0
      ∧ historyCost (jCost 1) 4 pointComplex = 0
      ∧ historyCost (jCost 1) 1 loop1Complex = 0
  history_cap2_nonzero : historyCost (jCost 1) 4 edgeComplex ≠ 0
  history_cap3_nonzero : historyCost (jCost 1) 4 forkComplex ≠ 0
  c27_armed_cap2 : C27TriggerAt 2 (jCost 1)
  c27_armed_cap3 : C27TriggerAt 3 (jCost 1)

theorem ledgerGeneratedVerdict : LedgerGeneratedVerdict where
  predicate_is_model := trivial
  jCost_is_ledgerGenerated := fun _ hk => jCost_ledgerGenerated hk
  decisions_cap1_2_3 :=
    ⟨jCost_ledgerGenerated_cap1, jCost_ledgerGenerated_cap2, jCost_ledgerGenerated_cap3⟩
  decoy_discriminates := censusVertexCost_not_ledgerGenerated
  history_cap1_zero := historyCost_table_cap1
  history_cap2_nonzero := historyCost_not_identically_zero_cap2
  history_cap3_nonzero := (historyCost_not_identically_zero_cap3).2.2
  c27_armed_cap2 := C27_trigger_armed_cap2
  c27_armed_cap3 := C27_trigger_armed_cap3

structure LedgerGeneratedIndex : Type where
  ledgerGenerated_jCost : Bool
  history_zero_cap1 : Bool
  history_zero_cap2 : Bool
  history_zero_cap3 : Bool
  c27_hard_stop_armed : Bool
  measure_flag_moved : Bool

def ledgerGeneratedIndex : LedgerGeneratedIndex where
  ledgerGenerated_jCost := true
  history_zero_cap1 := true
  history_zero_cap2 := false
  history_zero_cap3 := false
  c27_hard_stop_armed := true
  measure_flag_moved := false

theorem index_c27_armed : ledgerGeneratedIndex.c27_hard_stop_armed = true := rfl
theorem index_flag_unmoved : ledgerGeneratedIndex.measure_flag_moved = false := rfl
theorem index_jCost_true : ledgerGeneratedIndex.ledgerGenerated_jCost = true := rfl

end

/-! ## Axiom audit -/

#print axioms jCost_ledgerGenerated
#print axioms jCost_ledgerGenerated_cap1
#print axioms jCost_ledgerGenerated_cap2
#print axioms jCost_ledgerGenerated_cap3
#print axioms censusVertexCost_not_ledgerGenerated
#print axioms historyCost_jCost_one
#print axioms imbalanceSq_edge
#print axioms imbalanceSq_edge_native
#print axioms imbalanceSq_loop1_native
#print axioms historyCost_jCost_one_edge
#print axioms historyCost_table_cap1
#print axioms historyCost_not_identically_zero_cap2
#print axioms historyCost_not_identically_zero_cap3
#print axioms C27_trigger_armed_cap2
#print axioms C27_trigger_armed_cap3
#print axioms ledgerGeneratedVerdict
#print axioms historyCostSeedTable_edge_row_native

end Gap2LedgerGenerated
end SevenGaps
end Gravity
end IndisputableMonolith
