import IndisputableMonolith.Gravity.SevenGaps.Gap2KindRule

/-!
# Gap 2, fourth arc: does the dual-entry lattice force the counts-only premise?

The third arc (`Gap2KindRule`) named the premise the posting-cost derivation needs:
`ChargesCountsOnly`, that a letter's charge is a function of the three cell counts and the
letter's kind.  It left one question open and flagged it `lattice_forces_premise := false`:
whether the dual-entry lattice itself, one layer below `LetterCost`, forces that premise.  This
module answers it.

**The committed answer is no, twice over, and the second floor is the one that was not seen
coming.**  The lattice's charge is not a free real per letter; it is the strain of a
`DualEntryStrainState`, which is `phi * mag`: an integer column imbalance `phi = debit - credit`
capped at one quantum by `flux_unit`, times a nonnegative real magnitude `mag` that nothing in
the structure constrains.  So "the lattice" is two lattices, and the premise fails on each.

* **The magnitude floor.**  `mag` is an arbitrary nonnegative real per letter, so the strain
  `phi * mag` is not even required to be an integer, and it can exceed the flux quantum:
  `magReadsIncidenceLattice` gives a proper edge magnitude `2` and a loop edge magnitude `1`,
  so with block-constant imbalances the strain reads incidence through the magnitude
  (`magReadsIncidenceLattice_strain_edge`, strain `2` on a proper edge).  What the referee
  correctly insisted on, and what is now stated: this shows the magnitude factor is free to
  read incidence, and it shows the strain is not capped by the flux quantum; it does NOT show a
  non-integer strain, because `1` and `2` are integers, and the witness is not offered as one.

* **The flux floor.**  Even with every magnitude pinned to one, so the strain equals the
  integer imbalance `phi` and lies in `{-1, 0, +1}` per letter, `phi` may still read incidence:
  `incidencePhiLattice` puts a unit imbalance on exactly the proper edge letters, which is
  equivariant, not counts-only, and its induced letter cost is exactly the second arc's escape
  cost `incidenceCost 1`.  So the flux cap bounds the *imbalance*, not what the imbalance
  reads; and it bounds the strain only when the magnitude is also pinned, which the structure
  does not do.

The honest named premise is therefore a conjunction, `LatticeChargesCountsOnly`: counts-only
imbalances AND counts-only magnitudes.  The two conjuncts are independent in substance, both
directions exhibited (`dual_premise_conjuncts_independent`): `incidencePhiLattice` has
counts-only magnitudes (all one) and a not counts-only imbalance, and `magReadsIncidenceLattice`
has counts-only imbalances (every edge letter imbalance `+1`) and a magnitude that reads
incidence.  What the lattice structure forces, as a theorem, is `flux_unit`
(`lattice_forces_flux_unit`): a per-letter cap of one quantum on the integer imbalance.  Said
exactly, that is the Lean content; the English gloss that this is "all" the structure forces
and that it is "silent" on incidence is a reading, and is flagged as such in §4 rather than
stated as a theorem.  It is a cap on the imbalance, not on the strain, and not a bound on the
magnitude factor.

## What this settles and what it does not

It settles that the counts-only premise is not a theorem of the dual-entry structure; it is an
additional physical assumption, now stated at the layer where the charge actually lives.  The
successor question, one layer down again, is whether anything in the ledger's *dynamics* (the
posting rules that produce these states, not the state type) forces counts-only imbalances and
magnitudes.  That is a question about `LedgerPostingAdjacency` and the posting run, not about
the state space, and it is flagged open in the index.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LatticeKindRule

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation Gap2KindRule
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## §1. The lattice charge is a strain, and a lattice cost factors through it -/

/-- A **lattice cost** assigns a dual-entry strain state to each complex's posting alphabet and
reads the charge as the strain.  This is the cost notion one layer below `LetterCost`: rather
than a free real per letter, a letter carries an integer imbalance and a real magnitude, and
the charge is their product.  The third arc's `letter_cost_is_silent_on_the_state_space` said a
`LetterCost` takes no state; a lattice cost is precisely the state-bearing carrier that theorem
left room for. -/
structure LatticeCost where
  charge : ∀ (B : ℕ) (K : BoundedComplex B), DualEntryStrainState (PostingAlphabet K)

namespace LatticeCost

variable (lc : LatticeCost)

/-- The per-letter strain, the actual charge. -/
def strain (B : ℕ) (K : BoundedComplex B) (a : PostingAlphabet K) : ℝ :=
  (lc.charge B K).strain a

/-- The induced letter cost, forgetting the lattice structure. -/
def toLetterCost : LetterCost := fun B K a => lc.strain B K a

end LatticeCost

/-! ## §2. Floor one: the magnitude is unconstrained, and can read the count or incidence -/

/-- **The count-reading-magnitude witness.**  Each vertex letter carries a unit debit
(imbalance `+1`) and a magnitude equal to the vertex count; edge and tet letters carry zero.
Said plainly, this does NOT fail `ChargesCountsOnly`: the strain at a vertex letter is the
vertex count, which is a function of the counts, so the induced letter cost is counts-only and
this is not a countermodel to the third arc's premise.  Nor is it an independence witness for
the dual premise: its magnitude `nV` is counts-only, so it satisfies BOTH halves of
`LatticeChargesCountsOnly`.  Its only role is the observation that the magnitude factor is free
to read the count; the incidence-reading magnitude that does the independence work is
`magReadsIncidenceLattice`, and the countermodel to the third arc's premise is
`incidencePhiLattice`, in §3. -/
def pairMagLattice : LatticeCost where
  charge := fun _B K =>
    { debit := fun a => match a with
        | Sum.inl _ => 1
        | Sum.inr _ => 0
      credit := fun _ => 0
      mag := fun a => match a with
        | Sum.inl _ => (K.nV : ℝ)
        | Sum.inr _ => 0
      mag_nonneg := fun a => by
        cases a with
        | inl v => exact Nat.cast_nonneg K.nV
        | inr rest => exact le_rfl
      flux_unit := fun a => by
        cases a with
        | inl v => simp
        | inr rest => simp }

/-- The strain of `pairMagLattice` at a vertex letter is the vertex count. -/
theorem pairMagLattice_strain_vertex (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    pairMagLattice.strain B K (Sum.inl v) = (K.nV : ℝ) := by
  simp [LatticeCost.strain, pairMagLattice, DualEntryStrainState.strain,
    DualEntryStrainState.phi]

/-- **THEOREM (the magnitude at a vertex letter is the vertex count).**  The Lean content is
exactly the `rfl` shown: `mag (Sum.inl v) = (K.nV : ℝ)`.  It does not, by itself, prove that
the imbalances are counts-only (they are, but that is a separate fact), that the magnitude is
non-constant across complexes (no second complex is mentioned), or that the dual premise must
pin the magnitude (that is a design conclusion, not a theorem).  What it exhibits is the
building block of those facts: the magnitude factor at a vertex letter is the vertex count,
which is a count and therefore permitted by a counts-only premise.  The count-reading-magnitude
observation is used in `lattice_does_not_force_counts_only`; the magnitude-reading-incidence
witness that does the independence work is `magReadsIncidenceLattice`. -/
theorem pairMagLattice_mag_reads_count (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    (pairMagLattice.charge B K).mag (Sum.inl v) = (K.nV : ℝ) := rfl

/-! ## §3. Floor two: unit flux caps the imbalance, not what the charge reads -/

/-- **The incidence failure, on the lattice, through the imbalance.**  Each proper edge letter
carries a unit debit (imbalance `+1`), every other letter zero, every magnitude one.  The
strain is then the second arc's `incidenceCost 1`, restricted to the lattice: equivariant, not
counts-only, reading the incidence structure at the letter.  Said exactly, its strain takes
values in `{0, +1}` (credit is identically zero, so `-1` is never attained), which is a subset
of the flux range `{-1, 0, +1}` the cap permits.  This is the countermodel the integer flux
was supposed to exclude and does not. -/
def incidencePhiLattice : LatticeCost where
  charge := fun _B K =>
    { debit := fun a => match a with
        | Sum.inr (Sum.inl e) => if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then 1 else 0
        | _ => 0
      credit := fun _ => 0
      mag := fun _ => 1
      mag_nonneg := fun _ => zero_le_one
      flux_unit := fun a => by
        cases a with
        | inl v => simp
        | inr rest =>
          cases rest with
          | inl e =>
            simp only
            by_cases h : (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 <;> simp [h]
          | inr t => simp }

/-- The induced letter cost of `incidencePhiLattice` is exactly `incidenceCost 1`. -/
theorem incidencePhiLattice_toLetterCost_eq :
    incidencePhiLattice.toLetterCost = incidenceCost 1 := by
  funext B K a
  cases a with
  | inl v =>
    simp [LatticeCost.toLetterCost, LatticeCost.strain, incidencePhiLattice,
      DualEntryStrainState.strain, DualEntryStrainState.phi, incidenceCost]
  | inr rest =>
    cases rest with
    | inl e =>
      simp only [LatticeCost.toLetterCost, LatticeCost.strain, incidencePhiLattice,
        DualEntryStrainState.strain, DualEntryStrainState.phi, incidenceCost]
      by_cases h : (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 <;> simp [h]
    | inr t =>
      simp [LatticeCost.toLetterCost, LatticeCost.strain, incidencePhiLattice,
        DualEntryStrainState.strain, DualEntryStrainState.phi, incidenceCost]

/-- **THEOREM (the flux floor).**  `incidencePhiLattice` has every letter on the integer-flux
lattice with magnitude one, so its strain is an honest integer imbalance in `{-1, 0, +1}`, and
it is not counts-only: its induced letter cost is the incidence cost, which the third arc
proved fails `ChargesCountsOnly`.  So unit flux caps the size of a letter's charge and is
silent on what the charge reads. -/
theorem incidencePhiLattice_not_countsOnly :
    ¬ ChargesCountsOnly (incidencePhiLattice.toLetterCost) := by
  rw [incidencePhiLattice_toLetterCost_eq]
  exact chargesCountsOnly_excludes_incidence 1 one_ne_zero

/-- **THEOREM (the lattice does not force the counts-only premise).**  A lattice cost on the
integer-flux lattice whose imbalance reads incidence, so the induced letter cost is not
counts-only.  The first conjunct alone settles the English claim; the second is kept only as a
pointer to the structural fact (the magnitude is free to read the count) and does no work toward
the conclusion, which is why it is stated as a conjunction with an explicit note rather than
left to look load-bearing.  `ChargesCountsOnly` of the induced letter cost is an additional
premise, not a theorem of the lattice. -/
theorem lattice_does_not_force_counts_only :
    (∃ lc : LatticeCost, ¬ ChargesCountsOnly lc.toLetterCost)
      ∧ (∀ (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV),
          (pairMagLattice.charge B K).mag (Sum.inl v) = (K.nV : ℝ)) :=
  ⟨⟨incidencePhiLattice, incidencePhiLattice_not_countsOnly⟩,
    fun B K v => pairMagLattice_mag_reads_count B K v⟩

/-! ## §4. The honest named premise is a conjunction, and what the lattice does force -/

/-- **The dual named premise.**  A lattice charge is counts-only when BOTH its imbalance and
its magnitude are counts-only functions of the letter's kind.  Said carefully, this is a
*stronger sufficient condition* than the third arc's `ChargesCountsOnly` lifted to the lattice
(that lift is `ChargesCountsOnly ∘ toLetterCost`): the product `phi * mag` can be counts-only
while a factor is not, so conjunct-wise counts-only implies but is not implied by counts-only
strain.  The two conjuncts are independent in substance, both directions exhibited in
`dual_premise_conjuncts_independent`: `incidencePhiLattice` satisfies the magnitude half (all
magnitudes one) and fails the imbalance half, and `magReadsIncidenceLattice` satisfies the
imbalance half (every edge imbalance `+1`) while its magnitude reads incidence.  `pairMagLattice`
is NOT an independence witness: its magnitude `nV` is counts-only, so it satisfies both halves. -/
def LatticeChargesCountsOnly (lc : LatticeCost) : Prop :=
  (∃ fV fE fT : ℕ → ℕ → ℕ → ℤ, ∀ (B : ℕ) (K : BoundedComplex B),
      (∀ v : Fin K.nV, (lc.charge B K).phi (Sum.inl v) = fV K.nV K.nE K.nT)
        ∧ (∀ e : Fin K.nE, (lc.charge B K).phi (Sum.inr (Sum.inl e)) = fE K.nV K.nE K.nT)
        ∧ (∀ τ : Fin K.nT, (lc.charge B K).phi (Sum.inr (Sum.inr τ)) = fT K.nV K.nE K.nT))
    ∧ (∃ gV gE gT : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B),
      (∀ v : Fin K.nV, (lc.charge B K).mag (Sum.inl v) = gV K.nV K.nE K.nT)
        ∧ (∀ e : Fin K.nE, (lc.charge B K).mag (Sum.inr (Sum.inl e)) = gE K.nV K.nE K.nT)
        ∧ (∀ τ : Fin K.nT, (lc.charge B K).mag (Sum.inr (Sum.inr τ)) = gT K.nV K.nE K.nT))

/-- **THEOREM (the lattice forces the flux cap).**  Every lattice cost has every letter's
imbalance capped at one quantum in absolute value.  That is the entire Lean content: the
statement is a projection of the structure field `flux_unit`, and it proves `|phi| ≤ 1` and
nothing more.  The English gloss that this is "the whole of" what the structure forces, and
that it is "silent" on incidence, index, and count-dependence, is a reading the theorem does
not carry (a type cannot prove a universal about all its own consequences), so it is recorded
here as commentary and not as the theorem.  What is theorem-shaped is the cap itself, and it is
a cap on the integer imbalance, not on the strain and not on the magnitude factor. -/
theorem lattice_forces_flux_unit (lc : LatticeCost) (B : ℕ) (K : BoundedComplex B)
    (a : PostingAlphabet K) :
    |(lc.charge B K).phi a| ≤ 1 :=
  (lc.charge B K).flux_unit a

/-- **The second direction's witness.**  A lattice cost whose imbalances are counts-only
(every edge letter carries imbalance `+1`, vertices and tets `0`) but whose magnitude reads
incidence: a proper edge letter's magnitude is `2` and a loop edge's is `1`.  The strain at an
edge letter is then `2` on a proper edge and `1` on a loop, so the strain reads incidence
through the magnitude while the imbalance is counts-only.  This is the direction
`incidencePhiLattice` does not supply. -/
def magReadsIncidenceLattice : LatticeCost where
  charge := fun _B K =>
    { debit := fun a => match a with
        | Sum.inr (Sum.inl _e) => 1
        | _ => 0
      credit := fun _ => 0
      mag := fun a => match a with
        | Sum.inr (Sum.inl e) => if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then 2 else 1
        | _ => 1
      mag_nonneg := fun a => by
        cases a with
        | inl v => exact zero_le_one
        | inr rest =>
          cases rest with
          | inl e =>
            by_cases h : (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 <;> simp [h]
          | inr t => exact zero_le_one
      flux_unit := fun a => by
        cases a with
        | inl v => simp
        | inr rest =>
          cases rest with
          | inl e => simp
          | inr t => simp }

/-- The strain of `magReadsIncidenceLattice` at an edge letter is `1 * mag`, which is `2` on a
proper edge and `1` on a loop, so the strain reads incidence through the magnitude while the
imbalance is counts-only. -/
theorem magReadsIncidenceLattice_strain_edge (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE) :
    magReadsIncidenceLattice.strain B K (Sum.inr (Sum.inl e))
      = if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then 2 else 1 := by
  simp only [LatticeCost.strain, magReadsIncidenceLattice, DualEntryStrainState.strain,
    DualEntryStrainState.phi]
  by_cases h : (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 <;> simp [h]

/-- **THEOREM (the strain can exceed the flux quantum).**  With `mag` free, the strain at a
proper edge is `1 * 2 = 2`, so the integer-flux cap on the imbalance does not cap the strain at
one quantum.  Said exactly: `2` is an integer, so this is NOT a non-integer strain witness, and
the theorem is not offered as one; what it exhibits is that the strain exceeds the flux cap
because the magnitude is unconstrained.  A genuinely non-integer strain (say `mag = 1/2`) is
equally constructible but is not needed for any claim here, so it is not added.  The earlier
title "need not lie on the integer lattice's values" was false for this witness and is
corrected. -/
theorem magReadsIncidenceLattice_strain_exceeds_flux :
    magReadsIncidenceLattice.strain 2 twoBridges (Sum.inr (Sum.inl ⟨0, by decide⟩)) = 2 := by
  simp only [LatticeCost.strain, magReadsIncidenceLattice, DualEntryStrainState.strain,
    DualEntryStrainState.phi, twoBridges]
  norm_num

/-- **THEOREM (the two conjuncts are independent, both directions).**
Direction one: `incidencePhiLattice` has counts-only magnitudes (all one) and a not
counts-only imbalance.  Direction two: `magReadsIncidenceLattice` has counts-only imbalances
(every edge letter carries imbalance `+1`) and a magnitude that reads incidence.  So neither
half of the dual premise implies the other, and both must be assumed. -/
theorem dual_premise_conjuncts_independent :
    ((∃ gV gE gT : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B),
        (∀ v : Fin K.nV, (incidencePhiLattice.charge B K).mag (Sum.inl v) = gV K.nV K.nE K.nT)
          ∧ (∀ e : Fin K.nE,
              (incidencePhiLattice.charge B K).mag (Sum.inr (Sum.inl e)) = gE K.nV K.nE K.nT)
          ∧ (∀ τ : Fin K.nT,
              (incidencePhiLattice.charge B K).mag (Sum.inr (Sum.inr τ)) = gT K.nV K.nE K.nT))
      ∧ ¬ ChargesCountsOnly (incidencePhiLattice.toLetterCost))
    ∧ ((∃ fV fE fT : ℕ → ℕ → ℕ → ℤ, ∀ (B : ℕ) (K : BoundedComplex B),
        (∀ v : Fin K.nV, (magReadsIncidenceLattice.charge B K).phi (Sum.inl v) = fV K.nV K.nE K.nT)
          ∧ (∀ e : Fin K.nE,
              (magReadsIncidenceLattice.charge B K).phi (Sum.inr (Sum.inl e)) = fE K.nV K.nE K.nT)
          ∧ (∀ τ : Fin K.nT,
              (magReadsIncidenceLattice.charge B K).phi (Sum.inr (Sum.inr τ)) = fT K.nV K.nE K.nT))
      ∧ (magReadsIncidenceLattice.strain 2 twoBridges (Sum.inr (Sum.inl ⟨0, by decide⟩)) = 2
          ∧ magReadsIncidenceLattice.strain 2 twoLoops (Sum.inr (Sum.inl ⟨0, by decide⟩)) = 1)) := by
  refine ⟨⟨⟨fun _ _ _ => 1, fun _ _ _ => 1, fun _ _ _ => 1, fun B K => ⟨?_, ?_, ?_⟩⟩,
    incidencePhiLattice_not_countsOnly⟩,
    ⟨⟨fun _ _ _ => 0, fun _ _ _ => 1, fun _ _ _ => 0, fun B K => ⟨?_, ?_, ?_⟩⟩, ?_, ?_⟩⟩
  · intro v; rfl
  · intro e; rfl
  · intro τ; rfl
  · intro v; simp [DualEntryStrainState.phi, magReadsIncidenceLattice]
  · intro e; simp [DualEntryStrainState.phi, magReadsIncidenceLattice]
  · intro τ; simp [DualEntryStrainState.phi, magReadsIncidenceLattice]
  · exact magReadsIncidenceLattice_strain_exceeds_flux
  · simp only [LatticeCost.strain, magReadsIncidenceLattice, DualEntryStrainState.strain,
      DualEntryStrainState.phi, twoLoops]
    norm_num

/-! ## §5. Navigation index -/

structure LatticeIndex : Type where
  /-- A lattice cost exists whose induced letter cost is not counts-only. -/
  countermodel_on_lattice : Bool
  /-- The magnitude factor is free to read the count even with block-constant integer columns. -/
  mag_reads_count : Bool
  /-- The integer-flux lattice admits an incidence-reading imbalance. -/
  flux_reads_incidence : Bool
  /-- The lattice structure forces the per-letter unit cap on the integer imbalance
  (`lattice_forces_flux_unit`).  The name says "only" as commentary; no theorem proves the
  exclusivity, since a type cannot prove a universal about all its own consequences. -/
  lattice_forces_only_flux : Bool
  /-- The named premise at this layer is a conjunction over imbalance and magnitude. -/
  premise_is_a_conjunction : Bool
  /-- NOT proved, and refuted: that the dual-entry lattice forces the counts-only premise. -/
  lattice_forces_premise : Bool
  /-- NOT proved: the successor, whether the ledger's posting dynamics (the run, not the state
  type) forces counts-only imbalances and magnitudes. -/
  dynamics_forces_premise : Bool

def latticeIndex : LatticeIndex where
  countermodel_on_lattice := true
  mag_reads_count := true
  flux_reads_incidence := true
  lattice_forces_only_flux := true
  premise_is_a_conjunction := true
  lattice_forces_premise := false
  dynamics_forces_premise := false

theorem index_lattice_not_forced : latticeIndex.lattice_forces_premise = false := rfl

theorem index_dynamics_open : latticeIndex.dynamics_forces_premise = false := rfl

end

end Gap2LatticeKindRule
end SevenGaps
end Gravity
end IndisputableMonolith
