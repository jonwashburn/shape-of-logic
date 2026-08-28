import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Loom.LoopSpace
import IndisputableMonolith.Foundation.LinkingNecessity

/-!
# The requirement, derived from the closing of the books

The D=3 requirement (manuscript Axiom R: some probe cycle in the complement of
the recognized locus is not null-homologous there) has stood as the one named
input carrying recognition content beyond the structural layer. This module
derives it from the ledger, in three steps, so that the only remaining input is
the persistence of a completed recognition, a statement with no topology inside.

## The three steps

1. **The books close and blind the poster (walk level, proved).** The ledger's
   record is per-account column totals and nothing else; it retains no order.
   On a closed pass every account balances, debits equal credits axis by axis
   (`balanced_of_closed`, the double-entry conservation law on closed chains),
   and the reversed pass posts the identical record
   (`record_reverse_of_closed`). Hence no function of the poster's own record
   distinguishes the completed act from its reversal (`poster_record_blind`),
   and a reading assigning `n ≠ 0` to the pass and `-n` to its reversal is
   provably not a function of the poster's record (`registration_external`).
   The registered distinction of a completed act, if it survives at all,
   survives outside the books that posted it.

2. **Free deformation cannot change a record (cost level, proved).** A
   `LedgerReading` carries its bookkeeping: recognition-free deformation is
   cost-free (T2) and changing a posted record costs at least one unit
   (no-refund). Deformation-invariance is then a theorem
   (`LedgerReading.deform_invariant`), not an assumed field: the invariance
   clause of the deformation-erasure principle is discharged from the cost
   layer.

3. **Persistence forces the dimension (composition, proved).**
   `PersistedPostedDistinction`: some ledger reading of the completed
   configuration is nonzero, i.e. the completed act remains distinguishable
   from its reversal by something the substrate can post. This implies the
   deformation-erasure principle (`persisted_gives_dep`) and hence `D = 3` in
   every spatial realization (`persistence_forces_D3`), with non-vacuity at
   `D = 3` (`d3_realization_persists`) and erasability everywhere else
   (`persistence_fails_off_three`).

## Honesty

The principle remains a genuine input: the `D = 4` realization with the
everything-deforms kinematics refutes it (`persistence_not_forced`), exactly as
it refutes DEP. What this module changes is the vocabulary and the load: the
invariance half and the externality half of the old principle are now theorems
of the cost layer and of closure, and the irreducible residue is only that a
completed recognition is still a recognition, grounded in MP
(`Recognition.mp_holds`): an act whose completion erases every readable trace
of it is nothing recognizing itself.

Architecture citation discipline: the content-typed topology authority stays on
`PublicSpineLinkingClosure` (D-d3link-proj-20260723); this module consumes the
dual-pair route of `LinkingNecessity` (`dep_forces_D3`).

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RequirementFromLedgerClosure

open IndisputableMonolith.Patterns
open LinkingNecessity
open ClosedFramework
open HierarchyRealization

/-! ## Part 1: the books close, and what survives them (walk level) -/

/-- Debit count along a history: the number of steps at axis `i` made with the
coordinate rising (`false → true`), each step booked at the state it acts on. -/
def upCount {d : ℕ} : Pattern d → List (Fin d) → Fin d → ℕ
  | _, [], _ => 0
  | p, a :: L, i =>
      upCount (Loom.flip p a) L i + (if i = a ∧ p a = false then 1 else 0)

/-- Credit count along a history: the number of steps at axis `i` made with the
coordinate falling (`true → false`). -/
def downCount {d : ℕ} : Pattern d → List (Fin d) → Fin d → ℕ
  | _, [], _ => 0
  | p, a :: L, i =>
      downCount (Loom.flip p a) L i + (if i = a ∧ p a = true then 1 else 0)

/-- The record a pass leaves in its own ledger: per-account column totals,
debits and credits, and nothing else. Entries move tallies; tallies retain no
order. This is the full content of the manuscript's ledger record. -/
def record {d : ℕ} (w : Loom.Walk d) : Fin d → ℕ × ℕ :=
  fun i => (upCount w.start w.steps i, downCount w.start w.steps i)

/-- Each axis is a two-state counter: along any history the net of debits over
credits at axis `i` is the change of that coordinate, `0` or `±1`. -/
theorem net_change {d : ℕ} (p : Pattern d) (L : List (Fin d)) (i : Fin d) :
    (upCount p L i : ℤ) - (downCount p L i : ℤ)
      = (if List.foldl Loom.flip p L i then (1 : ℤ) else 0)
        - (if p i then (1 : ℤ) else 0) := by
  induction L generalizing p with
  | nil => simp [upCount, downCount]
  | cons a L ih =>
    simp only [upCount, downCount, List.foldl_cons]
    push_cast
    rw [show ((upCount (Loom.flip p a) L i : ℤ) + _) - _
        = ((upCount (Loom.flip p a) L i : ℤ) - (downCount (Loom.flip p a) L i : ℤ))
          + ((if i = a ∧ p a = false then (1 : ℤ) else 0)
             - (if i = a ∧ p a = true then (1 : ℤ) else 0)) from by ring]
    rw [ih (Loom.flip p a)]
    by_cases hi : i = a
    · subst hi
      cases hpa : p i <;> simp [Loom.flip, hpa] <;> ring
    · have hf : Loom.flip p a i = p i := by simp [Loom.flip, hi]
      simp [hi, hf]

/-- **The books close.** On a closed pass every account balances: debits equal
credits, axis by axis. This is the double-entry conservation law read on closed
chains, at walk level. -/
theorem balanced_of_closed {d : ℕ} (w : Loom.Walk d) (hw : w.Closed) (i : Fin d) :
    (record w i).1 = (record w i).2 := by
  have h := net_change w.start w.steps i
  have he : List.foldl Loom.flip w.start w.steps = w.start := hw
  rw [he] at h
  simp only [sub_self] at h
  have : (upCount w.start w.steps i : ℤ) = (downCount w.start w.steps i : ℤ) := by
    linarith
  exact_mod_cast this

/-- Every step at axis `i` is a debit or a credit: the columns exhaust the
postings, so the closed-pass gross count per axis is even, matching
`Loom.ClosureBalance.closed_iff_balanced`. -/
theorem upCount_add_downCount {d : ℕ} (p : Pattern d) (L : List (Fin d)) (i : Fin d) :
    upCount p L i + downCount p L i = L.count i := by
  induction L generalizing p with
  | nil => rfl
  | cons a L ih =>
    simp only [upCount, downCount, List.count_cons]
    rw [show upCount (Loom.flip p a) L i + (if i = a ∧ p a = false then 1 else 0)
          + (downCount (Loom.flip p a) L i + (if i = a ∧ p a = true then 1 else 0))
        = (upCount (Loom.flip p a) L i + downCount (Loom.flip p a) L i)
          + ((if i = a ∧ p a = false then 1 else 0)
             + (if i = a ∧ p a = true then 1 else 0)) from by ring]
    rw [ih (Loom.flip p a)]
    by_cases hi : i = a
    · subst hi
      cases hpa : p i <;> simp
    · simp [hi, Ne.symm hi]

/-- The same pass run backwards: it starts where the pass ended and unmakes each
step in reverse order. Every atomic distinction is remade with the opposite
orientation, so debits and credits exchange entry by entry. -/
def reverse {d : ℕ} (w : Loom.Walk d) : Loom.Walk d :=
  ⟨w.endpoint, w.steps.reverse⟩

/-- Flipping an axis twice is the identity. -/
theorem flip_flip {d : ℕ} (p : Pattern d) (a : Fin d) :
    Loom.flip (Loom.flip p a) a = p := by
  funext j
  by_cases h : j = a <;> simp [Loom.flip, h]

/-- Running a history backwards from its endpoint returns to its start. -/
theorem foldl_flip_reverse {d : ℕ} (p : Pattern d) (L : List (Fin d)) :
    List.foldl Loom.flip (List.foldl Loom.flip p L) L.reverse = p := by
  induction L generalizing p with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.foldl_append,
      List.foldl_nil]
    rw [ih (Loom.flip p a), flip_flip]

/-- Debits over a concatenated history split at the junction state. -/
theorem upCount_append {d : ℕ} (p : Pattern d) (L₁ L₂ : List (Fin d)) (i : Fin d) :
    upCount p (L₁ ++ L₂) i
      = upCount p L₁ i + upCount (List.foldl Loom.flip p L₁) L₂ i := by
  induction L₁ generalizing p with
  | nil => simp [upCount]
  | cons a L ih =>
    simp only [List.cons_append, upCount, List.foldl_cons]
    rw [ih (Loom.flip p a)]
    ring

/-- Credits over a concatenated history split at the junction state. -/
theorem downCount_append {d : ℕ} (p : Pattern d) (L₁ L₂ : List (Fin d)) (i : Fin d) :
    downCount p (L₁ ++ L₂) i
      = downCount p L₁ i + downCount (List.foldl Loom.flip p L₁) L₂ i := by
  induction L₁ generalizing p with
  | nil => simp [downCount]
  | cons a L ih =>
    simp only [List.cons_append, downCount, List.foldl_cons]
    rw [ih (Loom.flip p a)]
    ring

/-- The reversed history's debits are the history's credits. -/
theorem upCount_reverse {d : ℕ} (p : Pattern d) (L : List (Fin d)) (i : Fin d) :
    upCount (List.foldl Loom.flip p L) L.reverse i = downCount p L i := by
  induction L generalizing p with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons, List.reverse_cons]
    rw [upCount_append, ih (Loom.flip p a), foldl_flip_reverse]
    simp only [downCount, upCount]
    by_cases hi : i = a
    · subst hi
      cases hpa : p i <;> simp [Loom.flip, hpa]
    · simp [Loom.flip, hi]

/-- The reversed history's credits are the history's debits. -/
theorem downCount_reverse {d : ℕ} (p : Pattern d) (L : List (Fin d)) (i : Fin d) :
    downCount (List.foldl Loom.flip p L) L.reverse i = upCount p L i := by
  induction L generalizing p with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons, List.reverse_cons]
    rw [downCount_append, ih (Loom.flip p a), foldl_flip_reverse]
    simp only [downCount, upCount]
    by_cases hi : i = a
    · subst hi
      cases hpa : p i <;> simp [Loom.flip, hpa]
    · simp [Loom.flip, hi]

/-- **Reversal invisibility.** A closed pass and its reversal leave identical
records: the books both wrote retain nothing that tells the act from its
reversal, which is the exchange of its debit half with its credit half. -/
theorem record_reverse_of_closed {d : ℕ} (w : Loom.Walk d) (hw : w.Closed) :
    record (reverse w) = record w := by
  funext i
  have hu : upCount w.endpoint w.steps.reverse i = downCount w.start w.steps i :=
    upCount_reverse w.start w.steps i
  have hd : downCount w.endpoint w.steps.reverse i = upCount w.start w.steps i :=
    downCount_reverse w.start w.steps i
  have hb := balanced_of_closed w hw i
  simp only [record, reverse] at *
  rw [hu, hd]
  exact Prod.ext (by omega) (by omega)

/-- No reading of the poster's own record distinguishes the completed act from
its reversal. -/
theorem poster_record_blind {d : ℕ} {α : Sort*} (w : Loom.Walk d) (hw : w.Closed)
    (f : (Fin d → ℕ × ℕ) → α) : f (record (reverse w)) = f (record w) := by
  rw [record_reverse_of_closed w hw]

/-- **The registration is external.** A reading that assigns a completed pass
the value `n ≠ 0` and its reversal the value `-n` (the shape of every
orientation-sensitive account, the linking balance included) is provably not a
function of the poster's own record. What survives the closing of the books
survives outside them. -/
theorem registration_external {d : ℕ} (w : Loom.Walk d) (hw : w.Closed)
    (g : (Fin d → ℕ × ℕ) → ℤ) {n : ℤ} (hn : n ≠ 0)
    (hfwd : g (record w) = n) : g (record (reverse w)) ≠ -n := by
  rw [poster_record_blind w hw g, hfwd]
  omega

/-! ## Part 2: free deformation cannot change a record (cost level) -/

/-- A ledger reading of dual-pair configurations, carrying its bookkeeping
rather than assuming its invariance: `deformations_free` is T2 (recognition-free
deformation posts nothing and costs nothing), `record_change_costs` is the
no-refund floor (a transformation that changes a posted record costs at least
one unit), `split_zero` normalizes the erased configuration to balance zero. -/
structure LedgerReading (X : PairKinematics) where
  /-- The posted balance of a configuration. -/
  value : X.Config → ℤ
  /-- The cost of carrying one configuration to another. -/
  cost : X.Config → X.Config → ℝ
  /-- T2: recognition-free deformation is free. -/
  deformations_free : ∀ a b, X.deform a b → cost a b = 0
  /-- No-refund floor: changing a posted record costs at least one unit. -/
  record_change_costs : ∀ a b, X.deform a b → value a ≠ value b → 1 ≤ cost a b
  /-- The split configuration carries balance zero. -/
  split_zero : value X.split = 0

/-- **Free deformation fixes every record.** Invariance under recognition-free
deformation is a theorem of the cost layer, not an assumed field: a free change
of a posted record would cost at least one unit and exactly zero. -/
theorem LedgerReading.deform_invariant {X : PairKinematics} (R : LedgerReading X) :
    ∀ a b, X.deform a b → R.value a = R.value b := by
  intro a b h
  by_contra hne
  have h1 := R.record_change_costs a b h hne
  have h0 := R.deformations_free a b h
  rw [h0] at h1
  linarith

/-- Every ledger reading is a pairing observable: the invariance field of the
old principle is discharged from the cost layer. -/
def LedgerReading.toPairingObservable {X : PairKinematics} (R : LedgerReading X) :
    PairingObservable X :=
  ⟨R.value, R.deform_invariant, R.split_zero⟩

/-! ## Part 3: persistence forces the dimension -/

/-- **Persistence of the posted distinction** (ledger vocabulary, no topology
inside): some ledger reading of the completed configuration is nonzero. By
`registration_external` such a reading is necessarily external to the poster's
own record, and by the sign shape it is exactly what distinguishes the
completed act from its reversal: a balance `b` tells them apart iff `b ≠ -b`
iff `b ≠ 0`. The ground is MP: an act whose completion erases every readable
trace of it is nothing recognizing itself. -/
def PersistedPostedDistinction (X : PairKinematics) : Prop :=
  ∃ R : LedgerReading X, R.value X.pair ≠ 0

/-- Persistence implies the deformation-erasure principle, its invariance half
now carried by the cost layer. -/
theorem persisted_gives_dep (X : PairKinematics) :
    PersistedPostedDistinction X → DeformationErasurePrinciple X :=
  fun ⟨R, h⟩ => ⟨R.toPairingObservable, h⟩

/-- **The requirement, derived.** Persistence of the posted distinction forces
`D = 3` in every spatial realization of the dual pair. -/
theorem persistence_forces_D3 (D : DimensionForcing.Dimension)
    (R : SpatialDualPairRealization D) :
    PersistedPostedDistinction R.kin → D = 3 :=
  fun h => dep_forces_D3 D R (persisted_gives_dep _ h)

/-- Off `D = 3` the persistence principle fails in every realization: there a
completed act is erasable by free deformation, so its distinction does not
survive its own posting. -/
theorem persistence_fails_off_three (D : DimensionForcing.Dimension)
    (hD : D ≠ 3) (R : SpatialDualPairRealization D) :
    ¬ PersistedPostedDistinction R.kin :=
  fun h => hD (persistence_forces_D3 D R h)

/-- Non-vacuity at `D = 3`: the hierarchy's own realization persists, the
winding balance being the reading, at zero deformation cost. -/
theorem d3_realization_persists
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    PersistedPostedDistinction (hierarchySpatialRealization F H).kin := by
  refine ⟨⟨fun c => c, fun _ _ => 0, fun _ _ _ => rfl, ?_, rfl⟩, ?_⟩
  · intro a b hab hne
    exact absurd hab hne
  · show (2 : ℤ) ≠ 0
    norm_num

/-- **Honesty: the principle is a genuine input.** The `D = 4` realization with
the everything-deforms kinematics refutes it, exactly as it refutes DEP: the
structural layer does not force persistence. -/
theorem persistence_not_forced :
    ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      ¬ PersistedPostedDistinction R.kin :=
  ⟨4, fourDimRealization,
    fun h => unlinkedKinematics_refutes_dep (persisted_gives_dep _ h)⟩

/-! ## Certificate -/

/-- The requirement-derivation certificate: every field is a proved theorem of
this module or a re-exported ground. Together they replace the bare topological
requirement with: the books close and blind the poster, free deformation cannot
change a record, and the sole remaining input is that a completed recognition
is still a recognition. -/
structure RequirementDerivationCert : Prop where
  /-- Closed passes balance every account. -/
  books_close :
    ∀ {d : ℕ} (w : Loom.Walk d), w.Closed →
      ∀ i, (record w i).1 = (record w i).2
  /-- A closed pass and its reversal leave identical records. -/
  reversal_blind :
    ∀ {d : ℕ} (w : Loom.Walk d), w.Closed → record (reverse w) = record w
  /-- No orientation-odd nonzero reading is a function of the poster's record. -/
  registration_is_external :
    ∀ {d : ℕ} (w : Loom.Walk d), w.Closed →
      ∀ (g : (Fin d → ℕ × ℕ) → ℤ) (n : ℤ), n ≠ 0 →
        g (record w) = n → g (record (reverse w)) ≠ -n
  /-- Free deformation fixes every ledger reading. -/
  free_deformation_fixes_records :
    ∀ (X : PairKinematics) (R : LedgerReading X) (a b : X.Config),
      X.deform a b → R.value a = R.value b
  /-- Persistence implies the deformation-erasure principle. -/
  persistence_gives_dep :
    ∀ X : PairKinematics,
      PersistedPostedDistinction X → DeformationErasurePrinciple X
  /-- Persistence forces `D = 3` in every spatial realization. -/
  persistence_forces_dimension :
    ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      PersistedPostedDistinction R.kin → D = 3
  /-- The `D = 3` realization persists (non-vacuity). -/
  persistence_realized_at_three :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      PersistedPostedDistinction (hierarchySpatialRealization F H).kin
  /-- Off `D = 3` every realization erases the completed act. -/
  persistence_erasable_off_three :
    ∀ (D : DimensionForcing.Dimension), D ≠ 3 →
      ∀ R : SpatialDualPairRealization D, ¬ PersistedPostedDistinction R.kin
  /-- The principle is a genuine input (the `D = 4` decoy refutes it). -/
  persistence_genuine_input :
    ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      ¬ PersistedPostedDistinction R.kin
  /-- The ground of the principle: nothing cannot recognize itself. -/
  ground_mp : Recognition.MP

/-- The requirement-derivation certificate holds. -/
theorem requirementDerivationCert : RequirementDerivationCert where
  books_close := fun w hw i => balanced_of_closed w hw i
  reversal_blind := fun w hw => record_reverse_of_closed w hw
  registration_is_external := fun w hw g _n hn hfwd =>
    registration_external w hw g hn hfwd
  free_deformation_fixes_records := fun _X R a b h => R.deform_invariant a b h
  persistence_gives_dep := persisted_gives_dep
  persistence_forces_dimension := persistence_forces_D3
  persistence_realized_at_three := d3_realization_persists
  persistence_erasable_off_three := persistence_fails_off_three
  persistence_genuine_input := persistence_not_forced
  ground_mp := Recognition.mp_holds

end RequirementFromLedgerClosure
end Foundation
end IndisputableMonolith
