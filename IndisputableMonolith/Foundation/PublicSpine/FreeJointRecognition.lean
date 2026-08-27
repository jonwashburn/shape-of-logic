import IndisputableMonolith.Foundation.CostFromDistinction

/-!
# FreeJointRecognition — off-cert seed-compose prototype

Recognition-compatible binary operations on the free finite join-semilattice
of events (Finset-supported `FreeEvent`).

No law mentions hierarchy level 2. Classification is among a named finite
candidate family; xor/meet style compose is the mandatory fail witness.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace FreeJointRecognition

open CostFromDistinction
open Classical

/-- Free finite event: a finite set of atoms (free join-semilattice carrier). -/
structure FreeEvent (Atom : Type) where
  support : Finset Atom

variable {Atom : Type} [DecidableEq Atom]

instance : ConfigSpace (FreeEvent Atom) where
  emp := ⟨∅⟩
  join a b := ⟨a.support ∪ b.support⟩
  IsConsistent a := a.support = ∅
  Independent a b := Disjoint a.support b.support
  emp_consistent := rfl
  independent_symm := by
    intro a b h
    exact h.symm
  emp_independent := by
    intro a
    simp
  join_comm := by
    intro a b
    cases a; cases b
    simp [Finset.union_comm]
  join_assoc := by
    intro a b c
    cases a; cases b; cases c
    simp [Finset.union_assoc]
  emp_join := by
    intro a
    cases a
    simp
  consistent_of_join_indep := by
    intro a b _ hca hcb
    cases a; cases b
    simp at hca hcb ⊢
    exact ⟨hca, hcb⟩
  inconsistent_of_join_indep_left := by
    intro a b _ hinc hjoin
    apply hinc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxu : x ∈ a.support ∪ b.support := Finset.mem_union.mpr (Or.inl hx)
    simpa [ConfigSpace.join] using
      (Finset.eq_empty_iff_forall_notMem.mp hjoin x hxu)

/-- Canonical recognition-work cost: support cardinality. -/
noncomputable def freeCost : CostFunction (FreeEvent Atom) where
  C := fun a => (a.support.card : ℝ)
  nonneg := fun a => by exact_mod_cast Nat.zero_le a.support.card
  dichotomy := by
    intro a
    constructor
    · intro h
      have hnat : a.support.card = 0 := by exact_mod_cast h
      exact Finset.card_eq_zero.mp hnat
    · intro h
      rw [h]
      simp
  additivity := by
    intro a b hindep
    change ((a.support ∪ b.support).card : ℝ) =
      (a.support.card : ℝ) + (b.support.card : ℝ)
    exact_mod_cast (Finset.card_union_of_disjoint hindep)

/-- Named finite candidate family of binary ops (join + xor/meet-like alts). -/
inductive CandidateOp
  | join
  | meet
  | xor
  | leftProj
  | rightProj
  deriving DecidableEq, Repr

/-- Interpret a candidate as a concrete binary operation on free events. -/
def interp : CandidateOp → FreeEvent Atom → FreeEvent Atom → FreeEvent Atom
  | .join, a, b => ConfigSpace.join a b
  | .meet, a, b => ⟨a.support ∩ b.support⟩
  | .xor, a, b => ⟨symmDiff a.support b.support⟩
  | .leftProj, a, _ => a
  | .rightProj, _, b => b

/-- **Recognition-compatibility** (operational, free model).

1. Independent additivity of recognition-work cost.
2. Extensivity: both inputs' atoms appear in the result (no silent drop).
3. No invention: the result invents no atoms outside the inputs.

Together these force the free join on every pair; they mention no hierarchy
level. -/
def RecognitionCompatible (op : FreeEvent Atom → FreeEvent Atom → FreeEvent Atom) : Prop :=
  (∀ a b : FreeEvent Atom,
      ConfigSpace.Independent a b →
        freeCost.C (op a b) = freeCost.C a + freeCost.C b) ∧
  (∀ a b : FreeEvent Atom,
      a.support ⊆ (op a b).support ∧ b.support ⊆ (op a b).support) ∧
  (∀ a b : FreeEvent Atom,
      (op a b).support ⊆ a.support ∪ b.support)

/-- Join is Recognition-compatible. -/
theorem join_recognitionCompatible :
    RecognitionCompatible (Atom := Atom) (interp .join) := by
  refine ⟨?add, ?ext, ?sub⟩
  · intro a b hindep
    exact freeCost.additivity a b hindep
  · intro a b
    constructor
    · intro x hx; exact Finset.mem_union_left _ hx
    · intro x hx; exact Finset.mem_union_right _ hx
  · intro a b x hx
    simpa [interp, ConfigSpace.join] using hx

/-- Extensivity + no-invention ⇒ the op equals join on every pair. -/
theorem recognitionCompatible_support_eq_union
    (op : FreeEvent Atom → FreeEvent Atom → FreeEvent Atom)
    (h : RecognitionCompatible op) (a b : FreeEvent Atom) :
    (op a b).support = a.support ∪ b.support := by
  apply Finset.Subset.antisymm
  · exact h.2.2 a b
  · intro x hx
    rcases Finset.mem_union.mp hx with hxa | hxb
    · exact (h.2.1 a b).1 hxa
    · exact (h.2.1 a b).2 hxb

/-- Recognition-compatible ops equal `ConfigSpace.join` pointwise. -/
theorem recognitionCompatible_eq_join
    (op : FreeEvent Atom → FreeEvent Atom → FreeEvent Atom)
    (h : RecognitionCompatible op) (a b : FreeEvent Atom) :
    op a b = ConfigSpace.join a b := by
  have hs := recognitionCompatible_support_eq_union op h a b
  cases a with
  | mk sa =>
    cases b with
    | mk sb =>
      change FreeEvent.mk _ = FreeEvent.mk (sa ∪ sb)
      exact congrArg FreeEvent.mk hs

/-! ## Classification among the named candidate family -/

/-- Among the named candidates, Recognition-compatibility forces join
(requires a witness atom so projections/meet/xor can be separated). -/
theorem recog_compatible_ops_on_free_semilattice_eq_join
    [Nonempty Atom]
    (op : CandidateOp) (h : RecognitionCompatible (Atom := Atom) (interp op)) :
    op = .join := by
  let x : Atom := Classical.choice ‹Nonempty Atom›
  let e : FreeEvent Atom := ⟨{x}⟩
  match op with
  | .join => rfl
  | .meet =>
      have hsub := (h.2.1 e ConfigSpace.emp).1
      have hx : x ∈ e.support := by simp [e]
      have hx' : x ∈ (interp .meet e ConfigSpace.emp).support := hsub hx
      simp [interp, ConfigSpace.emp] at hx'
  | .xor =>
      have hsub := (h.2.1 e e).1
      have hx : x ∈ e.support := by simp [e]
      have hx' : x ∈ (interp .xor e e).support := hsub hx
      simp [interp, symmDiff_self] at hx'
  | .leftProj =>
      have hsub := (h.2.1 ConfigSpace.emp e).2
      have hx : x ∈ e.support := by simp [e]
      have hx' : x ∈ (interp .leftProj ConfigSpace.emp e).support := hsub hx
      simp [interp, ConfigSpace.emp] at hx'
  | .rightProj =>
      have hsub := (h.2.1 e ConfigSpace.emp).1
      have hx : x ∈ e.support := by simp [e]
      have hx' : x ∈ (interp .rightProj e ConfigSpace.emp).support := hsub hx
      simp [interp, ConfigSpace.emp] at hx'

/-! ## Mandatory fail witnesses (xor / meet) -/

/-- Concrete two-atom carrier for falsifiers. -/
abbrev Two := Bool

/-- Singleton free events on `Bool`. -/
def atomFalse : FreeEvent Two := ⟨{false}⟩
def atomTrue : FreeEvent Two := ⟨{true}⟩
def bothAtoms : FreeEvent Two := ⟨{false, true}⟩

/-- Xor/symmetric-diff compose fails Recognition-compatibility. -/
theorem xor_not_recognitionCompatible :
    ¬ RecognitionCompatible (Atom := Two) (interp .xor) := by
  intro h
  have hsub := (h.2.1 bothAtoms atomTrue).2
  have ht' : true ∈ (interp .xor bothAtoms atomTrue).support :=
    hsub (by simp [atomTrue])
  -- xor drops the shared atom: result support is `{false}`.
  have hres : (interp .xor bothAtoms atomTrue).support = ({false} : Finset Two) := by
    ext x
    fin_cases x <;> simp [interp, bothAtoms, atomTrue, Finset.mem_symmDiff]
  rw [hres] at ht'
  exact (Finset.notMem_singleton.mpr (by decide : true ≠ false)) ht'

/-- Meet compose fails Recognition-compatibility (additivity on independents). -/
theorem meet_not_recognitionCompatible :
    ¬ RecognitionCompatible (Atom := Two) (interp .meet) := by
  intro h
  have hindep : ConfigSpace.Independent atomFalse atomTrue := by
    change Disjoint atomFalse.support atomTrue.support
    decide
  have hadd := h.1 atomFalse atomTrue hindep
  -- meet of disjoint singletons is empty: cost 0 ≠ 1+1.
  change ((atomFalse.support ∩ atomTrue.support).card : ℝ) =
      (atomFalse.support.card : ℝ) + (atomTrue.support.card : ℝ) at hadd
  simp [atomFalse, atomTrue] at hadd
  norm_num at hadd

/-- Join is the unique Recognition-compatible candidate (on `Two`). -/
theorem unique_recog_compatible_candidate
    (op : CandidateOp)
    (h : RecognitionCompatible (Atom := Two) (interp op)) :
    op = .join :=
  recog_compatible_ops_on_free_semilattice_eq_join (Atom := Two) op h

/-- On disjoint supports, symmDiff equals union. -/
theorem symmDiff_eq_union_of_disjoint
    (a b : Finset Two) (h : Disjoint a b) : symmDiff a b = a ∪ b := by
  ext x
  simp [Finset.mem_symmDiff]
  constructor
  · intro hx
    rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact Or.inl hx
    · exact Or.inr hx
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, fun hb => Finset.disjoint_left.mp h hx hb⟩
    · exact Or.inr ⟨hx, fun ha => Finset.disjoint_left.mp h ha hx⟩

/-- Weak law (additivity alone) accepts xor on independent pairs. -/
theorem xor_preserves_additivity_on_independents
    (a b : FreeEvent Two) (hindep : ConfigSpace.Independent a b) :
    freeCost.C (interp .xor a b) = freeCost.C a + freeCost.C b := by
  have hEq : symmDiff a.support b.support = a.support ∪ b.support :=
    symmDiff_eq_union_of_disjoint a.support b.support hindep
  change ((symmDiff a.support b.support).card : ℝ) =
    (a.support.card : ℝ) + (b.support.card : ℝ)
  rw [hEq]
  exact_mod_cast (Finset.card_union_of_disjoint hindep)

/-- Drop-premise countermodel: xor satisfies the weak (additivity-only) law
on independents, yet fails full Recognition-compatibility. -/
theorem xor_accepted_by_weak_law_fails_full :
    (∀ a b : FreeEvent Two,
        ConfigSpace.Independent a b →
          freeCost.C (interp .xor a b) = freeCost.C a + freeCost.C b) ∧
    ¬ RecognitionCompatible (Atom := Two) (interp .xor) :=
  ⟨xor_preserves_additivity_on_independents, xor_not_recognitionCompatible⟩

end FreeJointRecognition
end PublicSpine
end Foundation
end IndisputableMonolith
