import Mathlib

/-!
# Virtue Independence and Minimality

This module proves that the 14 virtue effect signatures are distinct,
non-redundant (removing any breaks the 14-element completeness condition),
and mutually independent (each is absent from the list after its removal).
These are structural/combinatorial properties of the signature catalogue,
not semantic independence of the virtue transforms themselves.

All proofs are explicit - no `native_decide` (which uses compiler-trust axioms).
Only standard foundational axioms (propext, Quot.sound) are used.
-/

namespace IndisputableMonolith.Ethics.Virtues.Independence

/-! ## Effect Categories -/

/-- The four categories of ethical transformation -/
inductive VirtueCategory where
  | Relational    -- Love, Compassion, Sacrifice
  | Systemic      -- Justice, Temperance, Humility
  | Temporal      -- Wisdom, Patience, Prudence
  | Facilitative  -- Forgiveness, Gratitude, Courage, Hope, Creativity
  deriving DecidableEq, Repr

/-- Effect signature: category plus within-category index -/
structure EffectSignature where
  category : VirtueCategory
  index : ℕ
  deriving DecidableEq, Repr

/-! ## The 14 Virtue Signatures -/

def loveSignature : EffectSignature := ⟨.Relational, 0⟩
def compassionSignature : EffectSignature := ⟨.Relational, 1⟩
def sacrificeSignature : EffectSignature := ⟨.Relational, 2⟩
def justiceSignature : EffectSignature := ⟨.Systemic, 0⟩
def temperanceSignature : EffectSignature := ⟨.Systemic, 1⟩
def humilitySignature : EffectSignature := ⟨.Systemic, 2⟩
def wisdomSignature : EffectSignature := ⟨.Temporal, 0⟩
def patienceSignature : EffectSignature := ⟨.Temporal, 1⟩
def prudenceSignature : EffectSignature := ⟨.Temporal, 2⟩
def forgivenessSignature : EffectSignature := ⟨.Facilitative, 0⟩
def gratitudeSignature : EffectSignature := ⟨.Facilitative, 1⟩
def courageSignature : EffectSignature := ⟨.Facilitative, 2⟩
def hopeSignature : EffectSignature := ⟨.Facilitative, 3⟩
def creativitySignature : EffectSignature := ⟨.Facilitative, 4⟩

def allSignatures : List EffectSignature := [
  loveSignature, compassionSignature, sacrificeSignature,
  justiceSignature, temperanceSignature, humilitySignature,
  wisdomSignature, patienceSignature, prudenceSignature,
  forgivenessSignature, gratitudeSignature, courageSignature,
  hopeSignature, creativitySignature
]

theorem allSignatures_length : allSignatures.length = 14 := rfl

/-! ## Category Orthogonality -/

theorem Relational_ne_Systemic : VirtueCategory.Relational ≠ VirtueCategory.Systemic := by
  intro h; cases h

theorem Relational_ne_Temporal : VirtueCategory.Relational ≠ VirtueCategory.Temporal := by
  intro h; cases h

theorem Relational_ne_Facilitative : VirtueCategory.Relational ≠ VirtueCategory.Facilitative := by
  intro h; cases h

theorem Systemic_ne_Temporal : VirtueCategory.Systemic ≠ VirtueCategory.Temporal := by
  intro h; cases h

theorem Systemic_ne_Facilitative : VirtueCategory.Systemic ≠ VirtueCategory.Facilitative := by
  intro h; cases h

theorem Temporal_ne_Facilitative : VirtueCategory.Temporal ≠ VirtueCategory.Facilitative := by
  intro h; cases h

/-! ## Signature Distinctness -/

theorem sig_ne_of_cat_ne {s₁ s₂ : EffectSignature} (h : s₁.category ≠ s₂.category) : s₁ ≠ s₂ := by
  intro heq; apply h; cases heq; rfl

theorem sig_ne_of_idx_ne {s₁ s₂ : EffectSignature}
    (hi : s₁.index ≠ s₂.index) : s₁ ≠ s₂ := by
  intro heq; apply hi; cases heq; rfl

/-! ## All 14 Signatures Are Distinct -/

-- The key insight: we can prove nodup by showing all pairs are distinct,
-- which follows from either different categories or different indices

theorem all_signatures_distinct : allSignatures.Nodup := by
  unfold allSignatures
  -- Use Mathlib's decidability for List.Nodup with DecidableEq
  decide

/-! ## Independence Definitions -/

def SignatureIndependent (sig : EffectSignature) (sigs : List EffectSignature) : Prop :=
  sig ∉ sigs

def SignatureSetMinimal (sigs : List EffectSignature) : Prop :=
  sigs.Nodup

def SignatureSetComplete (sigs : List EffectSignature) : Prop :=
  sigs.length = 14 ∧ sigs.Nodup

/-! ## Core Theorems -/

theorem all_signatures_minimal : SignatureSetMinimal allSignatures :=
  all_signatures_distinct

theorem signatures_complete : SignatureSetComplete allSignatures :=
  ⟨allSignatures_length, all_signatures_distinct⟩

theorem signatures_non_redundant (i : Fin 14) :
    ¬SignatureSetComplete (allSignatures.eraseIdx i) := by
  unfold SignatureSetComplete
  intro ⟨h_len, _⟩
  have h_erased : (allSignatures.eraseIdx i).length = 13 := by
    simp only [List.length_eraseIdx]
    have h1 : allSignatures.length = 14 := rfl
    have h2 : i.val < 14 := i.isLt
    simp only [h1, h2, ↓reduceIte]
  omega

/-! ## Individual Virtue Independence -/

theorem all_virtues_independent (i : Fin 14) :
    SignatureIndependent allSignatures[i] (allSignatures.eraseIdx i) := by
  unfold SignatureIndependent
  have h_nodup := all_signatures_distinct
  have h_len : allSignatures.length = 14 := rfl
  -- Use nodup property: if a appears at position i, it doesn't appear elsewhere
  intro h_mem
  -- h_mem : allSignatures[i] ∈ allSignatures.eraseIdx i
  -- This means there exists j < length - 1 such that (eraseIdx i)[j] = allSignatures[i]
  -- But (eraseIdx i)[j] = allSignatures[k] where k = j if j < i else j + 1
  -- And k ≠ i, so by nodup, allSignatures[k] ≠ allSignatures[i]
  rw [List.mem_iff_getElem] at h_mem
  obtain ⟨j, hj, heq⟩ := h_mem
  have h_erase_len : (allSignatures.eraseIdx i).length = 13 := by
    simp only [List.length_eraseIdx, h_len, i.isLt, ↓reduceIte]
  rw [h_erase_len] at hj
  -- Now heq : (allSignatures.eraseIdx i)[j] = allSignatures[i]
  -- (eraseIdx i)[j] = allSignatures[if j < i then j else j + 1]
  have h_inj := List.nodup_iff_injective_getElem.mp h_nodup
  by_cases h_lt : j < i.val
  · -- k = j < i, so k ≠ i
    have h_ne : j ≠ i.val := Nat.ne_of_lt h_lt
    have h_j_lt : j < allSignatures.length := by omega
    have heq' : allSignatures[j] = allSignatures[i.val] := by
      rw [List.getElem_eraseIdx] at heq
      simp only [h_lt] at heq
      exact heq
    have := @h_inj ⟨j, h_j_lt⟩ ⟨i.val, i.isLt⟩ heq'
    simp only [Fin.mk.injEq] at this
    exact h_ne this
  · -- k = j + 1, and k ≠ i because j ≥ i implies j + 1 > i
    have h_ge : i.val ≤ j := Nat.ge_of_not_lt h_lt
    have h_ne : j + 1 ≠ i.val := by omega
    have h_j1_lt : j + 1 < allSignatures.length := by omega
    have heq' : allSignatures[j + 1] = allSignatures[i.val] := by
      rw [List.getElem_eraseIdx] at heq
      have h_not_lt : ¬(j < i.val) := h_lt
      simp only [h_not_lt] at heq
      exact heq
    have := @h_inj ⟨j + 1, h_j1_lt⟩ ⟨i.val, i.isLt⟩ heq'
    simp only [Fin.mk.injEq] at this
    exact h_ne this

/-! ## Master Theorem -/

theorem virtue_signatures_minimality_complete :
    SignatureSetMinimal allSignatures ∧
    SignatureSetComplete allSignatures ∧
    (∀ i : Fin 14, ¬SignatureSetComplete (allSignatures.eraseIdx i)) :=
  ⟨all_signatures_minimal, signatures_complete, signatures_non_redundant⟩

/-! ## Summary

All proofs use only:
- Standard foundational axioms (propext, Quot.sound)
- Decidability instances (no compiler-trust axioms)
- Explicit structural reasoning

NO `native_decide`, NO HOLES, NO custom axioms.
-/

end IndisputableMonolith.Ethics.Virtues.Independence
