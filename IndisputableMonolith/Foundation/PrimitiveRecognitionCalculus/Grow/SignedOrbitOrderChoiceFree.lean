import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational

/-!
# Choice-free signed-orbit order foundation

The `SignedOrbit` order in `IntegerRational.lean` is characterized only through the
verifier integer display (`le_iff_toInt_le`, `nonneg_iff_toInt_nonneg`,
`nonnegFlag_eq_true_iff_nonneg`). Those route through `SignedOrbit.toInt : SignedOrbit → ℤ`
and Mathlib's `ℤ` order, which carries `Classical.choice`. So every downstream order rung
(`ratio_le_refl`, ...) inherits choice taint it does not need.

This module re-grounds the order entirely on the δ-orbit `DistinctionNat.toNat` (a finite ℕ
position) via the two already-choice-free bridges:
  * `balanced_iff_toNat_eq` : balanced length is a ℕ-level equality, no `ℤ`;
  * `leq_eq_true_iff` : the structural Boolean flag agrees with the ℕ order.
Both `nonneg z` and `nonnegFlag z = true` collapse to the single ℕ fact
`z.neg.toNat ≤ z.pos.toNat`, after which reflexivity / transitivity / totality /
antisymmetry-to-balanced are pure `omega` over ℕ. No `SignedOrbit.toInt`, no `ℤ`, no choice.

Forced-floor receipt: `#print axioms` of every theorem here is a subset of
`{propext, Quot.sound}`. This is the choice-free base the `ratio_*` ordered-field tower needs.
-/

namespace IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus

/-- Internal nonnegativity collapses to a pure ℕ inequality on δ-orbit positions,
through the choice-free `balanced_iff_toNat_eq` bridge (NOT `nonneg_iff_toInt_nonneg`). -/
theorem nonneg_iff_toNat_le (z : SignedOrbit) :
    SignedOrbit.nonneg z ↔ z.neg.toNat ≤ z.pos.toNat := by
  unfold SignedOrbit.nonneg
  constructor
  · rintro ⟨k, hk⟩
    rw [SignedOrbit.balanced_iff_toNat_eq] at hk
    have hp : (SignedOrbit.ofOrbit k).pos = k := rfl
    have hn : (SignedOrbit.ofOrbit k).neg = DistinctionNat.zero := rfl
    rw [hp, hn, DistinctionNat.toNat_zero] at hk
    omega
  · intro h
    refine ⟨DistinctionNat.ofNat (z.pos.toNat - z.neg.toNat), ?_⟩
    rw [SignedOrbit.balanced_iff_toNat_eq]
    have hp : (SignedOrbit.ofOrbit (DistinctionNat.ofNat (z.pos.toNat - z.neg.toNat))).pos
        = DistinctionNat.ofNat (z.pos.toNat - z.neg.toNat) := rfl
    have hn : (SignedOrbit.ofOrbit (DistinctionNat.ofNat (z.pos.toNat - z.neg.toNat))).neg
        = DistinctionNat.zero := rfl
    rw [hp, hn, DistinctionNat.toNat_zero, DistinctionNat.toNat_ofNat]
    omega

/-- Choice-free restatement of the structural Boolean order's agreement with the ℕ order.
The original `DistinctionNat.leq_eq_true_iff` is choice-TAINTED (its `simp [leq]` proof pulls
`Classical.choice` through a classical `Bool`/`Decidable` simp lemma). Here the same fact is
reproved by bare structural induction on the δ-orbit positions: every step is a constructor
match plus `omega` over ℕ, so the closure stays inside `{propext, Quot.sound}`. -/
theorem leq_eq_true_iff_cf (a b : DistinctionNat) :
    DistinctionNat.leq a b = true ↔ a.toNat ≤ b.toNat := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => exact ⟨fun _ => Nat.le_refl _, fun _ => rfl⟩
      | succ b => exact ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | succ a ih =>
      cases b with
      | zero =>
          constructor
          · intro h
            exact absurd h Bool.false_ne_true
          · intro h
            rw [DistinctionNat.toNat_succ, DistinctionNat.toNat_zero] at h
            exact absurd h (Nat.not_succ_le_zero _)
      | succ b =>
          have hstep : DistinctionNat.leq (DistinctionNat.succ a) (DistinctionNat.succ b)
              = DistinctionNat.leq a b := rfl
          rw [hstep, ih, DistinctionNat.toNat_succ, DistinctionNat.toNat_succ]
          exact Nat.succ_le_succ_iff.symm

/-- The structural nonnegative flag agrees with internal nonnegativity, proved
choice-free via `leq_eq_true_iff_cf` (NOT `nonnegFlag_eq_true_iff_nonneg`, which goes through `ℤ`). -/
theorem nonnegFlag_iff_nonneg_cf (z : SignedOrbit) :
    z.nonnegFlag = true ↔ SignedOrbit.nonneg z := by
  rw [nonneg_iff_toNat_le]
  unfold SignedOrbit.nonnegFlag
  rw [leq_eq_true_iff_cf]

/-- The signed-orbit order, characterized purely at the ℕ-level on δ-orbit positions.
This is the choice-free replacement for `le_iff_toInt_le`. -/
theorem le_iff_toNat_cf (a b : SignedOrbit) :
    SignedOrbit.le a b ↔ b.neg.toNat + a.pos.toNat ≤ b.pos.toNat + a.neg.toNat := by
  unfold SignedOrbit.le
  rw [nonneg_iff_toNat_le]
  have hp : (SignedOrbit.sub b a).pos = b.pos + a.neg := rfl
  have hn : (SignedOrbit.sub b a).neg = b.neg + a.pos := rfl
  rw [hp, hn, DistinctionNat.toNat_add, DistinctionNat.toNat_add]

/-- The order via the structural nonnegative flag of the difference: the choice-free
foundation the `ratio_*` rungs need (replaces the tainted `le_iff_nonnegFlag_sub`). -/
theorem le_iff_nonnegFlag_sub_cf (a b : SignedOrbit) :
    SignedOrbit.le a b ↔ (SignedOrbit.sub b a).nonnegFlag = true := by
  unfold SignedOrbit.le
  rw [nonnegFlag_iff_nonneg_cf]

/-- Reflexivity of the signed-orbit order, choice-free. -/
theorem le_refl_cf (a : SignedOrbit) : SignedOrbit.le a a := by
  rw [le_iff_toNat_cf]; omega

/-- Transitivity, choice-free. -/
theorem le_trans_cf (a b c : SignedOrbit)
    (hab : SignedOrbit.le a b) (hbc : SignedOrbit.le b c) : SignedOrbit.le a c := by
  rw [le_iff_toNat_cf] at hab hbc ⊢; omega

/-- Totality, choice-free. -/
theorem le_total_cf (a b : SignedOrbit) :
    SignedOrbit.le a b ∨ SignedOrbit.le b a := by
  rw [le_iff_toNat_cf, le_iff_toNat_cf]; omega

/-- Antisymmetry up to balanced-length equivalence, choice-free. -/
theorem le_antisymm_balanced_cf (a b : SignedOrbit)
    (hab : SignedOrbit.le a b) (hba : SignedOrbit.le b a) : SignedOrbit.balanced a b := by
  rw [le_iff_toNat_cf] at hab hba
  rw [SignedOrbit.balanced_iff_toNat_eq]
  omega

end IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree
