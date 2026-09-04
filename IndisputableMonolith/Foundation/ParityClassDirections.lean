import Mathlib
import IndisputableMonolith.Loom.ClosureBalance

/-!
# The parity class of the cube as a system of directions

A history over `D` distinctions returns to its starting state exactly when every
axis has been flipped an even number of times. So the states a closed pass can
occupy form a *parity class*: the subsets of axes of even cardinality. That class
is handed to us by the closure argument, with no geometry added and no
dimension chosen.

This file reads each state as a direction from the centre of the cube, the flipped
axes pointing negative and the unflipped axes positive, and asks three questions
about the resulting set of directions. None of the three mentions a number.

* **Balanced.** The directions cancel: nothing is left over when they are summed.
* **Equiangular.** No direction is distinguishable from another by its relation
  to the rest: all pairwise inner products agree.
* **Spanning.** The directions reach the whole space: every member is nonzero,
  and no nonzero vector is orthogonal to all of them.

The main result is `balanced_equiangular_spanning_iff_three`: the three hold
together exactly when `D = 3`. An equivalent selector replaces spanning with
**antipodal-freeness** (the set never contains a direction together with its
opposite); that version is `balanced_equiangular_antipodalFree_iff_three`, kept
because `antipodalFree_iff_odd` shows the condition is exactly the oddness of
`D`, a parity condition on the dimension in disguise, which is why spanning is
preferred as the stated hypothesis. Under the spanning form, antipodal-freeness
at three is a corollary (`antipodalFree_three`): axes come out, not in.

Each condition is load-bearing, with a different dimension surviving when it is
dropped, so none is decoration:

| dropped | survivor | why it survives |
| --- | --- | --- |
| balanced | `D = 1` | one nonzero direction spanning the line, equiangular vacuously |
| spanning | `D = 2` | two opposite directions on a line, which cancel and are equiangular |
| equiangular | `D = 4` (and every `D ≥ 4`) | balanced and spanning, but two distinct angles occur |

The isotropy weakening of equiangularity selects nothing: `isotropy_offdiag`
and `isotropy_diag` show the class is a tight frame (spherical 2-design) at
every `D ≥ 3`, with `not_isotropic_two` the boundary case, so the demand that
does the selecting is tightness, not mere isotropy.

At `D = 3` the class has four members at pairwise inner product `-1`, which after
normalising by the common length `√3` is `-1/3`, the tetrahedral angle
`arccos(-1/3)`. Since three is odd, the class contains no opposite pair, so the
eight states of three distinctions are exactly those four axes taken with both
signs. The two signs are the debit and the credit of a single posting: both are
already states of the ledger, so the second slot on each axis is not an added
label.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ParityClassDirections

open Finset
open scoped symmDiff

/-- A state of `D` distinctions: the set of axes flipped away from the base state. -/
abbrev State (D : ℕ) := Finset (Fin D)

/-- The states a closed history can occupy: an even number of flips.
This is the class the closure balance argument hands us. -/
def evenClass (D : ℕ) : Finset (State D) :=
  Finset.univ.filter fun s => s.card % 2 = 0

lemma mem_evenClass {D : ℕ} {s : State D} : s ∈ evenClass D ↔ s.card % 2 = 0 := by
  simp [evenClass]

/-! ### The class is the one closure produces, not one we chose

`Loom.ClosureBalance.closed_iff_balanced` says a history comes home exactly when
every axis is flipped an even number of times. Two consequences pin the class
below without any appeal to geometry: a closed history has even length, and the
states an even-length history can reach are exactly the even-sized sets of
displaced axes. -/

/-- The axes a history leaves displaced from home. -/
def displaced {D : ℕ} (L : List (Fin D)) : State D :=
  Finset.univ.filter fun i => L.count i % 2 = 1

lemma sum_count_eq_length {D : ℕ} (L : List (Fin D)) :
    (∑ i : Fin D, L.count i) = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hsplit : (∑ i : Fin D, (a :: L).count i)
        = (∑ i : Fin D, L.count i) + ∑ i : Fin D, (if i = a then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i = a
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hsplit, ih]
    simp

/-- The number of displaced axes has the parity of the history's length. -/
theorem card_displaced_mod_two {D : ℕ} (L : List (Fin D)) :
    (displaced L).card % 2 = L.length % 2 := by
  classical
  have hcard : (displaced L).card = ∑ i : Fin D, L.count i % 2 := by
    unfold displaced
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : L.count i % 2 = 1
    · simp [h]
    · simp [h]; omega
  calc (displaced L).card % 2 = (∑ i : Fin D, L.count i % 2) % 2 := by rw [hcard]
    _ = (∑ i : Fin D, L.count i) % 2 := (Finset.sum_nat_mod Finset.univ 2 _).symm
    _ = L.length % 2 := by rw [sum_count_eq_length]

/-- **A closed history has even length.** Every axis is flipped evenly, and the
length is the sum of those counts. -/
theorem closed_length_even {D : ℕ} (w : Loom.Walk D) (h : w.Closed) :
    w.steps.length % 2 = 0 := by
  have hbal := (Loom.ClosureBalance.closed_iff_balanced w).mp h
  have hz : ∀ i : Fin D, w.steps.count i % 2 = 0 := fun i => Nat.even_iff.mp (hbal i)
  calc w.steps.length % 2 = (∑ i : Fin D, w.steps.count i) % 2 := by rw [sum_count_eq_length]
    _ = (∑ i : Fin D, w.steps.count i % 2) % 2 := Finset.sum_nat_mod Finset.univ 2 _
    _ = 0 := by simp [hz]

/-- An even-length history displaces an even number of axes. -/
theorem displaced_mem_evenClass {D : ℕ} {L : List (Fin D)} (h : L.length % 2 = 0) :
    displaced L ∈ evenClass D := by
  rw [mem_evenClass, card_displaced_mod_two]; exact h

/-- Every member of the class is reached by some even-length history, so the
class is not larger than what closure produces. -/
theorem exists_even_history {D : ℕ} {S : State D} (h : S ∈ evenClass D) :
    ∃ L : List (Fin D), L.length % 2 = 0 ∧ displaced L = S := by
  classical
  refine ⟨S.toList, ?_, ?_⟩
  · rw [Finset.length_toList]; exact mem_evenClass.mp h
  · have hnd : S.toList.Nodup := Finset.nodup_toList S
    ext i
    simp only [displaced, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S
    · rw [List.count_eq_one_of_mem hnd (Finset.mem_toList.mpr hi)]
      simp [hi]
    · rw [List.count_eq_zero_of_not_mem (fun hc => hi (Finset.mem_toList.mp hc))]
      simp [hi]

/-- Reading a state as a direction from the centre of the cube: a flipped axis
points negative, an unflipped axis positive. Every entry is `±1`, so all
directions have the same length and the reading privileges none of them. -/
def dir {D : ℕ} (s : State D) : Fin D → ℤ := fun i => if i ∈ s then -1 else 1

/-- Unnormalised inner product of two directions. Dividing by `D` gives the
cosine of the angle between them. -/
def ip {D : ℕ} (s t : State D) : ℤ := ∑ i, dir s i * dir t i

/-! ## The inner product counts disagreements -/

lemma filter_mem_univ {D : ℕ} (A : State D) :
    (Finset.univ.filter fun i => i ∈ A) = A := by
  ext i; simp

lemma sum_pm {D : ℕ} (A : State D) :
    (∑ i : Fin D, (if i ∈ A then (-1 : ℤ) else 1)) = (D : ℤ) - 2 * A.card := by
  classical
  have key : ∀ i : Fin D, (if i ∈ A then (-1 : ℤ) else 1)
      = 1 - 2 * (if i ∈ A then (1 : ℤ) else 0) := by
    intro i; by_cases h : i ∈ A <;> simp [h]
  calc (∑ i : Fin D, (if i ∈ A then (-1 : ℤ) else 1))
      = ∑ i : Fin D, ((1 : ℤ) - 2 * (if i ∈ A then (1 : ℤ) else 0)) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = (∑ _i : Fin D, (1 : ℤ)) - 2 * ∑ i : Fin D, (if i ∈ A then (1 : ℤ) else 0) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (D : ℤ) - 2 * A.card := by
        simp

lemma dir_mul_dir {D : ℕ} (s t : State D) (i : Fin D) :
    dir s i * dir t i = if i ∈ s ∆ t then (-1 : ℤ) else 1 := by
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [dir, Finset.mem_symmDiff, hs, ht]

/-- The inner product of two directions is the number of axes they agree on
minus the number they disagree on. -/
theorem ip_eq {D : ℕ} (s t : State D) :
    ip s t = (D : ℤ) - 2 * ((s ∆ t).card : ℤ) := by
  classical
  unfold ip
  rw [Finset.sum_congr rfl fun i _ => dir_mul_dir s t i, sum_pm]

/-- Every direction has the same length: the reading introduces no scale. -/
theorem ip_self {D : ℕ} (s : State D) : ip s s = (D : ℤ) := by
  simp [ip_eq]

/-! ## The three conditions -/

/-- The directions cancel. -/
def Balanced (D : ℕ) : Prop := ∀ i : Fin D, (∑ s ∈ evenClass D, dir s i) = 0

/-- No direction is distinguishable from another: every pair of distinct
directions subtends the same angle. -/
def Equiangular (D : ℕ) : Prop :=
  ∀ s ∈ evenClass D, ∀ t ∈ evenClass D, s ≠ t →
    ∀ u ∈ evenClass D, ∀ v ∈ evenClass D, u ≠ v → ip s t = ip u v

/-- The set names axes, not signed directions: no direction appears together
with its opposite. -/
def AntipodalFree (D : ℕ) : Prop :=
  ∀ s ∈ evenClass D, ∀ t ∈ evenClass D, dir s ≠ -dir t

/-- The directions reach the whole space: every member is nonzero, and the only
vector orthogonal to all of them is zero. Over `ℚ` the second clause is exactly
the statement that the class spans `ℚ^D`. -/
def Spanning (D : ℕ) : Prop :=
  (∀ s ∈ evenClass D, dir s ≠ 0) ∧
  ∀ v : Fin D → ℚ, (∀ s ∈ evenClass D, (∑ i, v i * (dir s i : ℚ)) = 0) → v = 0

instance instDecidableBalanced (D : ℕ) : Decidable (Balanced D) :=
  inferInstanceAs (Decidable (∀ i : Fin D, (∑ s ∈ evenClass D, dir s i) = 0))

instance instDecidableEquiangular (D : ℕ) : Decidable (Equiangular D) :=
  inferInstanceAs (Decidable (∀ s ∈ evenClass D, ∀ t ∈ evenClass D, s ≠ t →
    ∀ u ∈ evenClass D, ∀ v ∈ evenClass D, u ≠ v → ip s t = ip u v))

instance instDecidableAntipodalFree (D : ℕ) : Decidable (AntipodalFree D) :=
  inferInstanceAs (Decidable (∀ s ∈ evenClass D, ∀ t ∈ evenClass D, dir s ≠ -dir t))

/-! ## Antipodal-freeness is oddness of the dimension -/

lemma dir_compl {D : ℕ} (s : State D) : dir sᶜ = -dir s := by
  funext i
  by_cases h : i ∈ s <;> simp [dir, h]

/-- If two states give opposite directions, each is the other's complement. -/
lemma compl_of_dir_neg {D : ℕ} {s t : State D} (h : dir s = -dir t) : s = tᶜ := by
  ext i
  have hi : dir s i = -dir t i := by rw [h]; rfl
  by_cases ht : i ∈ t <;> by_cases hs : i ∈ s <;>
    simp [dir, hs, ht] at hi ⊢

/-- **Antipodal-freeness happens exactly in odd dimension.** In even dimension the
empty state and the all-flipped state are both in the class and point opposite
ways, so the class carries signs rather than axes. -/
theorem antipodalFree_iff_odd (D : ℕ) : AntipodalFree D ↔ Odd D := by
  constructor
  · intro h
    by_contra hodd
    have heven : D % 2 = 0 := by
      rcases Nat.even_or_odd D with he | ho
      · exact Nat.even_iff.mp he
      · exact absurd ho hodd
    have h0 : (∅ : State D) ∈ evenClass D := by simp [mem_evenClass]
    have h1 : (Finset.univ : State D) ∈ evenClass D := by
      simp [mem_evenClass, Finset.card_univ, heven]
    refine h _ h0 _ h1 ?_
    funext i
    simp [dir]
  · intro hodd s hs t ht hne
    have hcompl : s = tᶜ := compl_of_dir_neg hne
    have hcard : sᶜ.card = D - s.card := by
      simp [Finset.card_compl]
    have hs' : s.card % 2 = 0 := mem_evenClass.mp hs
    have ht' : t.card % 2 = 0 := mem_evenClass.mp ht
    have hle : s.card ≤ D := by
      simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ s)
    have hts : t.card = D - s.card := by
      have : tᶜᶜ = t := compl_compl t
      have hst : t = sᶜ := by rw [hcompl]; exact (compl_compl t).symm
      rw [hst, hcard]
    obtain ⟨k, hk⟩ := hodd
    omega

/-! ## Equiangularity caps the dimension at three

Two states of even size disagree on an even number of axes. When `D ≤ 3` the only
even sizes available are `0` and `2`, so any two distinct even states disagree on
exactly two axes and one angle occurs. From `D = 4` upward a state of size `4`
exists, and it disagrees with the empty state on four axes rather than two, so a
second angle appears. -/

/-- The first `k` axes, as a state of `D` distinctions. -/
def initSeg {D k : ℕ} (h : k ≤ D) : State D :=
  (Finset.range k).attachFin (by
    intro m hm
    simp only [Finset.mem_range] at hm
    omega)

lemma card_initSeg {D k : ℕ} (h : k ≤ D) : (initSeg h).card = k := by
  simp [initSeg]

lemma initSeg_mem {D k : ℕ} (h : k ≤ D) (hk : k % 2 = 0) :
    initSeg h ∈ evenClass D := by
  rw [mem_evenClass, card_initSeg]; exact hk

lemma symmDiff_empty_left {D : ℕ} (t : State D) : (∅ : State D) ∆ t = t := by
  simp

/-- **Above three dimensions the class is not equiangular.** -/
theorem not_equiangular_of_four_le {D : ℕ} (h : 4 ≤ D) : ¬ Equiangular D := by
  intro heq
  have h2 : (2 : ℕ) ≤ D := by omega
  have hE : (∅ : State D) ∈ evenClass D := by simp [mem_evenClass]
  have hA : initSeg h2 ∈ evenClass D := initSeg_mem h2 (by norm_num)
  have hB : initSeg h ∈ evenClass D := initSeg_mem h (by norm_num)
  have hAne : (∅ : State D) ≠ initSeg h2 := by
    intro hcon
    have := card_initSeg (D := D) (k := 2) h2
    rw [← hcon] at this
    simp at this
  have hBne : (∅ : State D) ≠ initSeg h := by
    intro hcon
    have := card_initSeg (D := D) (k := 4) h
    rw [← hcon] at this
    simp at this
  have key := heq _ hE _ hA hAne _ hE _ hB hBne
  rw [ip_eq, ip_eq, symmDiff_empty_left, symmDiff_empty_left,
      card_initSeg, card_initSeg] at key
  omega

/-- **Up to three dimensions the class is equiangular.** -/
theorem equiangular_of_le_three {D : ℕ} (h : D ≤ 3) : Equiangular D := by
  interval_cases D <;> decide

theorem equiangular_iff_le_three (D : ℕ) : Equiangular D ↔ D ≤ 3 := by
  constructor
  · intro heq
    by_contra hlt
    exact not_equiangular_of_four_le (by omega) heq
  · exact equiangular_of_le_three

/-! ## Balance fails only at one dimension -/

theorem not_balanced_one : ¬ Balanced 1 := by decide

/-! ## Where the class spans

At `D = 0` the single member is the zero vector, not a direction. At `D = 2`
both members lie on the line through `(+1, +1)`, so the plane is never entered.
At `D = 1` and at every `D ≥ 3` the class spans: from three dimensions up, the
all-ones direction and the pair states recover every basis vector. -/

theorem not_spanning_zero : ¬ Spanning 0 := by
  rintro ⟨h1, -⟩
  exact h1 ∅ (by simp [mem_evenClass]) (funext fun i => i.elim0)

theorem not_spanning_two : ¬ Spanning 2 := by
  rintro ⟨-, h2⟩
  have hv := h2 ![1, -1] ?_
  · have h0 := congrFun hv 0
    norm_num at h0
  · intro s hs
    fin_cases hs <;>
      simp [Fin.sum_univ_two, dir]

theorem spanning_one : Spanning 1 := by
  constructor
  · intro s _ h
    have h0 := congrFun h 0
    by_cases hm : (0 : Fin 1) ∈ s <;> simp [dir, hm] at h0
  · intro v hv
    have h := hv ∅ (by simp [mem_evenClass])
    funext i
    fin_cases i
    simpa [Fin.sum_univ_one, dir] using h

theorem spanning_of_three_le {D : ℕ} (hD : 3 ≤ D) : Spanning D := by
  constructor
  · intro s _ h
    have h0 := congrFun h ⟨0, by omega⟩
    by_cases hm : (⟨0, by omega⟩ : Fin D) ∈ s <;> simp [dir, hm] at h0
  · intro v hv
    have hsum : (∑ i, v i) = 0 := by
      have h := hv ∅ (by simp [mem_evenClass])
      simpa [dir] using h
    have hpair : ∀ i j : Fin D, i ≠ j → v i + v j = 0 := by
      intro i j hij
      have hmem : ({i, j} : Finset (Fin D)) ∈ evenClass D := by
        rw [mem_evenClass, Finset.card_insert_of_not_mem (by simpa using hij),
          Finset.card_singleton]
      have h := hv _ hmem
      have key : ∀ k : Fin D, v k * ((dir ({i, j} : State D) k : ℤ) : ℚ)
          = v k - 2 * (if k ∈ ({i, j} : Finset (Fin D)) then v k else 0) := by
        intro k
        by_cases hk : k ∈ ({i, j} : Finset (Fin D)) <;> simp [dir, hk] <;> ring
      rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_sub_distrib,
        hsum] at h
      rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_pair hij] at h
      linarith
    funext i
    obtain ⟨j, hj, k, hk, hjk⟩ :
        ∃ j ∈ Finset.univ.erase i, ∃ k ∈ Finset.univ.erase i, j ≠ k := by
      apply Finset.one_lt_card.mp
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    have e1 := hpair i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have e2 := hpair i k (Ne.symm (Finset.ne_of_mem_erase hk))
    have e3 := hpair j k hjk
    have : v i = 0 := by linarith
    simpa using this

/-! ## The main theorem -/

/-- **The parity class of the cube is a balanced, equiangular, spanning system
of directions exactly in three dimensions.** The hypothesis contains no
numeral: it is three properties of the class the closure argument produces,
and none of the three sorts dimensions by parity. -/
theorem balanced_equiangular_spanning_iff_three (D : ℕ) :
    (Balanced D ∧ Equiangular D ∧ Spanning D) ↔ D = 3 := by
  constructor
  · rintro ⟨hbal, heq, hspan⟩
    have hle : D ≤ 3 := (equiangular_iff_le_three D).mp heq
    interval_cases D
    · exact absurd hspan not_spanning_zero
    · exact absurd hbal not_balanced_one
    · exact absurd hspan not_spanning_two
    · rfl
  · rintro rfl
    exact ⟨by decide, by decide, spanning_of_three_le (by norm_num)⟩

/-- At the selected dimension the sign division is a conclusion, not a
hypothesis: no direction of the class is the negation of another, so the four
directions name four distinct axes. Axes come out, not in. -/
theorem antipodalFree_three : AntipodalFree 3 :=
  (antipodalFree_iff_odd 3).mpr (by decide)

/-- **The equivalent selector.** Replacing spanning with antipodal-freeness
selects the same dimension. Kept because `antipodalFree_iff_odd` exposes the
condition as the oddness of `D`, which is why it is not the stated hypothesis. -/
theorem balanced_equiangular_antipodalFree_iff_three (D : ℕ) :
    (Balanced D ∧ Equiangular D ∧ AntipodalFree D) ↔ D = 3 := by
  constructor
  · rintro ⟨hbal, heq, hanti⟩
    have hle : D ≤ 3 := (equiangular_iff_le_three D).mp heq
    have hodd : Odd D := (antipodalFree_iff_odd D).mp hanti
    interval_cases D
    · exact absurd hodd (by decide)
    · exact absurd hbal not_balanced_one
    · exact absurd hodd (by decide)
    · rfl
  · rintro rfl
    refine ⟨by decide, by decide, ?_⟩
    exact (antipodalFree_iff_odd 3).mpr (by decide)

/-! ## Each condition is load-bearing

Dropping any one of the three admits a dimension other than three, so none of
them is decoration and the theorem is not carried by a single clause. -/

theorem drop_balanced_admits_one : Equiangular 1 ∧ Spanning 1 :=
  ⟨by decide, spanning_one⟩

theorem drop_spanning_admits_two : Balanced 2 ∧ Equiangular 2 :=
  ⟨by decide, by decide⟩

theorem drop_equiangular_admits_four : Balanced 4 ∧ Spanning 4 :=
  ⟨by decide, spanning_of_three_le (by norm_num)⟩

/-- Load-bearing witnesses for the equivalent antipodal-free selector. -/
theorem drop_antipodalFree_admits_two : Balanced 2 ∧ Equiangular 2 :=
  ⟨by decide, by decide⟩

theorem drop_equiangular_admits_five : Balanced 5 ∧ AntipodalFree 5 :=
  ⟨by decide, (antipodalFree_iff_odd 5).mpr (by decide)⟩

/-! ## The isotropy weakening selects nothing

Weakening equiangularity to isotropy (no preferred direction, no preferred
quadratic form: the sum of outer products proportional to the identity) fails
to select: the class is a tight frame at every `D ≥ 3`. The off-diagonal
entries vanish exactly when a third axis exists to pair against, and at
`D = 2` they do not. What equiangularity demands beyond isotropy, tightness of
the simplex bound, is the demand doing the selecting. -/

/-- Diagonal entries of the outer-product sum: the common squared entry is the
class size. -/
theorem isotropy_diag {D : ℕ} (i : Fin D) :
    (∑ s ∈ evenClass D, dir s i * dir s i) = ((evenClass D).card : ℤ) := by
  have h : ∀ s ∈ evenClass D, dir s i * dir s i = 1 := by
    intro s _
    by_cases hm : i ∈ s <;> simp [dir, hm]
  rw [Finset.sum_congr rfl h]
  simp

/-- Off-diagonal entries of the outer-product sum vanish at every `D ≥ 3`:
toggling a third axis together with `i` is a parity-preserving involution that
flips the product's sign. -/
theorem isotropy_offdiag {D : ℕ} (hD : 3 ≤ D) {i j : Fin D} (hij : i ≠ j) :
    (∑ s ∈ evenClass D, dir s i * dir s j) = 0 := by
  classical
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin D, k ≠ i ∧ k ≠ j := by
    have hcard : 0 < ((Finset.univ.erase i).erase j).card := by
      rw [Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      omega
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
    exact ⟨k, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk),
      Finset.ne_of_mem_erase hk⟩
  have hik : i ≠ k := Ne.symm hki
  refine Finset.sum_involution
    (fun s _ => s ∆ ({i, k} : Finset (Fin D))) ?_ ?_ ?_ ?_
  · intro s _
    have hdi : dir (s ∆ ({i, k} : Finset (Fin D))) i = -dir s i := by
      by_cases hm : i ∈ s <;>
        simp [dir, Finset.mem_symmDiff, hm, hik]
    have hdj : dir (s ∆ ({i, k} : Finset (Fin D))) j = dir s j := by
      by_cases hm : j ∈ s <;>
        simp [dir, Finset.mem_symmDiff, hm, Ne.symm hij, hkj.symm, hij, hkj]
    rw [hdi, hdj]
    ring
  · intro s _ _
    intro hcon
    have : ({i, k} : Finset (Fin D)) = ∅ := by
      have := symmDiff_eq_left.mp hcon
      simpa using this
    simp at this
  · intro s hs
    rw [mem_evenClass] at hs
    show (s ∆ ({i, k} : Finset (Fin D))) ∈ evenClass D
    rw [mem_evenClass]
    set t : Finset (Fin D) := {i, k} with ht
    have hcard2 : t.card = 2 := by
      rw [ht, Finset.card_insert_of_notMem (by simpa using hik),
        Finset.card_singleton]
    have h1 : (s \ t).card + (s ∩ t).card = s.card :=
      Finset.card_sdiff_add_card_inter s t
    have h2 : (t \ s).card + (t ∩ s).card = t.card :=
      Finset.card_sdiff_add_card_inter t s
    have hcup : (s ∆ t).card = (s \ t).card + (t \ s).card := by
      rw [symmDiff_def, Finset.sup_eq_union,
        Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have hint : (s ∩ t).card = (t ∩ s).card := by rw [Finset.inter_comm]
    omega
  · intro s _
    show s ∆ ({i, k} : Finset (Fin D)) ∆ ({i, k} : Finset (Fin D)) = s
    exact symmDiff_symmDiff_cancel_right _ _

/-- At two dimensions the off-diagonal entry is `2`, not `0`: the boundary case
showing the involution needs a third axis. -/
theorem not_isotropic_two : (∑ s ∈ evenClass 2, dir s 0 * dir s 1) = 2 := by
  decide

/-! ## What the three dimensions deliver: four axes, both signs, eight states -/

/-- Four directions. -/
theorem card_evenClass_three : (evenClass 3).card = 4 := by decide

/-- The count is `D + 1`, and it is derived from the class rather than imposed. -/
theorem card_evenClass_three_eq_succ : (evenClass 3).card = 3 + 1 := by decide

/-- The tetrahedral angle. Unnormalised the inner product is `-1`; dividing by the
common squared length `3` gives `-1/3`, so the angle is `arccos (-1/3)`. -/
theorem ip_distinct_three (s : State 3) (hs : s ∈ evenClass 3)
    (t : State 3) (ht : t ∈ evenClass 3) (hne : s ≠ t) : ip s t = -1 := by
  revert hs ht hne; revert s t; decide

/-- Both signs of every axis are already states of the ledger: the four axes
taken with a debit and a credit exhaust the eight states of three distinctions.
No further label is needed to reach eight. -/
theorem two_signs_exhaust_states : 2 * (evenClass 3).card = 2 ^ 3 := by decide

/-! ## Where the slot count meets the pass length -/

lemma two_mul_succ_lt_two_pow : ∀ {D : ℕ}, 4 ≤ D → 2 * (D + 1) < 2 ^ D := by
  intro D
  induction D with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge n 4 with hn | hn
    · have hn3 : n = 3 := by omega
      subst hn3
      norm_num
    · have hprev := ih (by omega)
      have hpow : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by ring
      have htwo : 2 ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **Doubling the axis count meets the length of a complete pass at exactly three.**
`2 (D + 1)` is the number of slots, `2 ^ D` the number of states a pass must visit. -/
theorem slot_meets_pass (D : ℕ) : 2 * (D + 1) = 2 ^ D ↔ D = 3 := by
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_ge D 4 with hlt | hge
    · interval_cases D <;> simp_all
    · exact absurd h (Nat.ne_of_lt (two_mul_succ_lt_two_pow hge))
  · rintro rfl; norm_num

/-! ## Discriminators

A statement that fixes its own dimension carries no information about its
hypothesis, so the theorems above are stated uniformly in `D` and the numeral
appears only in the conclusion. -/

/-- For any predicate at all, including a false one and one mentioning no
geometry, the typed form holds by reflexivity. So `hypothesis about 3 → the
class at 3 has four members` establishes nothing about the hypothesis. -/
theorem typed_dimension_statement_is_free (P : ℕ → Prop) :
    P 3 → (evenClass 3).card = 4 :=
  fun _ => card_evenClass_three

/-- The conclusion is not a tautology: some dimension has a class of another
size, so a theorem concluding `= 4` must earn it. -/
theorem four_needs_the_hypothesis : ∃ D : ℕ, (evenClass D).card ≠ 4 :=
  ⟨2, by decide⟩

end ParityClassDirections
end Foundation
end IndisputableMonolith
