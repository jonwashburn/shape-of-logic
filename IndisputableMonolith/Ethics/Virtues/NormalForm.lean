import Mathlib

/-!
# Micro-Move Normal Forms

Canonical normal form for micro-move coefficient tables supporting DREAM scaffolding.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open scoped Classical BigOperators

open Finset

/-- Primitive generators in fixed canonical order. -/
inductive Primitive
  | Love | Justice | Forgiveness | Wisdom | Courage | Temperance | Prudence
  | Compassion | Gratitude | Patience | Humility | Hope | Creativity | Sacrifice
  deriving DecidableEq, Repr

/-- Canonical primitive order as a list. -/
def primitiveOrderList : List Primitive :=
  [ Primitive.Love, Primitive.Justice, Primitive.Forgiveness,
    Primitive.Wisdom, Primitive.Courage, Primitive.Temperance,
    Primitive.Prudence, Primitive.Compassion, Primitive.Gratitude,
    Primitive.Patience, Primitive.Humility, Primitive.Hope,
    Primitive.Creativity, Primitive.Sacrifice ]

lemma primitive_mem_order (p : Primitive) : p ∈ primitiveOrderList := by
  cases p <;> simp [primitiveOrderList]

lemma primitiveOrderList_nodup : primitiveOrderList.Nodup := by
  unfold primitiveOrderList
  decide

/-- Micro moves: (pair scope, primitive, coefficient). -/
structure MicroMove where
  pair : ℕ
  primitive : Primitive
  coeff : ℝ

namespace MicroMove

/-- Canonical micro-move normal form: coefficient table with finite support. -/
@[ext]
structure NormalForm where
  supportPairs : Finset ℕ
  coeff : ℕ → Primitive → ℝ
  zero_outside : ∀ {pair prim}, pair ∉ supportPairs → coeff pair prim = 0
  nontrivial : ∀ {pair}, pair ∈ supportPairs → ∃ prim, coeff pair prim ≠ 0

namespace NormalForm

/-- Canonical ordered list of supported pairs (ascending). -/
noncomputable def pairList (nf : NormalForm) : List ℕ :=
  nf.supportPairs.sort (· ≤ ·)

lemma pairList_mem {nf : NormalForm} {pair : ℕ} :
    pair ∈ pairList nf ↔ pair ∈ nf.supportPairs := by
  unfold pairList
  simp only [mem_sort]

lemma pairList_nodup (nf : NormalForm) : (pairList nf).Nodup := by
  unfold pairList
  simp only [sort_nodup]

/-- Micro-moves for a single pair. -/
noncomputable def rowMoves (nf : NormalForm) (pair : ℕ) : List MicroMove :=
  primitiveOrderList.filterMap (fun prim =>
    if nf.coeff pair prim = 0 then none
    else some ⟨pair, prim, nf.coeff pair prim⟩)

/-- Canonical ordered list of micro-moves. -/
noncomputable def toMoves (nf : NormalForm) : List MicroMove :=
  (pairList nf).flatMap (rowMoves nf)

/-- Aggregate coefficient for `(pair, primitive)` extracted from a move list. -/
noncomputable def aggCoeff (moves : List MicroMove) (pair : ℕ) (prim : Primitive) : ℝ :=
  ((moves.filter fun m => m.pair = pair ∧ m.primitive = prim).map (·.coeff)).sum

/-- **NormalForm construction**: The ofMicroMoves construction is well-formed.

Proof by contraposition: if aggCoeff is nonzero, pair must be in the filtered set.
-/
theorem ofMicroMoves_zero_outside (moves : List MicroMove) :
  ∀ {pair prim}, pair ∉ (moves.map (·.pair)).toFinset.filter (fun k =>
    ∃ prim, aggCoeff moves k prim ≠ 0) → aggCoeff moves pair prim = 0 := by
  intro pair prim h_not_mem
  by_contra h_ne
  apply h_not_mem
  rw [Finset.mem_filter, List.mem_toFinset]
  constructor
  · -- Show pair ∈ moves.map (·.pair)
    -- If aggCoeff ≠ 0, there's a move with matching pair and prim
    have h_filter_ne : (moves.filter fun m => m.pair = pair ∧ m.primitive = prim) ≠ [] := by
      intro h_empty
      unfold aggCoeff at h_ne
      rw [h_empty] at h_ne
      simp at h_ne
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ h_filter_ne
    rw [List.mem_filter] at hm
    simp only [decide_eq_true_eq] at hm
    rw [List.mem_map]
    exact ⟨m, hm.1, hm.2.1⟩
  · -- Show ∃ prim', aggCoeff moves pair prim' ≠ 0
    exact ⟨prim, h_ne⟩

theorem ofMicroMoves_nontrivial (moves : List MicroMove) :
  ∀ {pair}, pair ∈ (moves.map (·.pair)).toFinset.filter (fun k =>
    ∃ prim, aggCoeff moves k prim ≠ 0) → ∃ prim, aggCoeff moves pair prim ≠ 0 := by
  intro pair h_mem
  rw [Finset.mem_filter] at h_mem
  exact h_mem.2

/-- Build NormalForm from a move list (aggregates coefficients). -/
noncomputable def ofMicroMoves (moves : List MicroMove) : NormalForm where
  supportPairs := (moves.map (·.pair)).toFinset.filter (fun k =>
    ∃ prim, aggCoeff moves k prim ≠ 0)
  coeff := aggCoeff moves
  zero_outside := ofMicroMoves_zero_outside moves
  nontrivial := ofMicroMoves_nontrivial moves

/-- Every micro-move generated for `pair` stays within that pair scope.

Proof: rowMoves constructs MicroMove.mk with pair as first argument,
so any move in the list has m.pair = pair by construction. -/
theorem rowMoves_pair {nf : NormalForm} {pair : ℕ} {m : MicroMove}
    (hm : m ∈ rowMoves nf pair) : m.pair = pair := by
  classical
  unfold rowMoves at hm
  simp only [List.mem_filterMap] at hm
  obtain ⟨prim, _, heq⟩ := hm
  by_cases h : nf.coeff pair prim = 0 <;> simp only [h, ite_true, ite_false] at heq
  · cases heq
  · cases heq; rfl

/-- If a coefficient is non-zero, the corresponding micro-move appears in the row.

Proof: rowMoves uses filterMap which includes moves for non-zero coefficients. -/
theorem rowMoves_mem_of_coeff_ne_zero {nf : NormalForm} {pair : ℕ} {prim : Primitive}
    (hcoeff : nf.coeff pair prim ≠ 0) :
    ⟨pair, prim, nf.coeff pair prim⟩ ∈ rowMoves nf pair := by
  classical
  unfold rowMoves
  simp only [List.mem_filterMap]
  use prim, primitive_mem_order prim
  simp only [hcoeff, ite_false]

/-- Auxiliary lemma: sum over a primitive list.

This proof involves complex list manipulations with filterMap and filter.
The proof strategy:
- If coeff = 0: the filterMap excludes this primitive, so sum = 0
- If coeff ≠ 0: exactly one move matches, contributing the coefficient -/
theorem aggCoeff_rowMoves_aux_theorem
    (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    (((primitiveOrderList.filterMap fun q =>
          if nf.coeff pair q = 0 then none
          else some (MicroMove.mk pair q (nf.coeff pair q))).filter
        (fun m => m.pair = pair ∧ m.primitive = prim)).map
        (·.coeff)).sum
      = if prim ∈ primitiveOrderList then nf.coeff pair prim else 0 := by
  -- Since all primitives are in primitiveOrderList, the else branch is never reached
  have hmem : prim ∈ primitiveOrderList := primitive_mem_order prim
  simp only [hmem, ite_true]
  -- Let moves = filterMap result
  set moves := primitiveOrderList.filterMap fun q =>
      if nf.coeff pair q = 0 then none
      else some (MicroMove.mk pair q (nf.coeff pair q)) with hmoves_def
  -- All moves in `moves` have m.pair = pair (by construction)
  have h_all_pair : ∀ m ∈ moves, m.pair = pair := by
    intro m hm
    simp only [hmoves_def, List.mem_filterMap] at hm
    obtain ⟨q, _, h_some⟩ := hm
    by_cases hcoeff : nf.coeff pair q = 0
    · simp [hcoeff] at h_some
    · simp only [hcoeff, ite_false, Option.some.injEq] at h_some
      rw [← h_some]
  -- The filter condition `m.pair = pair ∧ m.primitive = prim` simplifies to `m.primitive = prim`
  have h_filter_eq : moves.filter (fun m => m.pair = pair ∧ m.primitive = prim) =
                     moves.filter (fun m => m.primitive = prim) := by
    apply List.filter_congr
    intro m hm
    simp only [decide_eq_decide]
    constructor
    · intro ⟨_, hp⟩; exact hp
    · intro hp; exact ⟨h_all_pair m hm, hp⟩
  rw [h_filter_eq]
  -- Now we need to show the sum of coeffs for moves with primitive = prim equals nf.coeff pair prim
  -- Case split on whether coeff is zero
  by_cases hcoeff : nf.coeff pair prim = 0
  · -- If coeff = 0, no move for prim was created, so filter is empty
    have h_prim_not_in : ∀ m ∈ moves, m.primitive ≠ prim := by
      intro m hm
      simp only [hmoves_def, List.mem_filterMap] at hm
      obtain ⟨q, _, h_some⟩ := hm
      by_cases hq : nf.coeff pair q = 0
      · simp [hq] at h_some
      · simp only [hq, ite_false, Option.some.injEq] at h_some
        rw [← h_some]
        intro h_eq
        simp at h_eq
        rw [h_eq] at hq
        exact hq hcoeff
    have h_filter_nil : moves.filter (fun m => m.primitive = prim) = [] := by
      rw [List.filter_eq_nil_iff]
      intro m hm
      simp only [decide_eq_true_eq]
      exact h_prim_not_in m hm
    simp [h_filter_nil, hcoeff]
  · -- If coeff ≠ 0, exactly one move with primitive = prim was created
    have h_prim_in_moves : ⟨pair, prim, nf.coeff pair prim⟩ ∈ moves := by
      simp only [hmoves_def, List.mem_filterMap]
      use prim, hmem
      simp [hcoeff]
    -- Show the filtered list is exactly this one element
    have h_unique : ∀ m ∈ moves, m.primitive = prim → m = ⟨pair, prim, nf.coeff pair prim⟩ := by
      intro m hm h_prim_eq
      simp only [hmoves_def, List.mem_filterMap] at hm
      obtain ⟨q, _, h_some⟩ := hm
      by_cases hq : nf.coeff pair q = 0
      · simp [hq] at h_some
      · simp only [hq, ite_false, Option.some.injEq] at h_some
        rw [← h_some] at h_prim_eq ⊢
        simp at h_prim_eq
        subst h_prim_eq
        rfl
    -- The filtered list equals [target] because target is the unique element matching the predicate
    have h_filter_singleton : moves.filter (fun m => m.primitive = prim) =
                              [⟨pair, prim, nf.coeff pair prim⟩] := by
      -- Show all elements in the filtered list equal the target
      have h_all_eq : ∀ m ∈ moves.filter (fun m => m.primitive = prim),
          m = ⟨pair, prim, nf.coeff pair prim⟩ := by
        intro m hm
        rw [List.mem_filter] at hm
        simp only [decide_eq_true_eq] at hm
        exact h_unique m hm.1 hm.2
      -- The filtered list is nonempty (contains target)
      have h_mem_filter : ⟨pair, prim, nf.coeff pair prim⟩ ∈ moves.filter (fun m => m.primitive = prim) := by
        rw [List.mem_filter]
        exact ⟨h_prim_in_moves, by simp⟩
      -- Any element in the list equals target, so list is either [] or [target]
      -- Since target ∈ list, it must be [target]
      cases hfilt : moves.filter (fun m => m.primitive = prim) with
      | nil =>
        exfalso
        rw [hfilt] at h_mem_filter
        simp at h_mem_filter
      | cons head tail =>
        -- head = target by h_all_eq
        have h_head_eq : head = ⟨pair, prim, nf.coeff pair prim⟩ := by
          apply h_all_eq
          rw [hfilt]
          simp
        -- tail = [] because any element in tail would also equal target,
        -- meaning target appears twice in a nodup list
        have h_tail_nil : tail = [] := by
          by_contra h_tail_ne
          obtain ⟨x, rest, h_tail_eq⟩ := List.exists_cons_of_ne_nil h_tail_ne
          have h_x_mem : x ∈ moves.filter (fun m => m.primitive = prim) := by
            rw [hfilt, h_tail_eq]
            simp
          have h_x_eq : x = ⟨pair, prim, nf.coeff pair prim⟩ := h_all_eq x h_x_mem
          -- Now head = x = target, so we have duplicate in filtered list
          have h_moves_prim_unique : ∀ a b, a ∈ moves → b ∈ moves → a.primitive = b.primitive → a = b := by
            intro a b ha hb h_prim_eq
            simp only [hmoves_def, List.mem_filterMap] at ha hb
            obtain ⟨pa, _, ha_some⟩ := ha
            obtain ⟨pb, _, hb_some⟩ := hb
            by_cases hpa : nf.coeff pair pa = 0 <;> simp [hpa] at ha_some
            by_cases hpb : nf.coeff pair pb = 0 <;> simp [hpb] at hb_some
            rw [← ha_some, ← hb_some] at h_prim_eq ⊢
            simp at h_prim_eq
            subst h_prim_eq
            rfl
          -- head and x are both in moves with same primitive, so head = x
          have h_head_in : head ∈ moves := by
            have : head ∈ moves.filter (fun m => m.primitive = prim) := by rw [hfilt]; simp
            rw [List.mem_filter] at this
            exact this.1
          have h_x_in : x ∈ moves := by
            rw [List.mem_filter] at h_x_mem
            exact h_x_mem.1
          have h_head_prim : head.primitive = prim := by
            have : head ∈ moves.filter (fun m => m.primitive = prim) := by rw [hfilt]; simp
            rw [List.mem_filter] at this
            simp only [decide_eq_true_eq] at this
            exact this.2
          have h_x_prim_eq_val_p : x.primitive = prim := by
            rw [List.mem_filter] at h_x_mem
            simp only [decide_eq_true_eq] at h_x_mem
            exact h_x_mem.2
          have h_head_x_eq : head = x := h_moves_prim_unique head x h_head_in h_x_in (by rw [h_head_prim, h_x_prim_eq_val_p])
          -- Filter of nodup is nodup, contradicting head = x appearing at indices 0 and 1
          have h_filter_nodup : (moves.filter (fun m => m.primitive = prim)).Nodup := by
            apply List.Nodup.filter
            simp only [hmoves_def]
            apply List.Nodup.filterMap _ primitiveOrderList_nodup
            intro a a' m hma hma'
            -- hma : m ∈ (if coeff a = 0 then none else some ...)
            -- hma' : m ∈ (if coeff a' = 0 then none else some ...)
            by_cases ha : nf.coeff pair a = 0 <;> by_cases ha' : nf.coeff pair a' = 0 <;>
              simp [ha, ha'] at hma hma'
            -- Both coeffs nonzero, so m = MicroMove for a and m = MicroMove for a'
            rw [← hma] at hma'
            simp only [MicroMove.mk.injEq, true_and] at hma'
            exact hma'.1.symm
          rw [hfilt, h_tail_eq] at h_filter_nodup
          simp only [List.nodup_cons] at h_filter_nodup
          have ⟨h_head_not_in_tail, _⟩ := h_filter_nodup
          rw [h_head_x_eq] at h_head_not_in_tail
          simp at h_head_not_in_tail
        rw [h_head_eq, h_tail_nil]
    simp [h_filter_singleton]

/-- Backward compatibility alias -/
theorem aggCoeff_rowMoves_aux_axiom
    (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    (((primitiveOrderList.filterMap fun q =>
          if nf.coeff pair q = 0 then none
          else some (MicroMove.mk pair q (nf.coeff pair q))).filter
        (fun m => m.pair = pair ∧ m.primitive = prim)).map
        (·.coeff)).sum
      = if prim ∈ primitiveOrderList then nf.coeff pair prim else 0 :=
  aggCoeff_rowMoves_aux_theorem nf pair prim

private lemma aggCoeff_rowMoves_aux
    (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    (((primitiveOrderList.filterMap fun q =>
          if nf.coeff pair q = 0 then none
          else some (MicroMove.mk pair q (nf.coeff pair q))).filter
        (fun m => m.pair = pair ∧ m.primitive = prim)).map
        (·.coeff)).sum
      = if prim ∈ primitiveOrderList then nf.coeff pair prim else 0 :=
  aggCoeff_rowMoves_aux_axiom nf pair prim

/-- Aggregated coefficient for a row equals the stored table value. -/
lemma aggCoeff_rowMoves (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    aggCoeff (rowMoves nf pair) pair prim = nf.coeff pair prim := by
  classical
  have hmem : prim ∈ primitiveOrderList := primitive_mem_order prim
  simpa [aggCoeff, rowMoves, hmem] using aggCoeff_rowMoves_aux nf pair prim

/-- Rows for distinct pairs contribute nothing to another pair's aggregation.

Proof: All moves in rowMoves nf k have m.pair = k (by rowMoves_pair),
so the filter for pair ≠ k yields an empty list. -/
theorem aggCoeff_rowMoves_of_ne (nf : NormalForm) {pair k : ℕ} {prim : Primitive}
    (hkp : k ≠ pair) : aggCoeff (rowMoves nf k) pair prim = 0 := by
  classical
  unfold aggCoeff
  -- All moves in rowMoves nf k have m.pair = k, so none satisfy m.pair = pair when k ≠ pair
  have h_filter_empty : (rowMoves nf k).filter (fun m => m.pair = pair ∧ m.primitive = prim) = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm
    simp only [decide_eq_true_eq, not_and]
    intro h_pair
    -- m ∈ rowMoves nf k implies m.pair = k
    have := rowMoves_pair hm
    -- But we assumed m.pair = pair, so k = pair, contradiction with hkp
    rw [h_pair] at this
    exact absurd this.symm hkp
  simp only [h_filter_empty, List.filter_nil, List.map_nil, List.sum_nil]

/-- Aggregation distributes over concatenation of move lists. -/
lemma aggCoeff_append (xs ys : List MicroMove) (pair : ℕ) (prim : Primitive) :
    aggCoeff (xs ++ ys) pair prim = aggCoeff xs pair prim + aggCoeff ys pair prim := by
  classical
  unfold aggCoeff
  simp only [List.filter_append, List.map_append, List.sum_append]

/-- Aggregation over a flat-mapped list of row moves. -/
theorem aggCoeff_flatMap (nf : NormalForm) (pair : ℕ) (prim : Primitive)
    (l : List ℕ) (hl : l.Nodup) :
    aggCoeff (l.flatMap (rowMoves nf)) pair prim
      = if pair ∈ l then aggCoeff (rowMoves nf pair) pair prim else 0 := by
  induction l with
  | nil =>
    simp only [List.flatMap_nil, List.not_mem_nil, ↓reduceIte]
    unfold aggCoeff
    simp
  | cons h t ih =>
    simp only [List.flatMap_cons]
    rw [aggCoeff_append]
    have hnodup_t : t.Nodup := hl.of_cons
    have h_not_mem : h ∉ t := hl.not_mem
    by_cases hpair : pair = h
    · -- pair = h: contribution comes from rowMoves nf h, and pair ∉ t (since h ∉ t)
      subst hpair
      simp only [List.mem_cons, true_or, ↓reduceIte]
      have h_pair_not_in_t : pair ∉ t := h_not_mem
      rw [ih hnodup_t]
      simp only [h_pair_not_in_t, ↓reduceIte, add_zero]
    · -- pair ≠ h: contribution from rowMoves nf h is 0
      have h_ne : h ≠ pair := Ne.symm hpair
      rw [aggCoeff_rowMoves_of_ne nf h_ne]
      simp only [zero_add]
      rw [ih hnodup_t]
      -- pair ∈ h :: t ↔ pair = h ∨ pair ∈ t, but pair ≠ h, so pair ∈ h :: t ↔ pair ∈ t
      simp only [List.mem_cons, hpair, false_or]

/-- Aggregated coefficient extracted from `toMoves` equals the canonical table. -/
lemma sumCoeffs_toMoves (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    aggCoeff (toMoves nf) pair prim = nf.coeff pair prim := by
  classical
  unfold toMoves
  have hflat := aggCoeff_flatMap (nf := nf) (pair := pair) (prim := prim)
    (l := pairList nf) (hl := pairList_nodup nf)
  by_cases hpair : pair ∈ pairList nf
  · have := aggCoeff_rowMoves (nf := nf) (pair := pair) (prim := prim)
    simpa [hflat, hpair] using this
  · have hsupp : pair ∉ nf.supportPairs := by
      simpa [pairList_mem] using hpair
    have hzero := nf.zero_outside (pair := pair) (prim := prim) hsupp
    simp [hflat, hpair, hzero]

/-- Non-zero coefficients guarantee the corresponding move appears in `toMoves`. -/
lemma mem_toMoves_of_coeff_ne_zero (nf : NormalForm) {pair : ℕ} {prim : Primitive}
    (hsupp : pair ∈ nf.supportPairs) (hcoeff : nf.coeff pair prim ≠ 0) :
    ⟨pair, prim, nf.coeff pair prim⟩ ∈ toMoves nf := by
  classical
  unfold toMoves
  have hpair : pair ∈ pairList nf := (pairList_mem).2 hsupp
  exact List.mem_flatMap.mpr
    ⟨pair, hpair, rowMoves_mem_of_coeff_ne_zero (nf := nf) (pair := pair) (prim := prim) hcoeff⟩

/-- The mapped pair list produced by `toMoves` contains any supported pair with non-zero coeff. -/
lemma pair_mem_toMoves_map (nf : NormalForm) {pair : ℕ} {prim : Primitive}
    (hsupp : pair ∈ nf.supportPairs) (hcoeff : nf.coeff pair prim ≠ 0) :
    pair ∈ ((toMoves nf).map (·.pair)).toFinset := by
  classical
  have hmove := mem_toMoves_of_coeff_ne_zero (nf := nf) hsupp hcoeff
  have hmap : pair ∈ (toMoves nf).map (·.pair) := by
    refine List.mem_map.mpr ?_
    refine ⟨⟨pair, prim, nf.coeff pair prim⟩, hmove, ?_⟩
    simp
  exact List.mem_toFinset.mpr hmap

/-- Normal forms round-trip through `toMoves` and `ofMicroMoves`. -/
theorem of_toMoves (nf : NormalForm) :
    ofMicroMoves (toMoves nf) = nf := by
  classical
  ext pair prim
  · constructor
    · intro hmem
      rcases Finset.mem_filter.mp hmem with ⟨hmap, hex⟩
      rcases hex with ⟨prim', hagg⟩
      have hcoeff : nf.coeff pair prim' ≠ 0 := by
        simpa [sumCoeffs_toMoves] using hagg
      have : pair ∈ nf.supportPairs := by
        by_contra hnot
        have := nf.zero_outside (pair := pair) (prim := prim') hnot
        exact hcoeff (by simpa [sumCoeffs_toMoves] using this)
      exact this
    · intro hmem
      obtain ⟨prim', hcoeff⟩ := nf.nontrivial hmem
      have hcoeff' : nf.coeff pair prim' ≠ 0 := hcoeff
      have hmap := pair_mem_toMoves_map (nf := nf) hmem hcoeff'
      have : aggCoeff (toMoves nf) pair prim' ≠ 0 := by
        simpa [sumCoeffs_toMoves] using hcoeff'
      refine Finset.mem_filter.mpr ⟨hmap, ?_⟩
      exact ⟨prim', this⟩
  · simpa [ofMicroMoves, sumCoeffs_toMoves]

/-- The canonical pair list matches the 16-window filtered enumeration. -/
theorem pairList_eq_filtered_range_theorem (nf : NormalForm)
    (hw : nf.supportPairs ⊆ Finset.range 16) :
    pairList nf = (List.range 16).filter (fun k => k ∈ nf.supportPairs) := by
  unfold pairList
  -- Both sides are sorted lists of the same elements
  have h_elements : ∀ x, x ∈ nf.supportPairs.sort (· ≤ ·) ↔ x ∈ (List.range 16).filter (fun k => k ∈ nf.supportPairs) := by
    intro x
    simp [mem_sort, List.mem_filter, List.mem_range]
    intro hx
    have : x < 16 := by
      have : x ∈ range 16 := hw hx
      simpa using this
    exact this
  -- Show both lists are sorted using SortedLT (strictly increasing)
  have h_sorted_lhs : (nf.supportPairs.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort _
  have h_sorted_rhs : ((List.range 16).filter (fun k => k ∈ nf.supportPairs)).SortedLT := by
    have h_range_sorted : (List.range 16).SortedLT := List.sortedLT_range 16
    exact (h_range_sorted.pairwise.filter _).sortedLT
  -- Show both lists have no duplicates
  have h_nodup_lhs : (nf.supportPairs.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have h_nodup_rhs : ((List.range 16).filter (fun k => k ∈ nf.supportPairs)).Nodup := by
    apply List.Nodup.filter
    exact List.nodup_range
  -- Build permutation from element equivalence (both lists are nodup)
  have h_perm : List.Perm (nf.supportPairs.sort (· ≤ ·)) ((List.range 16).filter (fun k => k ∈ nf.supportPairs)) := by
    rw [List.perm_ext_iff_of_nodup h_nodup_lhs h_nodup_rhs]
    intro x
    exact h_elements x
  -- Apply uniqueness of sorted lists
  exact h_perm.eq_of_sortedLE h_sorted_lhs.sortedLE h_sorted_rhs.sortedLE

/-- Backward compatibility alias -/
theorem pairList_eq_filtered_range_axiom (nf : NormalForm)
    (hw : nf.supportPairs ⊆ Finset.range 16) :
    pairList nf = (List.range 16).filter (fun k => k ∈ nf.supportPairs) :=
  pairList_eq_filtered_range_theorem nf hw

lemma pairList_eq_filtered_range (nf : NormalForm)
    (hw : nf.supportPairs ⊆ Finset.range 16) :
    pairList nf = (List.range 16).filter (fun k => k ∈ nf.supportPairs) :=
  pairList_eq_filtered_range_theorem nf hw

end NormalForm

end MicroMove

end Virtues
end Ethics
end IndisputableMonolith
