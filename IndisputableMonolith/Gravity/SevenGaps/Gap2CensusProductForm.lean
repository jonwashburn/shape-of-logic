import Mathlib

/-!
# Gap 2 / C11: the product-form census is orbit–stabilizer

The A36 campaign identified the mechanism behind the C11 anomaly: the anomaly
is exactly the loop-count residual (`Gap2AnomalyAsymptotics.lean`, kernel-
checked).  The analytic consequences of that mechanism (the `q(c) → 0` rate)
go through the **product-form census law**: over the cap-`c` ensemble of
isomorphism classes of `(nV, sorted directed edge multiset, nT)` weighted by
`μ = 1/|Aut|`, the mass of the `(n, k, j, t)` class is

  `w(n, k, j, t) = C(k, j) · n^j · (n² − n)^(k − j) / (n! · k! · M0)`,

with `M0 = (c+1) · Σ_{n,k} n^(2k)/(n! · k!)`, and conditional on `(n, k)` the
loop count is `Binomial(k, 1/n)`.  The A36 paper proof justifies the product
form by orbit–stabilizer for the relabeling group `S_n × S_k`; the product
law was independently re-derived and verified per `(nV, nE, n_loop)` cell at
caps 1–6 in three implementations (A36 hostile review, MINOR, landed).  This
module is the kernel-checked formalization of that justification, upgrading
the census product form from DERIVED-UNFORMALIZED to **THEOREM**.

## What is proved here

* `census_identity` (**the contract**): the sum of `1/|Aut|` over the
  isomorphism classes of the `(n, k, j)` cell equals the ordered-sequence
  count `C(k, j) · n^j · (n² − n)^(k − j)` divided by `n! · k!`.  Isomorphism
  classes are the orbits of `S_n × S_k` acting on ordered edge sequences, and
  `|Aut|` of a class is the stabilizer cardinality; the identity is Burnside's
  class formula instantiated at this action.
* `card_cell`: the ordered-sequence count itself,
  `|Cell n k j| = C(k, j) · n^j · (n² − n)^(k − j)`.
* `margin_count`: the marginal over the loop count is `n^(2k)` (the binomial
  theorem at `n + (n² − n) = n²`).
* `conditional_loop_pmf`: conditional on `(n, k)`, the loop count is
  `Binomial(k, 1/n)` — the exact pmf, as a corollary of the census identity's
  counting lemma.
* `total_mass_eq_M0`: the cap-`c` ensemble mass has the closed form
  `M0 = (c+1) · Σ_{n,k} n^(2k)/(n! · k!)`, the `(c+1)` being the free `nT`.
* `conditional_loop_mean`: `E[n_loop | n, k] = k/n`.

## Executable cross-checks

`a36_anomaly_mechanism.py` recomputes the same cell masses by enumeration at
caps 1–6 (zero mismatches against the frozen receipts).  The
`DecidabilityChecks` section re-verifies the counting theorem by kernel
computation (`decide`) on small cells and the full product-form mass identity
at caps 1 and 2, independently of the proofs above.

## Tags

All results in this file are THEOREM candidates: they are proved in Lean with
the base axiom triple `[propext, Classical.choice, Quot.sound]` (audited
below).  Classical choice enters only through the enumeration of the finite
orbit space and the choice of orbit representatives (`Quotient.out`); the
counts and the rational identities are constructive.
-/

namespace Gap2CensusProductForm

open Nat

/-- The relabeling group of the census: vertex permutations times edge-slot
permutations. -/
abbrev CensusGroup (n k : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin k)

/-- Ordered edge sequences: `k` directed edges on `n` vertices, positions
labeled.  Isomorphism classes of the C11 ensemble are the orbits of the
census group on these sequences. -/
abbrev EdgeSeq (n k : ℕ) := Fin k → Fin n × Fin n

/-- An edge is a loop when its endpoints coincide. -/
def IsLoop {n : ℕ} (e : Fin n × Fin n) : Prop := e.1 = e.2

instance {n : ℕ} (e : Fin n × Fin n) : Decidable (IsLoop e) :=
  inferInstanceAs (Decidable (e.1 = e.2))

/-- The set of loop positions of an edge sequence. -/
def loopSet {n k : ℕ} (f : EdgeSeq n k) : Finset (Fin k) :=
  Finset.univ.filter fun i => IsLoop (f i)

/-- The number of loops of an edge sequence. -/
def loopCount {n k : ℕ} (f : EdgeSeq n k) : ℕ := (loopSet f).card

/-- The `(n, k, j)` cell: edge sequences on `n` vertices with `k` edges and
exactly `j` loops.  An `abbrev` so that the subtype's `Fintype` and
decidability instances apply directly to cells. -/
abbrev Cell (n k j : ℕ) := { f : EdgeSeq n k // loopCount f = j }

/-- Off-diagonal pairs: the legal values of a non-loop edge.  An `abbrev` so
the subtype's `Fintype` instance applies directly. -/
abbrev OffDiag (n : ℕ) := { e : Fin n × Fin n // ¬ IsLoop e }

/-! ## The census group action

`S_n × S_k` acts on ordered edge sequences by permuting vertices (on both
endpoints) and edge positions.  The action is a left action: position `i` of
`g • f` is the relabeled edge `f (g₂⁻¹ i)`.  Loop status and loop count are
invariant, so the action descends to each cell. -/

section Action

variable {n k : ℕ}

instance : SMul (CensusGroup n k) (EdgeSeq n k) where
  smul g f i := (g.1 (f (g.2⁻¹ i)).1, g.1 (f (g.2⁻¹ i)).2)

theorem smul_edgeSeq (g : CensusGroup n k) (f : EdgeSeq n k) (i : Fin k) :
    (g • f) i = (g.1 (f (g.2⁻¹ i)).1, g.1 (f (g.2⁻¹ i)).2) := rfl

instance : MulAction (CensusGroup n k) (EdgeSeq n k) where
  one_smul f := by
    funext i
    simp only [smul_edgeSeq]
    show ((1 : Equiv.Perm (Fin n)) (f ((1 : Equiv.Perm (Fin k))⁻¹ i)).1,
        (1 : Equiv.Perm (Fin n)) (f ((1 : Equiv.Perm (Fin k))⁻¹ i)).2) = f i
    simp
  mul_smul g h f := by
    obtain ⟨g1, g2⟩ := g
    obtain ⟨h1, h2⟩ := h
    funext i
    simp only [smul_edgeSeq, Prod.mk_mul_mk, Equiv.Perm.mul_apply, mul_inv_rev]

/-- Loop status is invariant under relabeling (a permutation is injective). -/
theorem isLoop_smul_iff (g : CensusGroup n k) (f : EdgeSeq n k) (i : Fin k) :
    IsLoop ((g • f) i) ↔ IsLoop (f (g.2⁻¹ i)) := by
  rw [smul_edgeSeq]
  show (g.1 (f (g.2⁻¹ i)).1 = g.1 (f (g.2⁻¹ i)).2) ↔
    ((f (g.2⁻¹ i)).1 = (f (g.2⁻¹ i)).2)
  exact g.1.apply_eq_iff_eq

/-- The loop set is covariant: relabeling positions maps the loop set by the
position permutation. -/
theorem loopSet_smul (g : CensusGroup n k) (f : EdgeSeq n k) :
    loopSet (g • f) = (loopSet f).map ⟨g.2, g.2.injective⟩ := by
  ext i
  simp only [loopSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro h
    exact ⟨g.2⁻¹ i, (isLoop_smul_iff g f i).1 h, Equiv.apply_symm_apply g.2 i⟩
  · rintro ⟨j, hj, rfl⟩
    rw [isLoop_smul_iff, show g.2⁻¹ (g.2 j) = j from Equiv.symm_apply_apply g.2 j]
    exact hj

/-- The loop count is invariant under the census action. -/
theorem loopCount_smul (g : CensusGroup n k) (f : EdgeSeq n k) :
    loopCount (g • f) = loopCount f := by
  show (loopSet (g • f)).card = (loopSet f).card
  rw [loopSet_smul, Finset.card_map]

variable {j : ℕ}

instance : SMul (CensusGroup n k) (Cell n k j) where
  smul g f := ⟨g • f.1, by rw [loopCount_smul]; exact f.2⟩

theorem smul_cell (g : CensusGroup n k) (f : Cell n k j) :
    (g • f).1 = g • f.1 := rfl

instance : MulAction (CensusGroup n k) (Cell n k j) where
  one_smul f := Subtype.ext (one_smul _ f.1)
  mul_smul g h f := Subtype.ext (mul_smul g h f.1)

/-- A group element stabilizes a cell element iff it stabilizes the underlying
edge sequence. -/
theorem mem_stabilizer_cell (g : CensusGroup n k) (f : Cell n k j) :
    g ∈ MulAction.stabilizer (CensusGroup n k) f ↔ g • f.1 = f.1 := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  exact Iff.rfl

/-- The orbit relation of the census action: two cell elements are isomorphic
iff a vertex permutation and an edge-slot permutation carry one to the other. -/
scoped instance : Setoid (Cell n k j) :=
  MulAction.orbitRel (CensusGroup n k) (Cell n k j)

/-- Classical decidability of the orbit relation; used only to enumerate the
finite orbit space. -/
noncomputable scoped instance : DecidableRel ((· ≈ ·) : Cell n k j → Cell n k j → Prop) :=
  Classical.decRel _

/-- Stabilizer membership is constructively decidable: it is pointwise
equality of two edge sequences over a finite index type. -/
scoped instance (f : Cell n k j) :
    DecidablePred (· ∈ MulAction.stabilizer (CensusGroup n k) f) := fun g =>
  decidable_of_iff (∀ i : Fin k, (g • f.1) i = f.1 i)
    (((mem_stabilizer_cell g f).trans funext_iff).symm)

end Action

/-! ## Counting the cell

The cell count `C(k, j) · n^j · (n² − n)^(k − j)` comes from a product
decomposition: choose the `j` loop positions (`C(k, j)` ways), assign a
diagonal vertex to each loop position (`n^j` ways), and assign an
off-diagonal pair to each remaining position (`(n² − n)^(k − j)` ways). -/

section Counting

/-- The diagonal pairs are in bijection with the vertices. -/
def diagEquiv (n : ℕ) : { e : Fin n × Fin n // IsLoop e } ≃ Fin n where
  toFun e := e.1.1
  invFun i := ⟨⟨i, i⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    cases hab
    rfl
  right_inv _ := rfl

/-- There are `n² − n` off-diagonal pairs. -/
theorem card_offDiag (n : ℕ) : Nat.card (OffDiag n) = n ^ 2 - n := by
  have h : Fintype.card { e : Fin n × Fin n // ¬ IsLoop e } = n ^ 2 - n := by
    rw [Fintype.card_subtype_compl (fun e => IsLoop e), Fintype.card_congr (diagEquiv n),
      Fintype.card_prod, Fintype.card_fin, pow_two]
  rw [Nat.card_eq_fintype_card]
  exact h

/-- Sequences with a prescribed loop set map to their loop values (one vertex
per loop position) and their off-loop values (one off-diagonal pair per
remaining position). -/
def fiberTo {n k : ℕ} {S : Finset (Fin k)} (f : { f : EdgeSeq n k // loopSet f = S }) :
    (S → Fin n) × ((Sᶜ : Finset (Fin k)) → OffDiag n) :=
  ⟨fun i => (f.1 i.1).1, fun i =>
    ⟨f.1 i.1, fun hloop => by
      have hmem : i.1 ∈ loopSet f.1 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hloop⟩
      rw [f.2] at hmem
      exact (Finset.mem_compl.1 i.2) hmem⟩⟩

/-- The inverse: build an edge sequence from loop values and off-loop values. -/
def fiberInv {n k : ℕ} {S : Finset (Fin k)}
    (g : (S → Fin n) × ((Sᶜ : Finset (Fin k)) → OffDiag n)) :
    { f : EdgeSeq n k // loopSet f = S } :=
  ⟨fun i => if h : i ∈ S then (g.1 ⟨i, h⟩, g.1 ⟨i, h⟩) else (g.2 ⟨i, Finset.mem_compl.2 h⟩).1,
   by
    ext i
    simp only [loopSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S
    · rw [dif_pos hi]
      exact ⟨fun _ => hi, fun _ => rfl⟩
    · rw [dif_neg hi]
      exact ⟨fun hloop => ((g.2 ⟨i, Finset.mem_compl.2 hi⟩).2 hloop).elim,
        fun h => (hi h).elim⟩⟩

theorem fiberInv_apply {n k : ℕ} {S : Finset (Fin k)}
    (g : (S → Fin n) × ((Sᶜ : Finset (Fin k)) → OffDiag n)) (i : Fin k) :
    (fiberInv g).1 i =
      if h : i ∈ S then (g.1 ⟨i, h⟩, g.1 ⟨i, h⟩) else (g.2 ⟨i, Finset.mem_compl.2 h⟩).1 := rfl

/-- The fiber over a loop set factors as a product of independent choices. -/
def fiberEquiv {n k : ℕ} (S : Finset (Fin k)) :
    { f : EdgeSeq n k // loopSet f = S } ≃
      (S → Fin n) × ((Sᶜ : Finset (Fin k)) → OffDiag n) where
  toFun := fiberTo
  invFun := fiberInv
  left_inv f := by
    apply Subtype.ext
    funext i
    rw [fiberInv_apply]
    by_cases hi : i ∈ S
    · rw [dif_pos hi]
      have hloop : (f.1 i).1 = (f.1 i).2 := by
        have hmem : i ∈ loopSet f.1 := by
          rw [f.2]
          exact hi
        exact (Finset.mem_filter.1 hmem).2
      exact Prod.ext rfl hloop
    · rw [dif_neg hi]
      rfl
  right_inv g := by
    refine Prod.ext ?_ ?_
    · funext i
      show ((fiberInv g).1 i.1).1 = g.1 i
      rw [fiberInv_apply, dif_pos i.2]
    · funext i
      apply Subtype.ext
      show (fiberInv g).1 i.1 = (g.2 i).1
      rw [fiberInv_apply, dif_neg (Finset.mem_compl.1 i.2)]

/-- The fiber over a loop set of size `j` has `n^j · (n² − n)^(k − j)`
elements. -/
theorem card_fiber {n k : ℕ} (S : Finset (Fin k)) :
    Nat.card { f : EdgeSeq n k // loopSet f = S }
      = n ^ S.card * (n ^ 2 - n) ^ (k - S.card) := by
  rw [Nat.card_congr (fiberEquiv S), Nat.card_prod, Nat.card_fun, Nat.card_fun,
    Nat.card_fin, card_offDiag, Nat.card_eq_fintype_card, Fintype.card_coe,
    Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

/-- The cell decomposes over the possible loop sets. -/
def cellDecomp (n k j : ℕ) :
    Cell n k j ≃ Σ S : { S : Finset (Fin k) // S.card = j },
      { f : EdgeSeq n k // loopSet f = S.1 } where
  toFun f := ⟨⟨loopSet f.1, f.2⟩, f.1, rfl⟩
  invFun g := ⟨g.2.1, by
    show (loopSet g.2.1).card = j
    rw [g.2.2]
    exact g.1.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨S, hS⟩, f, hf⟩
    cases hf
    rfl

/-- **The cell count.**  The `(n, k, j)` cell has
`C(k, j) · n^j · (n² − n)^(k − j)` ordered edge sequences: choose the loop
positions, then the loop values, then the off-loop values. -/
theorem card_cell (n k j : ℕ) :
    Fintype.card (Cell n k j) = Nat.choose k j * (n ^ j * (n ^ 2 - n) ^ (k - j)) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (cellDecomp n k j),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hfiber : ∀ S : { S : Finset (Fin k) // S.card = j },
      Fintype.card { f : EdgeSeq n k // loopSet f = S.1 }
        = n ^ j * (n ^ 2 - n) ^ (k - j) := by
    intro S
    rw [← Nat.card_eq_fintype_card, card_fiber S.1, S.2]
  rw [Finset.sum_congr rfl fun S _ => hfiber S]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]

end Counting

/-! ## The census identity -/

/-- The ordered-sequence count of the `(n, k, j)` cell. -/
def cellCount (n k j : ℕ) : ℕ := Nat.choose k j * (n ^ j * (n ^ 2 - n) ^ (k - j))

/-- **The census identity (Burnside / orbit–stabilizer).**  The sum of
`1/|Aut|` over the isomorphism classes of the `(n, k, j)` cell — the
un-normalized mass the C11 ensemble assigns to that cell — equals the
ordered-sequence count divided by `n! · k!`.

Formally: the classes are the orbits of `CensusGroup n k = S_n × S_k` on
`Cell n k j`, the automorphism count of a class is the cardinality of the
stabilizer of any representative, and the identity is the class formula
`|X| = Σ_{orbits} |G| / |stab|` divided through by `|G|`, each natural
division being exact by Lagrange's theorem. -/
theorem census_identity (n k j : ℕ) :
    (∑ x : Quotient (MulAction.orbitRel (CensusGroup n k) (Cell n k j)),
      (1 : ℚ) / (Fintype.card (MulAction.stabilizer (CensusGroup n k) (Quotient.out x)) : ℚ))
    = (cellCount n k j : ℚ) / (n ! * k !) := by
  classical
  have hG : Fintype.card (CensusGroup n k) = n ! * k ! := by
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fin]
  have hX : Fintype.card (Cell n k j) = cellCount n k j := card_cell n k j
  have hcls := MulAction.card_eq_sum_card_group_div_card_stabilizer (CensusGroup n k)
    (Cell n k j)
  rw [hG, hX] at hcls
  have hdvd : ∀ ω : Quotient (MulAction.orbitRel (CensusGroup n k) (Cell n k j)),
      Fintype.card (MulAction.stabilizer (CensusGroup n k) ω.out) ∣ n ! * k ! := by
    intro ω
    rw [← hG, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hcast : ∀ ω : Quotient (MulAction.orbitRel (CensusGroup n k) (Cell n k j)),
      (((n ! * k !) / Fintype.card (MulAction.stabilizer (CensusGroup n k) ω.out) : ℕ) : ℚ)
        = ((n ! * k ! : ℕ) : ℚ) /
          (Fintype.card (MulAction.stabilizer (CensusGroup n k) ω.out) : ℚ) := by
    intro ω
    exact Nat.cast_div_charZero (K := ℚ) (hdvd ω)
  have hℚ : (cellCount n k j : ℚ)
      = ∑ ω : Quotient (MulAction.orbitRel (CensusGroup n k) (Cell n k j)),
          ((n ! * k ! : ℕ) : ℚ) /
            (Fintype.card (MulAction.stabilizer (CensusGroup n k) ω.out) : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hcls
    rw [Nat.cast_sum] at h
    rw [h]
    exact Finset.sum_congr rfl fun ω _ => hcast ω
  have hN : (n ! * k ! : ℚ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne')
      (Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne')
  rw [eq_div_iff_mul_eq hN, hℚ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ω _ => by rw [div_mul_eq_mul_div, one_mul, ← Nat.cast_mul]

/-! ## Corollaries: the binomial law and the closed-form normalization -/

section Corollaries

/-- `n + (n² − n) = n²`, the point at which the binomial theorem is applied. -/
theorem add_sq_sub (n : ℕ) : n + (n ^ 2 - n) = n ^ 2 := by
  rcases n with _ | n
  · simp
  · rw [Nat.add_comm,
      Nat.sub_add_cancel (le_self_pow (by omega : (1 : ℕ) ≤ n + 1) (by decide : (2 : ℕ) ≠ 0))]

/-- **The marginal count.**  Summing the cell count over the loop count gives
`n^(2k)`: the binomial theorem at `n + (n² − n) = n²`. -/
theorem margin_count (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), cellCount n k j) = n ^ (2 * k) := by
  have h : (∑ j ∈ Finset.range (k + 1), cellCount n k j) = (n + (n ^ 2 - n)) ^ k := by
    rw [(Commute.all _ _).add_pow k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cellCount, Nat.cast_id]
    ring
  rw [h, add_sq_sub, ← pow_mul]

/-- **The conditional binomial law.**  Conditional on `(n, k)`, the loop
count of a census class is `Binomial(k, 1/n)`: its probability mass function
is `C(k, j) · (1/n)^j · (1 − 1/n)^(k − j)`.  For `j > k` both sides vanish. -/
theorem conditional_loop_pmf (n k j : ℕ) (hn : n ≠ 0) :
    (cellCount n k j : ℚ) / ((n ^ (2 * k) : ℕ) : ℚ) =
      (Nat.choose k j : ℚ) * (1 / (n : ℚ)) ^ j * (1 - 1 / (n : ℚ)) ^ (k - j) := by
  rcases lt_or_ge k j with hjk | hjk
  · have h0 : Nat.choose k j = 0 := Nat.choose_eq_zero_of_lt hjk
    simp [cellCount, h0]
  · have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have h1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.2 hn
    have hsq : n ^ 2 - n = n * (n - 1) := by rw [pow_two, Nat.mul_sub_one]
    have hdecomp : 2 * k = j + j + (k - j) + (k - j) := by omega
    have hbase : (1 : ℚ) - 1 / (n : ℚ) = ((n : ℚ) - 1) / n := by field_simp
    rw [cellCount, hsq, mul_pow]
    push_cast [Nat.cast_sub h1]
    rw [hdecomp]
    simp only [pow_add]
    rw [hbase, div_pow, div_pow, one_pow]
    field_simp [hn']

/-- The normalization constant of the cap-`c` census law: the free `nT`
contributes the factor `c + 1`. -/
def censusM0 (c : ℕ) : ℚ :=
  (c + 1 : ℚ) * ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    ((n ^ (2 * k) : ℕ) : ℚ) / (n ! * k !)

/-- **The closed form of the census normalization.**  The total
un-normalized mass of the cap-`c` ensemble (summing over `n`, `k`, the free
`t`, and the loop count `j`) is
`M0 = (c+1) · Σ_{n,k} n^(2k)/(n! · k!)`. -/
theorem total_mass_eq_M0 (c : ℕ) :
    (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1), ∑ _t ∈ Finset.range (c + 1),
      ∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℚ) / (n ! * k !))
    = censusM0 c := by
  rw [censusM0]
  have ht : ∀ n k : ℕ, (∑ _t ∈ Finset.range (c + 1),
      ∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℚ) / (n ! * k !))
      = (c + 1 : ℚ) * (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℚ) / (n ! * k !)) := by
    intro n k
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  simp_rw [ht]
  simp only [← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_div, ← Nat.cast_sum, margin_count]

/-- Weighted binomial sum: `Σ_j j·C(k,j)·a^j·b^(k−j) = k·a·(a+b)^(k−1)`.  The
combinatorial heart of the conditional mean. -/
theorem sum_choose_weighted (a b k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), j * Nat.choose k j * a ^ j * b ^ (k - j))
      = k * a * (a + b) ^ (k - 1) := by
  cases k with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    simp only [zero_mul, add_zero]
    have hterm : ∀ j ∈ Finset.range (m + 1),
        (j + 1) * Nat.choose (m + 1) (j + 1) * a ^ (j + 1) * b ^ (m + 1 - (j + 1))
          = (m + 1) * a * (Nat.choose m j * a ^ j * b ^ (m - j)) := by
      intro j _
      have hch : (m + 1) * Nat.choose m j = (j + 1) * Nat.choose (m + 1) (j + 1) :=
        (Nat.add_one_mul_choose_eq m j).trans (mul_comm _ _)
      rw [Nat.add_sub_add_right, pow_succ, ← hch]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Nat.add_sub_cancel]
    congr 1
    rw [(Commute.all _ _).add_pow m]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.cast_id]; ring

/-- **The conditional mean.**  `E[n_loop | n, k] = k / n`, the mean of the
conditional binomial law. -/
theorem conditional_loop_mean (n k : ℕ) (hn : n ≠ 0) :
    (∑ j ∈ Finset.range (k + 1), (j : ℚ) * (cellCount n k j : ℚ) / ((n ^ (2 * k) : ℕ) : ℚ))
      = (k : ℚ) / n := by
  rcases k with _ | m
  · simp
  · have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have key : (∑ j ∈ Finset.range (m + 1 + 1), j * cellCount n (m + 1) j)
        = (m + 1) * n * (n ^ 2) ^ m := by
      have h := sum_choose_weighted n (n ^ 2 - n) (m + 1)
      rw [add_sq_sub n, Nat.add_sub_cancel] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cellCount]
      ring
    simp_rw [← Nat.cast_mul]
    rw [← Finset.sum_div, ← Nat.cast_sum, key]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow]
    have hpow : (n : ℚ) ^ (2 * (m + 1)) ≠ 0 := pow_ne_zero _ hn'
    rw [div_eq_div_iff hpow hn', pow_mul, pow_succ]
    ring

end Corollaries

/-! ## Decidability checks

Kernel computations cross-checking the counting theorem against the
executable specification `a36_anomaly_mechanism.py` (which verifies the
product form per cell at caps 1–6).  The cell-level checks compare
`Fintype.card (Cell n k j)`, computed by enumerating the subtype, against
`cellCount n k j`, computed from the formula, with no reference to the
proofs above.  The cap-level checks evaluate the full product-form mass
identity at caps 1 and 2: the counts by kernel computation in `ℕ`, and the
rational identity by instantiating the proved theorem. -/

section DecidabilityChecks

example : Fintype.card (Cell 1 1 0) = cellCount 1 1 0 := by decide
example : Fintype.card (Cell 1 1 1) = cellCount 1 1 1 := by decide
example : Fintype.card (Cell 2 1 0) = cellCount 2 1 0 := by decide
example : Fintype.card (Cell 2 1 1) = cellCount 2 1 1 := by decide
example : Fintype.card (Cell 2 2 0) = cellCount 2 2 0 := by decide
example : Fintype.card (Cell 2 2 1) = cellCount 2 2 1 := by decide
example : Fintype.card (Cell 2 2 2) = cellCount 2 2 2 := by decide
example : Fintype.card (Cell 2 3 1) = cellCount 2 3 1 := by decide
example : Fintype.card (Cell 3 2 1) = cellCount 3 2 1 := by decide
set_option maxRecDepth 8192 in
example : Fintype.card (Cell 3 3 0) = cellCount 3 3 0 := by decide
set_option maxRecDepth 8192 in
example : Fintype.card (Cell 3 3 1) = cellCount 3 3 1 := by decide
set_option maxRecDepth 8192 in
example : Fintype.card (Cell 3 3 2) = cellCount 3 3 2 := by decide
set_option maxRecDepth 8192 in
example : Fintype.card (Cell 3 3 3) = cellCount 3 3 3 := by decide
example : Fintype.card (Cell 2 2 3) = cellCount 2 2 3 := by decide

-- Cap-level product-form identity at cap 1, checked by the kernel in `ℕ`
-- (the rational version is `total_mass_eq_M0 1`; kernel `decide` on rational
-- sums is unreliable, so the executable cross-check runs on the counts).
set_option maxRecDepth 32768 in
example : (∑ n ∈ Finset.range 2, ∑ k ∈ Finset.range 2, ∑ _t ∈ Finset.range 2,
    ∑ j ∈ Finset.range (k + 1), cellCount n k j)
    = (1 + 1) * ∑ n ∈ Finset.range 2, ∑ k ∈ Finset.range 2, n ^ (2 * k) := by decide

/-- The rational cap-1 mass identity, as an instance of the proved theorem. -/
example : (∑ n ∈ Finset.range 2, ∑ k ∈ Finset.range 2, ∑ _t ∈ Finset.range 2,
    ∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℚ) / (n ! * k !))
    = censusM0 1 := total_mass_eq_M0 1

-- Cap-level product-form identity at cap 2, kernel-checked in `ℕ`.
set_option maxRecDepth 32768 in
example : (∑ n ∈ Finset.range 3, ∑ k ∈ Finset.range 3, ∑ _t ∈ Finset.range 3,
    ∑ j ∈ Finset.range (k + 1), cellCount n k j)
    = (2 + 1) * ∑ n ∈ Finset.range 3, ∑ k ∈ Finset.range 3, n ^ (2 * k) := by decide

/-- The rational cap-2 mass identity, as an instance of the proved theorem. -/
example : (∑ n ∈ Finset.range 3, ∑ k ∈ Finset.range 3, ∑ _t ∈ Finset.range 3,
    ∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℚ) / (n ! * k !))
    = censusM0 2 := total_mass_eq_M0 2

end DecidabilityChecks

#print axioms census_identity
#print axioms card_cell
#print axioms conditional_loop_pmf
#print axioms total_mass_eq_M0
#print axioms conditional_loop_mean
#print axioms margin_count

end Gap2CensusProductForm
