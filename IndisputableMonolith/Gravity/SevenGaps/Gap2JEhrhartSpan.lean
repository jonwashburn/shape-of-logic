import IndisputableMonolith.Gravity.SevenGaps.Gap2PostingCostDerivation

/-!
# Gap 2 / C2: the recognition cost of a letter in context, and the census span test

`Gap2PostingCostDerivation` reduces the measure to **aggregate linearity by kind**
(`FixedKindTotals`): the total charge of each kind is a fixed multiple of that kind's
count.  `Gap2FugacityPostingGluing` then showed the posting layer plus the gluing law
leaves the three rates entirely free.  The route this module tests is the one that
would fix them: define the recognition cost `J` of a letter from the **imbalance**
structure the ledger layer already carries, and read the three rates off its
census representation.

## §1-§2.  What `J` is, and that it is derived rather than stipulated

Ground truth is the kernel identity
`ChartFromLedgerMomentum.Jlog_eq_imbalance_sq_div_two_casimir`:

    recognition cost  =  (net ledger imbalance) ^ 2 / (2 * Casimir).

The complex-level ledger state of a letter is supplied by the carrier and not
invented here.  `BoundedComplex.edgeVerts` is an **ordered** pair, so every edge is
one directed recognition posting: it debits its head and credits its tail.  The
ledger state of a vertex letter `v` inside a complex `K` is therefore
`(indeg K v, outdeg K v)`, its net imbalance is `vertexImbalance K v`, and its
recognition cost is that imbalance squared over twice the Casimir (`jCost`).  An
edge letter is itself one balanced posting, one debit and one credit, so its
imbalance is zero; a top-cell letter is not a posting target, so its imbalance is
zero.  Both are charged nothing, which is a consequence of the dual-entry reading
and not a modelling choice made to be convenient.

Three properties are recorded because the route needs all three.  `jCost` is a
legitimate `LetterCost`, since the kernel's `LetterCost` already sees the whole
complex as well as the letter, so context dependence is the general case
(`jCost` needs no amendment to state).  It is gauge equivariant
(`jCost_equivariant`), so nothing below is an artifact of a labelling.  And the
bulk cancels: a vertex whose incident postings pair up is charged nothing
(`jCost_vanishes_on_balanced_vertex`), which is why `J` on a region of the
Freudenthal carrier accrues only at the boundary.

## §3.  The verdict: `J` induces no aggregate-linear letter cost

`jCost` is **not** `FixedKindTotals`, and the failing configuration is two
complexes with two cells between them.  A single vertex has no incident postings,
so its imbalance is zero, so the vertex block sums to zero, so `cV = 0`.  A single
edge has two vertices of imbalance one, so its vertex block sums to `1 / kappa`,
which must be `cV * 2 = 0`.  For any nonzero Casimir that is a contradiction
(`jCost_not_fixedKindTotals`).

The same quadratic is why `J` is not a valuation.  A two-edge path is two edges
glued along one vertex; the interface **imbalances** cancel exactly, so the middle
vertex is charged nothing, but the two edge **costs** do not cancel, and the path
costs `1 / kappa` against the `2 / kappa` a valuation would give
(`jCost_not_a_valuation`).  Bulk cancellation inside the square and additivity of
the square are different properties, and only the first one holds.

## §4-§5.  The census span test, and the 3D test's vacuity

§4 carries the moment vectors measured by exact enumeration of the Freudenthal
(Kuhn) carrier on dilates of a cube region, in the basis `(N^d, ..., N, 1)`.
Those numbers are MEASURED (`scripts/qg/qg_j_ehrhart_span_20260730.py`, exact
integer arithmetic, quasi-polynomial fits verified on held-out dilates); every
theorem below is a THEOREM about them.

* In four dimensions no rational triple of kind rates, and no triple plus an
  additive constant, reproduces `J`'s moment vector
  (`J4_not_in_census_span`, `J4_not_in_census_span_with_const`).  The obstruction
  is a single integer functional of the moments,
  `u = (0, 1, -2, 2, 0)`, which annihilates all three counts and the constant and
  returns `192` on `J` (`cert4_annihilates_census`, `cert4_sees_J4`).
* In three dimensions the same holds for the three counts alone
  (`J3_not_in_census_span`, certificate `(0, 1, -3, 6)`).
* **But the three-dimensional test with a constant column cannot fail.**  Its
  4-by-4 matrix has determinant `-108`, so the map from rates to moments is onto:
  *every* moment vector is in the span, `J`'s included
  (`census3_with_const_is_onto`, `census3_det`).  The inversion that theorem
  exhibits is exactly the published one,
  `c_E = (j2 - j1)/6`, `c_V = (3 j1 - j2)/6`, `c_T = (j3 - j2 + (2/3) j1)/6`, whose
  arithmetic is correct; what fails is the reading, because a square invertible
  system returns a triple for any input whatever and so discriminates nothing.
  The free prediction that was supposed to carry the content, `j0 = c_V`, is false
  on the measured moments: `j0 = 2` while `c_V = -4` (`j0_ne_cV_3D`).

## Scope

The verdict is exactly as strong as the object it is about: the recognition cost
built from vertex-level ledger imbalance on the Freudenthal carrier, over the
region families enumerated.  It closes that route and says nothing about a cost
built from some other imbalance referent.  It does not flip any flag; flag
`gap2_measure_derived` stays as it was, with its premise unchanged.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2JEhrhartSpan

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation

variable {B : ℕ}

/-! ## §1. The ledger state of a vertex letter, from the carrier's own incidence -/

/-- Out-postings at a vertex: edges whose ordered first endpoint is `v`.  These are
the credits of the dual-entry reading. -/
def outdeg (K : BoundedComplex B) (v : Fin K.nV) : ℕ :=
  (Finset.univ.filter fun e : Fin K.nE => (K.edgeVerts e).1 = v).card

/-- In-postings at a vertex: edges whose ordered second endpoint is `v`.  These are
the debits. -/
def indeg (K : BoundedComplex B) (v : Fin K.nV) : ℕ :=
  (Finset.univ.filter fun e : Fin K.nE => (K.edgeVerts e).2 = v).card

/-- **The net recognition imbalance of a vertex letter in context**: debits minus
credits, read off the carrier's ordered edge incidence.  Nothing is stipulated: the
ordering is already in `BoundedComplex.edgeVerts`. -/
def vertexImbalance (K : BoundedComplex B) (v : Fin K.nV) : ℤ :=
  (indeg K v : ℤ) - (outdeg K v : ℤ)

/-- The squared-imbalance total of a complex, the integer part of `J`. -/
def imbalanceSq (K : BoundedComplex B) : ℤ :=
  ∑ v : Fin K.nV, (vertexImbalance K v) ^ 2

theorem indeg_eq_sum (K : BoundedComplex B) (v : Fin K.nV) :
    indeg K v = ∑ e : Fin K.nE, if (K.edgeVerts e).2 = v then 1 else 0 := by
  classical
  simp only [indeg, Finset.card_filter]

theorem outdeg_eq_sum (K : BoundedComplex B) (v : Fin K.nV) :
    outdeg K v = ∑ e : Fin K.nE, if (K.edgeVerts e).1 = v then 1 else 0 := by
  classical
  simp only [outdeg, Finset.card_filter]

/-! ## §2. `jCost`: the derived letter cost, and its three needed properties -/

noncomputable section

/-- **The recognition cost of a letter in context.**  A vertex letter is charged its
net ledger imbalance squared over twice the Casimir, which is the kernel identity
`Jlog_eq_imbalance_sq_div_two_casimir` evaluated at the letter's own ledger state.
An edge letter is one balanced posting and a top-cell letter is not a posting
target, so both carry zero imbalance and zero charge. -/
def jCost (kappa : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inl v => ((vertexImbalance K v : ℝ)) ^ 2 / (2 * kappa)
  | Sum.inr _ => 0

@[simp] theorem jCost_inl (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    jCost kappa B K (Sum.inl v) = ((vertexImbalance K v : ℝ)) ^ 2 / (2 * kappa) := rfl

@[simp] theorem jCost_edge (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE) :
    jCost kappa B K (Sum.inr (Sum.inl e)) = 0 := rfl

@[simp] theorem jCost_tet (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (t : Fin K.nT) :
    jCost kappa B K (Sum.inr (Sum.inr t)) = 0 := rfl

/-- **`J` is the sum over its letters.**  The weak form of local additivity holds by
construction: the history cost of `jCost` is the vertex block sum, because the other
two blocks are silent. -/
theorem historyCost_jCost (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (jCost kappa) B K
      = ∑ v : Fin K.nV, jCost kappa B K (Sum.inl v) := by
  classical
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-- **Bulk cancellation, at the letter.**  A vertex whose incident postings pair up
carries zero imbalance and is charged nothing.  This is why `J` on a region of the
Freudenthal carrier accrues only on the boundary: an interior vertex has one
in-posting and one out-posting per displacement class. -/
theorem jCost_vanishes_on_balanced_vertex (kappa : ℝ) (B : ℕ) (K : BoundedComplex B)
    (v : Fin K.nV) (h : indeg K v = outdeg K v) :
    jCost kappa B K (Sum.inl v) = 0 := by
  have : vertexImbalance K v = 0 := by
    simp [vertexImbalance, h]
  simp [jCost_inl, this]

end

/-! ### Equivariance: the failure below is not a labelling artifact -/

theorem indeg_relabel {K K' : BoundedComplex B} (r : Relabel K K') (v : Fin K.nV) :
    indeg K v = indeg K' (r.vEquiv v) := by
  classical
  rw [indeg_eq_sum, indeg_eq_sum]
  refine Fintype.sum_equiv r.eEquiv _ _ ?_
  intro e
  rw [r.edge_comm e]
  by_cases h : (K.edgeVerts e).2 = v
  · simp [Prod.map, h]
  · have h' : ¬ (r.vEquiv ((K.edgeVerts e).2) = r.vEquiv v) := by
      intro hh; exact h (r.vEquiv.injective hh)
    simp [Prod.map, h, h']

theorem outdeg_relabel {K K' : BoundedComplex B} (r : Relabel K K') (v : Fin K.nV) :
    outdeg K v = outdeg K' (r.vEquiv v) := by
  classical
  rw [outdeg_eq_sum, outdeg_eq_sum]
  refine Fintype.sum_equiv r.eEquiv _ _ ?_
  intro e
  rw [r.edge_comm e]
  by_cases h : (K.edgeVerts e).1 = v
  · simp [Prod.map, h]
  · have h' : ¬ (r.vEquiv ((K.edgeVerts e).1) = r.vEquiv v) := by
      intro hh; exact h (r.vEquiv.injective hh)
    simp [Prod.map, h, h']

theorem vertexImbalance_relabel {K K' : BoundedComplex B} (r : Relabel K K')
    (v : Fin K.nV) : vertexImbalance K v = vertexImbalance K' (r.vEquiv v) := by
  simp [vertexImbalance, indeg_relabel r v, outdeg_relabel r v]

/-- **`jCost` is gauge equivariant.**  Labels are gauge for it, so every negative
result below is about the cost and not about a choice of names. -/
theorem jCost_equivariant (kappa : ℝ) : Equivariant (jCost kappa) := by
  intro B K K' r a
  cases a with
  | inl v =>
      simp only [postingAlphEquiv, Equiv.sumCongr_apply, Sum.map_inl, jCost_inl]
      rw [vertexImbalance_relabel r v]
  | inr b =>
      cases b with
      | inl e => simp [postingAlphEquiv]
      | inr t => simp [postingAlphEquiv]

/-! ## §3. The verdict: no aggregate-linear letter cost, and no valuation

Four explicit complexes at cap `4`.  `pointComplex` is one vertex; `edgeComplex` is
one edge; `pathComplex` is two edges glued along a vertex; `twoEdgeComplex` is two
disjoint edges. -/

/-- One vertex, no edges, no top cells. -/
def pointComplex : BoundedComplex 4 where
  nV := 1
  nE := 0
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => e.elim0
  tetVerts := fun t => t.elim0

/-- One directed edge `0 -> 1`. -/
def edgeComplex : BoundedComplex 4 where
  nV := 2
  nE := 1
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun _ => (0, 1)
  tetVerts := fun t => t.elim0

/-- Two edges glued along one vertex: `0 -> 1 -> 2`. -/
def pathComplex : BoundedComplex 4 where
  nV := 3
  nE := 2
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => if e = 0 then (0, 1) else (1, 2)
  tetVerts := fun t => t.elim0

/-- Two disjoint edges: `0 -> 1` and `2 -> 3`. -/
def twoEdgeComplex : BoundedComplex 4 where
  nV := 4
  nE := 2
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => if e = 0 then (0, 1) else (2, 3)
  tetVerts := fun t => t.elim0

theorem imbalance_point : ∀ v : Fin pointComplex.nV, vertexImbalance pointComplex v = 0 := by
  decide

theorem imbalance_edge_zero : vertexImbalance edgeComplex (0 : Fin 2) = -1 := by decide

theorem imbalance_edge_one : vertexImbalance edgeComplex (1 : Fin 2) = 1 := by decide

theorem imbalance_path_zero : vertexImbalance pathComplex (0 : Fin 3) = -1 := by decide

theorem imbalance_path_one : vertexImbalance pathComplex (1 : Fin 3) = 0 := by decide

theorem imbalance_path_two : vertexImbalance pathComplex (2 : Fin 3) = 1 := by decide

/-- **Non-vacuity of the bulk-cancellation clause.**  On the two-edge path the
middle vertex really is balanced and the two ends really are not, so
`jCost_vanishes_on_balanced_vertex` has an instance and a non-instance on the same
complex. -/
theorem path_middle_balanced_ends_not :
    indeg pathComplex (1 : Fin 3) = outdeg pathComplex (1 : Fin 3)
      ∧ indeg pathComplex (0 : Fin 3) ≠ outdeg pathComplex (0 : Fin 3)
      ∧ indeg pathComplex (2 : Fin 3) ≠ outdeg pathComplex (2 : Fin 3) := by
  decide

noncomputable section

theorem blockSum_point (kappa : ℝ) :
    (∑ v : Fin pointComplex.nV, jCost kappa 4 pointComplex (Sum.inl v)) = 0 := by
  simp [jCost_inl, imbalance_point]

theorem blockSum_edge (kappa : ℝ) (hk : kappa ≠ 0) :
    (∑ v : Fin edgeComplex.nV, jCost kappa 4 edgeComplex (Sum.inl v)) = 1 / kappa := by
  show (∑ v : Fin 2, jCost kappa 4 edgeComplex (Sum.inl v)) = 1 / kappa
  rw [Fin.sum_univ_two]
  simp only [jCost_inl, imbalance_edge_zero, imbalance_edge_one]
  push_cast
  field_simp <;> norm_num

theorem blockSum_path (kappa : ℝ) (hk : kappa ≠ 0) :
    (∑ v : Fin pathComplex.nV, jCost kappa 4 pathComplex (Sum.inl v)) = 1 / kappa := by
  show (∑ v : Fin 3, jCost kappa 4 pathComplex (Sum.inl v)) = 1 / kappa
  rw [Fin.sum_univ_three]
  simp only [jCost_inl, imbalance_path_zero, imbalance_path_one, imbalance_path_two]
  push_cast
  field_simp <;> norm_num

/-- **HEADLINE (the route fails at the letter).**  For every nonzero Casimir the
derived cost has no fixed kind totals, so it induces no additive letter cost by kind
and `measure_from_fixedKindTotals` cannot be applied to it.  The witness is two
complexes: a single vertex forces `cV = 0`, and a single edge then demands
`1 / kappa = 0`. -/
theorem jCost_not_fixedKindTotals (kappa : ℝ) (hk : kappa ≠ 0) :
    ¬ FixedKindTotals (jCost kappa) := by
  rintro ⟨cV, cE, cT, h⟩
  have hp := (h 4 pointComplex).1
  have he := (h 4 edgeComplex).1
  rw [blockSum_point kappa] at hp
  rw [blockSum_edge kappa hk] at he
  have h1 : ((pointComplex.nV : ℕ) : ℝ) = 1 := by
    show ((1 : ℕ) : ℝ) = 1
    norm_num
  have h2 : ((edgeComplex.nV : ℕ) : ℝ) = 2 := by
    show ((2 : ℕ) : ℝ) = 2
    norm_num
  rw [h1, mul_one] at hp
  rw [h2] at he
  have hcV : cV = 0 := hp.symm
  rw [hcV] at he
  have hz : (1 : ℝ) / kappa = 0 := by linarith
  exact (one_div_ne_zero hk) hz

/-- **The gluing failure, stated as arithmetic on three explicit complexes.**  The
two-edge path is two edges glued along one vertex, whose intersection is a single
vertex.  A valuation would give `1/kappa + 1/kappa - 0`; the path gives `1/kappa`.
The interface imbalances cancel exactly, and the interface costs do not. -/
theorem jCost_not_a_valuation (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 pathComplex
      ≠ historyCost (jCost kappa) 4 edgeComplex
        + historyCost (jCost kappa) 4 edgeComplex
        - historyCost (jCost kappa) 4 pointComplex := by
  rw [historyCost_jCost, historyCost_jCost, historyCost_jCost,
    blockSum_path kappa hk, blockSum_edge kappa hk, blockSum_point kappa]
  intro h
  have : (1 : ℝ) / kappa = 0 := by linarith
  exact (one_div_ne_zero hk) this

end

/-! ## §4. The census span test on the measured moment vectors

Moment vectors of the Freudenthal (Kuhn) carrier on cube dilates `R_N`, in the
basis `(N^d, ..., N, 1)`.  MEASURED by exact enumeration
(`scripts/qg/qg_j_ehrhart_span_20260730.py`); the fits reproduce held-out dilates
exactly, and both parity constituents of the period-doubled cell agree, so the
period-2 quasi-polynomial is a polynomial on this family.

`mJ4` is the moment vector of `2 * kappa * J`, whose leading coefficient is exactly
zero: `J` is a boundary functional of degree three in four dimensions. -/

/-- Vertex census of the 4D cube dilate: `(N+1)^4`. -/
def mV4 : Fin 5 → ℚ := ![1, 4, 6, 4, 1]

/-- Edge census of the 4D cube dilate over the fifteen displacement classes:
`(2N+1)^4 - (N+1)^4`. -/
def mE4 : Fin 5 → ℚ := ![15, 28, 18, 4, 0]

/-- Kuhn 4-simplex census of the 4D cube dilate: `24 N^4`. -/
def mT4 : Fin 5 → ℚ := ![24, 0, 0, 0, 0]

/-- The constant column. -/
def mC4 : Fin 5 → ℚ := ![0, 0, 0, 0, 1]

/-- MEASURED moment vector of `2 * kappa * J` on the 4D cube dilate. -/
def mJ4 : Fin 5 → ℚ := ![0, 512, 192, 32, 2]

/-- The obstruction functional: the integer combination of boundary strata that
every census column is blind to. -/
def cert4 : Fin 5 → ℚ := ![0, 1, -2, 2, 0]

def dot4 (u w : Fin 5 → ℚ) : ℚ := ∑ i, u i * w i

theorem cert4_annihilates_census :
    dot4 cert4 mV4 = 0 ∧ dot4 cert4 mE4 = 0 ∧ dot4 cert4 mT4 = 0
      ∧ dot4 cert4 mC4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [dot4, cert4, mV4, mE4, mT4, mC4, Fin.sum_univ_five] <;> norm_num

theorem cert4_sees_J4 : dot4 cert4 mJ4 = 192 := by
  simp [dot4, cert4, mJ4, Fin.sum_univ_five]
  norm_num

/-- **HEADLINE (outside the census span, four dimensions).**  No rational triple of
kind rates reproduces `J`'s measured moment vector on the 4D Freudenthal cube
dilate. -/
theorem J4_not_in_census_span :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 5, a * mV4 i + b * mE4 i + c * mT4 i = mJ4 i := by
  rintro ⟨a, b, c, h⟩
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [mV4, mE4, mT4, mJ4] at h1 h2 h3
  linarith

/-- **The same with an additive constant allowed.**  Adding a constant column does
not rescue it: the obstruction functional is blind to the constant too. -/
theorem J4_not_in_census_span_with_const :
    ¬ ∃ a b c d : ℚ,
      ∀ i : Fin 5, a * mV4 i + b * mE4 i + c * mT4 i + d * mC4 i = mJ4 i := by
  rintro ⟨a, b, c, d, h⟩
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [mV4, mE4, mT4, mC4, mJ4] at h1 h2 h3
  linarith

/-! ### The three-dimensional carrier, and why its published test cannot fail -/

def mV3 : Fin 4 → ℚ := ![1, 3, 3, 1]
def mE3 : Fin 4 → ℚ := ![7, 9, 3, 0]
def mT3 : Fin 4 → ℚ := ![6, 0, 0, 0]
def mC3 : Fin 4 → ℚ := ![0, 0, 0, 1]

/-- MEASURED moment vector of `2 * kappa * J` on the 3D cube dilate. -/
def mJ3 : Fin 4 → ℚ := ![0, 96, 24, 2]

def cert3 : Fin 4 → ℚ := ![0, 1, -3, 6]

def dot3 (u w : Fin 4 → ℚ) : ℚ := ∑ i, u i * w i

theorem cert3_annihilates_counts :
    dot3 cert3 mV3 = 0 ∧ dot3 cert3 mE3 = 0 ∧ dot3 cert3 mT3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [dot3, cert3, mV3, mE3, mT3, Fin.sum_univ_four] <;> norm_num

theorem cert3_sees_J3 : dot3 cert3 mJ3 = 36 := by
  simp [dot3, cert3, mJ3, Fin.sum_univ_four]
  norm_num

/-- No rational triple of kind rates reproduces `J`'s measured moment vector on the
3D Freudenthal cube dilate either. -/
theorem J3_not_in_census_span :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 4, a * mV3 i + b * mE3 i + c * mT3 i = mJ3 i := by
  rintro ⟨a, b, c, h⟩
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [mV3, mE3, mT3, mJ3] at h1 h2 h3
  linarith

/-- The published 3D census determinant, recomputed: `-108`, with the rows the four
boundary strata `(N^3, N^2, N, 1)` and the columns `(n_V, n_E, n_T, 1)`. -/
theorem census3_det :
    Matrix.det !![mV3 0, mE3 0, mT3 0, mC3 0;
                  mV3 1, mE3 1, mT3 1, mC3 1;
                  mV3 2, mE3 2, mT3 2, mC3 2;
                  mV3 3, mE3 3, mT3 3, mC3 3] = -108 := by
  simp [mV3, mE3, mT3, mC3, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Fin.succAbove] <;> norm_num

/-- **The three-dimensional test with a constant column is vacuous.**  The 4-by-4
census matrix is invertible, so the map from rates to moments is onto: for *every*
target moment vector a triple plus a constant exists, so no target can ever be
found outside the span and the test discriminates nothing.  The exhibited inversion
is exactly the published one, `c_E = (j2 - j1)/6`, `c_V = (3 j1 - j2)/6`,
`c_T = (j3 - j2 + (2/3) j1)/6`, `c_0 = j0 - c_V`, whose arithmetic is correct. -/
theorem census3_with_const_is_onto (t : Fin 4 → ℚ) :
    ∃ a b c d : ℚ,
      ∀ i : Fin 4, a * mV3 i + b * mE3 i + c * mT3 i + d * mC3 i = t i := by
  refine ⟨(3 * t 2 - t 1) / 6, (t 1 - t 2) / 6,
    (t 0 - t 1 + (2 / 3) * t 2) / 6, t 3 - (3 * t 2 - t 1) / 6, ?_⟩
  intro i
  fin_cases i <;> simp [mV3, mE3, mT3, mC3] <;> ring

/-- **The free prediction fails.**  `j0 = c_V` was the one independent consequence
the 3D inversion had left, and on the measured moments it is false: `j0 = 2` while
`c_V = -4`. -/
theorem j0_ne_cV_3D :
    mJ3 3 ≠ (3 * mJ3 2 - mJ3 1) / 6 := by
  simp [mJ3]
  norm_num

/-! ## §5. Certificate -/

/-- **The C2 span-test verdict.**  The derived cost is a gauge-equivariant letter
cost whose bulk cancels and which is the sum over its letters; it has no fixed kind
totals, it is not a valuation, and its measured moment vector lies outside the
census span in four dimensions with or without a constant column.  The published
three-dimensional inversion is arithmetically correct and vacuous, and its one free
prediction is false. -/
structure JEhrhartSpanVerdict : Prop where
  equivariant : ∀ kappa : ℝ, Equivariant (jCost kappa)
  bulk_cancels : ∀ (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV),
    indeg K v = outdeg K v → jCost kappa B K (Sum.inl v) = 0
  sum_over_letters : ∀ (kappa : ℝ) (B : ℕ) (K : BoundedComplex B),
    historyCost (jCost kappa) B K = ∑ v : Fin K.nV, jCost kappa B K (Sum.inl v)
  no_kind_totals : ∀ kappa : ℝ, kappa ≠ 0 → ¬ FixedKindTotals (jCost kappa)
  not_a_valuation : ∀ kappa : ℝ, kappa ≠ 0 →
    historyCost (jCost kappa) 4 pathComplex
      ≠ historyCost (jCost kappa) 4 edgeComplex
        + historyCost (jCost kappa) 4 edgeComplex
        - historyCost (jCost kappa) 4 pointComplex
  outside_span_4d :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 5, a * mV4 i + b * mE4 i + c * mT4 i = mJ4 i
  outside_span_4d_with_const :
    ¬ ∃ a b c d : ℚ,
      ∀ i : Fin 5, a * mV4 i + b * mE4 i + c * mT4 i + d * mC4 i = mJ4 i
  outside_span_3d :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 4, a * mV3 i + b * mE3 i + c * mT3 i = mJ3 i
  three_d_test_vacuous : ∀ t : Fin 4 → ℚ, ∃ a b c d : ℚ,
    ∀ i : Fin 4, a * mV3 i + b * mE3 i + c * mT3 i + d * mC3 i = t i
  three_d_determinant :
    Matrix.det !![mV3 0, mE3 0, mT3 0, mC3 0;
                  mV3 1, mE3 1, mT3 1, mC3 1;
                  mV3 2, mE3 2, mT3 2, mC3 2;
                  mV3 3, mE3 3, mT3 3, mC3 3] = -108
  free_prediction_fails : mJ3 3 ≠ (3 * mJ3 2 - mJ3 1) / 6

theorem jEhrhartSpanVerdict : JEhrhartSpanVerdict where
  equivariant := jCost_equivariant
  bulk_cancels := jCost_vanishes_on_balanced_vertex
  sum_over_letters := historyCost_jCost
  no_kind_totals := jCost_not_fixedKindTotals
  not_a_valuation := jCost_not_a_valuation
  outside_span_4d := J4_not_in_census_span
  outside_span_4d_with_const := J4_not_in_census_span_with_const
  outside_span_3d := J3_not_in_census_span
  three_d_test_vacuous := census3_with_const_is_onto
  three_d_determinant := census3_det
  free_prediction_fails := j0_ne_cV_3D

/-! ## Axiom audit -/

#print axioms historyCost_jCost
#print axioms jCost_vanishes_on_balanced_vertex
#print axioms jCost_equivariant
#print axioms path_middle_balanced_ends_not
#print axioms blockSum_point
#print axioms blockSum_edge
#print axioms blockSum_path
#print axioms jCost_not_fixedKindTotals
#print axioms jCost_not_a_valuation
#print axioms cert4_annihilates_census
#print axioms cert4_sees_J4
#print axioms J4_not_in_census_span
#print axioms J4_not_in_census_span_with_const
#print axioms cert3_annihilates_counts
#print axioms cert3_sees_J3
#print axioms J3_not_in_census_span
#print axioms census3_det
#print axioms census3_with_const_is_onto
#print axioms j0_ne_cV_3D
#print axioms jEhrhartSpanVerdict

end Gap2JEhrhartSpan
end SevenGaps
end Gravity
end IndisputableMonolith
