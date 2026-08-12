import IndisputableMonolith.Gravity.SevenGaps.Gap2JEhrhartSpan

/-!
# Gap 2 / C12: the oriented-face imbalance referent, and the census span test

`Gap2JEhrhartSpan` (lane A1.5) read the net ledger imbalance off **vertices** and
killed that route: the resulting recognition cost is gauge equivariant, is the sum
over its letters, and has bulk cancellation, but its measured moment vector lies
outside the span of the census in four dimensions.  That verdict was scoped to the
vertex referent and said nothing about a cost built from a different one.

This module builds the different one.

## §1.  The referent, and why it is not a relabelling of the old one

The vertex reading used a single structural fact: `BoundedComplex.edgeVerts` is an
**ordered** pair, so an edge is one directed posting, debiting its head and
crediting its tail, and a vertex's ledger state is its pair of degrees.

`BoundedComplex.tetVerts` is an **ordered** tuple too, `Fin K.nT → Fin 4 → Fin K.nV`.
The same reading one chain degree up says a top cell is one directed posting over
its own codimension-one facets, debiting the even-indexed ones and crediting the
odd-indexed ones.  That is the simplicial boundary with its alternating signs, and
the incidence sign of the `i`-th facet is `(-1)^i` (`facetSign`).  A facet is a
triangle, carried here as an ordered triple of vertices, and `orientSign` compares
two ordered triples: it returns `1` when they agree up to an even permutation, `-1`
up to an odd one, and `0` otherwise.  The net imbalance of an oriented face is then

    faceImbalance K f  =  sum over top cells tau and facet slots i of
                            (-1)^i * orientSign (facetTriple K tau i) f

and its recognition cost is that imbalance squared over twice the Casimir, which is
`ChartFromLedgerMomentum.Jlog_eq_imbalance_sq_div_two_casimir` evaluated at the face's
own ledger state.

**Genuinely different, not a relabelling.**  The vertex referent is the boundary of
the complex's *edge* data read at vertices; this is the boundary of its *top-cell*
data read at faces.  Different block of the incidence structure, different chain
degree, different arithmetic: the vertex imbalance of a Freudenthal region ranges over
the whole interval from `-15` to `15` in four dimensions (MEASURED), while the face
imbalance takes only the values `-2, -1, 0, 1, 2` under the raw chain ordering and only
`-1, 0, 1` under the oriented convention used here (both MEASURED).  The consequence matters.  A1.5's kill turned
on the fact that a squared imbalance is not a linear function of counts; a face
imbalance that is `0` or one of `1, -1` has an idempotent square, so the face-read `J` is a
plain *count* of unbalanced faces and does **not** inherit that obstruction.  It fails
for a different reason, given in §3.

**Orientation signed** (`faceImbalance_reverse`): reversing a face negates its
imbalance, unconditionally, because `revFace` is an involution that exchanges the
three even comparisons of `orientSign` with the three odd ones.  A degenerate triple,
one with a repeated vertex, is annihilated for the same reason, so it is charged
nothing without anyone stipulating that it should be.

## §2.  The cost, additivity, bulk cancellation

Faces are not letters: the posting alphabet has three blocks and none of them is the
face block.  So the charge is attributed to the top-cell letter that posts it,
`facetImbalanceSq K tau` being the sum of the four squared facet imbalances of `tau`
(`jFaceCost`).  **The attribution is invisible to the span test.**  A facet interior
to a region is a facet of two top cells whose incidences cancel, so it carries zero
imbalance and contributes nothing wherever it is booked; a boundary facet belongs to
exactly one top cell, so there is nothing to distribute.  The aggregate the census test
reads is therefore the same under any attribution, which closes the obvious escape
that the route was killed by a bookkeeping choice.

Three properties are recorded, the same three A1.5 needed.  `jFaceCost` is a
`LetterCost`, its history cost is the top-cell block sum (`historyCost_jFaceCost`), it
is gauge equivariant (`jFaceCost_equivariant`), and a top cell all of whose facets
balance is charged nothing (`jFaceCost_vanishes_on_balanced_tet`).  The last clause is
not vacuous: `twoTets` glues two top cells along one facet ordered so their incidences
oppose, and on that complex the shared facet really is balanced while the six others
really are not (`twoTets_shared_facet_balanced_others_not`).

## §3.  The verdict

`jFaceCost` has no fixed kind totals either (`jFaceCost_not_fixedKindTotals`), and the
witness says exactly what the cost is: one top cell has four unbalanced facets and
costs `2/kappa`, two glued along a facet have six and cost `3/kappa`, so the top-cell
block total is a boundary count and not a fixed multiple of the top-cell count.  This
is a different failure from A1.5's.  There the block sum was a sum of unbounded
squares; here it is a count, and counts are perfectly linear objects.  What defeats it
is that the thing being counted is a *surface*.

§4 carries the measured moments.  On the four-dimensional Freudenthal cube dilate the
oriented-face cost is exactly `48 N^3`, a pure surface term, and A1.5's obstruction
functional `cert4 = (0, 1, -2, 2, 0)` returns `48` on it.  The certificate is the same
one, which is not a coincidence and is made precise by the sharpest theorem here:

* `census4_with_const_span_iff` computes the census span exactly.  A moment vector
  lies in the span of the three counts plus a constant **if and only if**
  `cert4` annihilates it.  The span is a hyperplane, and the certificate is its normal.
* `no_pure_surface_term_in_census_span` is the corollary that matters: for every
  nonzero `a`, the moment vector `(0, a, 0, 0, 0)` is outside the span.  **No pure
  surface term of the four-dimensional Kuhn cube dilate is a per-kind charge**, whatever
  imbalance referent produced it.

That subsumes this route's kill through the corollary (its moment is a pure surface
term), and A1.5's kill through the iff (its moment is not: the certificate returns 192
on it).  It is not a closure of every bulk-cancelling referent: bulk cancellation
constrains the interior only, and one whose higher-strata moments satisfy
`a - 2b + 2c = 0` lies in the span by the iff, so the tension with census
representability holds at the pure-surface stratum rather than universally.  Both parity
constituents of the oblique-dihedral family are checked separately with their own
certificates, and the two variant readings measured alongside the primary one (the raw
ordered-tuple convention, and the circulation of postings around 2-simplices) fail as
well.

## Scope

The verdict is about the recognition cost built from oriented-face imbalance on the
Freudenthal carrier, over the cube and oblique-dihedral families, on both parity
constituents, at the dilate ranges enumerated (`N` to 23 in three dimensions, 17 in
four), plus the period-doubled cell verified identical to the cube at side `2N`.  It
closes the oriented-face referent.  It does not flip any flag: no triple was derived,
so nothing was compared to unit fugacity, and `gap2_measure_derived` stays as it was.

Numbers marked MEASURED come from `scripts/qg/qg_oriented_face_span_20260730.py`, exact
integer and rational arithmetic, quasi-polynomial fits verified against held-out
dilates.  The vertex-read totals of A1.5 were recomputed by that script as a
known-answer check on the instrument and reproduce A1.5's published moments exactly.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2OrientedFaceSpan

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation Gap2JEhrhartSpan

variable {B : ℕ}

/-! ## §1. Oriented faces and their signed incidence with an ordered top cell -/

/-- An **oriented face**: a triangle presented as an ordered triple of vertices.  The
orientation is the vertex order up to an even permutation, which is what `orientSign`
below reads. -/
abbrev OFace (n : ℕ) : Type := Fin n × Fin n × Fin n

/-- Cyclic rotation of an oriented face.  An even permutation, so it preserves
orientation. -/
def rotFace {n : ℕ} (f : OFace n) : OFace n := (f.2.1, f.2.2, f.1)

/-- Reversal of an oriented face, here the transposition of its first two vertices.
An odd permutation, so it reverses orientation. -/
def revFace {n : ℕ} (f : OFace n) : OFace n := (f.2.1, f.1, f.2.2)

theorem revFace_involutive {n : ℕ} (f : OFace n) : revFace (revFace f) = f := rfl

theorem revFace_eq_iff {n : ℕ} (f t : OFace n) : revFace f = t ↔ f = revFace t := by
  constructor
  · intro h; rw [← h, revFace_involutive]
  · intro h; rw [h, revFace_involutive]

theorem revFace_inj {n : ℕ} {f t : OFace n} : revFace f = revFace t ↔ f = t := by
  rw [revFace_eq_iff, revFace_involutive]

/-- Indicator of a decidable proposition, valued in the integers. -/
def ind (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- Logically equivalent propositions have equal indicators.  Stated as an equation
between integers rather than rewritten under the `if`, because the decidability instance
travels with the proposition and rewriting the proposition alone leaves a motive that is
not type correct. -/
theorem ind_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : ind p = ind q := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [ind, hp, hq]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [ind, hp, hq]

/-- **The signed incidence of two ordered triples.**  `orientSign t f` is `1` when `f`
is an even permutation of `t`, `-1` when it is an odd one, and `0` otherwise.  Written
as a signed sum of six indicators rather than a case split, because in that form the
orientation law `orientSign_rev` is a pairing of the six terms and needs no
nondegeneracy hypothesis: a triple with a repeated vertex has its even and odd classes
coincide, so the six terms cancel and it is annihilated. -/
def orientSign {n : ℕ} (t f : OFace n) : ℤ :=
  ind (f = t) + ind (f = rotFace t) + ind (f = rotFace (rotFace t))
    - ind (f = revFace t) - ind (f = revFace (rotFace t))
    - ind (f = revFace (rotFace (rotFace t)))

/-- **Orientation signed, at the incidence.**  Reversing the face flips every
incidence sign. -/
theorem orientSign_rev {n : ℕ} (t f : OFace n) :
    orientSign t (revFace f) = - orientSign t f := by
  unfold orientSign
  rw [ind_congr (revFace_eq_iff f t),
    ind_congr (revFace_eq_iff f (rotFace t)),
    ind_congr (revFace_eq_iff f (rotFace (rotFace t))),
    ind_congr (revFace_inj (f := f) (t := t)),
    ind_congr (revFace_inj (f := f) (t := rotFace t)),
    ind_congr (revFace_inj (f := f) (t := rotFace (rotFace t)))]
  ring

/-! ### Facets of an ordered top cell -/

/-- The `i`-th facet of an ordered top cell: drop the `i`-th vertex and keep the other
three in their order.  Nothing is stipulated; `BoundedComplex.tetVerts` already orders
them. -/
def facetTriple (K : BoundedComplex B) (τ : Fin K.nT) (i : Fin 4) : OFace K.nV :=
  if i = 0 then (K.tetVerts τ 1, K.tetVerts τ 2, K.tetVerts τ 3)
  else if i = 1 then (K.tetVerts τ 0, K.tetVerts τ 2, K.tetVerts τ 3)
  else if i = 2 then (K.tetVerts τ 0, K.tetVerts τ 1, K.tetVerts τ 3)
  else (K.tetVerts τ 0, K.tetVerts τ 1, K.tetVerts τ 2)

/-- The incidence sign of the `i`-th facet, `(-1)^i`: a top cell debits its
even-indexed facets and credits its odd-indexed ones. -/
def facetSign (i : Fin 4) : ℤ := if i = 0 ∨ i = 2 then 1 else -1

/-- **The net recognition imbalance of an oriented face in context.**  Debits minus
credits over every top cell of the complex, read off the carrier's own ordered
top-cell incidence. -/
def faceImbalance (K : BoundedComplex B) (f : OFace K.nV) : ℤ :=
  ∑ τ : Fin K.nT, ∑ i : Fin 4, facetSign i * orientSign (facetTriple K τ i) f

/-- **Orientation signed, at the face.**  A face and its reverse carry opposite
imbalance, in every complex, with no hypothesis on the complex. -/
theorem faceImbalance_reverse (K : BoundedComplex B) (f : OFace K.nV) :
    faceImbalance K (revFace f) = - faceImbalance K f := by
  unfold faceImbalance
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro τ _
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [orientSign_rev]
  ring

/-! ## §2. The derived letter cost -/

/-- The integer part of a top cell's charge: the sum of the squared imbalances of its
four facets. -/
def facetImbalanceSq (K : BoundedComplex B) (τ : Fin K.nT) : ℤ :=
  ∑ i : Fin 4, (faceImbalance K (facetTriple K τ i)) ^ 2

/-- The integer part of the whole complex's charge. -/
def imbalanceSqTotal (K : BoundedComplex B) : ℤ :=
  ∑ τ : Fin K.nT, facetImbalanceSq K τ

noncomputable section

/-- **The recognition cost of a letter in context, oriented-face reading.**  A top-cell
letter is charged the squared imbalance of each of the faces it posts, over twice the
Casimir.  Vertex and edge letters are not face-posting sources, so they are charged
nothing.

The attribution to the top-cell block is bookkeeping and the aggregate does not depend
on it: an interior facet has two opposing incidences, so its imbalance vanishes and it
contributes nothing wherever it is booked, and a boundary facet belongs to one top cell
only. -/
def jFaceCost (kappa : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inr (Sum.inr τ) => ((facetImbalanceSq K τ : ℝ)) / (2 * kappa)
  | _ => 0

@[simp] theorem jFaceCost_inl (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    jFaceCost kappa B K (Sum.inl v) = 0 := rfl

@[simp] theorem jFaceCost_edge (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE) :
    jFaceCost kappa B K (Sum.inr (Sum.inl e)) = 0 := rfl

@[simp] theorem jFaceCost_tet (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT) :
    jFaceCost kappa B K (Sum.inr (Sum.inr τ))
      = ((facetImbalanceSq K τ : ℝ)) / (2 * kappa) := rfl

/-- **`J` is the sum over its letters.**  The history cost is the top-cell block sum,
because the other two blocks are silent. -/
theorem historyCost_jFaceCost (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (jFaceCost kappa) B K
      = ∑ τ : Fin K.nT, jFaceCost kappa B K (Sum.inr (Sum.inr τ)) := by
  classical
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-- The history cost in closed form: the complex's integer charge over twice the
Casimir. -/
theorem historyCost_jFaceCost_eq (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (jFaceCost kappa) B K = ((imbalanceSqTotal K : ℝ)) / (2 * kappa) := by
  rw [historyCost_jFaceCost]
  simp only [jFaceCost_tet]
  rw [← Finset.sum_div]
  congr 1
  unfold imbalanceSqTotal
  push_cast
  rfl

/-- **Bulk cancellation, at the letter.**  A top cell whose facets all balance is
charged nothing.  On a region of the Freudenthal carrier an interior facet is a facet
of two top cells; whether their incidences oppose is a property of the ordering the
carrier supplies, and §4 measures which convention has it. -/
theorem jFaceCost_vanishes_on_balanced_tet (kappa : ℝ) (B : ℕ) (K : BoundedComplex B)
    (τ : Fin K.nT) (h : ∀ i : Fin 4, faceImbalance K (facetTriple K τ i) = 0) :
    jFaceCost kappa B K (Sum.inr (Sum.inr τ)) = 0 := by
  have hz : facetImbalanceSq K τ = 0 := by
    unfold facetImbalanceSq
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [h i]
    ring
  rw [jFaceCost_tet, hz]
  simp

end

/-! ### Equivariance: the failure below is not a labelling artifact -/

/-- Transport an oriented face along a vertex relabelling. -/
def mapTriple {m n : ℕ} (φ : Fin m ≃ Fin n) (t : OFace m) : OFace n :=
  (φ t.1, φ t.2.1, φ t.2.2)

theorem mapTriple_rotFace {m n : ℕ} (φ : Fin m ≃ Fin n) (t : OFace m) :
    rotFace (mapTriple φ t) = mapTriple φ (rotFace t) := rfl

theorem mapTriple_revFace {m n : ℕ} (φ : Fin m ≃ Fin n) (t : OFace m) :
    revFace (mapTriple φ t) = mapTriple φ (revFace t) := rfl

theorem mapTriple_inj {m n : ℕ} (φ : Fin m ≃ Fin n) (x y : OFace m) :
    mapTriple φ x = mapTriple φ y ↔ x = y := by
  unfold mapTriple
  simp [Prod.ext_iff]

theorem orientSign_map {m n : ℕ} (φ : Fin m ≃ Fin n) (t f : OFace m) :
    orientSign (mapTriple φ t) (mapTriple φ f) = orientSign t f := by
  unfold orientSign
  simp only [mapTriple_rotFace, mapTriple_revFace, mapTriple_inj]

theorem facetTriple_relabel {K K' : BoundedComplex B} (r : Relabel K K')
    (τ : Fin K.nT) (i : Fin 4) :
    facetTriple K' (r.tEquiv τ) i = mapTriple r.vEquiv (facetTriple K τ i) := by
  unfold facetTriple mapTriple
  split_ifs <;> simp [r.tet_comm]

theorem faceImbalance_relabel {K K' : BoundedComplex B} (r : Relabel K K')
    (f : OFace K.nV) : faceImbalance K f = faceImbalance K' (mapTriple r.vEquiv f) := by
  unfold faceImbalance
  refine Fintype.sum_equiv r.tEquiv _ _ ?_
  intro τ
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [facetTriple_relabel r τ i, orientSign_map]

theorem facetImbalanceSq_relabel {K K' : BoundedComplex B} (r : Relabel K K')
    (τ : Fin K.nT) : facetImbalanceSq K τ = facetImbalanceSq K' (r.tEquiv τ) := by
  unfold facetImbalanceSq
  refine Finset.sum_congr rfl ?_
  intro i _
  have h := faceImbalance_relabel r (facetTriple K τ i)
  rw [facetTriple_relabel r τ i, ← h]

/-- **`jFaceCost` is gauge equivariant.**  Labels are gauge for it, so every negative
result below is about the cost and not about a choice of names. -/
theorem jFaceCost_equivariant (kappa : ℝ) : Equivariant (jFaceCost kappa) := by
  intro B K K' r a
  cases a with
  | inl v => rfl
  | inr b =>
      cases b with
      | inl e => rfl
      | inr τ =>
          show jFaceCost kappa B K' (Sum.inr (Sum.inr (r.tEquiv τ)))
            = jFaceCost kappa B K (Sum.inr (Sum.inr τ))
          rw [jFaceCost_tet, jFaceCost_tet, ← facetImbalanceSq_relabel r τ]

/-! ## §3. The verdict at the finite complex: no aggregate-linear letter cost

Two explicit complexes.  `oneTet` is a single ordered top cell.  `twoTets` glues two of
them along one facet, ordered so their incidences on the shared facet oppose. -/

/-- One top cell on four vertices, ordered `(0, 1, 2, 3)`. -/
def oneTet : BoundedComplex 4 where
  nV := 4
  nE := 0
  nT := 1
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => e.elim0
  tetVerts := fun _ i => i

/-- Two top cells on five vertices sharing the facet `(1, 2, 3)`.  The second is
ordered `(1, 4, 2, 3)`, which presents the shared facet in slot `1` and so with the
opposite incidence sign to the first cell's slot `0`. -/
def twoTets : BoundedComplex 5 where
  nV := 5
  nE := 0
  nT := 2
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => e.elim0
  tetVerts := fun t i => if t = 0 then ![0, 1, 2, 3] i else ![1, 4, 2, 3] i

/-- MEASURED in the kernel: the single top cell has four unbalanced facets. -/
theorem facetImbalanceSq_oneTet : facetImbalanceSq oneTet (0 : Fin 1) = 4 := by decide

theorem imbalanceSqTotal_oneTet : imbalanceSqTotal oneTet = 4 := by decide

/-- MEASURED in the kernel: gluing two top cells along a facet leaves six unbalanced
facets, not eight.  The shared facet is charged nothing. -/
theorem imbalanceSqTotal_twoTets : imbalanceSqTotal twoTets = 6 := by decide

/-- **Non-vacuity of the bulk-cancellation clause.**  On `twoTets` the shared facet
really is balanced and the neighbouring facet of the same top cell really is not, so
`jFaceCost_vanishes_on_balanced_tet` has an instance and a non-instance on the same
complex. -/
theorem twoTets_shared_facet_balanced_others_not :
    faceImbalance twoTets (facetTriple twoTets (0 : Fin 2) (0 : Fin 4)) = 0
      ∧ faceImbalance twoTets (facetTriple twoTets (0 : Fin 2) (1 : Fin 4)) ≠ 0
      ∧ faceImbalance twoTets (facetTriple twoTets (1 : Fin 2) (1 : Fin 4)) = 0 := by
  decide

/-- **Non-vacuity of the orientation law.**  The imbalance really is nonzero somewhere,
so `faceImbalance_reverse` is not the statement that `0 = -0`. -/
theorem faceImbalance_reverse_nonvacuous :
    faceImbalance oneTet (facetTriple oneTet (0 : Fin 1) (0 : Fin 4)) = 1
      ∧ faceImbalance oneTet
          (revFace (facetTriple oneTet (0 : Fin 1) (0 : Fin 4))) = -1 := by
  decide

/-- A triple with a repeated vertex is annihilated, without anyone saying it should be. -/
theorem orientSign_degenerate_witness :
    orientSign ((0, 0, 1) : OFace 4) ((0, 0, 1) : OFace 4) = 0 := by decide

noncomputable section

theorem blockSum_oneTet (kappa : ℝ) :
    (∑ τ : Fin oneTet.nT, jFaceCost kappa 4 oneTet (Sum.inr (Sum.inr τ))) = 2 / kappa := by
  rw [← historyCost_jFaceCost, historyCost_jFaceCost_eq, imbalanceSqTotal_oneTet]
  push_cast
  ring

theorem blockSum_twoTets (kappa : ℝ) :
    (∑ τ : Fin twoTets.nT, jFaceCost kappa 5 twoTets (Sum.inr (Sum.inr τ)))
      = 3 / kappa := by
  rw [← historyCost_jFaceCost, historyCost_jFaceCost_eq, imbalanceSqTotal_twoTets]
  push_cast
  ring

/-- **HEADLINE (the route fails at the letter, for a new reason).**  For every nonzero
Casimir the oriented-face cost has no fixed kind totals, so
`measure_from_fixedKindTotals` cannot be applied to it.

The witness says what the object is.  A single top cell has four unbalanced facets and
its block sum is `2/kappa`, which forces `cT = 2/kappa`.  Two top cells glued along a
facet have six and their block sum is `3/kappa`, which demands `cT = 3/(2 kappa)`.  The
top-cell block total counts the *surface* of the complex, and a surface is not a fixed
multiple of a volume.

This is a different failure from `Gap2JEhrhartSpan.jCost_not_fixedKindTotals`.  There
the block sum was a sum of unbounded squares and the obstruction was that a square is
not linear.  Here every squared imbalance in the witness is `0` or `1`, the block sum
is a plain count, and the obstruction is what is being counted. -/
theorem jFaceCost_not_fixedKindTotals (kappa : ℝ) (hk : kappa ≠ 0) :
    ¬ FixedKindTotals (jFaceCost kappa) := by
  rintro ⟨cV, cE, cT, h⟩
  have h1 := (h 4 oneTet).2.2
  have h2 := (h 5 twoTets).2.2
  rw [blockSum_oneTet kappa] at h1
  rw [blockSum_twoTets kappa] at h2
  have e1 : ((oneTet.nT : ℕ) : ℝ) = 1 := by
    show ((1 : ℕ) : ℝ) = 1
    norm_num
  have e2 : ((twoTets.nT : ℕ) : ℝ) = 2 := by
    show ((2 : ℕ) : ℝ) = 2
    norm_num
  rw [e1, mul_one] at h1
  rw [e2] at h2
  rw [← h1] at h2
  simp only [div_eq_mul_inv] at h2
  have hinv : (kappa : ℝ)⁻¹ = 0 := by linarith
  exact hk (inv_eq_zero.mp hinv)

end

/-! ## §4. The census span test on the measured moment vectors

Moment vectors of the Freudenthal (Kuhn) carrier, in the basis `(N^d, ..., N, 1)`.
MEASURED by exact enumeration (`scripts/qg/qg_oriented_face_span_20260730.py`); every
quasi-polynomial fit reproduces its held-out dilates exactly, and the period-doubled
cell was verified identical to the cube at side `2N` on every measured quantity, in
three dimensions and in four.

The census columns are A1.5's, imported rather than restated, because the carrier and
the census are the same and only the target changed.  `mV4`, `mE4`, `mT4`, `mC4`,
`dot4` and `cert4` all come from `Gap2JEhrhartSpan`. -/

/-- MEASURED moment vector of `2 * kappa * J` for the oriented-face reading on the 4D
Freudenthal cube dilate, with the top cells carrying the orientation they inherit from
the ambient orientation of `R^4`.  It is exactly `48 N^3`: a pure surface term, which is
bulk cancellation in its sharpest quantitative form. -/
def mFor4 : Fin 5 → ℚ := ![0, 48, 0, 0, 0]

/-- MEASURED moment vector of the same reading with the raw increasing-chain ordering
the carrier writes down, `eps = 1` rather than `sign(sigma)`.  Its leading coefficient
is nonzero, which is the measurement that the raw convention does **not** bulk-cancel:
interior facets carry imbalance `2` or `-2` under it. -/
def mForRaw4 : Fin 5 → ℚ := ![240, -48, 0, 0, 0]

/-- MEASURED moment vector of the third reading of "oriented face": the circulation of
the directed postings around an oriented 2-simplex, the discrete curl of the posting
field.  On this carrier the circulation is `1` at every 2-simplex without exception, so
this reading is the 2-simplex count and carries no information about the region at all. -/
def mCurl4 : Fin 5 → ℚ := ![50, 48, 12, 0, 0]

theorem cert4_sees_mFor4 : dot4 cert4 mFor4 = 48 := by
  simp [dot4, cert4, mFor4, Fin.sum_univ_five]

theorem cert4_sees_mForRaw4 : dot4 cert4 mForRaw4 = -48 := by
  simp [dot4, cert4, mForRaw4, Fin.sum_univ_five]

theorem cert4_sees_mCurl4 : dot4 cert4 mCurl4 = 24 := by
  simp [dot4, cert4, mCurl4, Fin.sum_univ_five]
  norm_num

/-! ### The census span, computed exactly

The sharpest statement in this module, and the one that explains both kills.  The
census columns plus a constant span exactly the hyperplane `cert4` annihilates, so
membership is a single linear condition and the certificate is the normal. -/

/-- **THEOREM (the four-dimensional census span, exactly).**  A moment vector is a
rational combination of the three kind counts and a constant if and only if the
obstruction functional annihilates it.  The forward direction is A1.5's certificate; the
reverse direction exhibits the inverse, so this is an equality of sets and not a
one-sided bound. -/
theorem census4_with_const_span_iff (t : Fin 5 → ℚ) :
    (∃ a b c e : ℚ, ∀ i : Fin 5,
        a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = t i)
      ↔ dot4 cert4 t = 0 := by
  constructor
  · rintro ⟨a, b, c, e, h⟩
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp [mV4, mE4, mT4, mC4] at h1 h2 h3
    simp [dot4, cert4, Fin.sum_univ_five]
    linarith
  · intro h
    simp [dot4, cert4, Fin.sum_univ_five] at h
    refine ⟨3 * t 3 / 8 - t 2 / 12, t 2 / 12 - t 3 / 8,
      (t 0 - (3 * t 3 / 8 - t 2 / 12) - 15 * (t 2 / 12 - t 3 / 8)) / 24,
      t 4 - (3 * t 3 / 8 - t 2 / 12), ?_⟩
    intro i
    fin_cases i <;> simp [mV4, mE4, mT4, mC4] <;> linarith

/-- **THEOREM (no pure surface term is a per-kind charge).**  For every nonzero `a`, the
moment vector `(0, a, 0, 0, 0)` of a functional that is exactly `a N^3` on the
four-dimensional Kuhn cube dilate lies outside the census span, with or without a
constant column.

This is the general form of both kills in this line of work, and it is a prediction as
well as a verdict: any imbalance referent whatsoever whose recognition cost is a pure
surface term on this carrier will fail this test, and no rescoping of the referent
changes that. -/
theorem no_pure_surface_term_in_census_span (a : ℚ) (ha : a ≠ 0) :
    ¬ ∃ p q r s : ℚ, ∀ i : Fin 5,
      p * mV4 i + q * mE4 i + r * mT4 i + s * mC4 i
        = (![0, a, 0, 0, 0] : Fin 5 → ℚ) i := by
  intro hex
  have hz := (census4_with_const_span_iff _).mp hex
  simp [dot4, cert4, Fin.sum_univ_five] at hz
  exact ha hz

/-- **HEADLINE (outside the census span, four dimensions).**  No rational triple of kind
rates, with or without an additive constant, reproduces the oriented-face cost's measured
moment vector on the 4D Freudenthal cube dilate. -/
theorem mFor4_not_in_census_span_with_const :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mFor4 i := by
  intro hex
  have hz := (census4_with_const_span_iff _).mp hex
  rw [cert4_sees_mFor4] at hz
  norm_num at hz

theorem mFor4_not_in_census_span :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 5, a * mV4 i + b * mE4 i + c * mT4 i = mFor4 i := by
  rintro ⟨a, b, c, h⟩
  exact mFor4_not_in_census_span_with_const ⟨a, b, c, 0, by
    intro i; rw [← h i]; simp [mC4]⟩

/-- The raw ordered-tuple convention fails too, and by the same functional. -/
theorem mForRaw4_not_in_census_span_with_const :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mForRaw4 i := by
  intro hex
  have hz := (census4_with_const_span_iff _).mp hex
  rw [cert4_sees_mForRaw4] at hz
  norm_num at hz

/-- The circulation reading fails too. -/
theorem mCurl4_not_in_census_span_with_const :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mCurl4 i := by
  intro hex
  have hz := (census4_with_const_span_iff _).mp hex
  rw [cert4_sees_mCurl4] at hz
  norm_num at hz

/-! ### The oblique-dihedral family, both parity constituents

The cube census has a degenerate negative control (its top-cell column is a pure
monomial, so the leading unit vector is a census column), which is why A1.5 also
enumerated an oblique-dihedral region whose apex is half-integral and whose census is a
genuine period-2 quasi-polynomial.  Both of its parity constituents are carried here
with their own obstruction functionals. -/

def oV4e : Fin 5 → ℚ := ![1/4, 3/2, 13/4, 3, 1]
def oE4e : Fin 5 → ℚ := ![15/4, 17/2, 31/4, 5/2, 0]
def oT4 : Fin 5 → ℚ := ![6, -6, 0, 0, 0]

/-- MEASURED oriented-face moments on the 4D oblique region, even dilates. -/
def oFor4e : Fin 5 → ℚ := ![0, 21, -18, 0, 0]

def ocert4e : Fin 5 → ℚ := ![121, 121, -259, 210, 0]

def oV4o : Fin 5 → ℚ := ![1/4, 3/2, 3, 5/2, 3/4]
def oE4o : Fin 5 → ℚ := ![15/4, 17/2, 6, 1, -1/4]

/-- MEASURED oriented-face moments on the 4D oblique region, odd dilates. -/
def oFor4o : Fin 5 → ℚ := ![0, 21, -21, 0, 0]

def ocert4o : Fin 5 → ℚ := ![32, 32, -77, 70, 0]

theorem ocert4e_annihilates_census :
    dot4 ocert4e oV4e = 0 ∧ dot4 ocert4e oE4e = 0 ∧ dot4 ocert4e oT4 = 0
      ∧ dot4 ocert4e mC4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [dot4, ocert4e, oV4e, oE4e, oT4, mC4, Fin.sum_univ_five] <;> norm_num

theorem ocert4e_sees_oFor4e : dot4 ocert4e oFor4e = 7203 := by
  simp [dot4, ocert4e, oFor4e, Fin.sum_univ_five]
  norm_num

theorem ocert4o_annihilates_census :
    dot4 ocert4o oV4o = 0 ∧ dot4 ocert4o oE4o = 0 ∧ dot4 ocert4o oT4 = 0
      ∧ dot4 ocert4o mC4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [dot4, ocert4o, oV4o, oE4o, oT4, mC4, Fin.sum_univ_five] <;> norm_num

theorem ocert4o_sees_oFor4o : dot4 ocert4o oFor4o = 2289 := by
  simp [dot4, ocert4o, oFor4o, Fin.sum_univ_five]
  norm_num

/-- **Outside the span on the oblique region, even dilates.** -/
theorem oFor4e_not_in_census_span_with_const :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * oV4e i + b * oE4e i + c * oT4 i + e * mC4 i = oFor4e i := by
  rintro ⟨a, b, c, e, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [oV4e, oE4e, oT4, mC4, oFor4e] at h0 h1 h2 h3
  linarith

/-- **Outside the span on the oblique region, odd dilates.** -/
theorem oFor4o_not_in_census_span_with_const :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * oV4o i + b * oE4o i + c * oT4 i + e * mC4 i = oFor4o i := by
  rintro ⟨a, b, c, e, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [oV4o, oE4o, oT4, mC4, oFor4o] at h0 h1 h2 h3
  linarith

/-! ### Three dimensions, where the test with a constant column is vacuous

`Gap2JEhrhartSpan.census3_with_const_is_onto` already proved the 3D system with a
constant column returns a triple for any input whatever, so only the three-count system
discriminates there.  The oriented-face moments are `12 N^2` on the 3D cube dilate. -/

/-- MEASURED oriented-face moments on the 3D Freudenthal cube dilate. -/
def mFor3 : Fin 4 → ℚ := ![0, 12, 0, 0]

theorem cert3_sees_mFor3 : dot3 cert3 mFor3 = 12 := by
  simp [dot3, cert3, mFor3, Fin.sum_univ_four]

theorem mFor3_not_in_census_span :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 4, a * mV3 i + b * mE3 i + c * mT3 i = mFor3 i := by
  rintro ⟨a, b, c, h⟩
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [mV3, mE3, mT3, mFor3] at h1 h2 h3
  linarith

/-! ## §5. Certificate -/

/-- **The C12 oriented-face verdict.**  The oriented-face imbalance is a signed referent
read off the carrier's own ordered top-cell incidence; the cost built from it is a gauge
equivariant letter cost whose history is the sum over its letters and whose bulk cancels;
it has no fixed kind totals; and its measured moment vector lies outside the census span
in four dimensions on both region families and both parity constituents.  The census span
is computed exactly, so the kill is a hyperplane condition rather than a failed search,
and the corollary closes every pure surface term at once. -/
structure OrientedFaceSpanVerdict : Prop where
  orientation_signed : ∀ (B : ℕ) (K : BoundedComplex B) (f : OFace K.nV),
    faceImbalance K (revFace f) = - faceImbalance K f
  equivariant : ∀ kappa : ℝ, Equivariant (jFaceCost kappa)
  sum_over_letters : ∀ (kappa : ℝ) (B : ℕ) (K : BoundedComplex B),
    historyCost (jFaceCost kappa) B K
      = ∑ τ : Fin K.nT, jFaceCost kappa B K (Sum.inr (Sum.inr τ))
  bulk_cancels : ∀ (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT),
    (∀ i : Fin 4, faceImbalance K (facetTriple K τ i) = 0) →
      jFaceCost kappa B K (Sum.inr (Sum.inr τ)) = 0
  bulk_cancellation_nonvacuous :
    faceImbalance twoTets (facetTriple twoTets (0 : Fin 2) (0 : Fin 4)) = 0
      ∧ faceImbalance twoTets (facetTriple twoTets (0 : Fin 2) (1 : Fin 4)) ≠ 0
      ∧ faceImbalance twoTets (facetTriple twoTets (1 : Fin 2) (1 : Fin 4)) = 0
  no_kind_totals : ∀ kappa : ℝ, kappa ≠ 0 → ¬ FixedKindTotals (jFaceCost kappa)
  span_is_a_hyperplane : ∀ t : Fin 5 → ℚ,
    (∃ a b c e : ℚ, ∀ i : Fin 5,
        a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = t i)
      ↔ dot4 cert4 t = 0
  no_surface_term : ∀ a : ℚ, a ≠ 0 →
    ¬ ∃ p q r s : ℚ, ∀ i : Fin 5,
      p * mV4 i + q * mE4 i + r * mT4 i + s * mC4 i
        = (![0, a, 0, 0, 0] : Fin 5 → ℚ) i
  outside_span_4d_cube :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 5, a * mV4 i + b * mE4 i + c * mT4 i = mFor4 i
  outside_span_4d_cube_with_const :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mFor4 i
  outside_span_4d_oblique_even :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * oV4e i + b * oE4e i + c * oT4 i + e * mC4 i = oFor4e i
  outside_span_4d_oblique_odd :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * oV4o i + b * oE4o i + c * oT4 i + e * mC4 i = oFor4o i
  outside_span_3d :
    ¬ ∃ a b c : ℚ, ∀ i : Fin 4, a * mV3 i + b * mE3 i + c * mT3 i = mFor3 i
  raw_convention_also_outside :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mForRaw4 i
  circulation_reading_also_outside :
    ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
      a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mCurl4 i

theorem orientedFaceSpanVerdict : OrientedFaceSpanVerdict where
  orientation_signed := fun _ K f => faceImbalance_reverse K f
  equivariant := jFaceCost_equivariant
  sum_over_letters := historyCost_jFaceCost
  bulk_cancels := jFaceCost_vanishes_on_balanced_tet
  bulk_cancellation_nonvacuous := twoTets_shared_facet_balanced_others_not
  no_kind_totals := jFaceCost_not_fixedKindTotals
  span_is_a_hyperplane := census4_with_const_span_iff
  no_surface_term := no_pure_surface_term_in_census_span
  outside_span_4d_cube := mFor4_not_in_census_span
  outside_span_4d_cube_with_const := mFor4_not_in_census_span_with_const
  outside_span_4d_oblique_even := oFor4e_not_in_census_span_with_const
  outside_span_4d_oblique_odd := oFor4o_not_in_census_span_with_const
  outside_span_3d := mFor3_not_in_census_span
  raw_convention_also_outside := mForRaw4_not_in_census_span_with_const
  circulation_reading_also_outside := mCurl4_not_in_census_span_with_const

/-! ## §6. Flag status

Nothing moves.  The condition for reporting a triple of chemical potentials was a
consistent system; the system is inconsistent on the discriminating family, so no triple
exists and there is nothing to compare against unit fugacity.  Flag
`gap2_measure_derived` stays exactly as it was. -/

structure OrientedFaceIndex : Type where
  /-- The referent is signed, derived from the carrier's ordered top-cell incidence, and
  is not the vertex referent of `Gap2JEhrhartSpan`. -/
  referent_is_new : Bool
  /-- The cost is a gauge-equivariant letter cost summing over its letters. -/
  cost_is_wellformed : Bool
  /-- Bulk cancellation holds at the letter and the clause has a witness and a
  non-witness on one complex. -/
  bulk_cancels : Bool
  /-- The square is idempotent on this referent, so A1.5's non-linearity obstruction is
  NOT inherited.  The failure below has a different cause. -/
  inherits_a15_quadratic_obstruction : Bool
  /-- The moment vector is outside the census span in four dimensions, on both region
  families and both parity constituents. -/
  outside_span_4d : Bool
  /-- The census span is computed exactly as a hyperplane, so no pure surface term of
  this carrier can ever be a per-kind charge. -/
  span_computed_exactly : Bool
  /-- NOT produced: a triple of chemical potentials.  The system is inconsistent, so no
  comparison to unit fugacity was made and none was possible. -/
  triple_derived : Bool
  /-- NOT moved. -/
  measure_flag_moved : Bool

def orientedFaceIndex : OrientedFaceIndex where
  referent_is_new := true
  cost_is_wellformed := true
  bulk_cancels := true
  inherits_a15_quadratic_obstruction := false
  outside_span_4d := true
  span_computed_exactly := true
  triple_derived := false
  measure_flag_moved := false

theorem index_no_triple : orientedFaceIndex.triple_derived = false := rfl

theorem index_flag_unmoved : orientedFaceIndex.measure_flag_moved = false := rfl

theorem index_not_the_a15_obstruction :
    orientedFaceIndex.inherits_a15_quadratic_obstruction = false := rfl

/-! ## Axiom audit -/

#print axioms orientSign_rev
#print axioms faceImbalance_reverse
#print axioms faceImbalance_reverse_nonvacuous
#print axioms orientSign_degenerate_witness
#print axioms historyCost_jFaceCost
#print axioms historyCost_jFaceCost_eq
#print axioms jFaceCost_vanishes_on_balanced_tet
#print axioms orientSign_map
#print axioms facetTriple_relabel
#print axioms faceImbalance_relabel
#print axioms facetImbalanceSq_relabel
#print axioms jFaceCost_equivariant
#print axioms facetImbalanceSq_oneTet
#print axioms imbalanceSqTotal_oneTet
#print axioms imbalanceSqTotal_twoTets
#print axioms twoTets_shared_facet_balanced_others_not
#print axioms blockSum_oneTet
#print axioms blockSum_twoTets
#print axioms jFaceCost_not_fixedKindTotals
#print axioms cert4_sees_mFor4
#print axioms cert4_sees_mForRaw4
#print axioms cert4_sees_mCurl4
#print axioms census4_with_const_span_iff
#print axioms no_pure_surface_term_in_census_span
#print axioms mFor4_not_in_census_span
#print axioms mFor4_not_in_census_span_with_const
#print axioms mForRaw4_not_in_census_span_with_const
#print axioms mCurl4_not_in_census_span_with_const
#print axioms ocert4e_annihilates_census
#print axioms ocert4e_sees_oFor4e
#print axioms ocert4o_annihilates_census
#print axioms ocert4o_sees_oFor4o
#print axioms oFor4e_not_in_census_span_with_const
#print axioms oFor4o_not_in_census_span_with_const
#print axioms cert3_sees_mFor3
#print axioms mFor3_not_in_census_span
#print axioms orientedFaceSpanVerdict

end Gap2OrientedFaceSpan
end SevenGaps
end Gravity
end IndisputableMonolith
