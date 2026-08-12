import IndisputableMonolith.Gravity.SevenGaps.Gap2OrientedFaceSpan

/-!
# Gap 2 / A1.7: the letter-cost dichotomy, decided

`Gap2JEhrhartSpan` (A1.5) and `Gap2OrientedFaceSpan` (A1.6) each built a gauge-equivariant
recognition cost out of an imbalance referent on the Freudenthal carrier, each cost had
bulk cancellation, and each died on the same clause: no fixed kind totals, because the
surviving total is a *surface* and a surface is not a fixed multiple of a volume.  Two
kills with one cause invite the obvious question, and this module answers it: is that
failure an accident of the two referents, or is it a theorem about the carrier?

It is a theorem about the carrier.

## STRENGTH, in one sentence

The impossibility is exactly this conditional and nothing wider: **for any family of
bounded complexes whose three counts are the MEASURED four-dimensional Freudenthal cube
census at every dilate (the proof samples five, `0` through `4`, and the robustness
variant `surface_at_positive_dilates_forces_zero` works from the five positive dilates
alone), a letter cost with fixed kind totals whose history over those dilates equals
`a * N^3 + e` has `a = e = 0` and all three rates zero, so its
history cost is identically zero at every complex and every cap** (`surface_and_kindTotals_force_zero`,
`surface_and_fixedKindTotals_force_zero_historyCost`).  Four things are worth reading off
that sentence before anything else.

* **Gauge equivariance is not used.**  It appears in neither the statement nor the proof,
  so the theorem holds on the strictly wider class of costs that are not equivariant
  (`equivariance_is_not_load_bearing`, with a non-equivariant witness inside the
  hypothesis class).  Hypothesis (i) of the question as posed is free.
* **The three atom normalizations are not assumed, they are derived**
  (`atom_normalizations_are_derived`).  That is the sharpening over the kernel theorem
  `Gap2PostingCostDerivation.fixedKindTotals_and_atoms_force_zero_historyCost`, which
  needs `NormalizedAtTheAtoms` in its binders.  Bulk cancellation on the dilate family
  replaces it, and does so without leaning on the family's degenerate member
  (`surface_at_positive_dilates_forces_zero` uses only `N` in `1..5`).
* **The letter cost is NOT forced to zero, and saying otherwise would be false.**  The
  fibre over the zero history cost is infinite: `centeredIncidenceCost t` is equivariant,
  has fixed kind totals, is bulk-cancelling in the sharp sense, and is a nonzero letter
  cost for every nonzero `t` (`the_letter_level_fibre_is_not_a_point`).  What is forced
  is everything the weight can see.
* **What the impossibility buys is the measure.**  Under (ii) and (iii) the Boltzmann
  numerator is identically one, so the posted weight is exactly the reciprocal order of
  the alphabet's sort-respecting gauge group and the class measure is exactly `mu`
  (`the_measure_is_exactly_the_gauge_divisor`).  The cost layer contributes no factor, and
  the rate-derivation route through this class of costs is closed.

## Which hypothesis does the work, measured

Three load-bearing checks, each a kernel-checked countermodel where one exists.

* **(iii) fixed kind totals is load-bearing.**  `surfaceCost t` is equivariant, its history
  on every census family is exactly `t * N^3` (a pure surface term, `a = t`), it is not
  zero, and it has no fixed kind totals (`fixed_kind_totals_is_load_bearing`).  Its
  physical counterpart is A1.6's oriented-face cost, whose MEASURED total on the real
  carrier is exactly `48 N^3`; `surfaceCost` is the synthetic member of the same hypothesis
  class that makes the check kernel-checked rather than measured.
* **(ii) bulk cancellation is load-bearing.**  `kindRateCost 1 0 0`, which charges every
  vertex letter one unit, is equivariant, has fixed kind totals, has nonzero history cost,
  and by the headline itself cannot be bulk-cancelling on any census family
  (`bulk_cancellation_is_load_bearing`).
* **(i) gauge equivariance is NOT load-bearing.**  There is no countermodel to exhibit,
  because the theorem is proved without the hypothesis.  What is exhibited instead is that
  dropping it genuinely widens the class rather than being vacuous: `indexTiltCost t` has
  fixed kind totals, is bulk-cancelling, is a nonzero letter cost, and is not equivariant.

## Where the boundary of (ii) actually sits, and it is sharp

Bulk cancellation in the loose sense, "the leading term vanishes", does **not** force the
cost to zero.  `kindRateCost 1 0 (-(1/24))` charges each vertex one unit and each Kuhn
4-simplex `-1/24`, its total on the census family is `4N^3 + 6N^2 + 4N + 1`, and its
leading coefficient is exactly zero (`purity_of_the_surface_term_is_load_bearing`).  So it
is not the absence of a bulk term that kills, it is the *purity* of what is left.

Purity has an exact width, and the module measures both sides of it.  A surface term plus
an additive corner constant dies (`surface_and_kindTotals_force_zero`).  A surface term
plus an area term with no constant dies too (`surfaceArea_and_kindTotals_force_zero`).
Their union does not: rates `(1, -1, 7/12)` give the total `-24N^3 - 12N^2 + 1`, which is
bulk-free and linear-term-free and still nonzero (`the_two_relaxations_cannot_be_combined`).
So "surface plus constant" and "surface plus area" are each maximal, and no wider form of
(ii) supports the theorem.

## Why the census does it, in A1.6's own language

The finite-complex argument above is a linear system at five dilates, and the reason it is
nonsingular is the geometry A1.6 already computed.  `surface_moment_forces_zero_rates`
states the same fact in moment coordinates: a rational triple of kind rates whose census
combination is the pure surface moment vector `(0, a, 0, 0, 0)` has `a = 0` and all three
rates zero.  Its `a = 0` half is exactly
`Gap2OrientedFaceSpan.no_pure_surface_term_in_census_span`, the corollary A1.6 drew from
computing the census span as a hyperplane; the remaining half is that the three census
columns are linearly independent (`census4_columns_independent`), which is why zero
moments force zero rates rather than leaving a kernel.

## Scope

The verdict is about letter costs on the Freudenthal carrier, over families realizing the
four-dimensional Kuhn cube census, with bulk cancellation read in A1.6's sharp
quantitative form.  It does not say a substrate must charge this way, and it does not
touch flag 8 or any other flag.  The census counts are imported from A1.5's MEASURED
moment vectors and tied to them by theorem (`censusV_eq_moments` and its two siblings), so
no number is re-entered by hand.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LetterCostDichotomy

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Gap2JEhrhartSpan Gap2OrientedFaceSpan

variable {B : ℕ}

/-! ## §1. The census of the four-dimensional Freudenthal cube dilate

The three counts of the dilate at side `N`, as integers, together with the theorems tying
them to A1.5's MEASURED moment vectors.  Nothing here is a new measurement: `mV4`, `mE4`
and `mT4` are imported, and the three lemmas below are the only place the closed forms
appear. -/

/-- Vertex census of the four-dimensional cube dilate, `(N+1)^4`. -/
def censusV (N : ℕ) : ℕ := (N + 1) ^ 4

/-- Edge census of the four-dimensional cube dilate over the fifteen displacement classes,
`(2N+1)^4 - (N+1)^4`. -/
def censusE (N : ℕ) : ℕ := 15 * N ^ 4 + 28 * N ^ 3 + 18 * N ^ 2 + 4 * N

/-- Kuhn 4-simplex census of the four-dimensional cube dilate, `24 N^4`. -/
def censusT (N : ℕ) : ℕ := 24 * N ^ 4

/-- Evaluate a moment vector in the basis `(N^4, N^3, N^2, N, 1)`. -/
def evalMoments (m : Fin 5 → ℚ) (N : ℕ) : ℚ :=
  m 0 * (N : ℚ) ^ 4 + m 1 * (N : ℚ) ^ 3 + m 2 * (N : ℚ) ^ 2 + m 3 * (N : ℚ) + m 4

theorem censusV_eq_moments (N : ℕ) : (censusV N : ℚ) = evalMoments mV4 N := by
  simp only [censusV, evalMoments, mV4, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four]
  push_cast
  ring

theorem censusE_eq_moments (N : ℕ) : (censusE N : ℚ) = evalMoments mE4 N := by
  simp only [censusE, evalMoments, mE4, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four]
  push_cast
  ring

theorem censusT_eq_moments (N : ℕ) : (censusT N : ℚ) = evalMoments mT4 N := by
  simp only [censusT, evalMoments, mT4, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four]
  push_cast
  ring

theorem censusV_pos (N : ℕ) : 0 < censusV N := by
  unfold censusV
  exact pow_pos (Nat.succ_pos N) 4

/-! ## §2. A dilate family, and the fact that there is one

A `CensusDilateFamily` is a family of bounded complexes whose three counts follow the
census.  The impossibility below quantifies over every such family, so it is stronger the
larger that class is, and `flatFamily` records that the class is not empty.  The
incidence data of `flatFamily` is deliberately trivial: what the theorem reads off a
family is its census, and nothing else. -/

/-- A family of bounded complexes realizing the four-dimensional Freudenthal cube census
at every dilate. -/
structure CensusDilateFamily where
  cap : ℕ → ℕ
  K : ∀ N : ℕ, BoundedComplex (cap N)
  nV_eq : ∀ N : ℕ, (K N).nV = censusV N
  nE_eq : ∀ N : ℕ, (K N).nE = censusE N
  nT_eq : ∀ N : ℕ, (K N).nT = censusT N

/-- A cap large enough for all three census counts at side `N`. -/
def flatCap (N : ℕ) : ℕ := censusV N + censusE N + censusT N

/-- A complex with the census counts and no incidence content. -/
def flatComplex (N : ℕ) : BoundedComplex (flatCap N) where
  nV := censusV N
  nE := censusE N
  nT := censusT N
  hV := by unfold flatCap; omega
  hE := by unfold flatCap; omega
  hT := by unfold flatCap; omega
  edgeVerts := fun _ => (⟨0, censusV_pos N⟩, ⟨0, censusV_pos N⟩)
  tetVerts := fun _ _ => ⟨0, censusV_pos N⟩

/-- **Non-vacuity of the hypothesis class.**  A census dilate family exists. -/
def flatFamily : CensusDilateFamily where
  cap := flatCap
  K := flatComplex
  nV_eq := fun _ => rfl
  nE_eq := fun _ => rfl
  nT_eq := fun _ => rfl

/-! ## §3. Bulk cancellation, in A1.6's sharp quantitative form

A1.6 measured that the oriented-face cost on the four-dimensional cube dilate is exactly
`48 N^3`, and called that bulk cancellation in its sharpest quantitative form: the total
is a pure surface functional of the side.  `SurfaceTotal` states that condition, with an
additive corner constant allowed, since forbidding one would be a hypothesis nobody has a
reason to impose.  `SurfaceAreaTotal` is the other maximal relaxation, an area term
allowed and no constant. -/

/-- **Bulk cancellation, sharp form.**  The history cost over the dilate at side `N` is a
pure surface term plus at most an additive corner constant. -/
def SurfaceTotal (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ) : Prop :=
  ∀ N : ℕ, historyCost c (F.cap N) (F.K N) = a * (N : ℝ) ^ 3 + e

/-- **Bulk cancellation, the other maximal relaxation.**  Surface plus area, no constant. -/
def SurfaceAreaTotal (F : CensusDilateFamily) (c : LetterCost) (a b : ℝ) : Prop :=
  ∀ N : ℕ, historyCost c (F.cap N) (F.K N) = a * (N : ℝ) ^ 3 + b * (N : ℝ) ^ 2

/-- The history cost of a cost with fixed kind totals, on a census family, in the census
counts.  This is the only bridge between the cost layer and the carrier. -/
theorem historyCost_on_family {c : LetterCost} {cV cE cT : ℝ}
    (h : KindTotalRates c cV cE cT) (F : CensusDilateFamily) (N : ℕ) :
    historyCost c (F.cap N) (F.K N)
      = cV * (censusV N : ℝ) + cE * (censusE N : ℝ) + cT * (censusT N : ℝ) := by
  rw [historyCost_of_kindTotalRates h (F.cap N) (F.K N), F.nV_eq, F.nE_eq, F.nT_eq]

/-! ## §4. The headline: the three conditions force the history cost to zero -/

/-- **THE IMPOSSIBILITY.**  On any family realizing the four-dimensional Freudenthal cube
census, a letter cost with fixed kind totals whose history over the dilates is a pure
surface term plus a constant has all three rates zero, zero surface coefficient, and zero
constant.

Gauge equivariance is absent from the statement and from the proof.  The three atom
normalizations are absent too: `e = 0` is a conclusion, not a binder. -/
theorem surface_and_kindTotals_force_zero (F : CensusDilateFamily) {c : LetterCost}
    {cV cE cT a e : ℝ} (hk : KindTotalRates c cV cE cT) (hs : SurfaceTotal F c a e) :
    cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ e = 0 := by
  have key : ∀ N : ℕ,
      cV * (censusV N : ℝ) + cE * (censusE N : ℝ) + cT * (censusT N : ℝ)
        = a * (N : ℝ) ^ 3 + e := by
    intro N
    rw [← historyCost_on_family hk F N]
    exact hs N
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  norm_num [censusV, censusE, censusT] at h0 h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The degenerate member of the family is not doing the work.**  The same conclusion
follows from the surface form at the five positive dilates `1..5` alone, so nobody can read
the theorem as the atom normalizations smuggled in through `N = 0`, whose complex is the
vertex atom. -/
theorem surface_at_positive_dilates_forces_zero (F : CensusDilateFamily) {c : LetterCost}
    {cV cE cT a e : ℝ} (hk : KindTotalRates c cV cE cT)
    (hs : ∀ N : ℕ, 1 ≤ N → historyCost c (F.cap N) (F.K N) = a * (N : ℝ) ^ 3 + e) :
    cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ e = 0 := by
  have key : ∀ N : ℕ, 1 ≤ N →
      cV * (censusV N : ℝ) + cE * (censusE N : ℝ) + cT * (censusT N : ℝ)
        = a * (N : ℝ) ^ 3 + e := by
    intro N hN
    rw [← historyCost_on_family hk F N]
    exact hs N hN
  have h1 := key 1 (by norm_num)
  have h2 := key 2 (by norm_num)
  have h3 := key 3 (by norm_num)
  have h4 := key 4 (by norm_num)
  have h5 := key 5 (by norm_num)
  norm_num [censusV, censusE, censusT] at h1 h2 h3 h4 h5
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The other maximal relaxation dies too.**  Surface plus area, with no constant
allowed, forces every coefficient to zero. -/
theorem surfaceArea_and_kindTotals_force_zero (F : CensusDilateFamily) {c : LetterCost}
    {cV cE cT a b : ℝ} (hk : KindTotalRates c cV cE cT) (hs : SurfaceAreaTotal F c a b) :
    cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ b = 0 := by
  have key : ∀ N : ℕ,
      cV * (censusV N : ℝ) + cE * (censusE N : ℝ) + cT * (censusT N : ℝ)
        = a * (N : ℝ) ^ 3 + b * (N : ℝ) ^ 2 := by
    intro N
    rw [← historyCost_on_family hk F N]
    exact hs N
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  norm_num [censusV, censusE, censusT] at h0 h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The history cost is identically zero, at every complex and every cap.**  Not only on
the family: three rates pinned to zero pin the whole linear functional. -/
theorem surface_and_fixedKindTotals_force_zero_historyCost (F : CensusDilateFamily)
    {c : LetterCost} {a e : ℝ} (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (B : ℕ) (K : BoundedComplex B) : historyCost c B K = 0 := by
  obtain ⟨cV, cE, cT, hk⟩ := h
  obtain ⟨hV, hE, hT, _, _⟩ := surface_and_kindTotals_force_zero F hk hs
  rw [historyCost_of_kindTotalRates hk B K, hV, hE, hT]
  ring

/-- **The content of the impossibility: the measure is exactly the gauge divisor.**  The
Boltzmann numerator is identically one, the posted weight is the reciprocal order of the
alphabet's sort-respecting gauge group, and the class measure is `mu`.  The cost layer
contributes no factor, so no rate can be read off it. -/
theorem the_measure_is_exactly_the_gauge_divisor (F : CensusDilateFamily) {c : LetterCost}
    {a e : ℝ} (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (B : ℕ) (K : BoundedComplex B) :
    Real.exp (-(historyCost c B K)) = 1
      ∧ postedWeight c B K = gibbsWeight K
      ∧ postedWeight c B K = 1 / (Nat.card (AlphabetGauge K) : ℝ)
      ∧ classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  have hz : ∀ (B' : ℕ) (K' : BoundedComplex B'), historyCost c B' K' = 0 :=
    fun B' K' => surface_and_fixedKindTotals_force_zero_historyCost F h hs B' K'
  have hgib : ∀ (B' : ℕ) (K' : BoundedComplex B'), postedWeight c B' K' = gibbsWeight K' := by
    intro B' K'
    unfold postedWeight
    rw [hz B' K', neg_zero, Real.exp_zero, one_mul]
  refine ⟨by rw [hz B K, neg_zero, Real.exp_zero], hgib B K, ?_, ?_⟩
  · rw [hgib B K, gibbsWeight_eq_inv_card_alphabetGauge]
  · have hfun : postedWeight c B = fun K' : BoundedComplex B => gibbsWeight K' := by
      funext K'
      exact hgib B K'
    rw [hfun]
    exact classMass_gibbsWeight_eq_mu K

/-- **The atom normalizations are derived, not assumed.**  This is the sharpening over
`Gap2PostingCostDerivation.fixedKindTotals_and_atoms_force_zero_historyCost`, which needs
`NormalizedAtTheAtoms` in its binders and gets the same conclusion.  Bulk cancellation on
the dilate family does that job instead. -/
theorem atom_normalizations_are_derived (F : CensusDilateFamily) {c : LetterCost}
    {a e : ℝ} (h : FixedKindTotals c) (hs : SurfaceTotal F c a e) :
    NormalizedAtTheAtoms (postedWeight c) := by
  intro B' K' hv hi
  rw [(the_measure_is_exactly_the_gauge_divisor F h hs B' K').2.1]
  exact gibbsWeight_eq_one_at_atoms K' hv hi

/-! ## §5. The same fact in A1.6's moment coordinates

The linear system at five dilates is nonsingular for a reason A1.6 computed: the census
span is the hyperplane the obstruction functional annihilates, so no pure surface term is
in it, and the three census columns are independent, so zero moments force zero rates. -/

/-- The three census columns are linearly independent over the rationals.  Read off the
constant, linear and leading strata in that order. -/
theorem census4_columns_independent {cV cE cT : ℚ}
    (h : ∀ i : Fin 5, cV * mV4 i + cE * mE4 i + cT * mT4 i = 0) :
    cV = 0 ∧ cE = 0 ∧ cT = 0 := by
  have h4 := h 4
  have h3 := h 3
  have h0 := h 0
  simp [mV4, mE4, mT4] at h0 h3 h4
  refine ⟨h4, ?_, ?_⟩ <;> linarith

/-- **THE IMPOSSIBILITY, in moment coordinates.**  A rational triple of kind rates whose
census combination is a pure surface moment vector has zero surface coefficient and zero
rates.  The first half is exactly A1.6's `no_pure_surface_term_in_census_span`; the second
is column independence. -/
theorem surface_moment_forces_zero_rates {cV cE cT a : ℚ}
    (h : ∀ i : Fin 5,
      cV * mV4 i + cE * mE4 i + cT * mT4 i = (![0, a, 0, 0, 0] : Fin 5 → ℚ) i) :
    cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 := by
  have ha : a = 0 := by
    by_contra hne
    refine no_pure_surface_term_in_census_span a hne ⟨cV, cE, cT, 0, ?_⟩
    intro i
    rw [zero_mul, add_zero]
    exact h i
  subst ha
  have hz : ∀ i : Fin 5, cV * mV4 i + cE * mE4 i + cT * mT4 i = 0 := by
    intro i
    rw [h i]
    fin_cases i <;> simp
  obtain ⟨hV, hE, hT⟩ := census4_columns_independent hz
  exact ⟨hV, hE, hT, rfl⟩

/-! ## §6. The load-bearing checks

One countermodel per hypothesis that has one, and for the hypothesis that has none, the
measurement that its absence widens the class rather than emptying it. -/

/-- The letter cost charging the three fixed rates, one per kind. -/
def kindRateCost (cV cE cT : ℝ) : LetterCost := fun _ _ a =>
  match a with
  | Sum.inl _ => cV
  | Sum.inr (Sum.inl _) => cE
  | Sum.inr (Sum.inr _) => cT

theorem kindRateCost_kindRates (cV cE cT : ℝ) :
    KindRates (kindRateCost cV cE cT) cV cE cT :=
  fun _ _ => ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem kindRateCost_kindOnly (cV cE cT : ℝ) : KindOnly (kindRateCost cV cE cT) :=
  ⟨cV, cE, cT, kindRateCost_kindRates cV cE cT⟩

theorem kindRateCost_equivariant (cV cE cT : ℝ) : Equivariant (kindRateCost cV cE cT) :=
  kindOnly_equivariant (kindRateCost_kindOnly cV cE cT)

theorem kindRateCost_fixedKindTotals (cV cE cT : ℝ) :
    FixedKindTotals (kindRateCost cV cE cT) :=
  kindOnly_fixedKindTotals (kindRateCost_kindOnly cV cE cT)

theorem historyCost_kindRateCost_on_family (cV cE cT : ℝ) (F : CensusDilateFamily)
    (N : ℕ) :
    historyCost (kindRateCost cV cE cT) (F.cap N) (F.K N)
      = cV * (censusV N : ℝ) + cE * (censusE N : ℝ) + cT * (censusT N : ℝ) :=
  historyCost_on_family (kindRates_kindTotalRates (kindRateCost_kindRates cV cE cT)) F N

theorem historyCost_kindRateCost_dust_one (cV cE cT : ℝ) :
    historyCost (kindRateCost cV cE cT) 1 (dust 1) = cV := by
  rw [historyCost_of_kindRates (kindRateCost_kindRates cV cE cT) 1 (dust 1)]
  simp

/-- **(ii) is load-bearing.**  The cost charging one unit per vertex letter is equivariant,
has fixed kind totals, and has nonzero history cost, so it satisfies (i) and (iii) and
fails only (ii).  That it fails (ii) on every census family is the headline read
backwards: were it bulk-cancelling, its vertex rate would be zero. -/
theorem bulk_cancellation_is_load_bearing (F : CensusDilateFamily) :
    Equivariant (kindRateCost 1 0 0)
      ∧ FixedKindTotals (kindRateCost 1 0 0)
      ∧ historyCost (kindRateCost 1 0 0) 1 (dust 1) ≠ 0
      ∧ ¬ ∃ a e : ℝ, SurfaceTotal F (kindRateCost 1 0 0) a e := by
  refine ⟨kindRateCost_equivariant 1 0 0, kindRateCost_fixedKindTotals 1 0 0, ?_, ?_⟩
  · rw [historyCost_kindRateCost_dust_one]
    norm_num
  · rintro ⟨a, e, hs⟩
    obtain ⟨hV, _, _, _, _⟩ :=
      surface_and_kindTotals_force_zero F (kindRates_kindTotalRates
        (kindRateCost_kindRates 1 0 0)) hs
    norm_num at hV

/-- **The purity of the surface term is load-bearing, not the absence of a bulk term.**
Charging each vertex one unit and each Kuhn 4-simplex `-1/24` gives a total whose leading
coefficient is exactly zero, and the cost is equivariant, has fixed kind totals, and is
nonzero.  So (ii) read loosely as "the bulk cancels" does not decide the question; only the
sharp form does. -/
theorem purity_of_the_surface_term_is_load_bearing (F : CensusDilateFamily) :
    Equivariant (kindRateCost 1 0 (-(1/24)))
      ∧ FixedKindTotals (kindRateCost 1 0 (-(1/24)))
      ∧ historyCost (kindRateCost 1 0 (-(1/24))) 1 (dust 1) ≠ 0
      ∧ ∀ N : ℕ, historyCost (kindRateCost 1 0 (-(1/24))) (F.cap N) (F.K N)
          = 4 * (N : ℝ) ^ 3 + 6 * (N : ℝ) ^ 2 + 4 * (N : ℝ) + 1 := by
  refine ⟨kindRateCost_equivariant _ _ _, kindRateCost_fixedKindTotals _ _ _, ?_, ?_⟩
  · rw [historyCost_kindRateCost_dust_one]
    norm_num
  · intro N
    rw [historyCost_kindRateCost_on_family]
    simp only [censusV, censusE, censusT]
    push_cast
    ring

/-- **The two relaxations of (ii) cannot be combined.**  Rates `(1, -1, 7/12)` give the
total `-24N^3 - 12N^2 + 1`: no bulk term, no linear term, a surface term, an area term and
a constant, and the rates are not zero.  So "surface plus constant" and "surface plus
area" are each maximal, and their union supports no theorem. -/
theorem the_two_relaxations_cannot_be_combined (F : CensusDilateFamily) :
    Equivariant (kindRateCost 1 (-1) (7/12))
      ∧ FixedKindTotals (kindRateCost 1 (-1) (7/12))
      ∧ historyCost (kindRateCost 1 (-1) (7/12)) 1 (dust 1) ≠ 0
      ∧ ∀ N : ℕ, historyCost (kindRateCost 1 (-1) (7/12)) (F.cap N) (F.K N)
          = (-24) * (N : ℝ) ^ 3 + (-12) * (N : ℝ) ^ 2 + 1 := by
  refine ⟨kindRateCost_equivariant _ _ _, kindRateCost_fixedKindTotals _ _ _, ?_, ?_⟩
  · rw [historyCost_kindRateCost_dust_one]
    norm_num
  · intro N
    rw [historyCost_kindRateCost_on_family]
    simp only [censusV, censusE, censusT]
    push_cast
    ring

/-! ### (iii): a nonzero equivariant cost whose total is a pure surface term

The physical witness for this slot is A1.6's oriented-face cost, whose total on the real
carrier is MEASURED to be exactly `48 N^3`.  A measurement is not a kernel check, so what
stands here is a synthetic member of the same hypothesis class: a cost that reads the side
of the region off the vertex census and charges the surface it implies. -/

/-- The side of a cube dilate, recovered from its vertex census. -/
def sideOf (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n) - 1

theorem sideOf_censusV (N : ℕ) : sideOf (censusV N) = N := by
  have h : censusV N = ((N + 1) ^ 2) ^ 2 := by
    unfold censusV
    ring
  unfold sideOf
  rw [h, Nat.sqrt_eq', Nat.sqrt_eq']
  omega

theorem sideOf_one : sideOf 1 = 0 := by
  have h : censusV 0 = 1 := by norm_num [censusV]
  have hs := sideOf_censusV 0
  rw [h] at hs
  exact hs

theorem sideOf_sixteen : sideOf 16 = 1 := by
  have h : censusV 1 = 16 := by norm_num [censusV]
  have hs := sideOf_censusV 1
  rw [h] at hs
  exact hs

noncomputable section

/-- The **surface cost**: every vertex letter carries an equal share of a charge that is
the cube of the region's side.  Equivariant, since it reads only the vertex count. -/
def surfaceCost (t : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => t * (sideOf K.nV : ℝ) ^ 3 / (K.nV : ℝ)
  | Sum.inr _ => 0

@[simp] theorem surfaceCost_inl (t : ℝ) (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    surfaceCost t B K (Sum.inl v) = t * (sideOf K.nV : ℝ) ^ 3 / (K.nV : ℝ) := rfl

@[simp] theorem surfaceCost_edge (t : ℝ) (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE) :
    surfaceCost t B K (Sum.inr (Sum.inl e)) = 0 := rfl

@[simp] theorem surfaceCost_tet (t : ℝ) (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT) :
    surfaceCost t B K (Sum.inr (Sum.inr τ)) = 0 := rfl

theorem vertexBlockSum_surfaceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B)
    (h : K.nV ≠ 0) :
    (∑ v : Fin K.nV, surfaceCost t B K (Sum.inl v)) = t * (sideOf K.nV : ℝ) ^ 3 := by
  classical
  have hne : (K.nV : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  simp only [surfaceCost_inl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem historyCost_surfaceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) (h : K.nV ≠ 0) :
    historyCost (surfaceCost t) B K = t * (sideOf K.nV : ℝ) ^ 3 := by
  classical
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [surfaceCost_edge, surfaceCost_tet, Finset.sum_const_zero, add_zero]
  exact vertexBlockSum_surfaceCost t B K h

/-- The surface cost is gauge equivariant: it reads only the vertex count, which a
relabeling preserves. -/
theorem surfaceCost_equivariant (t : ℝ) : Equivariant (surfaceCost t) := by
  intro B K K' r a
  rcases a with v | (e | τ)
  · show surfaceCost t B K' (Sum.inl (r.vEquiv v)) = surfaceCost t B K (Sum.inl v)
    rw [surfaceCost_inl, surfaceCost_inl, size_v r]
  · rfl
  · rfl

/-- **The surface cost is bulk-cancelling in the sharp sense, with coefficient `t`.** -/
theorem surfaceCost_surfaceTotal (F : CensusDilateFamily) (t : ℝ) :
    SurfaceTotal F (surfaceCost t) t 0 := by
  intro N
  have hne : (F.K N).nV ≠ 0 := by
    rw [F.nV_eq N]
    exact (censusV_pos N).ne'
  rw [historyCost_surfaceCost t (F.cap N) (F.K N) hne, F.nV_eq N, sideOf_censusV N]
  ring

/-- **The surface cost has no fixed kind totals.**  A single vertex has side zero and
costs nothing, which forces the vertex rate to zero; sixteen vertices have side one and
cost `t`, which then demands `t = 0`. -/
theorem surfaceCost_not_fixedKindTotals {t : ℝ} (ht : t ≠ 0) :
    ¬ FixedKindTotals (surfaceCost t) := by
  rintro ⟨cV, cE, cT, h⟩
  have h1 := (h 1 (dust 1)).1
  have h2 := (h 16 (dust 16)).1
  rw [vertexBlockSum_surfaceCost t 1 (dust 1) (by simp)] at h1
  rw [vertexBlockSum_surfaceCost t 16 (dust 16) (by simp)] at h2
  simp only [dust_nV, sideOf_one, sideOf_sixteen, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat] at h1 h2
  norm_num at h1 h2
  exact ht (by linarith)

/-- **(iii) is load-bearing.**  A nonzero gauge-equivariant cost whose total on every
census family is exactly the pure surface term `t N^3`, and which has no fixed kind
totals.  Drop (iii) and the impossibility is false. -/
theorem fixed_kind_totals_is_load_bearing (F : CensusDilateFamily) {t : ℝ} (ht : t ≠ 0) :
    Equivariant (surfaceCost t)
      ∧ SurfaceTotal F (surfaceCost t) t 0
      ∧ ¬ FixedKindTotals (surfaceCost t)
      ∧ historyCost (surfaceCost t) 16 (dust 16) ≠ 0 := by
  refine ⟨surfaceCost_equivariant t, surfaceCost_surfaceTotal F t,
    surfaceCost_not_fixedKindTotals ht, ?_⟩
  rw [historyCost_surfaceCost t 16 (dust 16) (by simp)]
  simp only [dust_nV, sideOf_sixteen, Nat.cast_one, one_pow, mul_one]
  exact ht

/-! ### (i): equivariance is not load-bearing, and dropping it widens the class

There is no countermodel to exhibit here, because the theorem never used the hypothesis.
What is worth measuring is that its absence widens the class rather than emptying it: a
cost outside it that satisfies (ii) and (iii) and is not zero. -/

/-- A cost that charges the first vertex letter the whole of a debt the remaining vertex
letters each pay back one unit of.  Every block sum is zero, and the letter it charges
depends on the letter's index, so labels are not gauge for it. -/
def indexTiltCost (t : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inl v => if (v : ℕ) = 0 then t * ((K.nV : ℝ) - 1) else -t
  | Sum.inr _ => 0

@[simp] theorem indexTiltCost_inl (t : ℝ) (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    indexTiltCost t B K (Sum.inl v)
      = if (v : ℕ) = 0 then t * ((K.nV : ℝ) - 1) else -t := rfl

@[simp] theorem indexTiltCost_edge (t : ℝ) (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE) :
    indexTiltCost t B K (Sum.inr (Sum.inl e)) = 0 := rfl

@[simp] theorem indexTiltCost_tet (t : ℝ) (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT) :
    indexTiltCost t B K (Sum.inr (Sum.inr τ)) = 0 := rfl

theorem vertexSum_indexTilt (t : ℝ) (n : ℕ) :
    (∑ v : Fin n, (if (v : ℕ) = 0 then t * ((n : ℝ) - 1) else -t)) = 0 := by
  classical
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.sum_univ_succ]
    have hz : ((0 : Fin (m + 1)) : ℕ) = 0 := rfl
    have hs : ∀ i : Fin m, ((i.succ : Fin (m + 1)) : ℕ) ≠ 0 := by
      intro i
      rw [Fin.val_succ]
      omega
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => if_neg (hs i)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [if_pos hz]
    push_cast
    ring

theorem indexTiltCost_kindTotalRates (t : ℝ) : KindTotalRates (indexTiltCost t) 0 0 0 := by
  classical
  intro B K
  refine ⟨?_, ?_, ?_⟩
  · simp only [indexTiltCost_inl]
    rw [vertexSum_indexTilt t K.nV]
    ring
  · simp
  · simp

theorem indexTiltCost_fixedKindTotals (t : ℝ) : FixedKindTotals (indexTiltCost t) :=
  ⟨0, 0, 0, indexTiltCost_kindTotalRates t⟩

theorem historyCost_indexTiltCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (indexTiltCost t) B K = 0 := by
  rw [historyCost_of_kindTotalRates (indexTiltCost_kindTotalRates t) B K]
  ring

theorem indexTiltCost_surfaceTotal (F : CensusDilateFamily) (t : ℝ) :
    SurfaceTotal F (indexTiltCost t) 0 0 := by
  intro N
  rw [historyCost_indexTiltCost]
  ring

/-- The first vertex of the two-point dust. -/
def v0Dust2 : Fin (dust 2).nV := ⟨0, by decide⟩

/-- The second vertex of the two-point dust. -/
def v1Dust2 : Fin (dust 2).nV := ⟨1, by decide⟩

/-- Swap the two vertices of the two-point dust.  With no incidence data both commutation
conditions are vacuous, so this is a relabeling. -/
def swapDust2 : Relabel (dust 2) (dust 2) where
  vEquiv := Equiv.swap v0Dust2 v1Dust2
  eEquiv := Equiv.refl _
  tEquiv := Equiv.refl _
  edge_comm := fun e => e.elim0
  tet_comm := fun t _ => t.elim0

theorem swapDust2_v0 : swapDust2.vEquiv v0Dust2 = v1Dust2 :=
  Equiv.swap_apply_left _ _

/-- The first vertex letter of the two-point dust is charged `t`. -/
theorem indexTiltCost_at_v0 (t : ℝ) :
    indexTiltCost t 2 (dust 2) (Sum.inl v0Dust2) = t := by
  rw [indexTiltCost_inl]
  norm_num [v0Dust2]

/-- The second vertex letter of the two-point dust is charged `-t`. -/
theorem indexTiltCost_at_v1 (t : ℝ) :
    indexTiltCost t 2 (dust 2) (Sum.inl v1Dust2) = -t := by
  rw [indexTiltCost_inl]
  norm_num [v1Dust2]

/-- **The tilt cost is not gauge equivariant.**  Swapping the two vertices of the two-point
dust carries a letter charged `t` to a letter charged `-t`. -/
theorem indexTiltCost_not_equivariant {t : ℝ} (ht : t ≠ 0) :
    ¬ Equivariant (indexTiltCost t) := by
  intro h
  have hEq := h 2 (dust 2) (dust 2) swapDust2 (Sum.inl v0Dust2)
  rw [show postingAlphEquiv swapDust2.vEquiv swapDust2.eEquiv swapDust2.tEquiv
      (Sum.inl v0Dust2) = Sum.inl (swapDust2.vEquiv v0Dust2) from rfl, swapDust2_v0,
    indexTiltCost_at_v1, indexTiltCost_at_v0] at hEq
  exact ht (by linarith)

/-- **(i) is not load-bearing, and its absence widens the class.**  The tilt cost has fixed
kind totals, is bulk-cancelling in the sharp sense, is a nonzero letter cost, and is not
equivariant.  The impossibility applies to it unchanged, which is the point: no
countermodel exists for (i) because (i) was never used. -/
theorem equivariance_is_not_load_bearing (F : CensusDilateFamily) {t : ℝ} (ht : t ≠ 0) :
    FixedKindTotals (indexTiltCost t)
      ∧ SurfaceTotal F (indexTiltCost t) 0 0
      ∧ ¬ Equivariant (indexTiltCost t)
      ∧ indexTiltCost t 2 (dust 2) (Sum.inl v0Dust2) ≠ 0
      ∧ ∀ (B : ℕ) (K : BoundedComplex B), historyCost (indexTiltCost t) B K = 0 := by
  refine ⟨indexTiltCost_fixedKindTotals t, indexTiltCost_surfaceTotal F t,
    indexTiltCost_not_equivariant ht, ?_, historyCost_indexTiltCost t⟩
  rw [indexTiltCost_at_v0]
  exact ht

/-! ## §7. What is NOT forced: the letter-level fibre

The question as posed asks for a nonzero letter cost.  Read at the letter, the answer is
that one exists and the library already had it, which is why the impossibility above is
stated at the history cost and not at the letter.  The centered incidence cost reads
incidence at every edge letter, is equivariant, has fixed kind totals, is bulk-cancelling
with coefficient zero, and is nonzero.  What it is not is visible to the weight. -/

/-- **The fibre over the zero history cost is not a point.**  For every nonzero `t` the
centered incidence cost satisfies all three conditions and is a nonzero letter cost, while
its history cost is identically zero.  So "no nonzero cost" is false at the letter and true
at everything the posted weight can see, and the impossibility must be stated at the
history cost. -/
theorem the_letter_level_fibre_is_not_a_point (F : CensusDilateFamily) {t : ℝ} (ht : t ≠ 0) :
    Equivariant (centeredIncidenceCost t)
      ∧ FixedKindTotals (centeredIncidenceCost t)
      ∧ SurfaceTotal F (centeredIncidenceCost t) 0 0
      ∧ centeredIncidenceCost t 3 loopAndBridge (Sum.inr (Sum.inl ⟨1, by decide⟩)) ≠ 0
      ∧ ∀ (B : ℕ) (K : BoundedComplex B), historyCost (centeredIncidenceCost t) B K = 0 := by
  refine ⟨centeredIncidenceCost_equivariant t, fixedKindTotals_centeredIncidenceCost t,
    ?_, ?_, fun B K => historyCost_centeredIncidenceCost t B K⟩
  · intro N
    rw [historyCost_centeredIncidenceCost]
    ring
  · rw [(centeredIncidence_charges_on_loopAndBridge t).2]
    exact ht

/-! ## §8. Certificate -/

/-- **The A1.7 dichotomy verdict.**  The impossibility horn landed, at the history cost and
not at the letter.  Every clause below is a theorem of this module or of one it imports. -/
structure LetterCostDichotomyVerdict : Prop where
  family_exists : True
  impossibility : ∀ (F : CensusDilateFamily) (c : LetterCost) (cV cE cT a e : ℝ),
    KindTotalRates c cV cE cT → SurfaceTotal F c a e →
      cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ e = 0
  history_cost_is_zero : ∀ (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ),
    FixedKindTotals c → SurfaceTotal F c a e →
      ∀ (B : ℕ) (K : BoundedComplex B), historyCost c B K = 0
  measure_is_the_divisor : ∀ (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ),
    FixedKindTotals c → SurfaceTotal F c a e →
      ∀ (B : ℕ) (K : BoundedComplex B),
        postedWeight c B K = 1 / (Nat.card (AlphabetGauge K) : ℝ)
          ∧ classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K
  atoms_derived : ∀ (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ),
    FixedKindTotals c → SurfaceTotal F c a e → NormalizedAtTheAtoms (postedWeight c)
  positive_dilates_suffice : ∀ (F : CensusDilateFamily) (c : LetterCost) (cV cE cT a e : ℝ),
    KindTotalRates c cV cE cT →
      (∀ N : ℕ, 1 ≤ N → historyCost c (F.cap N) (F.K N) = a * (N : ℝ) ^ 3 + e) →
        cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ e = 0
  surface_plus_area_also_dies : ∀ (F : CensusDilateFamily) (c : LetterCost)
      (cV cE cT a b : ℝ), KindTotalRates c cV cE cT → SurfaceAreaTotal F c a b →
        cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ b = 0
  moment_form : ∀ cV cE cT a : ℚ,
    (∀ i : Fin 5, cV * mV4 i + cE * mE4 i + cT * mT4 i
        = (![0, a, 0, 0, 0] : Fin 5 → ℚ) i) → cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0
  kind_totals_load_bearing : ∀ (F : CensusDilateFamily) (t : ℝ), t ≠ 0 →
    Equivariant (surfaceCost t) ∧ SurfaceTotal F (surfaceCost t) t 0
      ∧ ¬ FixedKindTotals (surfaceCost t)
  bulk_cancellation_load_bearing : ∀ F : CensusDilateFamily,
    ¬ ∃ a e : ℝ, SurfaceTotal F (kindRateCost 1 0 0) a e
  equivariance_not_load_bearing : ∀ (F : CensusDilateFamily) (t : ℝ), t ≠ 0 →
    FixedKindTotals (indexTiltCost t) ∧ SurfaceTotal F (indexTiltCost t) 0 0
      ∧ ¬ Equivariant (indexTiltCost t)
  purity_is_the_boundary : ∀ F : CensusDilateFamily,
    ∀ N : ℕ, historyCost (kindRateCost 1 0 (-(1/24))) (F.cap N) (F.K N)
      = 4 * (N : ℝ) ^ 3 + 6 * (N : ℝ) ^ 2 + 4 * (N : ℝ) + 1
  relaxations_incompatible : ∀ F : CensusDilateFamily,
    ∀ N : ℕ, historyCost (kindRateCost 1 (-1) (7/12)) (F.cap N) (F.K N)
      = (-24) * (N : ℝ) ^ 3 + (-12) * (N : ℝ) ^ 2 + 1
  letter_fibre_not_a_point : ∀ (F : CensusDilateFamily) (t : ℝ), t ≠ 0 →
    Equivariant (centeredIncidenceCost t) ∧ FixedKindTotals (centeredIncidenceCost t)
      ∧ SurfaceTotal F (centeredIncidenceCost t) 0 0
      ∧ centeredIncidenceCost t 3 loopAndBridge (Sum.inr (Sum.inl ⟨1, by decide⟩)) ≠ 0

theorem letterCostDichotomyVerdict : LetterCostDichotomyVerdict where
  family_exists := trivial
  impossibility := fun F c _ _ _ _ _ hk hs => surface_and_kindTotals_force_zero F hk hs
  history_cost_is_zero := fun F c _ _ h hs B K =>
    surface_and_fixedKindTotals_force_zero_historyCost F h hs B K
  measure_is_the_divisor := fun F c _ _ h hs B K =>
    ⟨(the_measure_is_exactly_the_gauge_divisor F h hs B K).2.2.1,
      (the_measure_is_exactly_the_gauge_divisor F h hs B K).2.2.2⟩
  atoms_derived := fun F c _ _ h hs => atom_normalizations_are_derived F h hs
  positive_dilates_suffice := fun F c _ _ _ _ _ hk hs =>
    surface_at_positive_dilates_forces_zero F hk hs
  surface_plus_area_also_dies := fun F c _ _ _ _ _ hk hs =>
    surfaceArea_and_kindTotals_force_zero F hk hs
  moment_form := fun _ _ _ _ h => surface_moment_forces_zero_rates h
  kind_totals_load_bearing := fun F t ht =>
    ⟨(fixed_kind_totals_is_load_bearing F ht).1,
      (fixed_kind_totals_is_load_bearing F ht).2.1,
      (fixed_kind_totals_is_load_bearing F ht).2.2.1⟩
  bulk_cancellation_load_bearing := fun F => (bulk_cancellation_is_load_bearing F).2.2.2
  equivariance_not_load_bearing := fun F t ht =>
    ⟨(equivariance_is_not_load_bearing F ht).1,
      (equivariance_is_not_load_bearing F ht).2.1,
      (equivariance_is_not_load_bearing F ht).2.2.1⟩
  purity_is_the_boundary := fun F => (purity_of_the_surface_term_is_load_bearing F).2.2.2
  relaxations_incompatible := fun F => (the_two_relaxations_cannot_be_combined F).2.2.2
  letter_fibre_not_a_point := fun F t ht =>
    ⟨(the_letter_level_fibre_is_not_a_point F ht).1,
      (the_letter_level_fibre_is_not_a_point F ht).2.1,
      (the_letter_level_fibre_is_not_a_point F ht).2.2.1,
      (the_letter_level_fibre_is_not_a_point F ht).2.2.2.1⟩

/-! ## §9. Flag status

Nothing moves.  The impossibility closes a route to a triple of chemical potentials rather
than producing one, so there is still nothing to compare against unit fugacity and
`gap2_measure_derived` stays exactly as it was.  What the module changes is the frontier:
the open question is no longer whether some other imbalance referent escapes, it is whether
the substrate forces aggregate linearity by kind at all. -/

structure DichotomyIndex : Type where
  /-- The dichotomy is decided, and the impossibility horn landed. -/
  dichotomy_decided : Bool
  /-- The forcing is at the history cost, and the letter cost is NOT forced to zero. -/
  forced_at_history_not_at_letter : Bool
  /-- Gauge equivariance is absent from the statement and the proof. -/
  equivariance_used : Bool
  /-- The three atom normalizations are derived rather than assumed. -/
  atom_normalizations_derived : Bool
  /-- The sharp form of bulk cancellation is exactly maximal: two relaxations, each
  maximal, incompatible with each other. -/
  boundary_of_bulk_cancellation_measured : Bool
  /-- NOT produced: a triple of chemical potentials.  The impossibility closes the route
  rather than deriving a rate. -/
  triple_derived : Bool
  /-- NOT moved. -/
  measure_flag_moved : Bool

def dichotomyIndex : DichotomyIndex where
  dichotomy_decided := true
  forced_at_history_not_at_letter := true
  equivariance_used := false
  atom_normalizations_derived := true
  boundary_of_bulk_cancellation_measured := true
  triple_derived := false
  measure_flag_moved := false

theorem index_no_triple : dichotomyIndex.triple_derived = false := rfl

theorem index_flag_unmoved : dichotomyIndex.measure_flag_moved = false := rfl

theorem index_equivariance_unused : dichotomyIndex.equivariance_used = false := rfl

end

/-! ## Axiom audit -/

#print axioms censusV_eq_moments
#print axioms censusE_eq_moments
#print axioms censusT_eq_moments
#print axioms historyCost_on_family
#print axioms surface_and_kindTotals_force_zero
#print axioms surface_at_positive_dilates_forces_zero
#print axioms surfaceArea_and_kindTotals_force_zero
#print axioms surface_and_fixedKindTotals_force_zero_historyCost
#print axioms the_measure_is_exactly_the_gauge_divisor
#print axioms atom_normalizations_are_derived
#print axioms census4_columns_independent
#print axioms surface_moment_forces_zero_rates
#print axioms bulk_cancellation_is_load_bearing
#print axioms purity_of_the_surface_term_is_load_bearing
#print axioms the_two_relaxations_cannot_be_combined
#print axioms sideOf_censusV
#print axioms historyCost_surfaceCost
#print axioms surfaceCost_equivariant
#print axioms surfaceCost_surfaceTotal
#print axioms surfaceCost_not_fixedKindTotals
#print axioms fixed_kind_totals_is_load_bearing
#print axioms vertexSum_indexTilt
#print axioms indexTiltCost_kindTotalRates
#print axioms indexTiltCost_not_equivariant
#print axioms equivariance_is_not_load_bearing
#print axioms the_letter_level_fibre_is_not_a_point
#print axioms letterCostDichotomyVerdict

end Gap2LetterCostDichotomy
end SevenGaps
end Gravity
end IndisputableMonolith
