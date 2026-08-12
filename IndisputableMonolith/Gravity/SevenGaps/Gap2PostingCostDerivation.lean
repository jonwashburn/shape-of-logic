import IndisputableMonolith.Gravity.SevenGaps.Gap2SizeBlindnessReach

/-!
# Gap 2: premise (i) derived from a posting cost, and the premise that derivation needs

`Gap2GluingDerivation` assumes premise (i), size-blindness of the labeled weight, and
`Gap2SizeBlindnessReach` shows that no premise of the form *the weight cannot distinguish
complexes that agree on `X`* supplies it while being weaker than it: blindness to `X` forces
size-blindness for every weight exactly when `X` resolves no more than the three counts.  What
that rules out is a *weaker* sufficient premise of this shape; it does not say the two conditions
are interchangeable, and they are not, since the coarse class also contains conditions strictly
stronger than premise (i) (`unsorted_is_strictly_stronger`).  That dichotomy quantifies over
**indistinguishability** premises, and this module goes at premise (i) with a premise of a
different kind, one that assigns the weight instead of failing to separate it.

## The layer this module works at

`GaugeHistoryMeasure` presents a complex as a posted history, and the reading of that
presentation is MODEL: `PostingAlphabet K = Fin K.nV ⊕ Fin K.nE ⊕ Fin K.nT` is a three-block
index type with canonical injections, and nothing in the library defines an emission process or
proves that substrate dynamics produces those letters.  "The substrate posts one letter per cell"
is how the type is *read*, not something derived, and additivity of a cost over those postings is
the unproved physical attachment the whole module rests on.  Two things then have posting-layer
readings.

The **divisor** does: `gibbsWeight K = 1 / (nV! nE! nT!)` is the reciprocal of the order of
the alphabet's sort-respecting gauge group, the three symmetric groups on the three letter
blocks (`gibbsWeight_eq_inv_card_alphabetGauge`).  That group is not a new object: it is
`Gap2GaugeVolume.SectorGroup` (`alphabetGauge_eq_sectorGroup`), which that module already proved
is in bijection with the relabeling witnesses out of `K` (`sectorEquiv`).  So the identification is
real rather than a rename, and its content is borrowed rather than added: what §1 contributes is
that the same group is what the alphabet's three blocks admit.

The **numerator** does too, once a cost is added.  A `LetterCost` assigns a real number to
each letter.  The `historyCost` of a complex is the sum of its letters' costs, which is
ledger additivity over postings and nothing more.  The `postedWeight` is the Boltzmann factor
of that cost over the gauge volume, and **the exponential is a third modeling choice, not a
consequence of the first two**: nothing here derives that a charge enters the weight as
`exp(-cost)` rather than through some other strictly decreasing map, and the derivation below uses
`exp` throughout.  It is named here because §7's inventory of what stands undischarged missed it
twice.

## §3, the derivation: kind-only letter costs give premise (i), and then the measure

A letter cost is **kind-only** when a letter's cost depends on which of the three blocks it
came from and on nothing else.  Then:

* the history cost is `cV·nV + cE·nE + cT·nT` (`historyCost_of_kindRates`), so the posted
  weight is size-blind (`postedWeight_sizeBlind`) and premise (i) holds in exactly the form
  the derivation states it (`posting_cost_derives_premise_one`);
* the three unit normalizations then force `cV = cE = cT = 0`
  (`kindRates_atoms_force_zero`), because the gauge volume is `1` at each atom, so the
  Boltzmann factor must be too;
* hence the weight is the Gibbs weight (`posting_cost_derives_gibbs`) and the class measure
  is `mu` exactly (`posting_cost_derives_mu`).

**No gluing premise appears in that chain.**  Premise (ii) is not used, not assumed, and not
needed.  Be precise about what replaces it, because the loose version of this sentence is wrong.
The deflation theorem needs only premise (i), and what it gives is the *shape* `q(sizes)/|Aut K|`,
not `mu`: for a general size-blind weight the class mass is the sector fugacity over the
automorphism count, and `mu` requires the fugacity to be one.  So premise (i) supplies the
`1/|Aut K|` dependence and the normalizations supply the numerator, which is the job premise (ii)
used to do by recursion.  The premise set is satisfied at the intended point
(`posting_premises_satisfiable`), so none of this is vacuous.

That premise (ii) is gone does not mean it was idle, and the module says what it was for
rather than leaving the reader to wonder.  Its job in `Gap2GluingDerivation` is to propagate
the three unit normalizations from the atoms out to every size triple, which premise (i) alone
cannot do, since three values do not determine a function of the counts.  What replaces it here
is **linearity in the counts**, and that is a premise rather than a consequence of the carrier.
Summing a per-letter charge over an alphabet with one letter per cell does *not* make the total
linear in the counts: `pairCost` charges each vertex letter the vertex count, so its history cost
is `nV(nV-1)` (`historyCost_pairCost`).  Linearity arrives only with `KindRates` or
`FixedKindTotals`, and once it is assumed, a linear function vanishing at three independent points
vanishes everywhere.  That the job is real is measured, not asserted:
`costSizeBlind_and_atoms_do_not_give_gibbs` exhibits a cost satisfying premise (i) and all three
normalizations whose weight is not the Gibbs weight, so drop linearity and keep everything else and
the derivation stops.

Three things must be said in the same breath, or the claim is inflated.

First, the gauge divisor is a **premise, not a definition**.  Writing it into `postedWeight`
would hide it, so `PostedBy` states it as one equation, which packs three things and not two: that
the charge of a complex is the sum of its letters' charges, that the charge enters through `exp`,
and that the unit of recognition is shared evenly over the alphabet's gauge orbits.
`measure_from_posting_premises` is the derivation with that premise, `KindOnly`, and the atom
normalizations all three in the binders, and it is the statement to read.  §7 then measures how
much `PostedBy` restricts and the answer is almost nothing: every strictly positive weight is posted
by some cost at every complex with a cell (`postedBy_constrains_only_the_empty_complex`).  **That
measurement is unconditional and therefore does not say `PostedBy` is free given the kind clause**,
since the cost it constructs is generally not kind-only.  What it does say is that no
restrictiveness can be attributed to the divisor by itself.

Second, the premise set is a **single point at the weight**, under §3's premise and under §7's
corrected one alike, and the reason is older than either.  Kind-only plus the three normalizations
forces the cost to be identically zero (`kindOnly_and_atoms_force_zeroCost`); aggregate linearity
plus the same three forces the history cost to be identically zero
(`fixedKindTotals_and_atoms_force_zero_historyCost`).  But the general fact is that *any*
equivariant cost posts `mu` exactly when its Boltzmann numerator is identically one
(`equivariant_posts_mu_iff_numerator_one`), which follows from a uniqueness theorem
`Gap2GaugeVolume` proved before this module existed.  So the chain above is rigidity rather than
computation, the premises select which cost rather than producing the answer, and the cost layer
contributes no factor to the measure.  `mu` itself is the orbit count over the gauge volume, so the
divisor is one of its two sources and the cost is neither.

Third, these premises are **jointly stronger** than premise (i), not weaker.  What premise (i)
amounts to at this layer is exactly that the *total* charge is a function of the three counts
(`postedWeight_sizeBlind_iff`), and kind-only is strictly stronger than that
(`costSizeBlind_not_kindOnly`: a cost charging each vertex letter the vertex count is
size-blind and not kind-only).  So the trade is explicit.  Premise (ii) is gone, and premise
(i) is replaced by a statement about single postings, which is a different kind of assumption in a
place where the kind of assumption is the whole question.  Not a *locality* statement, and the word
is avoided from here on: `KindRates` demands the same three reals at every complex and every cap, so
it is a global condition on the charging rule, not constancy within one complex.

## §4-§5, the hard stop: the named premise is incidence-silence

Kind-only is the only clause of the derivation that constrains the weight away from the empty
complex and the three atoms, so the question is what forces it.  Gauge equivariance does not.
`incidenceCost t` charges `t` for an edge letter whose two endpoints
differ and nothing for any other letter.  It is a well-formed letter cost, it is equivariant
under every relabeling (`incidenceCost_equivariant`), because a relabeling carries an edge
with distinct endpoints to an edge with distinct endpoints, and it is not kind-only
(`incidenceCost_not_kindOnly`).  Its posted weight is exactly the proper-edge escape of
`Gap2SizeBlindnessReach` at `lam = exp(-t)` (`postedWeight_incidenceCost`), so it satisfies
every hypothesis of the derivation except premise (i)
(`incidencePosting_satisfiesTheOtherHypotheses`), is not size-blind, and its class mass at the
two-bridge class is `exp(-2t)/|Aut|` against `1/|Aut|`.

So the escape is not an artifact of working with abstract weights.  A charging rule of the shape
this module formalizes, one letter per cell with a cost per posting, produces it.  Whether a
substrate charges this way is not a question any theorem here answers; what is closed is that
nothing in the posting layer as formalized rules the rule out.  §5's headline is
`incidence_silence_suffices_and_equivariance_does_not`, and its name is deliberately not "needs":
kind-only is strictly stronger than premise (i), so what needs it is this route to the measure,
and the necessity §5 proves is only that the natural weakening of it fails.

**The name of the premise is corrected in §7, and the correction matters.**  Letter-level
incidence silence is *not* the boundary.  A cost may read incidence at every letter of a kind and
still produce `mu` exactly, provided what it reads cancels when that block is summed
(`centeredIncidence_is_the_measure`).  What suffices is **aggregate linearity by kind**: the total
charge of each kind is a fixed multiple of that kind's count.  `FixedKindTotals` states it, it is
strictly weaker than kind-only, and together with the three normalizations it derives the measure
(`measure_from_fixedKindTotals`).  Not on its own: the normalizations are load-bearing there, since
they are exactly what kills the three rates, and aggregate linearity by itself gives only premise
(i) at the cost layer (`fixedKindTotals_costSizeBlind`).  "Incidence silence" is the right slogan
for the block sum and the wrong one for the letter.

## §6, what the stronger premise costs, measured

Kind-only is strictly stronger than premise (i) as a condition on weights, and saying so is
not a hedge; it is the price.  The uniform labeled weight `sizeWeight 1` is size-blind and is
not the posted weight of any kind-only cost (`sizeBlind_not_always_posted`), because
`f · gaugeVol` would have to be exponential in the counts and a factorial is not.  What that
excludes is a wrong answer: `sizeWeight 1` is the decoy whose class mass is `gaugeVol/|Aut|`,
and the intended answer is a kind-only posted weight (`postedWeight_zeroCost`).  So the
strengthening removes the decoy and keeps the answer, which is what a strengthening should do.

## Scope, and what this leaves open

This does not prove aggregate linearity, and it does not prove kind-only.  It shows that either
one, conjoined with the three normalizations, derives premise (i) and then the measure, that
equivariance delivers neither, and that the gap sits at whether the *block sum* of a kind's charges
is a fixed multiple of that kind's count.  Whether the substrate forces that, from the definition of
`PostingAlphabet` or from anything else in the ledger layer, is open, and it is the residual worth
attacking.

**It is not the only thing left, and counting the rest correctly took two referees.**  Five
assumptions stand behind `measure_from_posting_premises`.  `PostedBy` packs three: that the charge
of a complex is the sum of its letters' charges, built into `historyCost` before any premise is
stated and which nobody here has attacked; that the charge enters the weight through `exp`, which
is a modeling choice no theorem here motivates; and that one unit of recognition is shared evenly
over the alphabet's gauge orbits, which restricts nothing but the empty complex.  Then the kind
clause, and then `NormalizedAtTheAtoms`, which is fully restrictive rather than cosmetic: it is what
kills the three rates, and without it a nonzero triple of rates gives a posted weight that is not
the Gibbs weight at all.

So the honest ranking is: posting additivity and the Boltzmann form are untouched, gauge sharing is
nearly free on its own, and the kind clause and the normalizations are both restrictive.  An earlier
version of this section said the kind clause was *the only* restrictive premise, which was wrong on
the normalizations and is withdrawn.

This also revises the conjecture `Gap2SizeBlindnessReach` left, which guessed that the missing
premise would have to come from "structure that is not a function of the complex".  Half of
that is wrong: `KindOnly` is a condition on a letter cost, which is a function of the complex.
The half that survives is the other one, that it has to be a cost that assigns the weight
rather than a symmetry that fails to separate it.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2PostingCostDerivation

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach

noncomputable section

variable {B B' : ℕ}

/-! ## §1. The alphabet's gauge group, and the Gibbs weight as its inverse order

The divisor in `gibbsWeight` remains the imported formula `1/(nV! nE! nT!)`; what this section adds
is an identification of it, not a replacement.  The number it is the reciprocal of is the number of
ways to hand out the letters of the posting alphabet within their three blocks, which is the order
of the sort-respecting gauge group of the alphabet.  `Gap2SizeBlindnessReach.RespectsKinds` is the
condition that *names* block-respecting transports among alphabet equivalences; that the
block-respecting equivalences are in bijection with `AlphabetGauge` is the natural next lemma and is
not proved here, so read `RespectsKinds` as a definition and `card_alphabetGauge` as the count. -/

/-- The **sort-respecting gauge group of the posting alphabet**: independent relabelings of
the vertex block, the edge block, and the tetrahedron block.

**This is `Gap2GaugeVolume.SectorGroup` and not a new object.**  Stating it here under a
posting-layer name would be a rename dressed as a discovery, so `alphabetGauge_eq_sectorGroup`
records the identity, and the content behind it belongs to `Gap2GaugeVolume`: `sectorEquiv` proves
this group is in bijection with the (target, witness) pairs out of `K`, which is what makes it the
gauge group of the labeling rather than a product of permutation groups with a convenient order.
Everything §1 adds is the observation that the same group is what the posting alphabet's three
blocks admit. -/
abbrev AlphabetGauge (K : BoundedComplex B) : Type :=
  Equiv.Perm (Fin K.nV) × Equiv.Perm (Fin K.nE) × Equiv.Perm (Fin K.nT)

/-- The posting alphabet's gauge group is the carrier's sector group, definitionally.  Recorded so
no reader takes §1 for an independent derivation of the divisor. -/
theorem alphabetGauge_eq_sectorGroup (K : BoundedComplex B) :
    AlphabetGauge K = Gap2GaugeVolume.SectorGroup K := rfl

theorem card_alphabetGauge (K : BoundedComplex B) :
    Nat.card (AlphabetGauge K)
      = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
  Gap2GaugeVolume.card_sectorGroup K

/-- **The Gibbs weight is one unit of recognition per gauge orbit of the alphabet.**  Its
divisor is the order of `AlphabetGauge`, so the weight is stated entirely in posting-layer
terms. -/
theorem gibbsWeight_eq_inv_card_alphabetGauge (K : BoundedComplex B) :
    gibbsWeight K = 1 / (Nat.card (AlphabetGauge K) : ℝ) := by
  unfold gibbsWeight
  rw [card_alphabetGauge]

/-! ## §2. Letter costs, the history cost, and the posted weight -/

/-- A **letter cost**: one real number per posting-alphabet letter, for each complex at each
size cap.  Nothing more, and in particular nothing about a substrate: this is a function on an index
type, and the ledger reading of it, that each posting costs something, is how it is meant rather
than anything a declaration here establishes. -/
def LetterCost : Type :=
  ∀ (B : ℕ) (K : BoundedComplex B), PostingAlphabet K → ℝ

/-- The **history cost**: the sum of the costs of a complex's letters.  Additivity of the
ledger over postings is the entire content of this definition, and it is the one thing this
module assumes about a cost before any premise is stated. -/
def historyCost (c : LetterCost) (B : ℕ) (K : BoundedComplex B) : ℝ :=
  ∑ a : PostingAlphabet K, c B K a

/-- The **posted weight** of a letter cost: the Boltzmann factor of the history cost, divided
by the gauge volume of the alphabet (`gibbsWeight_eq_inv_card_alphabetGauge`). -/
def postedWeight (c : LetterCost) (B : ℕ) (K : BoundedComplex B) : ℝ :=
  Real.exp (-(historyCost c B K)) * gibbsWeight K

theorem postedWeight_pos (c : LetterCost) (B : ℕ) (K : BoundedComplex B) :
    0 < postedWeight c B K :=
  mul_pos (Real.exp_pos _) (gibbsWeight_positive K)

/-- **Gauge equivariance of a letter cost.**  The cost of a letter is unchanged by transport
along the alphabet equivalence a relabeling induces.  This is the posting-layer form of
"labels are gauge", and §4 measures that it is strictly weaker than kind-only. -/
def Equivariant (c : LetterCost) : Prop :=
  ∀ (B : ℕ) (K K' : BoundedComplex B) (r : Relabel K K') (a : PostingAlphabet K),
    c B K' (postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv a) = c B K a

/-- An equivariant cost has a relabeling-invariant history cost: the alphabet equivalence
re-indexes the sum. -/
theorem historyCost_invariant {c : LetterCost} (hc : Equivariant c) {K K' : BoundedComplex B}
    (r : Relabel K K') : historyCost c B K = historyCost c B K' := by
  unfold historyCost
  exact Fintype.sum_equiv (postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv) _ _
    (fun a => (hc B K K' r a).symm)

theorem postedWeight_invariant {c : LetterCost} (hc : Equivariant c) {K K' : BoundedComplex B}
    (h : Equivalent K K') : postedWeight c B K = postedWeight c B K' := by
  obtain ⟨r⟩ := h
  unfold postedWeight
  rw [historyCost_invariant hc r, gibbsWeight_invariant ⟨r⟩]

/-! ## §3. Kind-only letter costs derive premise (i), and then the measure -/

/-- `c` charges the three **rates** `cV`, `cE`, `cT`: a vertex letter costs `cV` in every
complex at every cap, an edge letter `cE`, a tetrahedron letter `cT`. -/
def KindRates (c : LetterCost) (cV cE cT : ℝ) : Prop :=
  ∀ (B : ℕ) (K : BoundedComplex B),
    (∀ v : Fin K.nV, c B K (Sum.inl v) = cV)
      ∧ (∀ e : Fin K.nE, c B K (Sum.inr (Sum.inl e)) = cE)
      ∧ (∀ τ : Fin K.nT, c B K (Sum.inr (Sum.inr τ)) = cT)

/-- **The premise.**  A letter's cost is a function of its kind and of nothing else, with the same
three reals at every complex and every cap.  What matters structurally is that this is a condition on
a *cost* rather than on what a weight can distinguish, which is what puts it outside the family
`Gap2SizeBlindnessReach`'s dichotomy covers.  Whether a substrate charges this way is a separate
question and no declaration here touches it. -/
def KindOnly (c : LetterCost) : Prop :=
  ∃ cV cE cT : ℝ, KindRates c cV cE cT

/-- **The history cost of a kind-only cost is linear in the three counts.**  This is the whole
mechanism: the alphabet has one letter per cell, so summing a per-kind charge over it counts
cells. -/
theorem historyCost_of_kindRates {c : LetterCost} {cV cE cT : ℝ} (h : KindRates c cV cE cT)
    (B : ℕ) (K : BoundedComplex B) :
    historyCost c B K = cV * (K.nV : ℝ) + cE * (K.nE : ℝ) + cT * (K.nT : ℝ) := by
  classical
  obtain ⟨hV, hE, hT⟩ := h B K
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have e1 : ∑ v : Fin K.nV, c B K (Sum.inl v) = (K.nV : ℝ) * cV := by
    rw [Finset.sum_congr rfl (fun v _ => hV v), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have e2 : ∑ e : Fin K.nE, c B K (Sum.inr (Sum.inl e)) = (K.nE : ℝ) * cE := by
    rw [Finset.sum_congr rfl (fun e _ => hE e), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have e3 : ∑ τ : Fin K.nT, c B K (Sum.inr (Sum.inr τ)) = (K.nT : ℝ) * cT := by
    rw [Finset.sum_congr rfl (fun τ _ => hT τ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [e1, e2, e3]
  ring

/-- A kind-only cost is equivariant.  Recorded so that §4's cost cannot be dismissed for
being equivariant when the intended one is too. -/
theorem kindOnly_equivariant {c : LetterCost} (h : KindOnly c) : Equivariant c := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  intro B K K' r a
  rcases a with x | (y | z)
  · rw [show postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv (Sum.inl x)
        = Sum.inl (r.vEquiv x) from rfl, (hc B K').1, (hc B K).1]
  · rw [show postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv (Sum.inr (Sum.inl y))
        = Sum.inr (Sum.inl (r.eEquiv y)) from rfl, (hc B K').2.1, (hc B K).2.1]
  · rw [show postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv (Sum.inr (Sum.inr z))
        = Sum.inr (Sum.inr (r.tEquiv z)) from rfl, (hc B K').2.2, (hc B K).2.2]

/-- **THEOREM (a kind-only posting cost gives premise (i)).**  The posted weight of a
kind-only cost is size-blind, in exactly the sense `Gap2SizeBlindnessReach.SizeBlind` states
and therefore in exactly the sense premise (i) needs. -/
theorem postedWeight_sizeBlind {c : LetterCost} (h : KindOnly c) :
    SizeBlind (postedWeight c) := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  intro B B' K L hv he ht
  unfold postedWeight gibbsWeight
  rw [historyCost_of_kindRates hc B K, historyCost_of_kindRates hc B' L, hv, he, ht]

/-- **THEOREM (premise (i), in the derivation's own words).**  `Gap2GluingDerivation` states
premise (i) as "the labeled weight is `sizeWeight f` for some size function `f`".  A kind-only
posting cost produces such an `f`. -/
theorem posting_cost_derives_premise_one {c : LetterCost} (h : KindOnly c) :
    ∃ f : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B),
      postedWeight c B K = sizeWeight f K :=
  (sizeBlind_iff_exists_sizeFun (postedWeight c)).mp (postedWeight_sizeBlind h)

/-- **THEOREM (the three normalizations pin all three rates to zero).**  Stated for any cost whose
history cost is linear in the three counts, because §7 needs it at a premise strictly weaker than
kind-only.  The gauge volume is `1` at each of the three atoms, so a unit weight there forces a
unit Boltzmann factor, and a unit Boltzmann factor forces the exponent to vanish.  The three atoms
are `bouquet 0 0`, `bouquet 1 0` and `bouquet 0 1`, at sizes `(1,0,0)`, `(1,1,0)` and
`(1,0,1)`. -/
theorem linearCost_atoms_force_zero {c : LetterCost} {cV cE cT : ℝ}
    (hlin : ∀ (B : ℕ) (K : BoundedComplex B),
      historyCost c B K = cV * (K.nV : ℝ) + cE * (K.nE : ℝ) + cT * (K.nT : ℝ))
    (hn : NormalizedAtTheAtoms (postedWeight c)) : cV = 0 ∧ cE = 0 ∧ cT = 0 := by
  have hone : ∀ (B : ℕ) (K : BoundedComplex B), K.nV = 1 → K.nE + K.nT ≤ 1 →
      Real.exp (-(cV * (K.nV : ℝ) + cE * (K.nE : ℝ) + cT * (K.nT : ℝ))) = 1 := by
    intro B K hv hi
    have h1 := hn B K hv hi
    unfold postedWeight at h1
    rw [hlin B K, gibbsWeight_eq_one_at_atoms K hv hi, mul_one] at h1
    exact h1
  have hV : cV = 0 := by
    have h1 := hone _ (bouquet 0 0) rfl (by norm_num)
    simp only [bouquet_nV, bouquet_nE, bouquet_nT, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, add_zero] at h1
    rw [← Real.exp_zero] at h1
    have := Real.exp_eq_exp.mp h1
    linarith
  have hE : cE = 0 := by
    have h1 := hone _ (bouquet 1 0) rfl (by norm_num)
    simp only [bouquet_nV, bouquet_nE, bouquet_nT, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, add_zero] at h1
    rw [← Real.exp_zero] at h1
    have := Real.exp_eq_exp.mp h1
    linarith
  have hT : cT = 0 := by
    have h1 := hone _ (bouquet 0 1) rfl (by norm_num)
    simp only [bouquet_nV, bouquet_nE, bouquet_nT, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, add_zero] at h1
    rw [← Real.exp_zero] at h1
    have := Real.exp_eq_exp.mp h1
    linarith
  exact ⟨hV, hE, hT⟩

/-- The kind-only case, which is the one §3 uses. -/
theorem kindRates_atoms_force_zero {c : LetterCost} {cV cE cT : ℝ} (hc : KindRates c cV cE cT)
    (hn : NormalizedAtTheAtoms (postedWeight c)) : cV = 0 ∧ cE = 0 ∧ cT = 0 :=
  linearCost_atoms_force_zero (historyCost_of_kindRates hc) hn

/-- **THEOREM (the posted weight is forced to be the Gibbs weight).**  A kind-only cost that
is unit at the three atoms charges nothing at all, so the weight is one unit of recognition
per gauge orbit of the alphabet. -/
theorem posting_cost_derives_gibbs {c : LetterCost} (h : KindOnly c)
    (hn : NormalizedAtTheAtoms (postedWeight c)) (B : ℕ) (K : BoundedComplex B) :
    postedWeight c B K = gibbsWeight K := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  obtain ⟨hV, hE, hT⟩ := kindRates_atoms_force_zero hc hn
  unfold postedWeight
  rw [historyCost_of_kindRates hc B K, hV, hE, hT]
  simp only [zero_mul, add_zero, neg_zero, Real.exp_zero, one_mul]

/-- The class mass of the Gibbs weight is the RS measure.  This is the deflation theorem at
unit tilt; no gluing premise is involved. -/
theorem classMass_gibbsWeight_eq_mu (K : BoundedComplex B) :
    classMass (fun K' : BoundedComplex B => gibbsWeight K')
      (Quotient.mk (relabelSetoid B) K) = mu K := by
  have h : (fun K' : BoundedComplex B => gibbsWeight K') = statWeight loopStat 1 B := by
    funext K'
    unfold statWeight
    rw [one_pow, one_mul]
  rw [h]
  exact classMass_statWeight_at_one loopStat K

/-- **THE DERIVATION.**  If the ledger cost of a history is the sum of its letters' costs, a
letter's cost depends only on its kind, and the three atoms are free, then the class measure
is `mu K = 1/|Aut K|` for every complex at every cap.

Premise (ii) of `Gap2GluingDerivation`, gluing multiplicativity, is not used anywhere in the
chain that proves this, and neither is any restriction on which pairs glue.  The `1/|Aut|`
comes from the deflation theorem, which needs only premise (i), and the three rates are pinned
by the normalizations directly rather than through a recursion.  So this derivation replaces
premise (i) by a posting-layer premise and drops premise (ii) entirely. -/
theorem posting_cost_derives_mu {c : LetterCost} (h : KindOnly c)
    (hn : NormalizedAtTheAtoms (postedWeight c)) (B : ℕ) (K : BoundedComplex B) :
    classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  have hfun : postedWeight c B = fun K' : BoundedComplex B => gibbsWeight K' := by
    funext K'
    exact posting_cost_derives_gibbs h hn B K'
  rw [hfun]
  exact classMass_gibbsWeight_eq_mu K

/-! ### The two premises, made visible in the statement

`postedWeight` bakes the gauge divisor into a definition, and a definition is not a premise a
reader can see.  It is one: the claim that a labeled complex carries one unit of recognition
divided by the number of ways to hand out its letters.  `PostedBy` says it out loud, and
`measure_from_posting_premises` is the derivation with both premises in the binders. -/

/-- **`w` is posted by the letter cost `c`.**  Two assumptions in one predicate, and they are
the two the derivation runs on: the charge of a complex is the *sum* of its letters' charges
(ledger additivity over postings, which is `historyCost`), and the unit of recognition is
shared evenly over the alphabet's gauge orbits (the divisor).  Neither mentions what the
weight can or cannot distinguish. -/
def PostedBy (w : ∀ B : ℕ, BoundedComplex B → ℝ) (c : LetterCost) : Prop :=
  ∀ (B : ℕ) (K : BoundedComplex B),
    w B K = Real.exp (-(historyCost c B K)) / (Nat.card (AlphabetGauge K) : ℝ)

theorem postedBy_postedWeight (c : LetterCost) : PostedBy (postedWeight c) c := by
  intro B K
  unfold postedWeight
  rw [gibbsWeight_eq_inv_card_alphabetGauge]
  ring

theorem postedBy_eq_postedWeight {w : ∀ B : ℕ, BoundedComplex B → ℝ} {c : LetterCost}
    (h : PostedBy w c) (B : ℕ) (K : BoundedComplex B) : w B K = postedWeight c B K := by
  rw [h B K]
  unfold postedWeight
  rw [gibbsWeight_eq_inv_card_alphabetGauge]
  ring

/-- **THE DERIVATION, with every premise in the binders.**  A weight posted by a kind-only
letter cost and unit at the three atoms is the Gibbs weight, and its class measure is
`mu K = 1/|Aut K|`, at every complex and every cap.

Three binders, packing five assumptions.  `PostedBy` is ledger additivity over postings, plus the
charge entering through `exp`, plus even sharing of the unit over the alphabet's gauge orbits.
`KindOnly` is that a letter's charge depends on its kind alone, with the same rates everywhere.
`NormalizedAtTheAtoms` is the three unit normalizations the derivation module also assumes.
**Premise (ii), gluing multiplicativity, appears nowhere.**

The honest comparison with `Gap2GluingDerivation`, since these premises are not weaker: the first
two jointly imply premise (i) and are not implied by it (`sizeBlind_not_always_posted`).  What the
strengthening buys is that premise (ii) is gone and that the surviving premises constrain a *cost*
rather than a weight's resolving power, which is the family `Gap2SizeBlindnessReach`'s dichotomy
covers.  Say that carefully: the dichotomy does not show resolving-power premises *cannot* supply
premise (i), since a coarse one does supply it; what it shows is that none of them supplies it while
being strictly weaker than it. -/
theorem measure_from_posting_premises {w : ∀ B : ℕ, BoundedComplex B → ℝ} {c : LetterCost}
    (hpost : PostedBy w c) (hkind : KindOnly c) (hn : NormalizedAtTheAtoms w) (B : ℕ)
    (K : BoundedComplex B) :
    w B K = gibbsWeight K
      ∧ classMass (w B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  have hfun : w = postedWeight c := by
    funext B' K'
    exact postedBy_eq_postedWeight hpost B' K'
  subst hfun
  exact ⟨posting_cost_derives_gibbs hkind hn B K, posting_cost_derives_mu hkind hn B K⟩

/-! ### What premise (i) is, exactly, at the posting layer

Premise (i) is not `KindOnly`.  It is the weaker condition that the *total* charge is a
function of the three counts, and the equivalence is exact.  Saying so is what keeps the
derivation from claiming more than it does: `KindOnly` fixes each single posting's charge, globally,
and premise (i) constrains only the total. -/

/-- The total charge is a function of the three counts. -/
def CostSizeBlind (c : LetterCost) : Prop :=
  ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    K.nV = L.nV → K.nE = L.nE → K.nT = L.nT → historyCost c B K = historyCost c B' L

/-- **THEOREM (premise (i) at the posting layer, exactly).**  A posted weight is size-blind
precisely when its total charge is a function of the three counts.  So the posting presentation
does not weaken premise (i) by itself; it relocates it to the cost. -/
theorem postedWeight_sizeBlind_iff (c : LetterCost) :
    SizeBlind (postedWeight c) ↔ CostSizeBlind c := by
  constructor
  · intro h B B' K L hv he ht
    have hEq := h B B' K L hv he ht
    unfold postedWeight at hEq
    have hgib : gibbsWeight K = gibbsWeight L := by
      unfold gibbsWeight
      rw [hv, he, ht]
    have hpos : (0 : ℝ) < gibbsWeight L := gibbsWeight_positive L
    rw [hgib] at hEq
    have hexp : Real.exp (-(historyCost c B K)) = Real.exp (-(historyCost c B' L)) :=
      mul_right_cancel₀ hpos.ne' hEq
    have := Real.exp_eq_exp.mp hexp
    linarith
  · intro h B B' K L hv he ht
    unfold postedWeight
    rw [h B B' K L hv he ht]
    unfold gibbsWeight
    rw [hv, he, ht]

theorem kindOnly_costSizeBlind {c : LetterCost} (h : KindOnly c) : CostSizeBlind c := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  intro B B' K L hv he ht
  rw [historyCost_of_kindRates hc B K, historyCost_of_kindRates hc B' L, hv, he, ht]

/-- A letter cost that charges each vertex letter the vertex count.  Its total charge is
`nV²`, a function of the counts, so it satisfies premise (i); and it is not kind-only, since
the rate varies with the complex. -/
def squareCost : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => (K.nV : ℝ)
  | Sum.inr _ => 0

theorem historyCost_squareCost (B : ℕ) (K : BoundedComplex B) :
    historyCost squareCost B K = (K.nV : ℝ) * (K.nV : ℝ) := by
  classical
  unfold historyCost squareCost
  rw [Fintype.sum_sum_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **THEOREM (kind-only is strictly stronger than premise (i) at the cost layer too).**  A
cost whose per-letter rate reads the vertex count is size-blind at the level of totals and is
not kind-only.  So the derivation's premise is genuinely a locality assumption about single
postings, not premise (i) in disguise, and the module says so rather than letting a reader
assume the two coincide. -/
theorem costSizeBlind_not_kindOnly :
    CostSizeBlind squareCost ∧ ¬ KindOnly squareCost := by
  refine ⟨?_, ?_⟩
  · intro B B' K L hv _ _
    rw [historyCost_squareCost, historyCost_squareCost, hv]
  · rintro ⟨cV, cE, cT, hc⟩
    have h1 : (0 : ℕ) < 1 := by norm_num
    have h2 : (0 : ℕ) < 2 := by norm_num
    have hd1 : squareCost 1 (dust 1) (Sum.inl ⟨0, h1⟩) = cV := (hc 1 (dust 1)).1 ⟨0, h1⟩
    have hd2 : squareCost 2 (dust 2) (Sum.inl ⟨0, h2⟩) = cV := (hc 2 (dust 2)).1 ⟨0, h2⟩
    have e1 : squareCost 1 (dust 1) (Sum.inl ⟨0, h1⟩) = ((dust 1).nV : ℝ) := rfl
    have e2 : squareCost 2 (dust 2) (Sum.inl ⟨0, h2⟩) = ((dust 2).nV : ℝ) := rfl
    rw [e1, dust_nV] at hd1
    rw [e2, dust_nV] at hd2
    rw [← hd1] at hd2
    norm_num at hd2

/-! ### What premise (ii) was doing, and what replaced it

"Gluing multiplicativity is gone" invites the reading that it was doing nothing.  It was.  In
`Gap2GluingDerivation` premise (ii) drives a recursion that propagates the three unit
normalizations from the atoms out to every size triple.  Premise (i) alone does not do that: the
atoms are three points and a function of the counts is not determined by three of its values.

What replaces it here is not nothing, it is **linearity**.  A per-letter charge summed over an
alphabet with one letter per cell is linear in the counts, and a linear function that vanishes
at those three points vanishes everywhere.  So the trade is precise: premise (ii)'s propagation
job is done by the linearity that per-letter charging supplies for free, and the theorem below
measures that the job is real, by exhibiting a cost that satisfies premise (i) and the three
normalizations and still gets the weight wrong. -/

/-- A cost charging each vertex letter one unit per *other* vertex.  Its total is the number of
ordered pairs of distinct vertices, `nV(nV-1)`, which vanishes on every one-vertex complex. -/
def pairCost : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => (K.nV : ℝ) - 1
  | Sum.inr _ => 0

theorem historyCost_pairCost (B : ℕ) (K : BoundedComplex B) :
    historyCost pairCost B K = (K.nV : ℝ) * ((K.nV : ℝ) - 1) := by
  classical
  unfold historyCost pairCost
  rw [Fintype.sum_sum_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **THEOREM (premise (i) plus the three normalizations do not give the Gibbs weight).**  The
pair cost satisfies premise (i), since its total is a function of the vertex count, and it is
unit at all three atoms, since its total vanishes whenever `nV = 1`.  Its weight at two isolated
vertices is `exp(-2)` times the Gibbs weight, so it is not the Gibbs weight, and the derivation's
conclusion fails at the first link of the chain.

This is what premise (ii) was for in `Gap2GluingDerivation`, and what the linearity of per-letter
charging replaces here.  It also shows the `KindOnly` premise is not decoration on top of premise
(i): drop linearity, keep everything else, and the derivation stops. -/
theorem costSizeBlind_and_atoms_do_not_give_gibbs :
    CostSizeBlind pairCost
      ∧ NormalizedAtTheAtoms (postedWeight pairCost)
      ∧ ¬ KindOnly pairCost
      ∧ postedWeight pairCost 2 (dust 2) ≠ gibbsWeight (dust 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B B' K L hv _ _
    rw [historyCost_pairCost, historyCost_pairCost, hv]
  · intro B K hv hi
    unfold postedWeight
    rw [historyCost_pairCost, hv, gibbsWeight_eq_one_at_atoms K hv hi]
    norm_num
  · rintro ⟨cV, cE, cT, hc⟩
    have h1 : (0 : ℕ) < 1 := by norm_num
    have h2 : (0 : ℕ) < 2 := by norm_num
    have hd1 : pairCost 1 (dust 1) (Sum.inl ⟨0, h1⟩) = cV := (hc 1 (dust 1)).1 ⟨0, h1⟩
    have hd2 : pairCost 2 (dust 2) (Sum.inl ⟨0, h2⟩) = cV := (hc 2 (dust 2)).1 ⟨0, h2⟩
    have e1 : pairCost 1 (dust 1) (Sum.inl ⟨0, h1⟩) = ((dust 1).nV : ℝ) - 1 := rfl
    have e2 : pairCost 2 (dust 2) (Sum.inl ⟨0, h2⟩) = ((dust 2).nV : ℝ) - 1 := rfl
    rw [e1, dust_nV] at hd1
    rw [e2, dust_nV] at hd2
    rw [← hd1] at hd2
    norm_num at hd2
  · unfold postedWeight
    rw [historyCost_pairCost, dust_nV]
    intro hEq
    have hpos : (0 : ℝ) < gibbsWeight (dust 2) := gibbsWeight_positive (dust 2)
    have hone : Real.exp (-((2 : ℝ) * ((2 : ℝ) - 1))) = 1 := by
      have : Real.exp (-((2 : ℝ) * ((2 : ℝ) - 1))) * gibbsWeight (dust 2)
          = 1 * gibbsWeight (dust 2) := by rw [one_mul]; exact_mod_cast hEq
      exact mul_right_cancel₀ hpos.ne' this
    rw [← Real.exp_zero] at hone
    have := Real.exp_eq_exp.mp hone
    norm_num at this

/-! ### The premise set is satisfied, at the intended point -/

/-- The letter cost that charges nothing. -/
def zeroCost : LetterCost := fun _ _ _ => 0

theorem zeroCost_kindRates : KindRates zeroCost 0 0 0 :=
  fun _ _ => ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem zeroCost_kindOnly : KindOnly zeroCost :=
  ⟨0, 0, 0, zeroCost_kindRates⟩

theorem postedWeight_zeroCost (B : ℕ) (K : BoundedComplex B) :
    postedWeight zeroCost B K = gibbsWeight K := by
  unfold postedWeight historyCost zeroCost
  simp

theorem zeroCost_normalizedAtTheAtoms : NormalizedAtTheAtoms (postedWeight zeroCost) := by
  intro B K hv hi
  rw [postedWeight_zeroCost]
  exact gibbsWeight_eq_one_at_atoms K hv hi

/-- **Non-vacuity.**  The premises of the derivation are satisfiable, and satisfied exactly at
the intended answer: a free ledger posts the Gibbs weight and returns `mu`. -/
theorem posting_premises_satisfiable :
    KindOnly zeroCost ∧ NormalizedAtTheAtoms (postedWeight zeroCost)
      ∧ (∀ (B : ℕ) (K : BoundedComplex B), postedWeight zeroCost B K = gibbsWeight K)
      ∧ (∀ (B : ℕ) (K : BoundedComplex B),
          classMass (postedWeight zeroCost B) (Quotient.mk (relabelSetoid B) K) = mu K) :=
  ⟨zeroCost_kindOnly, zeroCost_normalizedAtTheAtoms, postedWeight_zeroCost,
    fun B K => posting_cost_derives_mu zeroCost_kindOnly zeroCost_normalizedAtTheAtoms B K⟩

/-! ## §4. The cost that reads incidence: equivariant, normalized, and not kind-only -/

/-- The **incidence-aware letter cost**: an edge letter whose two endpoints differ costs `t`,
every other letter is free.  A perfectly well-formed charging rule at the posting layer. -/
def incidenceCost (t : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl e) => if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then t else 0
  | Sum.inr (Sum.inr _) => 0

@[simp] theorem incidenceCost_inl (t : ℝ) (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    incidenceCost t B K (Sum.inl v) = 0 := rfl

@[simp] theorem incidenceCost_edge (t : ℝ) (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE) :
    incidenceCost t B K (Sum.inr (Sum.inl e))
      = if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then t else 0 := rfl

@[simp] theorem incidenceCost_tet (t : ℝ) (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT) :
    incidenceCost t B K (Sum.inr (Sum.inr τ)) = 0 := rfl

/-- **The history cost of the incidence cost is `t` times the proper-edge count.**  So the
statistic `Gap2SizeBlindnessReach` used as an escape is exactly what a posting ledger charges
under this rule. -/
theorem historyCost_incidenceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (incidenceCost t) B K = t * (properEdgeCount K : ℝ) := by
  classical
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [incidenceCost_inl, incidenceCost_edge, incidenceCost_tet,
    Finset.sum_const_zero, zero_add, add_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold properEdgeCount
  ring

/-- **THEOREM (the incidence cost reproduces the escape).**  Its posted weight is the
proper-edge escape weight of `Gap2SizeBlindnessReach` at tilt `exp(-t)`.  Since the two functions are
equal, everything the reach bound proved about that weight holds of this posted weight.  What that
licenses is that the escape is realizable *inside this formalism*, as the posted weight of a
well-formed letter cost; it says nothing about what a substrate posts. -/
theorem postedWeight_incidenceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    postedWeight (incidenceCost t) B K = statWeight properStat (Real.exp (-t)) B K := by
  have hpow : ∀ n : ℕ, Real.exp (-(t * (n : ℝ))) = Real.exp (-t) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hstep : -(t * ((k + 1 : ℕ) : ℝ)) = -(t * (k : ℝ)) + -t := by push_cast; ring
      rw [hstep, Real.exp_add, ih, pow_succ]
  unfold postedWeight statWeight
  rw [historyCost_incidenceCost, hpow]
  rfl

theorem postedWeight_incidenceCost_eq (t : ℝ) :
    postedWeight (incidenceCost t) = statWeight properStat (Real.exp (-t)) := by
  funext B K
  exact postedWeight_incidenceCost t B K

theorem exp_neg_pos (t : ℝ) : 0 < Real.exp (-t) := Real.exp_pos _

theorem exp_neg_ne_one {t : ℝ} (ht : t ≠ 0) : Real.exp (-t) ≠ 1 := by
  intro h
  rw [← Real.exp_zero] at h
  have := Real.exp_eq_exp.mp h
  exact ht (by linarith)

/-- **THEOREM (the incidence cost is gauge-equivariant).**  A relabeling carries an edge with
distinct endpoints to an edge with distinct endpoints, so the charge transports.  This is the
theorem that closes the obvious escape from §5: one cannot rule the incidence cost out for
breaking gauge invariance, because it does not. -/
theorem incidenceCost_equivariant (t : ℝ) : Equivariant (incidenceCost t) := by
  intro B K K' r a
  rcases a with x | (y | z)
  · rfl
  · rw [show postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv (Sum.inr (Sum.inl y))
        = Sum.inr (Sum.inl (r.eEquiv y)) from rfl, incidenceCost_edge, incidenceCost_edge]
    exact if_congr (not_congr (loop_iff_of_relabel r y).symm) rfl rfl
  · rfl

/-- Every edge of `twoBridges` has distinct endpoints. -/
theorem twoBridges_edges_proper : ∀ e : Fin twoBridges.nE,
    (twoBridges.edgeVerts e).1 ≠ (twoBridges.edgeVerts e).2 := by decide

/-- No edge of `twoLoops` has distinct endpoints. -/
theorem twoLoops_edges_loop : ∀ e : Fin twoLoops.nE,
    ¬ ((twoLoops.edgeVerts e).1 ≠ (twoLoops.edgeVerts e).2) := by decide

/-- **THEOREM (the incidence cost is not kind-only).**  Two complexes at the same cap with the
same number of edges charge the same edge letter differently: `twoBridges` charges `t` and
`twoLoops` charges nothing.  So no triple of rates can reproduce it. -/
theorem incidenceCost_not_kindOnly {t : ℝ} (ht : t ≠ 0) : ¬ KindOnly (incidenceCost t) := by
  rintro ⟨cV, cE, cT, hc⟩
  have h2 : (0 : ℕ) < 2 := by norm_num
  have hb : incidenceCost t 2 twoBridges (Sum.inr (Sum.inl ⟨0, h2⟩)) = cE :=
    (hc 2 twoBridges).2.1 ⟨0, h2⟩
  have hl : incidenceCost t 2 twoLoops (Sum.inr (Sum.inl ⟨0, h2⟩)) = cE :=
    (hc 2 twoLoops).2.1 ⟨0, h2⟩
  rw [incidenceCost_edge, if_pos (twoBridges_edges_proper ⟨0, h2⟩)] at hb
  rw [incidenceCost_edge, if_neg (twoLoops_edges_loop ⟨0, h2⟩)] at hl
  exact ht (hb.trans hl.symm)

/-- The posted weight of the incidence cost fails premise (i). -/
theorem incidencePosting_not_sizeBlind {t : ℝ} (ht : t ≠ 0) :
    ¬ SizeBlind (postedWeight (incidenceCost t)) := by
  rw [postedWeight_incidenceCost_eq]
  exact properEscape_not_sizeBlind (exp_neg_pos t) (exp_neg_ne_one ht)

/-- **THEOREM.**  The posted weight of the incidence cost satisfies every hypothesis the
derivation places on the weight other than premise (i): relabeling invariance, strict
positivity, unit on the empty complex, unit at all three atoms, and gluing multiplicativity at
every pair whose automorphism counts multiply. -/
theorem incidencePosting_satisfiesTheOtherHypotheses (t : ℝ) :
    SatisfiesTheOtherHypotheses (postedWeight (incidenceCost t)) := by
  rw [postedWeight_incidenceCost_eq]
  exact properEscape_satisfiesTheOtherHypotheses (exp_neg_pos t)

/-- **THEOREM.**  The class mass of the incidence-posted weight is not the RS measure. -/
theorem incidencePosting_classMass_ne_mu {t : ℝ} (ht : t ≠ 0) :
    classMass (postedWeight (incidenceCost t) 2) (Quotient.mk (relabelSetoid 2) twoBridges)
      ≠ mu twoBridges := by
  rw [postedWeight_incidenceCost_eq]
  exact properEscape_classMass_ne_mu (exp_neg_pos t) (exp_neg_ne_one ht)

/-! ## §5. The named premise -/

/-- **THE NAMED PREMISE, AS A SANDWICH.**  Three conjunct groups: what suffices, what does not
suffice from below, and what does not suffice from the side.

**Sufficient.**  A ledger cost additive over postings that charges by kind alone, with free
atoms, forces the class measure to be `mu` at every complex and every cap, with no gluing
premise anywhere in the argument.  That is incidence silence doing the whole job: **a posting's
cost is a function of its kind and not of the incidence its letter participates in.**

**Not sufficient from below.**  Weakening kind-only to premise (i) itself, which at this layer is
exactly `CostSizeBlind` (`postedWeight_sizeBlind_iff`), breaks the derivation: `pairCost` is
size-blind at the level of totals, unit at all three atoms, and its weight is not the Gibbs
weight.  So the derivation needs strictly more than premise (i) at the cost layer, which is the
one direction of necessity this module proves.

**Not sufficient from the side.**  Gauge equivariance does not supply it.  For any nonzero charge
`t`, the cost that charges an edge letter with distinct endpoints is equivariant under every
relabeling, is unit at the three atoms, satisfies every remaining hypothesis of the derivation,
is not kind-only, and produces a weight that is not size-blind and whose class mass is not `mu`.

**What is left open, and why the name is not "needs".**  Kind-only is strictly stronger than
premise (i) (`costSizeBlind_not_kindOnly`), so it would be false to say premise (i) *needs*
incidence silence; what needs it is this route to the *measure*, and even there the necessity
proved is only that the natural weakening fails.  Incidence silence is not an indistinguishability
premise, so `Gap2SizeBlindnessReach`'s dichotomy does not apply to it.

**Superseded on the sufficiency side, and by a theorem in this file.**  The open question in the
previous paragraph, whether something strictly between `CostSizeBlind` and `KindOnly` suffices, is
answered yes in §7: `FixedKindTotals` is strictly between them and derives the measure
(`measure_from_fixedKindTotals`, `fixedKindTotals_not_kindOnly`).  So the first conjunct here is
true but not sharp, and the sufficient premise to cite is the aggregate one.  What survives
unchanged is the third group, that equivariance supplies neither. -/
theorem incidence_silence_suffices_and_equivariance_does_not {t : ℝ} (ht : t ≠ 0) :
    (∀ c : LetterCost, KindOnly c → NormalizedAtTheAtoms (postedWeight c) →
        ∀ (B : ℕ) (K : BoundedComplex B),
          classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ∧ (CostSizeBlind pairCost ∧ NormalizedAtTheAtoms (postedWeight pairCost)
          ∧ postedWeight pairCost 2 (dust 2) ≠ gibbsWeight (dust 2))
      ∧ Equivariant (incidenceCost t)
      ∧ NormalizedAtTheAtoms (postedWeight (incidenceCost t))
      ∧ SatisfiesTheOtherHypotheses (postedWeight (incidenceCost t))
      ∧ ¬ KindOnly (incidenceCost t)
      ∧ ¬ SizeBlind (postedWeight (incidenceCost t))
      ∧ classMass (postedWeight (incidenceCost t) 2)
          (Quotient.mk (relabelSetoid 2) twoBridges) ≠ mu twoBridges :=
  ⟨fun _ h hn B K => posting_cost_derives_mu h hn B K,
    ⟨costSizeBlind_and_atoms_do_not_give_gibbs.1,
      costSizeBlind_and_atoms_do_not_give_gibbs.2.1,
      costSizeBlind_and_atoms_do_not_give_gibbs.2.2.2⟩,
    incidenceCost_equivariant t,
    (incidencePosting_satisfiesTheOtherHypotheses t).2.2.2.1,
    incidencePosting_satisfiesTheOtherHypotheses t,
    incidenceCost_not_kindOnly ht,
    incidencePosting_not_sizeBlind ht,
    incidencePosting_classMass_ne_mu ht⟩

/-- **THEOREM (equivariance does not separate the two costs).**  Both the intended free ledger
and the incidence-aware ledger are gauge-equivariant, and only the first is kind-only.  So the
gap between the premise the derivation needs and the gauge principle it might have hoped to
get it from is real, not an artifact of how equivariance was stated. -/
theorem equivariance_does_not_give_kindOnly {t : ℝ} (ht : t ≠ 0) :
    Equivariant zeroCost ∧ Equivariant (incidenceCost t)
      ∧ KindOnly zeroCost ∧ ¬ KindOnly (incidenceCost t) :=
  ⟨kindOnly_equivariant zeroCost_kindOnly, incidenceCost_equivariant t,
    zeroCost_kindOnly, incidenceCost_not_kindOnly ht⟩

/-! ## §6. What the stronger premise costs, measured

Kind-only implies premise (i) and is not implied by it.  The honest way to record that is to
name a size-blind weight the posting layer cannot produce, and then to say which one it is. -/

/-- **THEOREM (kind-only is strictly stronger than premise (i)).**  The uniform labeled weight,
which is size-blind, is the posted weight of no kind-only cost.  The second conjunct is why that
is a feature: the weight so excluded is not the Gibbs weight, `1` against `1/2` at two isolated
vertices, so the strengthening removes a wrong answer, and the intended one is still posted
(`postedWeight_zeroCost`).

The mechanism of the proof is worth stating, since it is the reason no repair rescues the
uniform weight: a posted weight is `exp(-linear in the counts) / gaugeVol`, so setting it equal
to a constant would make `gaugeVol` exponential in the counts, and a factorial is not.  Two
complexes suffice to see it, one vertex and two. -/
theorem sizeBlind_not_always_posted :
    (¬ ∃ c : LetterCost, KindOnly c
        ∧ ∀ (B : ℕ) (K : BoundedComplex B),
            sizeWeight (fun _ _ _ => (1 : ℝ)) K = postedWeight c B K)
      ∧ sizeWeight (fun _ _ _ => (1 : ℝ)) (dust 2) ≠ gibbsWeight (dust 2) := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    unfold sizeWeight gibbsWeight
    norm_num [Nat.factorial]
  rintro ⟨c, ⟨cV, cE, cT, hc⟩, heq⟩
  have hg1 : gibbsWeight (dust 1) = 1 := by
    unfold gibbsWeight
    norm_num [Nat.factorial]
  have hg2 : gibbsWeight (dust 2) = 1 / 2 := by
    unfold gibbsWeight
    norm_num [Nat.factorial]
  have h1 := heq 1 (dust 1)
  have h2 := heq 2 (dust 2)
  unfold sizeWeight postedWeight at h1 h2
  rw [historyCost_of_kindRates hc 1 (dust 1), hg1, mul_one] at h1
  rw [historyCost_of_kindRates hc 2 (dust 2), hg2] at h2
  simp only [dust_nV, dust_nE, dust_nT, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat,
    mul_one, mul_zero, add_zero] at h1 h2
  have hcv : cV = 0 := by
    rw [← Real.exp_zero] at h1
    have := Real.exp_eq_exp.mp h1.symm
    linarith
  rw [hcv] at h2
  norm_num at h2

/-! ## §7. Where the content actually sits, measured three ways

A cross-family referee read §1-§6 on 2026-07-29 and returned three findings that survive checking.
Each is a theorem below, because each one narrows a claim §1-§6 made.

**One: the premise set is a single point.**  Kind-only plus the three normalizations force the
letter cost to be identically zero (`kindOnly_and_atoms_force_zeroCost`), so the collapse to
`gibbsWeight` happens because no nonzero kind-only cost survives normalization, not because a cost
was computed.  Legitimate as rigidity, and worth knowing exactly: three normalizations pin three
global rates, and after that the cost apparatus has no content left.

**Two: `PostedBy` restricts almost nothing.**  Every strictly positive weight is posted by some
letter cost at every complex carrying at least one cell
(`postedBy_constrains_only_the_empty_complex`), by spreading `-log (w · gaugeVol)` evenly over the
letters.  So §3's framing, that naming the gauge divisor as a premise rather than hiding it in a
definition keeps the accounting honest, understated the situation: the divisor is not a restrictive
premise on its own, it is a change of variables.  The one place `PostedBy` bites is the empty complex,
where it forces the weight to be one.

Two limits on that, both found later and both real.  The theorem quantifies over unrestricted letter
costs, and the cost it constructs is generally not kind-only, so it does **not** say `PostedBy` is
free given the kind clause; it says no restrictiveness is attributable to the divisor by itself.  And
the restrictive premises are the kind clause *and* `NormalizedAtTheAtoms`: drop the normalizations
and a nonzero rate triple gives a posted weight that is not the Gibbs weight, so an earlier sentence
here calling the kind clause the only restrictive one was wrong and is withdrawn.

**Three, and this changes the headline: per-letter incidence silence is not the boundary.**  A
letter cost may read incidence at every letter of a kind and still produce the measure exactly,
provided what it reads cancels in that block's sum.  `centeredIncidenceCost t` charges a proper edge
letter
`t · (nE - properEdgeCount)` and a loop letter `-t · properEdgeCount`.  It is equivariant under
every relabeling, it is not kind-only, it reads incidence, and its total charge is zero at every
complex, so its posted weight is exactly `gibbsWeight` and its class measure is exactly `mu`
(`centeredIncidence_is_the_measure`).

What suffices is aggregate linearity by kind: the total charge of each kind is a fixed multiple of
that kind's count.  `FixedKindTotals` states it.  It is strictly weaker than kind-only
(`fixedKindTotals_not_kindOnly`, witnessed by the centered cost), strictly stronger than premise (i)
at the cost layer (`pairCost`, from §3b), and with the three normalizations it derives the measure
(`measure_from_fixedKindTotals`; the normalizations are load-bearing there, since aggregate
linearity alone gives only `CostSizeBlind`).  That is the corrected named premise, and "incidence
silence" is the right slogan only for the aggregate, never for the letter.

**Four, and this one is ours rather than the referee's.**  Finding one applies to the corrected
premise as well, one level up.  Aggregate linearity plus the three normalizations forces the whole
*history cost* to zero, not just three rates
(`fixedKindTotals_and_atoms_force_zero_historyCost`), so the Boltzmann numerator is identically
one and the posted weight is exactly the reciprocal gauge volume
(`the_measure_is_the_gauge_divisor`).  The room the aggregate premise has over kind-only is
therefore real at the letters and invisible at the weight: `centeredIncidenceCost` and `zeroCost`
are different costs with the same weight.

**Five, and it subsumes four.**  The referee's next read found that the collapse in four is not
caused by any premise this module names.  `Gap2GaugeVolume.invariant_weight_gives_measure_iff` says
the Gibbs weight is the unique *relabeling-invariant* labeled weight whose class mass is `mu`, and
an equivariant cost has an invariant posted weight, so an equivariant cost posts `mu` exactly when
its numerator is identically one (`equivariant_posts_mu_iff_numerator_one`), with no kind clause and
no normalizations in the argument.  That theorem predates this module.  The honest reading is
therefore that the premises of §3 and §7 select *which* cost and cannot contribute a factor to the
answer, and that no premise on an equivariant cost ever could.

**And one thing four got wrong, corrected here rather than left standing.**  "Every factor of `mu`
comes from the divisor" is false.  `classMass` sums the weight over the class, so `mu` is the orbit
count over the gauge volume by orbit-stabilizer, and the orbit count is a second independent
contributor.  What is true is that the *cost* contributes none. -/

/-- **THEOREM (the derivation's premise set is a single point).**  A kind-only cost that is unit at
the three atoms is the zero cost, letter by letter.  So `posting_cost_derives_gibbs` is a rigidity
statement: nothing about the cost was computed, because the premises admit exactly one cost. -/
theorem kindOnly_and_atoms_force_zeroCost {c : LetterCost} (h : KindOnly c)
    (hn : NormalizedAtTheAtoms (postedWeight c)) (B : ℕ) (K : BoundedComplex B)
    (a : PostingAlphabet K) : c B K a = 0 := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  obtain ⟨hV, hE, hT⟩ := kindRates_atoms_force_zero hc hn
  obtain ⟨hv, he, ht⟩ := hc B K
  rcases a with x | (y | z)
  · rw [hv x, hV]
  · rw [he y, hE]
  · rw [ht z, hT]

/-- The number of letters is the total cell count. -/
theorem card_postingAlphabet (K : BoundedComplex B) :
    Fintype.card (PostingAlphabet K) = K.nV + K.nE + K.nT := by
  simp [PostingAlphabet, add_assoc]

theorem card_alphabetGauge_pos (K : BoundedComplex B) :
    (0 : ℝ) < (Nat.card (AlphabetGauge K) : ℝ) := by
  rw [card_alphabetGauge]
  have h : 0 < Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
    Nat.mul_pos (Nat.factorial_pos _)
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  exact_mod_cast h

/-- **THEOREM (`PostedBy` is a change of variables, not a restriction).**  Every strictly positive
weight is posted by some letter cost, at every complex with at least one cell: spread
`-log (w · gaugeVol)` evenly over the letters and the Boltzmann factor reproduces `w · gaugeVol` by
construction.

So the honest reading of §3 is that the gauge divisor supplies the symmetry factor outright, and the
cost layer contributes only the numerator.  The single place the premise bites is the empty complex,
which has no letters, where the history cost is `0` and the gauge volume is `1`, so `PostedBy`
forces the weight to be one there. -/
theorem postedBy_constrains_only_the_empty_complex
    (w : ∀ B : ℕ, BoundedComplex B → ℝ) (hw : ∀ (B : ℕ) (K : BoundedComplex B), 0 < w B K) :
    ∃ c : LetterCost, ∀ (B : ℕ) (K : BoundedComplex B), 0 < K.nV + K.nE + K.nT →
      w B K = Real.exp (-(historyCost c B K)) / (Nat.card (AlphabetGauge K) : ℝ) := by
  classical
  refine ⟨fun B K _ => -(Real.log (w B K * (Nat.card (AlphabetGauge K) : ℝ)))
      / ((K.nV + K.nE + K.nT : ℕ) : ℝ), ?_⟩
  intro B K hN
  have hG := card_alphabetGauge_pos K
  have hwG : (0 : ℝ) < w B K * (Nat.card (AlphabetGauge K) : ℝ) := mul_pos (hw B K) hG
  have hN' : ((K.nV + K.nE + K.nT : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((K.nV + K.nE + K.nT : ℕ) : ℝ) := by exact_mod_cast hN
    exact this.ne'
  have hH : historyCost (fun B K _ =>
      -(Real.log (w B K * (Nat.card (AlphabetGauge K) : ℝ)))
        / ((K.nV + K.nE + K.nT : ℕ) : ℝ)) B K
      = -(Real.log (w B K * (Nat.card (AlphabetGauge K) : ℝ))) := by
    unfold historyCost
    rw [Finset.sum_const, Finset.card_univ, card_postingAlphabet, nsmul_eq_mul]
    field_simp
  rw [hH, neg_neg, Real.exp_log hwG]
  field_simp

/-! ### The corrected premise: aggregate linearity by kind -/

/-- `c` has **kind totals** `cV`, `cE`, `cT`: at every complex, the total charge over the vertex
letters is `cV · nV`, over the edge letters `cE · nE`, and over the tetrahedron letters `cT · nT`.
Individual letters are unconstrained, so a letter may read whatever it likes provided the block
sum comes out right. -/
def KindTotalRates (c : LetterCost) (cV cE cT : ℝ) : Prop :=
  ∀ (B : ℕ) (K : BoundedComplex B),
    (∑ v : Fin K.nV, c B K (Sum.inl v)) = cV * (K.nV : ℝ)
      ∧ (∑ e : Fin K.nE, c B K (Sum.inr (Sum.inl e))) = cE * (K.nE : ℝ)
      ∧ (∑ τ : Fin K.nT, c B K (Sum.inr (Sum.inr τ))) = cT * (K.nT : ℝ)

/-- **The corrected premise.**  Aggregate linearity by kind. -/
def FixedKindTotals (c : LetterCost) : Prop := ∃ cV cE cT : ℝ, KindTotalRates c cV cE cT

theorem historyCost_of_kindTotalRates {c : LetterCost} {cV cE cT : ℝ}
    (h : KindTotalRates c cV cE cT) (B : ℕ) (K : BoundedComplex B) :
    historyCost c B K = cV * (K.nV : ℝ) + cE * (K.nE : ℝ) + cT * (K.nT : ℝ) := by
  classical
  obtain ⟨hV, hE, hT⟩ := h B K
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hV, hE, hT]
  ring

theorem kindRates_kindTotalRates {c : LetterCost} {cV cE cT : ℝ}
    (h : KindRates c cV cE cT) : KindTotalRates c cV cE cT := by
  classical
  intro B K
  obtain ⟨hV, hE, hT⟩ := h B K
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun v _ => hV v), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  · rw [Finset.sum_congr rfl (fun e _ => hE e), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  · rw [Finset.sum_congr rfl (fun τ _ => hT τ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring

theorem kindOnly_fixedKindTotals {c : LetterCost} (h : KindOnly c) : FixedKindTotals c := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  exact ⟨cV, cE, cT, kindRates_kindTotalRates hc⟩

theorem fixedKindTotals_costSizeBlind {c : LetterCost} (h : FixedKindTotals c) :
    CostSizeBlind c := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  intro B B' K L hv he ht
  rw [historyCost_of_kindTotalRates hc B K, historyCost_of_kindTotalRates hc B' L, hv, he, ht]

/-- **THEOREM (the corrected premise derives the measure).**  Aggregate linearity by kind, plus
the three normalizations, gives the Gibbs weight and `mu`, with no gluing premise and no
constraint on individual letters. -/
theorem measure_from_fixedKindTotals {c : LetterCost} (h : FixedKindTotals c)
    (hn : NormalizedAtTheAtoms (postedWeight c)) (B : ℕ) (K : BoundedComplex B) :
    postedWeight c B K = gibbsWeight K
      ∧ classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  have hlin := historyCost_of_kindTotalRates hc
  obtain ⟨hV, hE, hT⟩ := linearCost_atoms_force_zero hlin hn
  have hgib : ∀ (B' : ℕ) (K' : BoundedComplex B'), postedWeight c B' K' = gibbsWeight K' := by
    intro B' K'
    unfold postedWeight
    rw [hlin B' K', hV, hE, hT]
    simp only [zero_mul, add_zero, neg_zero, Real.exp_zero, one_mul]
  refine ⟨hgib B K, ?_⟩
  have hfun : postedWeight c B = fun K' : BoundedComplex B => gibbsWeight K' := by
    funext K'
    exact hgib B K'
  rw [hfun]
  exact classMass_gibbsWeight_eq_mu K

/-! ### The cost that reads incidence and posts the measure anyway -/

/-- The **centered** incidence cost.  A proper edge letter costs `t · (nE - properEdgeCount K)`
and a loop letter costs `-t · properEdgeCount K`; vertex and tetrahedron letters cost nothing.  Every
*edge* letter reads the incidence structure, and the edge block total is zero at every complex.  The
silence on the other two kinds is real and the witness does not need it broken: what it refutes is
that silence must hold at every letter, and one kind's letters suffice for that. -/
def centeredIncidenceCost (t : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl e) =>
      t * ((if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then (K.nE : ℝ) else 0)
            - (properEdgeCount K : ℝ))
  | Sum.inr (Sum.inr _) => 0

@[simp] theorem centeredIncidenceCost_inl (t : ℝ) (B : ℕ) (K : BoundedComplex B)
    (v : Fin K.nV) : centeredIncidenceCost t B K (Sum.inl v) = 0 := rfl

@[simp] theorem centeredIncidenceCost_edge (t : ℝ) (B : ℕ) (K : BoundedComplex B)
    (e : Fin K.nE) : centeredIncidenceCost t B K (Sum.inr (Sum.inl e))
      = t * ((if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then (K.nE : ℝ) else 0)
              - (properEdgeCount K : ℝ)) := rfl

@[simp] theorem centeredIncidenceCost_tet (t : ℝ) (B : ℕ) (K : BoundedComplex B)
    (τ : Fin K.nT) : centeredIncidenceCost t B K (Sum.inr (Sum.inr τ)) = 0 := rfl

/-- **The centering identity.**  The edge letters of the centered cost sum to zero: the proper
edges contribute `t · nE · p` and every one of the `nE` edges is debited `t · p`. -/
theorem edgeSum_centeredIncidenceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    (∑ e : Fin K.nE, centeredIncidenceCost t B K (Sum.inr (Sum.inl e))) = 0 := by
  classical
  have hp : (∑ e : Fin K.nE,
      (if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then (K.nE : ℝ) else 0))
      = (K.nE : ℝ) * (properEdgeCount K : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    unfold properEdgeCount
    ring
  have hc : (∑ _e : Fin K.nE, (properEdgeCount K : ℝ))
      = (K.nE : ℝ) * (properEdgeCount K : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [centeredIncidenceCost_edge]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hp, hc, sub_self, mul_zero]

theorem historyCost_centeredIncidenceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (centeredIncidenceCost t) B K = 0 := by
  classical
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [centeredIncidenceCost_inl, centeredIncidenceCost_tet, Finset.sum_const_zero,
    zero_add, add_zero]
  exact edgeSum_centeredIncidenceCost t B K

theorem postedWeight_centeredIncidenceCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    postedWeight (centeredIncidenceCost t) B K = gibbsWeight K := by
  unfold postedWeight
  rw [historyCost_centeredIncidenceCost, neg_zero, Real.exp_zero, one_mul]

/-- The centered cost is gauge-equivariant: a relabeling preserves the edge count, the
proper-edge count, and whether a given edge's endpoints differ. -/
theorem centeredIncidenceCost_equivariant (t : ℝ) : Equivariant (centeredIncidenceCost t) := by
  intro B K K' r a
  rcases a with x | (y | z)
  · rfl
  · have hE : (K'.nE : ℝ) = (K.nE : ℝ) := by rw [size_e r]
    have hP : (properEdgeCount K' : ℝ) = (properEdgeCount K : ℝ) := by
      rw [properEdgeCount_congr r]
    have hIf : (if (K'.edgeVerts (r.eEquiv y)).1 ≠ (K'.edgeVerts (r.eEquiv y)).2
          then (K'.nE : ℝ) else 0)
        = (if (K.edgeVerts y).1 ≠ (K.edgeVerts y).2 then (K.nE : ℝ) else 0) := by
      rw [hE]
      exact if_congr (not_congr (loop_iff_of_relabel r y).symm) rfl rfl
    rw [show postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv (Sum.inr (Sum.inl y))
        = Sum.inr (Sum.inl (r.eEquiv y)) from rfl, centeredIncidenceCost_edge,
      centeredIncidenceCost_edge, hIf, hP]
  · rfl

/-- Three vertices, one loop and one proper edge: the smallest complex whose two edge letters
must be charged differently by the centered cost. -/
def loopAndBridge : BoundedComplex 3 where
  nV := 3
  nE := 2
  nT := 0
  hV := le_refl 3
  hE := by norm_num
  hT := Nat.zero_le 3
  edgeVerts := fun e => if e = 0 then (0, 0) else (1, 2)
  tetVerts := fun t => t.elim0

theorem properEdgeCount_loopAndBridge : properEdgeCount loopAndBridge = 1 := by decide

theorem loopAndBridge_nE : loopAndBridge.nE = 2 := rfl

/-- The loop letter is charged `-t · p` with `p = 1`, and the proper-edge letter `t · (nE - p)`
with `nE = 2`, so the two letters of the same kind are charged `-t` and `t`. -/
theorem centeredIncidence_charges_on_loopAndBridge (t : ℝ) :
    centeredIncidenceCost t 3 loopAndBridge (Sum.inr (Sum.inl ⟨0, by decide⟩)) = -t
      ∧ centeredIncidenceCost t 3 loopAndBridge (Sum.inr (Sum.inl ⟨1, by decide⟩)) = t := by
  constructor
  · rw [centeredIncidenceCost_edge, properEdgeCount_loopAndBridge, if_neg (by decide)]
    norm_num
  · rw [centeredIncidenceCost_edge, properEdgeCount_loopAndBridge, if_pos (by decide),
      loopAndBridge_nE]
    norm_num

/-- **THEOREM (the centered cost is not kind-only).**  At `loopAndBridge` the loop letter is
charged `-t` and the proper-edge letter `t`, so no single edge rate reproduces it. -/
theorem centeredIncidenceCost_not_kindOnly {t : ℝ} (ht : t ≠ 0) :
    ¬ KindOnly (centeredIncidenceCost t) := by
  rintro ⟨cV, cE, cT, hc⟩
  obtain ⟨hloop, hprop⟩ := centeredIncidence_charges_on_loopAndBridge t
  have h0 : (-t : ℝ) = cE := by rw [← hloop]; exact (hc 3 loopAndBridge).2.1 _
  have h1 : (t : ℝ) = cE := by rw [← hprop]; exact (hc 3 loopAndBridge).2.1 _
  exact ht (by linarith)

/-- **THEOREM (per-letter incidence silence is not the boundary).**  For every nonzero `t` the
centered cost reads incidence at every edge letter, is gauge-equivariant, is not kind-only, is
unit at the three atoms, and its posted weight is exactly the Gibbs weight with class measure
exactly `mu`.

So a cost may see incidence and still deliver the intended measure.  What the derivation needs is
not silence at the letter but linearity in the aggregate, which the centered cost has: its kind
totals are all zero (`fixedKindTotals_centeredIncidenceCost`). -/
theorem centeredIncidence_is_the_measure {t : ℝ} (ht : t ≠ 0) (B : ℕ) (K : BoundedComplex B) :
    Equivariant (centeredIncidenceCost t)
      ∧ ¬ KindOnly (centeredIncidenceCost t)
      ∧ NormalizedAtTheAtoms (postedWeight (centeredIncidenceCost t))
      ∧ postedWeight (centeredIncidenceCost t) B K = gibbsWeight K
      ∧ classMass (postedWeight (centeredIncidenceCost t) B)
          (Quotient.mk (relabelSetoid B) K) = mu K := by
  have hgib : ∀ (B' : ℕ) (K' : BoundedComplex B'),
      postedWeight (centeredIncidenceCost t) B' K' = gibbsWeight K' :=
    fun B' K' => postedWeight_centeredIncidenceCost t B' K'
  refine ⟨centeredIncidenceCost_equivariant t, centeredIncidenceCost_not_kindOnly ht, ?_,
    hgib B K, ?_⟩
  · intro B' K' hv hi
    rw [hgib B' K']
    exact gibbsWeight_eq_one_at_atoms K' hv hi
  · have hfun : postedWeight (centeredIncidenceCost t) B
        = fun K' : BoundedComplex B => gibbsWeight K' := by
      funext K'
      exact hgib B K'
    rw [hfun]
    exact classMass_gibbsWeight_eq_mu K

theorem fixedKindTotals_centeredIncidenceCost (t : ℝ) :
    FixedKindTotals (centeredIncidenceCost t) := by
  classical
  refine ⟨0, 0, 0, ?_⟩
  intro B K
  refine ⟨?_, ?_, ?_⟩
  · simp
  · rw [edgeSum_centeredIncidenceCost]; ring
  · simp

/-- **THEOREM (aggregate linearity is strictly weaker than kind-only).**  The centered cost has
kind totals and is not kind-only, so the corrected premise is genuinely weaker than the one §3
used, and still derives the measure (`measure_from_fixedKindTotals`). -/
theorem fixedKindTotals_not_kindOnly {t : ℝ} (ht : t ≠ 0) :
    FixedKindTotals (centeredIncidenceCost t) ∧ ¬ KindOnly (centeredIncidenceCost t) :=
  ⟨fixedKindTotals_centeredIncidenceCost t, centeredIncidenceCost_not_kindOnly ht⟩

/-- **THEOREM (aggregate linearity is strictly stronger than premise (i)).**  `pairCost` is
size-blind at the level of totals and does not have kind totals, since its vertex block sums to
`nV(nV-1)` rather than to a fixed multiple of `nV`.  That it is also unit at the three atoms is not a
conjunct here; it is `costSizeBlind_and_atoms_do_not_give_gibbs`, which is where the pair is used to
show the normalizations do not rescue a non-linear cost. -/
theorem costSizeBlind_not_fixedKindTotals :
    CostSizeBlind pairCost ∧ ¬ FixedKindTotals pairCost := by
  refine ⟨costSizeBlind_and_atoms_do_not_give_gibbs.1, ?_⟩
  rintro ⟨cV, cE, cT, hc⟩
  have h1 := historyCost_of_kindTotalRates hc 1 (dust 1)
  have h2 := historyCost_of_kindTotalRates hc 2 (dust 2)
  rw [historyCost_pairCost] at h1 h2
  simp only [dust_nV, dust_nE, dust_nT, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat,
    mul_zero, add_zero] at h1 h2
  norm_num at h1 h2
  linarith

/-! ### How much room the corrected premise really has

§7's third finding says the aggregate premise has room the kind-only one does not, and that is
true of the letter costs and false of the weight.  The two theorems below separate those, because
the difference is the whole honest reading of this module. -/

/-- **THEOREM (the aggregate premise collapses too, one level up).**  Aggregate linearity by kind
plus the three normalizations forces the *history cost* to be identically zero, not merely at the
atoms.  Three normalizations pin three rates and a linear function of the counts vanishing at three
independent points vanishes everywhere, and this argument never looked at a single letter.

So `measure_from_fixedKindTotals` is rigidity in exactly the way `posting_cost_derives_gibbs` was:
the premises admit one history cost.  What the aggregate premise buys over kind-only is a family of
letter costs realizing that one history cost
(`centeredIncidence_is_the_measure`), and the weight cannot see which member you picked. -/
theorem fixedKindTotals_and_atoms_force_zero_historyCost {c : LetterCost}
    (h : FixedKindTotals c) (hn : NormalizedAtTheAtoms (postedWeight c))
    (B : ℕ) (K : BoundedComplex B) : historyCost c B K = 0 := by
  obtain ⟨cV, cE, cT, hc⟩ := h
  have hlin := historyCost_of_kindTotalRates hc
  obtain ⟨hV, hE, hT⟩ := linearCost_atoms_force_zero hlin hn
  rw [hlin B K, hV, hE, hT]
  ring

/-- **THEOREM (the cost layer contributes no factor of the weight).**  Under the corrected premise
and the three normalizations the Boltzmann numerator is identically `1`, and the posted weight is
exactly the reciprocal order of the alphabet's sort-respecting gauge group.

**Two corrections to how this was first written.**  It is *not* true that "every factor of `mu`
comes from the divisor": `classMass` sums the weight over the class, so
`mu K = |orbit K| / |AlphabetGauge K|` by orbit-stabilizer
(`Gap2GaugeVolume.orbitCard_mul_autCard`), and the orbit count is independently load-bearing.  What
is true is the narrower thing this theorem says, that the *cost* contributes no factor.  And the
cause is not the premises named here: `equivariant_posts_mu_iff_numerator_one` gets the same
collapse from equivariance alone, so this theorem is a corollary of a fact the library held before
the module existed.  Kept because it is the form that mentions the premises a reader arrives
holding. -/
theorem the_measure_is_the_gauge_divisor {c : LetterCost} (h : FixedKindTotals c)
    (hn : NormalizedAtTheAtoms (postedWeight c)) (B : ℕ) (K : BoundedComplex B) :
    Real.exp (-(historyCost c B K)) = 1
      ∧ postedWeight c B K = 1 / (Nat.card (AlphabetGauge K) : ℝ)
      ∧ classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  have hz : ∀ (B' : ℕ) (K' : BoundedComplex B'), historyCost c B' K' = 0 :=
    fun B' K' => fixedKindTotals_and_atoms_force_zero_historyCost h hn B' K'
  refine ⟨by rw [hz B K, neg_zero, Real.exp_zero], ?_, (measure_from_fixedKindTotals h hn B K).2⟩
  unfold postedWeight
  rw [hz B K, neg_zero, Real.exp_zero, one_mul, gibbsWeight_eq_inv_card_alphabetGauge]

/-! ### The collapse is not this module's premises

A cross-family referee read §7 and found the theorem above is not the sharpest form, for a reason
that had been sitting in the library since before this module existed.  `Gap2GaugeVolume`'s
`invariant_weight_gives_measure_iff` says the Gibbs weight is the *unique* relabeling-invariant
labeled weight whose class mass is `mu`.  Every equivariant letter cost has a relabeling-invariant
posted weight (`postedWeight_invariant`).  Compose the two and the collapse to a unit numerator
follows from equivariance and from wanting `mu`, with no kind clause, no aggregate linearity, and no
atom normalizations anywhere in the argument. -/

/-- **THEOREM (no equivariant cost contributes a factor to the measure, whatever premise picks
it out).**  For an equivariant letter cost, the posted weight's class mass is `mu` at every complex
exactly when the Boltzmann numerator is identically one.

This subsumes `the_measure_is_the_gauge_divisor` and relocates the finding.  The collapse is not
caused by kind-only, by aggregate linearity, or by the three normalizations: it is caused by asking
a gauge-invariant cost to reproduce `mu`, and `invariant_weight_gives_measure_iff` had already
settled that before this module was written.  What the premises of §3 and §7 do is pick out *which*
cost, and the honest reading of the whole module is that they cannot do anything else.

**Where equivariance is load-bearing, and where the statement is open.**  The reverse direction
needs no invariance: a unit numerator makes the posted weight the Gibbs weight outright.  The
forward direction runs through the uniqueness theorem and so needs it.  Whether a *non*-equivariant
cost can post `mu` with a numerator that is not identically one, by having the orbit sum of its
Boltzmann factors come out to the orbit count while the individual terms differ, is not settled
here; the referee's construction for it is not formalized and this docstring does not claim it. -/
theorem equivariant_posts_mu_iff_numerator_one {c : LetterCost} (hc : Equivariant c) (B : ℕ) :
    (∀ K : BoundedComplex B,
        classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ↔ ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1 := by
  have hinv : ∀ K K' : BoundedComplex B, Equivalent K K' →
      postedWeight c B K = postedWeight c B K' :=
    fun _ _ h => postedWeight_invariant hc h
  have hgibbs : (∀ K : BoundedComplex B, postedWeight c B K = gibbsWeight K)
      ↔ ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1 := by
    constructor
    · intro h K
      have hg := gibbsWeight_positive K
      have hK := h K
      unfold postedWeight at hK
      have hcancel : Real.exp (-(historyCost c B K)) * gibbsWeight K = 1 * gibbsWeight K := by
        rw [one_mul]
        exact hK
      exact mul_right_cancel₀ hg.ne' hcancel
    · intro h K
      unfold postedWeight
      rw [h K, one_mul]
  refine Iff.trans ?_ hgibbs
  refine Iff.trans ?_ (Gap2GaugeVolume.invariant_weight_gives_measure_iff (postedWeight c B) hinv)
  exact (MeasureSubstrateBlocker.gaugeCountingPrinciple_iff_mu_on_representatives
    (classMass (postedWeight c B))).symm

/-! ## §8. Navigation index

Flags only.  Two are deliberately `false`: the premise this module names is not itself derived,
and the cost layer is not shown to contribute any factor of the measure because
`equivariant_posts_mu_iff_numerator_one` proves it contributes none.  Those are the frontier
Gap 2's measure now sits on.  The non-equivariant case, open when this index was written, is now
settled affirmatively downstream: `Gap2NonEquivariantPosting.tiltedCost_posts_mu` with
`numerator_ne_one_at_loopAndBridge`.  A fourth flag flipped
to `true` in the other direction: the letter cost under §3's premises is not merely unique up to the
three rates, it is unique outright and equal to zero. -/

structure PostingIndex : Type where
  /-- Kind-only posting costs plus free atoms derive `mu`, with no gluing premise. -/
  kind_only_derives_mu : Bool
  /-- Every premise appears in the binders of the headline, the gauge divisor included.  Three
  binders, packing five assumptions. -/
  premises_visible_in_statement : Bool
  /-- The Gibbs divisor is the order of the alphabet's sort-respecting gauge group. -/
  divisor_is_alphabet_gauge_volume : Bool
  /-- The incidence-aware cost is gauge-equivariant and not kind-only, so equivariance does
  not supply the premise. -/
  equivariance_insufficient : Bool
  /-- The incidence-aware cost reproduces the reach bound's escape, so the escape is realizable
  inside this formalism as the posted weight of a well-formed letter cost.  Not a claim about what a
  substrate posts. -/
  escape_is_postable : Bool
  /-- Kind-only is strictly stronger than premise (i), measured twice: at the uniform weight
  and at the cost layer. -/
  strictness_measured : Bool
  /-- The corrected premise, aggregate linearity by kind, derives `mu` and is strictly between
  premise (i) at the cost layer and kind-only. -/
  aggregate_premise_derives_mu : Bool
  /-- NOT proved: that the substrate forces incidence silence, at the letter or in the aggregate. -/
  incidence_silence_derived : Bool
  /-- Proved, and stronger than first flagged: under §3's premises the letter cost is unique
  outright, being identically zero (`kindOnly_and_atoms_force_zeroCost`).  Under §7's weaker premise
  it is not unique, and the history cost is (`fixedKindTotals_and_atoms_force_zero_historyCost`). -/
  letter_cost_unique : Bool
  /-- NOT proved, and in fact refuted: that the cost layer contributes any factor of the measure.
  Every equivariant cost posts `mu` exactly when its numerator is identically one
  (`equivariant_posts_mu_iff_numerator_one`), so no premise on an equivariant cost can. -/
  cost_layer_contributes_a_factor : Bool
  /-- SETTLED affirmatively downstream (`Gap2NonEquivariantPosting`): a non-equivariant cost
  CAN post `mu` with a numerator other than one, the orbit sum of its Boltzmann factors matching
  the orbit count while the terms differ (`tiltedCost_posts_mu`,
  `numerator_ne_one_at_loopAndBridge`, `nonequivariant_posting_family`). -/
  nonequivariant_numerator_settled : Bool

def postingIndex : PostingIndex where
  kind_only_derives_mu := true
  premises_visible_in_statement := true
  divisor_is_alphabet_gauge_volume := true
  equivariance_insufficient := true
  escape_is_postable := true
  strictness_measured := true
  aggregate_premise_derives_mu := true
  incidence_silence_derived := false
  letter_cost_unique := true
  cost_layer_contributes_a_factor := false
  nonequivariant_numerator_settled := true

theorem index_silence_not_derived : postingIndex.incidence_silence_derived = false := rfl

/-- The flag reads `true` and the theorem in the file is stronger than the flag's first wording:
under `KindOnly` plus the atom normalizations the cost is not merely pinned up to three rates, it is
identically zero. -/
theorem index_cost_unique_under_kind_only : postingIndex.letter_cost_unique = true := rfl

theorem index_cost_layer_contributes_nothing :
    postingIndex.cost_layer_contributes_a_factor = false := rfl

/-- Settled downstream in `Gap2NonEquivariantPosting`: the non-equivariant case named in this
flag's original docstring is answered affirmatively by an explicit witness family. -/
theorem index_nonequivariant_settled : postingIndex.nonequivariant_numerator_settled = true := rfl

end

end Gap2PostingCostDerivation
end SevenGaps
end Gravity
end IndisputableMonolith
