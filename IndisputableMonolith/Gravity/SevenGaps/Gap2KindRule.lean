import IndisputableMonolith.Gravity.SevenGaps.Gap2PostingCostDerivation
import IndisputableMonolith.Gravity.Analysis.RecognitionDualEntryEnrichment4D

/-!
# Gap 2, third arc: does the letter-cost space force the kind rule?

The residual left by `Gap2PostingCostDerivation` is the kind clause: a letter's cost is a
function of its kind and of nothing else, with the same three reals at every complex.  That
module derived premise (i) and then the measure from a posted kind-only cost normalized at the
atoms, with no gluing premise, and it flagged `incidence_silence_derived := false`: whether the
substrate forces the kind rule was left open.  This module settles what can be settled in Lean
about that, at the layer where it is statable, and the answer has three parts, each of which is
a theorem rather than a reading.  **The scope is the letter-cost space, and the header says so
because a referee rightly objected when an earlier version asked "does the ledger force it":
the ledger's dual-entry lattice is one layer below `LetterCost`, and whether THAT forces the
rule is the open successor, not what is settled here.**

## T1, the kind rule fails in the letter-cost space, and not only by incidence

`incidenceCost` charges `t` for a proper edge letter and nothing for any other letter.  It is a
well-formed `LetterCost`, gauge-equivariant (`incidenceCost_equivariant`), not kind-only
(`incidenceCost_not_kindOnly`), and its posted weight is not size-blind
(`incidencePosting_not_sizeBlind`).  So the letter-cost space admits incidence-aware equivariant
charging rules that break the kind clause, and nothing in the definition of `LetterCost`
excludes them.

The vertex count read as a vertex letter charge (`pairCost`) is equivariant
(`pairCost_equivariant`), not kind-only (`pairCost_not_kindOnly`), and size-blind at the level of
totals (`pairCost_costSizeBlind`).  So incidence is not the only way to fail the kind rule: a
non-constant counts-only charge fails it too.  Said with the scope a referee required: this is
one exhibited witness, not a comparison of countermodel sets, and "every size-function letter
charge fails" would be false since a constant size-function is kind-only.  Whether "reads sizes"
and "reads incidence" are independent is a definitional matter of which fields of `K` a charge
inspects, not a theorem here.

## T2, where the exclusion lives: the measure formula, within this framework

`GaugeHistoryMeasure` pins its counted histories to the balanced zero dual-entry state
(`CanonicalHistory.state_canonical`), and the tempting reading is that this pinning is what
excludes the countermodel.  Within the framework as it stands it does not, and the reason is
the type of `LetterCost`, which takes a complex and an alphabet letter and no dual-entry state.
The theorem `letter_cost_is_silent_on_the_state_space` is an `rfl` projection recording exactly
that, and its docstring now says what it cannot say: a cost notion defined on a state-bearing
carrier could depend on the state, and nothing here rules that out.  Inside the current cost
API, though, the pinning acts on histories and a cost is not a history, so the pinning cannot be
what admits or excludes a cost.  What excludes the countermodel's weight from the measure, in
this framework, is the measure formula: the class mass of the incidence posting at the
two-bridge class is `exp(-2t)/|Aut|`, not `1/|Aut|` (`countermodel_weight_classMass_ne_mu`),
because the Boltzmann numerator is not identically one while the gauge divisor is the same for
every invariant weight.

The pinning's role is therefore upstream of the cost layer entirely: it makes the counted
histories countable (one per labeled complex, by `CanonicalHistory.fiber_unique`), which is what
lets the orbit count be finite and equal to the labeled-complex orbit count.  That is a counting
normalization, not a charge selection.

## T3, the named premise, and what it costs

Since the kind rule is not forced, the premise that closes the derivation is named:
`ChargesCountsOnly`, that a letter's charge is a function of the three counts and of the letter's
kind.  It gives the per-complex totals form with count-dependent rates
(`chargesCountsOnly_kindTotals_perComplex`), which is NOT the second arc's `FixedKindTotals`:
those rates are three fixed reals across all complexes, and the difference is `pairCost`, which
is counts-only with vertex rate `nV - 1` and so satisfies the new premise but not the fixed one.
The global kind rule is the special case where the three count functions are constant, and that
special case is what the atom normalizations then pin to zero.  **The premise is an authored
restriction on `LetterCost`, not a constraint the alphabet forces**: the alphabet's letters are
indexed, `indexCost` reads that index and is excluded by the premise, so the premise forbids
data the alphabet does carry.  What recommends it is that it is statable purely in counts and
kinds, that it is strictly weaker than kind-only (one-way witness `pairCost`; the converse
direction `KindOnly → ChargesCountsOnly` is immediate and not stated in this module), and that
the normalizations lift it from count-dependent rates to zero.  The physical content, said in
one sentence: a posting's charge may know how many cells of each kind the complex has, and which
kind the posting is, and nothing else.

## What this arc does not settle

Whether the ledger, at the dual-entry layer below `LetterCost`, forces `ChargesCountsOnly` is
open and is the honest successor question.  This arc showed the answer cannot come from the
posting alphabet's own structure, because the alphabet does not carry the dual-entry state and
the current cost API cannot see it.  The successor question is whether the dual-entry lattice
itself, the integer columns with unit flux, forces the charge to be counts-only, and that is a
question about `DualEntryStrainState`, not about `PostingAlphabet`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2KindRule

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## §1. T1: the countermodel needs no incidence; the vertex count suffices -/

/-- The vertex charge of `pairCost` at a transported vertex letter: the transport of a vertex
letter is a vertex letter, and `pairCost` there reads the target's vertex count.  Stated
directly rather than by `cases` on the transported letter, which leaves a dependent match
`simp` will not close. -/
theorem pairCost_equivariant : Equivariant pairCost := by
  intro B K K' r a
  have hnv : K'.nV = K.nV := by
    have h : K.nV = K'.nV := by
      simpa using
        (Fintype.card_eq.mpr ⟨r.vEquiv⟩ : Fintype.card (Fin K.nV) = Fintype.card (Fin K'.nV))
    exact h.symm
  cases a with
  | inl v =>
    show (K'.nV : ℝ) - 1 = (K.nV : ℝ) - 1
    rw [hnv]
  | inr rest =>
    cases rest with
    | inl e => rfl
    | inr t => rfl

/-- The one-vertex complex, the vertex atom (sizes (1,0,0)). -/
def oneVertex : BoundedComplex 1 where
  nV := 1
  nE := 0
  nT := 0
  hV := le_refl 1
  hE := Nat.zero_le 1
  hT := Nat.zero_le 1
  edgeVerts := fun e => e.elim0
  tetVerts := fun t => t.elim0

/-- **THEOREM (the vertex-count charge is not kind-only).**  The charge is `↑nV - 1`, which is
`1` at the two-vertex complex and `0` at the one-vertex complex, so no single vertex rate
matches both.  The kind rule demands one real for every complex, and the count charge varies
with the count.  Note the two-vertex complex alone does not separate anything (the charge is
uniform over its two letters); the separation is across sizes. -/
theorem pairCost_not_kindOnly : ¬ KindOnly pairCost := by
  rintro ⟨cV, cE, cT, h⟩
  obtain ⟨hV, -, -⟩ := h 2 twoLoops
  obtain ⟨hV1, -, -⟩ := h 1 oneVertex
  have h2 := hV ⟨0, by decide⟩
  have h1 := hV1 ⟨0, by decide⟩
  have h2' : (1 : ℝ) = cV := by
    have := h2
    simp only [pairCost, twoLoops] at this
    norm_num at this
    exact this
  have h1' : (0 : ℝ) = cV := by
    have := h1
    simp only [pairCost, oneVertex] at this
    norm_num at this
    exact this
  rw [← h1'] at h2'
  norm_num at h2'

/-- **THEOREM (the vertex-count charge is size-blind at the level of totals).**  The history
cost is `nV(nV-1)`, a function of the counts.  This is the second arc's
`historyCost_pairCost`, restated as `CostSizeBlind`. -/
theorem pairCost_costSizeBlind : CostSizeBlind pairCost := by
  intro B B' K L hv he ht
  rw [historyCost_pairCost, historyCost_pairCost, hv]

/-- **THEOREM (the kind rule fails without any incidence).**  A failure of the kind clause by
counting rather than by incidence exists and is equivariant.  This is T1's sharpened verdict,
and its scope is stated exactly: one exhibited witness, `pairCost`.  What the theorem does not
contain, because the conjunction does not say it, is the English gloss that the countermodel
space is "strictly larger than the incidence family" or that it contains "every size-function
letter charge".  The first is a comparison of sets this module never defines, and the second is
false (a constant size-function is kind-only).  What is true and what the witness shows is that
a non-constant counts-only charge can fail the kind rule, so incidence is not the only way to
fail it.  Whether "reads sizes" and "reads incidence" are independent is a definitional matter
of which fields of `K` a charge inspects, not a theorem here. -/
theorem kind_rule_fails_by_counting :
    Equivariant pairCost ∧ ¬ KindOnly pairCost ∧ CostSizeBlind pairCost :=
  ⟨pairCost_equivariant, pairCost_not_kindOnly, pairCost_costSizeBlind⟩

/-- **THEOREM (the kind rule fails by incidence too).**  The second arc's countermodel,
restated for comparison.  The two failures are independent: `pairCost` is size-blind and
`incidenceCost` is not; `incidenceCost` reads incidence and `pairCost` does not. -/
theorem kind_rule_fails_by_incidence (t : ℝ) (ht : t ≠ 0) :
    Equivariant (incidenceCost t) ∧ ¬ KindOnly (incidenceCost t) ∧
      ¬ SizeBlind (postedWeight (incidenceCost t)) :=
  ⟨incidenceCost_equivariant t, incidenceCost_not_kindOnly ht,
    incidencePosting_not_sizeBlind ht⟩

/-! ## §2. T2: the exclusion lives in the measure formula, not the pinning -/

/-- **THEOREM (a `LetterCost`, as defined, takes no state).**  `PostedBoundedHistory.mk K S`
projects to `K` under `.K`, and a `LetterCost` is a function of a complex and an alphabet
letter, so two posted histories on the same complex with different dual-entry states give the
same letter charge.  The proof is `rfl` and the statement is a projection: it says the current
cost API has no state argument, and nothing more.  What it does NOT say, because a type cannot
say it, is that no cost notion could ever depend on the state; a cost defined on
`PostedBoundedHistory` itself, rather than on `BoundedComplex`, could.  Within the framework as
it stands, though, the `state_canonical` pinning acts on histories and a cost is not a history,
so the pinning cannot be what admits or excludes a cost.  That framework-internal conclusion is
the T2 answer, and this theorem states its scope rather than leaving the stronger reading. -/
theorem letter_cost_is_silent_on_the_state_space (c : LetterCost) (B : ℕ)
    (K : BoundedComplex B) (S₁ S₂ : DualEntryStrainState (PostingAlphabet K))
    (a : PostingAlphabet K) :
    c B (PostedBoundedHistory.mk K S₁).K a = c B (PostedBoundedHistory.mk K S₂).K a := rfl

/-- **THEOREM (the history cost is state-independent, same scope).**  The same projection at
the level of the total charge, with the same limit: about the current `LetterCost` API, not
about every cost notion one could define on a state-bearing carrier. -/
theorem history_cost_is_silent_on_the_state_space (c : LetterCost) (B : ℕ)
    (K : BoundedComplex B) (S₁ S₂ : DualEntryStrainState (PostingAlphabet K)) :
    historyCost c B (PostedBoundedHistory.mk K S₁).K
      = historyCost c B (PostedBoundedHistory.mk K S₂).K := rfl

/-- **THEOREM (the measure formula is what excludes the escape).**  The class mass of the
incidence posting at the two-bridge class is `exp(-2t)` over the automorphism count, and for
`t ≠ 0` that is not the measure value `1/|Aut|`.  Every invariant weight shares the same gauge
divisor, so the difference is entirely in the Boltzmann numerator, which is not identically
one.  This restates the second arc's `incidencePosting_classMass_ne_mu` as the answer to T2's
question: the escape is excluded by the gauge-divisor formula for the class mass, not by any
canonicality condition on a state. -/
theorem countermodel_weight_classMass_ne_mu (t : ℝ) (ht : t ≠ 0) :
    classMass (postedWeight (incidenceCost t) 2)
        (Quotient.mk (relabelSetoid 2) twoBridges) ≠ mu twoBridges :=
  incidencePosting_classMass_ne_mu ht

/-- **THEOREM (the pinning is a counting normalization, and that is all).**  The fiber of
counted histories over a labeled complex is a singleton, which is what makes the orbit count
equal the labeled-complex orbit count.  Said as a restatement of
`CanonicalHistory.fiber_unique`: the pinning's content is that there is exactly one counted
history per complex, not that some charges are admitted and others excluded.  (A `def`, not a
`theorem`: `Unique` is Type-valued.) -/
def pinning_is_a_counting_normalization (B : ℕ) (K : BoundedComplex B) :
    Unique {CH : CanonicalHistory B // CH.underlying = K} :=
  CanonicalHistory.fiber_unique K

/-! ## §3. T3: the named premise, its strength, and its physical content -/

/-- **The named premise.**  A letter's charge is a function of the three counts and of the
letter's kind: for each kind there is a function of the counts giving every letter of that kind
its charge, the same function at every complex.  Said carefully, this is an authored restriction
on `LetterCost`, not a constraint the alphabet forces: the alphabet's letters are indexed, and
`indexCost` reads that index and is excluded by this premise, so the premise forbids data the
alphabet does carry.  What recommends it is that it is statable purely in terms of counts and
kinds, the two things a letter's charge is allowed to depend on if it is to give a size-blind
totals form, and that it excludes both exhibited failures while admitting the count charge. -/
def ChargesCountsOnly (c : LetterCost) : Prop :=
  (∃ fV : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV),
    c B K (Sum.inl v) = fV K.nV K.nE K.nT)
  ∧ (∃ fE : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE),
    c B K (Sum.inr (Sum.inl e)) = fE K.nV K.nE K.nT)
  ∧ (∃ fT : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT),
    c B K (Sum.inr (Sum.inr τ)) = fT K.nV K.nE K.nT)

/-- **THEOREM (the named premise gives per-complex kind rates).**  Within one complex, every
letter of a kind shares one charge, so per-complex kind rates exist.  This is NOT the kind
rule: the rates vary with the complex's counts.  The global kind rule, one triple of reals for
all complexes, is the special case where the three count functions are constant, and this
theorem does not give that case. -/
theorem chargesCountsOnly_perComplex_kindRates (c : LetterCost) (h : ChargesCountsOnly c)
    (B : ℕ) (K : BoundedComplex B) :
    ∃ cV cE cT : ℝ,
      (∀ v : Fin K.nV, c B K (Sum.inl v) = cV)
        ∧ (∀ e : Fin K.nE, c B K (Sum.inr (Sum.inl e)) = cE)
        ∧ (∀ τ : Fin K.nT, c B K (Sum.inr (Sum.inr τ)) = cT) := by
  obtain ⟨⟨fV, hV⟩, ⟨fE, hE⟩, ⟨fT, hT⟩⟩ := h
  exact ⟨fV K.nV K.nE K.nT, fE K.nV K.nE K.nT, fT K.nV K.nE K.nT,
    fun v => hV B K v, fun e => hE B K e, fun τ => hT B K τ⟩

/-- **THEOREM (the named premise gives the totals form, with count-dependent rates).**  The
block sum of each kind is the per-letter value times the count, where the value is the kind
function at that complex's counts.  This is NOT `FixedKindTotals`, whose rates are three fixed
reals across all complexes; it is the per-complex statement, and the difference is the whole
point of §3: a counts-only charge may vary its rates with the counts, as `pairCost` does with
vertex rate `nV - 1`.  The global kind rule is the special case where the three functions are
constant, and that special case is what the atom normalizations then pin to zero. -/
theorem chargesCountsOnly_kindTotals_perComplex (c : LetterCost) (h : ChargesCountsOnly c)
    (B : ℕ) (K : BoundedComplex B) :
    ∃ cV cE cT : ℝ,
      (∑ v : Fin K.nV, c B K (Sum.inl v)) = cV * (K.nV : ℝ)
        ∧ (∑ e : Fin K.nE, c B K (Sum.inr (Sum.inl e))) = cE * (K.nE : ℝ)
        ∧ (∑ τ : Fin K.nT, c B K (Sum.inr (Sum.inr τ))) = cT * (K.nT : ℝ) := by
  obtain ⟨⟨fV, hV⟩, ⟨fE, hE⟩, ⟨fT, hT⟩⟩ := h
  classical
  refine ⟨fV K.nV K.nE K.nT, fE K.nV K.nE K.nT, fT K.nV K.nE K.nT, ?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun v _ => hV B K v), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_comm]
  · rw [Finset.sum_congr rfl (fun e _ => hE B K e), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_comm]
  · rw [Finset.sum_congr rfl (fun τ _ => hT B K τ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- The **index charge**: each vertex letter is charged its own index.  Not counts-only,
because a function of the counts cannot give letter 0 charge 0 and letter 1 charge 1 at the
same sizes.  This is the witness that the named premise excludes per-letter data the alphabet
does not carry, while admitting count data it does. -/
def indexCost : LetterCost := fun _ _ a =>
  match a with
  | Sum.inl v => (v : ℝ)
  | Sum.inr _ => 0

@[simp] theorem indexCost_inl (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV) :
    indexCost B K (Sum.inl v) = (v : ℝ) := rfl

/-- **THEOREM (the index charge is not counts-only).**  At the two-vertex complex, the two
vertex letters are charged `0` and `1`, so no single function of the counts gives both. -/
theorem indexCost_not_chargesCountsOnly : ¬ ChargesCountsOnly indexCost := by
  rintro ⟨⟨fV, hV⟩, -, -⟩
  have h0 := hV 2 twoLoops ⟨0, by decide⟩
  have h1 := hV 2 twoLoops ⟨1, by decide⟩
  simp only [indexCost_inl] at h0 h1
  -- h0 : ((⟨0,_⟩ : Fin 2) : ℝ) = fV ...; h1 : ((⟨1,_⟩ : Fin 2) : ℝ) = fV ...
  have h0' : (0 : ℝ) = fV twoLoops.nV twoLoops.nE twoLoops.nT := by
    have := h0
    norm_num at this
    exact this
  have h1' : (1 : ℝ) = fV twoLoops.nV twoLoops.nE twoLoops.nT := by
    have := h1
    norm_num at this
    exact this
  rw [← h0'] at h1'
  norm_num at h1'

/-- **THEOREM (the named premise excludes the incidence countermodel).**  `ChargesCountsOnly`
rules out the incidence failure: a loop letter and a proper edge letter at the same sizes
(2,2,0) receive charges `0` and `t` from `incidenceCost`, and one function of the counts cannot
give both.  What it does NOT rule out is `pairCost`, which is counts-only; so the named premise
is not "the letter charge is trivial", it is "the letter charge reads nothing the alphabet does
not carry". -/
theorem chargesCountsOnly_excludes_incidence (t : ℝ) (ht : t ≠ 0) :
    ¬ ChargesCountsOnly (incidenceCost t) := by
  rintro ⟨-, ⟨fE, hE⟩, -⟩
  have hloop := hE 2 twoLoops ⟨0, by decide⟩
  have hbridge := hE 2 twoBridges ⟨0, by decide⟩
  simp only [incidenceCost_edge] at hloop hbridge
  -- loop edge: endpoints (0,0), so `if ... ≠ ... then t else 0` = 0
  -- bridge edge: endpoints (0,1), so the charge is t
  have hloop' : (0 : ℝ) = fE twoLoops.nV twoLoops.nE twoLoops.nT := by
    have := hloop
    norm_num [twoLoops] at this
    exact this
  have hbridge' : t = fE twoBridges.nV twoBridges.nE twoBridges.nT := by
    have := hbridge
    norm_num [twoBridges] at this
    exact this
  -- the two `fE` applications are at the same arguments (2,2,0)
  have hsame : fE twoLoops.nV twoLoops.nE twoLoops.nT
      = fE twoBridges.nV twoBridges.nE twoBridges.nT := rfl
  rw [hsame] at hloop'
  rw [← hbridge'] at hloop'
  exact ht hloop'.symm

/-- **THEOREM (pairCost is counts-only).**  The vertex-count charge reads only the vertex
count, so it satisfies the named premise.  This is the theorem that keeps the premise honest:
it does not say letters are uncharged, it says charges read the counts. -/
theorem pairCost_chargesCountsOnly : ChargesCountsOnly pairCost := by
  refine ⟨⟨fun nV _ _ => (nV : ℝ) - 1, ?_⟩, ⟨fun _ _ _ => 0, ?_⟩, ⟨fun _ _ _ => 0, ?_⟩⟩
  · intro B K v
    simp only [pairCost]
  · intro B K e
    rfl
  · intro B K τ
    rfl

/-- **THEOREM (kind rates are kind-only).**  A cost with constant per-kind letter rates across
all complexes is kind-only.  This is a restatement of `KindOnly` through its `KindRates`
definition, and the named premise plays no role in it: the three rate hypotheses are already
`KindRates`.  It is here so the module says explicitly, rather than implying, that the global
kind rule is the constant-function special case of the named premise; the closure into the
measure is then the second arc's `posting_cost_derives_mu`, cited and not re-proved.  The
earlier name of this theorem overclaimed a routing through `ChargesCountsOnly` and is
corrected. -/
theorem kindOnly_of_constant_rates (c : LetterCost)
    (cV cE cT : ℝ)
    (hV : ∀ (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV), c B K (Sum.inl v) = cV)
    (hE : ∀ (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE), c B K (Sum.inr (Sum.inl e)) = cE)
    (hT : ∀ (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT), c B K (Sum.inr (Sum.inr τ)) = cT) :
    KindOnly c :=
  ⟨cV, cE, cT, fun B K => ⟨hV B K, hE B K, hT B K⟩⟩

/-! ## §4. Navigation index

Flags only.  Two are deliberately `false`: the kind rule is not forced by the letter-cost
space, and whether the dual-entry lattice below it forces the named premise is open. -/

structure KindRuleIndex : Type where
  /-- The kind rule fails in the letter-cost space by counting alone (`pairCost`). -/
  kind_rule_fails_by_counting : Bool
  /-- The kind rule fails in the letter-cost space by incidence (`incidenceCost`). -/
  kind_rule_fails_by_incidence : Bool
  /-- The cost layer cannot see the dual-entry state space, so the canonicality pinning
  cannot be what excludes the countermodel. -/
  exclusion_not_from_pinning : Bool
  /-- What excludes the countermodel's weight from the measure is the gauge-divisor formula:
  the class mass is `exp(-2t)/|Aut|`, not `1/|Aut|`. -/
  exclusion_is_measure_formula : Bool
  /-- The named premise gives the per-complex totals form with count-dependent rates. -/
  premise_gives_kindTotals : Bool
  /-- The named premise excludes the incidence countermodel and admits the count charge. -/
  premise_discriminates : Bool
  /-- NOT proved, and refuted as a reading of the letter-cost space: the kind rule is forced
  there.  It is not, by two independent countermodels. -/
  kind_rule_forced : Bool
  /-- NOT proved: the successor question, whether the dual-entry lattice forces the named
  premise.  This module's theorems say the premise is statable at the alphabet and that the
  state space is invisible there, so the answer must come from the lattice's own structure. -/
  lattice_forces_premise : Bool

def kindRuleIndex : KindRuleIndex where
  kind_rule_fails_by_counting := true
  kind_rule_fails_by_incidence := true
  exclusion_not_from_pinning := true
  exclusion_is_measure_formula := true
  premise_gives_kindTotals := true
  premise_discriminates := true
  kind_rule_forced := false
  lattice_forces_premise := false

theorem index_kind_rule_not_forced : kindRuleIndex.kind_rule_forced = false := rfl

theorem index_lattice_question_open : kindRuleIndex.lattice_forces_premise = false := rfl

end

end Gap2KindRule
end SevenGaps
end Gravity
end IndisputableMonolith
