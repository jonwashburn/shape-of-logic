import IndisputableMonolith.Gravity.SevenGaps.Gap2DynamicsKindRule

/-!
# Gap 2, sixth arc: the pinned-carrier floor and the uniqueness wall

Track A1.2 of `QG/plans/QG_Full_Theory_Completion_20260729.html` asks whether
`GaugeCountingPrinciple` can be derived from substrate structure richer than counting at the
posting layer.  The committed answer is no, and this module makes the no precise with kernel
content, after a referee read forced the honest version of it.  The answer has three parts:
what the pinned carrier provably contains, the uniqueness theorem that does the real
excluding, and the one route nothing excludes, which is the premise itself.

**Part one: the pinned carrier, by design.**  `GaugeHistoryMeasure` builds counted histories
by pinning every history's dual-entry state to `balancedZeroState`, so that counted histories
are one per complex and the count does not inflate; the unpinned `PostedBoundedHistory` still
carries a free `DualEntryStrainState`.  §1 and §2 kernel-check what that design choice leaves:
on `CanonicalHistory` the count is exactly the complex count
(`canonical_count_eq_complex_count`), and every state-factored weight evaluated there is a
function of the complex alone (`state_factored_weight_is_complex_function`).  These are
theorems about the pinned carrier, not discoveries that the posting layer holds nothing.  The
free state exists one type up and the pin discards it; a derivation that routes through the
pinned counted carrier has only the complex to work with, and one that does not is in part
three.

**Part two: the uniqueness wall, which was already in the library.**  The theorem that
actually excludes a derivation is `Gap2GaugeVolume.invariant_weight_gives_measure_iff`: among
relabeling-invariant labeled weights on complexes, the gauge-counting principle holds of the
class mass if and only if the weight is exactly the Gibbs weight.  So with relabeling
invariance fixed, demanding the principle forces the weight to be the very Gibbs form whose
selection *is* the premise.  No relabeling-invariant enrichment can derive the principle from
anything, because invariance plus the principle leaves no degree of freedom.  The same wall
stands at the cost layer: `Gap2PostingCostDerivation.equivariant_posts_mu_iff_numerator_one`
says an equivariant letter cost posts `mu` exactly when its Boltzmann numerator is identically
one, so no equivariant cost contributes a factor either.

**Part three: the routes the wall does not touch, named exactly.**  Two routes are untouched
by §3, and the boundary claim is scoped to the weight-based classes the cited theorems
quantify over.  First, *premise-level* justifications of the Gibbs weight from a more basic
symmetry principle (indifference, exchangeability, maximum entropy): the wall forces any
relabeling-invariant weight satisfying the principle to *be* Gibbs, but says nothing about
deriving the Gibbs weight itself from something prior; that would be a reduction of the
premise, not a derivation from richer structure, and nothing here or in the library supplies
one.  Second, label-asymmetric structure, a cost or weight that distinguishes between
labelings of one complex: §4 exhibits one (`vertexIndexCost`, which charges by vertex index,
is not equivariant), so this route is inhabited.  A label-asymmetric derivation of the
principle would still have to *justify* label indifference rather than assume it, and label
indifference, each labeling counted once, equivalently the Gibbs weight `1/(nV! nE! nT!)`, is
the premise the measure rests on.  The library's cost arcs name the asymmetric case as the
non-equivariant case, which remains open.

**The A1.2 verdict.**  On the pinned carrier there is nothing richer than the complex to
derive from.  For relabeling-invariant enrichments and equivariant posting costs, uniqueness
excludes every derivation of the principle from anything but the principle.  The untouched
routes are premise-level justifications of label indifference, symmetric or asymmetric; none
is supplied.  Combined with the fifth arc (the dynamics forces no charge restriction), the
measure now rests on one named physical premise, label indifference, and the frontier that
could discharge it is a derivation from a prior symmetry principle or from the actual posting
schedule nature executes, the same schedule the fifth arc named.

## Honest tagging

§1, §2 and §4 are THEOREM (kernel-checked in this module).  §3 re-stands existing THEOREMs
under names that say what they exclude here.  The `1/(nV! nE! nT!)` gauge volume is THEOREM
(`pairCount_eq_factorials`), and orbit-stabilizer accounting is THEOREM
(`orbitCard_mul_autCard`), recorded in §5 so the one factor the measure carries beyond
counting is visible as a theorem rather than a premise.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2PostingLayerFloor

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation Gap2KindRule
open Gap2LatticeKindRule Gap2DynamicsKindRule
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## §1. On the pinned carrier, counting is complex counting

The pinned carrier `CanonicalHistory` is a *design choice* of the measure construction: the
state is fixed to `balancedZeroState` so counted histories are one per complex.  The collapse
this produces was first recorded as `Gap2MeasureStatusBinding.historyCarrier_equiv_plainCarrier`;
this section kernel-checks its cardinal form, which is the form the floor needs. -/

/-- **THEOREM (pinned counting is complex counting).**  The number of pinned bounded histories
at bound `B` equals the number of bounded complexes at bound `B`.  Content: after the design
pin `state = balancedZeroState`, the counted history carries exactly the complex; the
dual-entry enrichment contributes no factor to the count.  Scope: this is a theorem about
`CanonicalHistory`, not about the unpinned `PostedBoundedHistory`, which still carries a free
state. -/
theorem canonical_count_eq_complex_count (B : ℕ) :
    Nat.card (GaugeHistoryMeasure.CanonicalHistory B) = Nat.card (BoundedComplex B) := by
  exact Nat.card_congr (GaugeHistoryMeasure.CanonicalHistory.equivUnderlying)

/-! ## §2. On the pinned carrier, state-factored weights are functions of the complex -/

/-- **THEOREM (state-factored weights collapse on the pinned carrier).**  If a weight on
histories factors as `F K s` (complex, state), then evaluated on the pinned carrier it equals
`g K` for a function of the complex alone: `F CH.underlying CH.H.state = g CH.underlying`,
because the pin forces `CH.H.state = balancedZeroState _`.  Scope: the collapse happens *on
`CanonicalHistory`*, where `state_canonical` pins `s`; it says nothing about weights on the
unpinned carrier.  Any derivation of the counting principle that routes through the pinned
counted carrier therefore receives nothing state-dependent from the posting layer; what it can
receive from the unpinned carrier is §4's question. -/
theorem state_factored_weight_is_complex_function {B : ℕ}
    (F : ∀ (K : BoundedComplex B), DualEntryStrainState (PostingAlphabet K) → ℝ) :
    ∃ g : BoundedComplex B → ℝ, ∀ CH : GaugeHistoryMeasure.CanonicalHistory B,
      F CH.underlying CH.H.state = g CH.underlying := by
  refine ⟨fun K => F K (balancedZeroState _), fun CH => ?_⟩
  exact congrArg (F CH.underlying) CH.state_canonical

/-- **THEOREM (the pinned fiber is constant).**  Two pinned histories over the same underlying
complex are equal: the posted history carries only the complex and the state, the states are
both pinned, and the pinning proofs agree by proof irrelevance.  So the fiber of the pinning
over a complex is a subsingleton.  Scope: constancy holds because the pin makes it hold, which
is the design of `CanonicalHistory`, not a property discovered about the posting layer. -/
theorem canonical_state_fiber_constant {B : ℕ}
    (CH₁ CH₂ : GaugeHistoryMeasure.CanonicalHistory B)
    (h : CH₁.underlying = CH₂.underlying) : CH₁ = CH₂ := by
  obtain ⟨⟨K₁, s₁⟩, hc₁⟩ := CH₁
  obtain ⟨⟨K₂, s₂⟩, hc₂⟩ := CH₂
  change K₁ = K₂ at h
  subst h
  have hs : s₁ = s₂ := hc₁.trans hc₂.symm
  subst hs
  rfl

/-! ## §3. The uniqueness wall: invariant enrichments cannot derive the principle

The theorems in this section are not new; they are the load-bearing exclusions, re-stood under
names that say what they exclude for this arc.  The referee's point is accepted: §1 and §2
alone would only show the pinned carrier is empty, leaving every unpinned route open.  These
two theorems close the relabeling-invariant and equivariant routes outright. -/

/-- **THEOREM (the uniqueness wall, Gap2GaugeVolume re-stood).**  Among relabeling-invariant
labeled weights on complexes, the gauge-counting principle holds of the class mass if and only
if the weight is the Gibbs weight pointwise.  Consequence for the derivation demand: with
relabeling invariance fixed, asking for the principle leaves no degree of freedom, so no
invariant enrichment can derive the principle from anything more primitive; the principle and
the Gibbs premise are the same assumption stated twice. -/
theorem invariant_enrichment_unique_gibbs (B : ℕ) (w : BoundedComplex B → ℝ)
    (hinv : ∀ K K', Equivalent K K' → w K = w K') :
    MeasureSubstrateBlocker.GaugeCountingPrinciple (classMass w) ↔
      ∀ K : BoundedComplex B, w K = gibbsWeight K :=
  invariant_weight_gives_measure_iff w hinv

/-- **THEOREM (the uniqueness wall at the cost layer, Gap2PostingCostDerivation re-stood).**
An equivariant letter cost posts `mu` at bound `B` exactly when its Boltzmann numerator is
identically one.  Consequence for the derivation demand: no equivariant posting cost can
contribute a factor to the measure, whatever premise picks the cost out; asking an equivariant
cost for `mu` is asking for the Gibbs weight back.  The non-equivariant case is not covered
here and is §4. -/
theorem equivariant_cost_contributes_no_factor {c : LetterCost} (hc : Equivariant c) (B : ℕ) :
    (∀ K : BoundedComplex B,
        classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ↔ ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1 :=
  equivariant_posts_mu_iff_numerator_one hc B

/-! ## §4. The asymmetric route the wall does not touch, exhibited

The wall of §3 quantifies over relabeling-invariant weights and equivariant costs.  Its
complement within the letter-cost class is the label-asymmetric costs, and for the no-go to
be honest about its own boundary that complement must be shown inhabited: there must exist a
letter cost that is *not* equivariant.  This section exhibits the simplest one, a cost that
reads the vertex label itself, and refutes its equivariance with a vertex swap on a complex
whose incidence conditions are vacuous.  A second untouched route, premise-level derivations
of the Gibbs weight from symmetric first principles, is not a letter-cost class at all and is
disclosed in the header rather than exhibited. -/

/-- Two isolated vertices, no edges or tetrahedra: sizes `(2,0,0)`.  Every vertex bijection is
a relabeling of this complex because the incidence conditions are vacuous, which makes it the
cheapest place to exhibit label-asymmetry. -/
def twoIsoVerts : BoundedComplex 2 where
  nV := 2
  nE := 0
  nT := 0
  hV := le_refl 2
  hE := Nat.zero_le 2
  hT := Nat.zero_le 2
  edgeVerts := fun e => e.elim0
  tetVerts := fun t => t.elim0

/-- The vertex swap as a self-relabeling of `twoIsoVerts`.  The edge and tet conditions are
vacuous (`Fin 0`), so the swap needs no incidence compatibility. -/
def twoIsoVertsSwap : Relabel twoIsoVerts twoIsoVerts where
  vEquiv := Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩
  eEquiv := Equiv.refl _
  tEquiv := Equiv.refl _
  edge_comm := fun e => e.elim0
  tet_comm := fun t => t.elim0

/-- The vertex-index cost: charge each vertex letter its index as a real, charge edge and
tetrahedron letters nothing.  It reads the label, so it is the simplest letter cost that is
not gauge-equivariant. -/
def vertexIndexCost : LetterCost := fun _ _ a =>
  match a with
  | Sum.inl v => ((v : ℕ) : ℝ)
  | _ => 0

/-- **THEOREM (label-asymmetric costs exist).**  The vertex-index cost is not equivariant:
transporting vertex letter `0` along the swap gives vertex letter `1`, whose cost is `1 ≠ 0`.
So the class §3 does not cover is inhabited, and the one route the wall leaves open, a
label-asymmetric derivation of label indifference, is a route through real objects, not
through an empty type. -/
theorem vertexIndexCost_not_equivariant : ¬ Equivariant vertexIndexCost := by
  intro h
  have h1 := h 2 twoIsoVerts twoIsoVerts twoIsoVertsSwap (Sum.inl ⟨0, by decide⟩)
  have htransport : postingAlphEquiv twoIsoVertsSwap.vEquiv twoIsoVertsSwap.eEquiv
      twoIsoVertsSwap.tEquiv (Sum.inl ⟨0, by decide⟩) = Sum.inl (⟨1, by decide⟩ : Fin 2) := by
    show Sum.inl (Equiv.swap ⟨0, by decide⟩ (⟨1, by decide⟩ : Fin 2) ⟨0, by decide⟩) = _
    rw [Equiv.swap_apply_left]
  rw [htransport] at h1
  norm_num [vertexIndexCost] at h1

/-- **THEOREM (the asymmetric case is inhabited).**  There exists a letter cost that is not
gauge-equivariant.  This is the honesty clause of the no-go: within the letter-cost class, the
structure the uniqueness wall does not cover is label-asymmetric structure, and such structure
exists.  What does not currently exist is a label-asymmetric derivation of label indifference;
that is the named open case.  The second untouched route, premise-level derivations of the
Gibbs weight from symmetric first principles, is outside the letter-cost class and is
disclosed in the module header. -/
theorem label_asymmetric_structure_exists : ∃ c : LetterCost, ¬ Equivariant c :=
  ⟨vertexIndexCost, vertexIndexCost_not_equivariant⟩

/-! ## §5. The one factor beyond counting, as a theorem -/

/-- **THEOREM (orbit-stabilizer, re-stood).**  The gauge orbit card of a complex times the
cardinality of its automorphism group is the label count `nV! * (nE! * nT!)`.  Recorded here
so the accounting the measure relies on is visible as a theorem of the library, not a premise:
the label count and the orbit count are both computed, and what the measure selects among the
results is the premise named in §6. -/
theorem irreducible_input_is_orbit_stabilizer {B : ℕ} (K : BoundedComplex B) :
    gaugeOrbitCard K * Nat.card (Aut K)
      = K.nV.factorial * (K.nE.factorial * K.nT.factorial) :=
  Gap2GaugeVolume.orbitCard_mul_autCard K

/-! ## §6. The floor, the verdict, and the index -/

/-- **THEOREM (the posting-layer floor, reframed).**  The five-part verdict of this arc at
bound `B`:

1.  On the pinned carrier, counting is complex counting.
2.  On the pinned carrier, every state-factored weight is a function of the complex.
3.  Among relabeling-invariant labeled weights, the counting principle forces the Gibbs
    weight, so no invariant enrichment derives the principle from anything more primitive.
4.  No equivariant posting cost contributes a factor to the measure.
5.  Label-asymmetric costs exist: the asymmetric route the wall does not touch is inhabited.

What the conjunction does not contain: any claim that the posting layer as a whole holds
nothing (the unpinned carrier carries a free state, and the fifth arc showed the dynamics
imposes no charge restriction); any claim that premise-level derivations of the Gibbs weight
from symmetric first principles (indifference, exchangeability, maximum entropy) are excluded,
because they are not and the wall is silent on premise reduction; any claim that the open
routes are closed (a label-asymmetric derivation of label indifference is neither exhibited
nor refuted here); and any completeness claim beyond the weight-based classes the cited
theorems quantify over.  The measure's remaining premise is exactly label indifference. -/
theorem posting_layer_floor (B : ℕ) :
    (Nat.card (GaugeHistoryMeasure.CanonicalHistory B) = Nat.card (BoundedComplex B)) ∧
    (∀ F : ∀ (K : BoundedComplex B), DualEntryStrainState (PostingAlphabet K) → ℝ,
      ∃ g : BoundedComplex B → ℝ, ∀ CH : GaugeHistoryMeasure.CanonicalHistory B,
        F CH.underlying CH.H.state = g CH.underlying) ∧
    (∀ w : BoundedComplex B → ℝ, (∀ K K', Equivalent K K' → w K = w K') →
      (MeasureSubstrateBlocker.GaugeCountingPrinciple (classMass w) ↔
        ∀ K : BoundedComplex B, w K = gibbsWeight K)) ∧
    (∀ c : LetterCost, Equivariant c →
      ((∀ K : BoundedComplex B,
          classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K) ↔
        ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1)) ∧
    (∃ c : LetterCost, ¬ Equivariant c) :=
  ⟨canonical_count_eq_complex_count B,
   fun F => ⟨fun K => F K (balancedZeroState _),
     fun CH => congrArg (F CH.underlying) CH.state_canonical⟩,
   invariant_enrichment_unique_gibbs B,
   fun _c hc => equivariant_cost_contributes_no_factor hc B,
   label_asymmetric_structure_exists⟩

/-- The index of the sixth arc.  Every flag is a Prop proved or refuted in `index_audit` from
the theorems of this module; nothing is assigned by fiat.  `premise_named_at` is documentation,
a pointer to where the measure's one remaining premise lives, and the audit does not check it
because it is a name, not a claim. -/
structure Index where
  pinned_carrier_count_is_complex_count : Prop
  pinned_state_fiber_is_constant : Prop
  invariant_enrichment_unique_gibbs : Prop
  equivariant_cost_contributes_no_factor : Prop
  label_asymmetric_structure_exists : Prop
  premise_named_at : String

def index : Index where
  pinned_carrier_count_is_complex_count :=
    ∀ B : ℕ, Nat.card (GaugeHistoryMeasure.CanonicalHistory B) = Nat.card (BoundedComplex B)
  pinned_state_fiber_is_constant :=
    ∀ {B : ℕ} (CH₁ CH₂ : GaugeHistoryMeasure.CanonicalHistory B),
      CH₁.underlying = CH₂.underlying → CH₁ = CH₂
  invariant_enrichment_unique_gibbs :=
    ∀ (B : ℕ) (w : BoundedComplex B → ℝ), (∀ K K', Equivalent K K' → w K = w K') →
      (MeasureSubstrateBlocker.GaugeCountingPrinciple (classMass w) ↔
        ∀ K : BoundedComplex B, w K = gibbsWeight K)
  equivariant_cost_contributes_no_factor :=
    ∀ (c : LetterCost), Equivariant c → ∀ B : ℕ,
      ((∀ K : BoundedComplex B,
          classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K) ↔
        ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1)
  label_asymmetric_structure_exists := ∃ c : LetterCost, ¬ Equivariant c
  premise_named_at := "label indifference (Gibbs weight 1/(nV! nE! nT!)); only a label-asymmetric derivation could discharge it"

/-- The audit pinning every index flag to its theorem. -/
theorem index_audit : index.pinned_carrier_count_is_complex_count ∧
    index.pinned_state_fiber_is_constant ∧
    index.invariant_enrichment_unique_gibbs ∧
    index.equivariant_cost_contributes_no_factor ∧
    index.label_asymmetric_structure_exists := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B
    exact canonical_count_eq_complex_count B
  · intro B CH₁ CH₂ h
    exact canonical_state_fiber_constant CH₁ CH₂ h
  · intro B w hinv
    exact invariant_enrichment_unique_gibbs B w hinv
  · intro c hc B
    exact equivariant_cost_contributes_no_factor hc B
  · exact label_asymmetric_structure_exists

end

#print axioms canonical_count_eq_complex_count
#print axioms state_factored_weight_is_complex_function
#print axioms canonical_state_fiber_constant
#print axioms invariant_enrichment_unique_gibbs
#print axioms equivariant_cost_contributes_no_factor
#print axioms vertexIndexCost_not_equivariant
#print axioms label_asymmetric_structure_exists
#print axioms irreducible_input_is_orbit_stabilizer
#print axioms posting_layer_floor
#print axioms index_audit

end Gap2PostingLayerFloor
end SevenGaps
end Gravity
end IndisputableMonolith
