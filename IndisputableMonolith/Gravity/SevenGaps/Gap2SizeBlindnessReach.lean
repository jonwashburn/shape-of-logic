import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingDerivation
import IndisputableMonolith.Gravity.SevenGaps.GaugeHistoryMeasure

/-!
# Gap 2: how far the gluing premise reaches, and why the posting layer cannot close it

`Gap2GluingDerivation` derives the class measure from two premises plus three normalizations.
The premises:

* **(i) size-blindness**, the labeled weight depends only on the three index sizes;
* **(ii) gluing multiplicativity**, class mass multiplies over disjoint unions at pairs
  where the automorphism count multiplies.

The normalizations, assumed by the final theorem `CarrierShuffle.gibbs_of_unit_fugacities` on
top of the premises: the size function is `1` at the three **atoms** `(1,0,0)`, `(1,1,0)` and
`(1,0,1)`, the single vertex, the single loop, the single degenerate tetrahedron.  Without them
premise (i) and premise (ii) leave three free positive constants
(`residue_is_exactly_three_positive_constants`).

Its deflation theorem (`classMass_sizeWeight_eq_fugacity_div_autCard`) showed that premise (i)
alone already produces the symmetry factor `q(s)/|Aut K|`.  Premise (i) is assumed.  This module
attacks it and reports two results, one positive and one negative.

## §1-§3, the reach bound: the other five hypotheses do not imply premise (i)

An **additive incidence statistic** is a natural-valued function of a complex that is
relabeling-invariant, adds over disjoint unions, and vanishes on the empty complex.  The three
index sizes qualify.  So do two functions of the incidence data: the **loop count**, the number
of edges whose endpoints coincide, and the **proper-edge count**, the number whose endpoints
differ.  §1 defines both and §2 proves both additive.

For any such statistic and any positive real `lam`, the weight `lam ^ (stat K) / (nV! nE! nT!)`
is relabeling-invariant, strictly positive, unit on the empty complex, and satisfies premise (ii)
at every pair whose automorphism counts multiply, hence at each of the four families the
derivation's `CarrierShuffle` premise is stated at (`all_four_families_available` discharges the
hypothesis for all four; `statWeight_glues_at_dust_edge` instantiates the one with no side
condition).  No binomial correction appears, because the statistic adds exactly where the
automorphism count multiplies.  Its class mass is `lam ^ (stat K) / |Aut K|`, so it leaves the
symmetry factor untouched and multiplies it by `lam ^ stat`.

The three normalizations then decide *which* statistic survives, and this is the sharpest thing
in §3.  They kill the loop-count escape, because the single loop has loop count one, so that
escape's weight there is `lam` (`loopEscape_fails_the_atoms`).  They do not touch the proper-edge
escape, whose statistic vanishes on every single-vertex complex, atoms included
(`properEdgeCount_eq_zero_of_nV_le_one`).  So the normalizations are not idle, and they are also
not enough.

The proper-edge escape at any positive `lam ≠ 1` therefore satisfies invariance, positivity, unit
on the empty complex, unit at all three atoms, and premise (ii) at every eligible pair, is not
size-blind, and its class mass at the two-bridge class is `lam²/|Aut|` against the measure's
`1/|Aut|` (`size_blindness_not_forced_by_the_other_hypotheses`).  Both witnesses sit at sizes
`(2,2,0)`; at `lam = 1` the escape is the Gibbs weight and *is* size-blind
(`statWeight_sizeBlind_at_one`, at every statistic, so it controls the proper-edge escape and not
only the loop-count one), so the separation is a property of the tilt and not of a malformed
construction.

**Scope.**  Premise (i) is load-bearing for the conclusion, not merely for the shape of the
argument.  This does not say premise (ii) is empty; the sharper statement of that is the
derivation module's own `gluing_alone_does_not_force_mu`.  The reach bound is stated against
premise (ii) in its restricted form, at eligible pairs; the escape fails the unrestricted
predicate `GluesGenerally` (`statWeight_not_gluesGenerally`), and so does the RS measure, which
is the same theorem at `lam = 1` and the reason the derivation could not have assumed the
unrestricted form.  Unrestricted gluing is not inconsistent on its own, since
`uniform_gluesGenerally` satisfies it; what `unrestricted_gluing_inconsistent` refutes is its
conjunction with the four restricted equations for a positive size-blind weight.  Nor is "the
pairs where automorphism counts multiply" a characterization of eligibility; no such
characterization exists in the library.

This compiles a refutation carried only in prose since the 2026-07-28 panel killed the
cluster-decomposition route: an exponential in an additive incidence statistic escapes the
premise-(ii) side of the derivation, for *every* such statistic.  Against the full hypothesis
bundle the claim is narrower and the normalizations are why: only statistics vanishing at the
three atoms survive, which the loop count does not (`loopEscape_fails_the_atoms`) and the
proper-edge count does.

## §4-§6, the negative result: no indistinguishability premise is both weaker and sufficient

`GaugeHistoryMeasure.PostingAlphabet K` is `Fin K.nV ⊕ Fin K.nE ⊕ Fin K.nT`: the substrate
posts one letter per cell, sorted into three kinds, and none per incidence.  It was defined
for the posted-history presentation, not for this argument.  The natural hope is that premise
(i) is what that alphabet says, so that the premise moves from the measure to the substrate.

§4 makes the hope precise, against the library object itself, and §5 proves it in both
directions: a weight is `sizeWeight f` for some size function `f` exactly when it is blind to
everything but the posting alphabet read with its sorting into cell kinds
(`premise_one_iff_alphabetBlind`).

§6 kills the hope and then generalizes the reason.  The alphabet is a *function of* the size
triple (`postingAlphabet_is_determined_by_the_sizes`): two complexes with the same three
counts have sort-respecting equivalent posting alphabets no matter how their cells are wired,
the two witnesses of §3 among them.  So the alphabet carries no information about incidence to
begin with, and the equivalence of §5 is a reformulation rather than a derivation.

The general form is a single equivalence, `blindness_forces_premise_one_iff_coarse`: blindness to an
invariant forces premise (i) for every weight **exactly when** that invariant never separates two
complexes with the same three counts.  The two directions are the two horns
(`coarse_invariant_blindness_implies_sizeBlind`,
`fine_invariant_blindness_does_not_imply_sizeBlind`, exhaustive by `invariant_coarse_or_fine`, and
available separately as `indistinguishability_premises_never_weaken_premise_one` for the fine
witness).  On the coarse side blindness already implies premise (i), so nothing was weakened.  On
the fine side it does not, witnessed by a strictly positive two-valued weight that is also
relabeling-invariant whenever the invariant is.  Neither horn assumes invariance, so the coverage
has no gap at label-sensitive readouts, and both are general rather than instantiated.

At one fine invariant the failure survives the whole rest of the hypothesis set: the invariant
reading the three counts together with the proper-edge count, where the escape of §3 is blind to
it, satisfies all five remaining hypotheses, is not size-blind, and has the wrong class mass
(`fine_horn_survives_the_other_hypotheses`).  That is one invariant, chosen to contain the escape's
own statistic, and not a statement about the fine side in general.

**What this licenses.**  No premise of the form *the weight cannot distinguish complexes that agree
on `X`* is both strictly weaker than premise (i) and sufficient for it: if it is sufficient then `X`
is coarse, and blindness to a coarse `X` already implies premise (i).  It does not license the
converse, so blindness to `X` and premise (i) are not interchangeable; the coarse side contains
conditions strictly stronger than premise (i) and `unsorted_is_strictly_stronger` is one.  So the hope
this module started from, that the substrate supplies premise (i) by not resolving incidence, is
closed.  The posting alphabet lands on the coarse side, which is why pointing at it does not help.
The coarse side is not a single point: blindness to the total cell count lands there and is strictly
stronger,
so much so that it contradicts the derivation's own conclusion
(`unsorted_is_strictly_stronger`), which is why "premise (i) renamed" would be the wrong reading of
the coarse side.

**What it does not license, stated so no reader has to find it.**  Four things.  It does not prove
premise (i) needs a premise from outside this family, since the equivalence quantifies over one
blindness premise and not over conjunctions or over derivations.  It does not rule out that some
fine invariant *other* than the one instantiated might, conjoined with the five remaining
hypotheses, force premise (i); that conjunction is restrictive and the question is open.  The fine
horn's general witness carries only positivity and invariance, not the normalizations or gluing.
And no theorem here is about what a substrate posts or resolves; the substrate language throughout
is motivation for which mathematical questions were asked.  The conjecture the module leaves, tagged
as conjecture: the premise has to come from structure that is not a function of the complex, a cost
or a dynamics that assigns the weight rather than a symmetry that fails to separate it.  §8 of the
plan and the companion module `Gap2PostingCostDerivation` act on that conjecture.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2SizeBlindnessReach

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation

/-! ## §1. An incidence statistic on the bounded carrier

`Gap2EnrichedCarrierPhase.selfLoopCount` is the same statistic on the exact-signature
carrier `ExactComplex v e t`.  The path-sum measure lives on `BoundedComplex B`, so the
statistic has to be recreated here; the invariance argument is the same one. -/

variable {B B' : ℕ}

/-- The number of edges of `K` whose two endpoints coincide.  A function of the incidence
data that is *not* a function of the three index sizes. -/
def loopCount (K : BoundedComplex B) : ℕ :=
  (Finset.univ.filter (fun i : Fin K.nE => (K.edgeVerts i).1 = (K.edgeVerts i).2)).card

theorem loopCount_eq_sum (K : BoundedComplex B) :
    loopCount K
      = ∑ i : Fin K.nE, (if (K.edgeVerts i).1 = (K.edgeVerts i).2 then 1 else 0) := by
  unfold loopCount
  rw [Finset.card_filter]

/-- A relabeling carries loop edges to loop edges, because it acts on endpoints by an
injection. -/
theorem loop_iff_of_relabel {K K' : BoundedComplex B} (r : Relabel K K') (i : Fin K.nE) :
    ((K.edgeVerts i).1 = (K.edgeVerts i).2)
      ↔ ((K'.edgeVerts (r.eEquiv i)).1 = (K'.edgeVerts (r.eEquiv i)).2) := by
  rw [r.edge_comm i]
  simp only [Prod.map_fst, Prod.map_snd]
  exact (r.vEquiv.injective.eq_iff).symm

/-- **THEOREM (the loop count is a class function).**  Relabeling-invariant, so it descends
to relabeling classes, exactly as the three index sizes do. -/
theorem loopCount_congr {K K' : BoundedComplex B} (r : Relabel K K') :
    loopCount K = loopCount K' := by
  classical
  unfold loopCount
  refine Finset.card_bij (fun i _ => r.eEquiv i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (loop_iff_of_relabel r i).mp hi
  · intro i _ j _ h
    exact r.eEquiv.injective h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨r.eEquiv.symm j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := (loop_iff_of_relabel r (r.eEquiv.symm j)).mpr
    simpa using this (by simpa using hj)

theorem loopCount_invariant {K K' : BoundedComplex B} (h : Equivalent K K') :
    loopCount K = loopCount K' := by
  obtain ⟨r⟩ := h
  exact loopCount_congr r

/-! ## §2. The loop count adds over disjoint unions

This is what lets the escape weight satisfy premise (ii) with no correction: the statistic
is additive exactly where the automorphism count is multiplicative. -/

theorem inlV_inj {m n : ℕ} {a b : Fin m} (h : (inlV a : Fin (m + n)) = inlV b) : a = b :=
  Sum.inl_injective (finSumFinEquiv.injective h)

theorem inrV_inj {m n : ℕ} {a b : Fin n} (h : (inrV a : Fin (m + n)) = inrV b) : a = b :=
  Sum.inr_injective (finSumFinEquiv.injective h)

@[simp] theorem dunion_edgeVerts_inl (K : BoundedComplex B) (L : BoundedComplex B')
    (e : Fin K.nE) :
    (dunion K L).edgeVerts (finSumFinEquiv (Sum.inl e))
      = (inlV (K.edgeVerts e).1, inlV (K.edgeVerts e).2) := by
  simp [dunion]

@[simp] theorem dunion_edgeVerts_inr (K : BoundedComplex B) (L : BoundedComplex B')
    (e : Fin L.nE) :
    (dunion K L).edgeVerts (finSumFinEquiv (Sum.inr e))
      = (inrV (L.edgeVerts e).1, inrV (L.edgeVerts e).2) := by
  simp [dunion]

/-- **THEOREM (the loop count is additive over disjoint unions).** -/
theorem loopCount_dunion (K : BoundedComplex B) (L : BoundedComplex B') :
    loopCount (dunion K L) = loopCount K + loopCount L := by
  classical
  rw [loopCount_eq_sum, loopCount_eq_sum, loopCount_eq_sum]
  have h1 : (∑ i : Fin (dunion K L).nE,
        (if ((dunion K L).edgeVerts i).1 = ((dunion K L).edgeVerts i).2 then 1 else 0))
      = ∑ s : Fin K.nE ⊕ Fin L.nE,
          (if ((dunion K L).edgeVerts (finSumFinEquiv s)).1
              = ((dunion K L).edgeVerts (finSumFinEquiv s)).2 then 1 else 0) :=
    (Fintype.sum_equiv finSumFinEquiv _ _ (fun _ => rfl)).symm
  rw [h1, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [dunion_edgeVerts_inl]
    by_cases hc : (K.edgeVerts e).1 = (K.edgeVerts e).2
    · simp [hc]
    · simp only [if_neg hc]
      rw [if_neg (fun h => hc (inlV_inj h))]
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [dunion_edgeVerts_inr]
    by_cases hc : (L.edgeVerts e).1 = (L.edgeVerts e).2
    · simp [hc]
    · simp only [if_neg hc]
      rw [if_neg (fun h => hc (inrV_inj h))]

theorem loopCount_emptyComplex (B : ℕ) : loopCount (emptyComplex B) = 0 := by
  simp [loopCount, emptyComplex]

/-! ### A second statistic, which survives the three unit normalizations

The derivation's final step assumes more than the two premises.
`Gap2GluingDerivation.CarrierShuffle.gibbs_of_unit_fugacities` also assumes the size function
is `1` at the three **atoms** `(1,0,0)`, `(1,1,0)` and `(1,0,1)`: the single vertex, the single
loop, the single degenerate tetrahedron.  Translated off the size function and onto a labeled
weight, that says the weight is `1` at every complex with one vertex and at most one incidence.

Those three normalizations kill the loop-count escape, since the single loop has loop count one
(`loopEscape_fails_the_atoms`).  That is a real strength measurement: the normalizations are not
idle.  They do not kill the mechanism.  The number of edges whose endpoints *differ* is also an
additive incidence statistic, it vanishes at every complex with one vertex, and it still
separates the two witnesses of §3, in the other direction. -/

/-- The number of edges of `K` whose two endpoints differ.  Like `loopCount` this is a function
of the incidence data and not of the three sizes; unlike `loopCount` it vanishes at every
complex with a single vertex, which is what the three unit normalizations require. -/
def properEdgeCount (K : BoundedComplex B) : ℕ :=
  (Finset.univ.filter (fun i : Fin K.nE => (K.edgeVerts i).1 ≠ (K.edgeVerts i).2)).card

theorem properEdgeCount_eq_sum (K : BoundedComplex B) :
    properEdgeCount K
      = ∑ i : Fin K.nE, (if (K.edgeVerts i).1 ≠ (K.edgeVerts i).2 then 1 else 0) := by
  unfold properEdgeCount
  rw [Finset.card_filter]

theorem properEdgeCount_congr {K K' : BoundedComplex B} (r : Relabel K K') :
    properEdgeCount K = properEdgeCount K' := by
  classical
  unfold properEdgeCount
  refine Finset.card_bij (fun i _ => r.eEquiv i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun hc => hi ((loop_iff_of_relabel r i).mpr hc)
  · intro i _ j _ h
    exact r.eEquiv.injective h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨r.eEquiv.symm j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hc
    exact hj (by simpa using (loop_iff_of_relabel r (r.eEquiv.symm j)).mp hc)

theorem properEdgeCount_invariant {K K' : BoundedComplex B} (h : Equivalent K K') :
    properEdgeCount K = properEdgeCount K' := by
  obtain ⟨r⟩ := h
  exact properEdgeCount_congr r

@[simp] theorem inlV_eq_iff {m n : ℕ} {a b : Fin m} :
    (inlV a : Fin (m + n)) = inlV b ↔ a = b :=
  ⟨inlV_inj, fun h => by rw [h]⟩

@[simp] theorem inrV_eq_iff {m n : ℕ} {a b : Fin n} :
    (inrV a : Fin (m + n)) = inrV b ↔ a = b :=
  ⟨inrV_inj, fun h => by rw [h]⟩

/-- **THEOREM (the proper-edge count is additive over disjoint unions).** -/
theorem properEdgeCount_dunion (K : BoundedComplex B) (L : BoundedComplex B') :
    properEdgeCount (dunion K L) = properEdgeCount K + properEdgeCount L := by
  classical
  rw [properEdgeCount_eq_sum, properEdgeCount_eq_sum, properEdgeCount_eq_sum]
  have h1 : (∑ i : Fin (dunion K L).nE,
        (if ((dunion K L).edgeVerts i).1 ≠ ((dunion K L).edgeVerts i).2 then 1 else 0))
      = ∑ s : Fin K.nE ⊕ Fin L.nE,
          (if ((dunion K L).edgeVerts (finSumFinEquiv s)).1
              ≠ ((dunion K L).edgeVerts (finSumFinEquiv s)).2 then 1 else 0) :=
    (Fintype.sum_equiv finSumFinEquiv _ _ (fun _ => rfl)).symm
  rw [h1, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [dunion_edgeVerts_inl]
    simp
  · refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [dunion_edgeVerts_inr]
    simp

/-- **THEOREM (the proper-edge count vanishes on every single-vertex complex).**  With one
vertex there is nothing for an edge's two endpoints to differ between.  This is what makes the
escape built from it satisfy the three unit normalizations. -/
theorem properEdgeCount_eq_zero_of_nV_le_one (K : BoundedComplex B) (h : K.nV ≤ 1) :
    properEdgeCount K = 0 := by
  classical
  unfold properEdgeCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp only [ne_eq, not_not]
  have h1 : ((K.edgeVerts i).1 : ℕ) < 1 := lt_of_lt_of_le (K.edgeVerts i).1.isLt h
  have h2 : ((K.edgeVerts i).2 : ℕ) < 1 := lt_of_lt_of_le (K.edgeVerts i).2.isLt h
  exact Fin.ext (by omega)

theorem properEdgeCount_emptyComplex (B : ℕ) : properEdgeCount (emptyComplex B) = 0 :=
  properEdgeCount_eq_zero_of_nV_le_one _ (by simp [emptyComplex])

/-! ## §3. The escape mechanism, and the reach bound -/

/-- An **additive incidence statistic**: a natural-valued function of a complex that is
relabeling-invariant, adds over disjoint unions, and vanishes on the empty complex.

The three index sizes satisfy this, and so does the loop count, which is why this is the
exact level of generality at which the restricted gluing premise fails to force premise (i):
the premise sees the additivity and cannot see whether the statistic reads incidence. -/
structure AdditiveStat where
  stat : ∀ B : ℕ, BoundedComplex B → ℕ
  invariant : ∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → stat B K = stat B K'
  additive : ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    stat (B + B') (dunion K L) = stat B K + stat B' L
  vanishes : ∀ B : ℕ, stat B (emptyComplex B) = 0

/-- The loop count is an additive incidence statistic.  It ignores the cap argument, so the
escape built from it is a single function of a complex and not a cap-indexed family. -/
def loopStat : AdditiveStat where
  stat := fun _ K => loopCount K
  invariant := fun _ _ _ h => loopCount_invariant h
  additive := fun _ _ K L => loopCount_dunion K L
  vanishes := fun B => loopCount_emptyComplex B

/-- The proper-edge count is an additive incidence statistic. -/
def properStat : AdditiveStat where
  stat := fun _ K => properEdgeCount K
  invariant := fun _ _ _ h => properEdgeCount_invariant h
  additive := fun _ _ K L => properEdgeCount_dunion K L
  vanishes := fun B => properEdgeCount_emptyComplex B

/-- The **escape weight** of a statistic: the inverse gauge volume tilted by an exponential in that
statistic.  At `lam = 1` this is `gibbsWeight` and is size-blind.

At other positive `lam` what holds depends on the statistic, and the general facts are only the
four proved below: invariance, positivity, unit on the empty complex, and premise (ii) at every
eligible pair.  Whether it is size-blind, and whether it is unit at the three atoms, are both
properties of the particular statistic.  A statistic that is constant leaves the weight size-blind;
`loopStat` fails the atoms (`loopEscape_fails_the_atoms`); `properStat` fails size-blindness while
satisfying the atoms, which is the combination the reach bound needs. -/
noncomputable def statWeight (φ : AdditiveStat) (lam : ℝ) (B : ℕ) (K : BoundedComplex B) :
    ℝ :=
  lam ^ (φ.stat B K) * gibbsWeight K

theorem gibbsWeight_positive (K : BoundedComplex B) : 0 < gibbsWeight K := by
  unfold gibbsWeight
  have hGn : 0 < Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
    Nat.mul_pos (Nat.factorial_pos _)
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have hG : (0 : ℝ)
      < ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
    exact_mod_cast hGn
  positivity

theorem statWeight_invariant (φ : AdditiveStat) (lam : ℝ) {K K' : BoundedComplex B}
    (h : Equivalent K K') : statWeight φ lam B K = statWeight φ lam B K' := by
  unfold statWeight
  rw [φ.invariant B K K' h, gibbsWeight_invariant h]

theorem statWeight_pos (φ : AdditiveStat) {lam : ℝ} (hlam : 0 < lam) (B : ℕ)
    (K : BoundedComplex B) : 0 < statWeight φ lam B K :=
  mul_pos (pow_pos hlam _) (gibbsWeight_positive K)

theorem statWeight_emptyComplex (φ : AdditiveStat) (lam : ℝ) (B : ℕ) :
    statWeight φ lam B (emptyComplex B) = 1 := by
  unfold statWeight gibbsWeight
  rw [φ.vanishes B]
  norm_num [emptyComplex]

/-- **THEOREM (the class mass of an escape weight).**  The symmetry factor survives
untouched; the tilt sits beside it as a factor `lam ^ stat`. -/
theorem classMass_statWeight (φ : AdditiveStat) (lam : ℝ) (K : BoundedComplex B) :
    classMass (statWeight φ lam B) (Quotient.mk (relabelSetoid B) K)
      = lam ^ (φ.stat B K) / (Nat.card (Aut K) : ℝ) := by
  classical
  rw [classMass_of_invariant _ (fun _ _ h => statWeight_invariant φ lam h)]
  have hout : statWeight φ lam B (Quotient.out (Quotient.mk (relabelSetoid B) K))
      = statWeight φ lam B K :=
    statWeight_invariant φ lam (equivalent_out K)
  rw [hout, orbitCardClass_mk]
  have hA : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by exact_mod_cast autCard_pos K
  have hGn : 0 < Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
    Nat.mul_pos (Nat.factorial_pos _)
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have hG : (0 : ℝ)
      < ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
    exact_mod_cast hGn
  have hGc : (gaugeOrbitCard K : ℝ) * (Nat.card (Aut K) : ℝ)
      = ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
    exact_mod_cast orbitCard_mul_autCard K
  unfold statWeight gibbsWeight
  rw [eq_div_iff hA.ne']
  calc (gaugeOrbitCard K : ℝ)
        * (lam ^ (φ.stat B K)
            * (1 / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)))
        * (Nat.card (Aut K) : ℝ)
      = lam ^ (φ.stat B K)
          * (((gaugeOrbitCard K : ℝ) * (Nat.card (Aut K) : ℝ))
              / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)) := by
        ring
    _ = lam ^ (φ.stat B K) := by rw [hGc, div_self hG.ne', mul_one]

/-- **THEOREM (the escape satisfies premise (ii) where the derivation uses it).**  At every
pair whose automorphism counts multiply, the class mass of an escape weight multiplies over
the disjoint union, with no binomial correction.  `all_four_families_available` discharges
this hypothesis at all four families `CarrierShuffle` is stated at.

This is the *restricted* premise.  The unrestricted predicate `GluesGenerally` is a different and
stronger condition, which the escape fails (`statWeight_not_gluesGenerally`).  It is not
inconsistent by itself: `uniform_gluesGenerally` satisfies it.  What
`unrestricted_gluing_inconsistent` refutes is the conjunction of unrestricted gluing with the four
restricted equations, for a positive weight that is already size-blind. -/
theorem statWeight_glues (φ : AdditiveStat) (lam : ℝ) (K : BoundedComplex B)
    (L : BoundedComplex B')
    (haut : Nat.card (Aut (dunion K L)) = Nat.card (Aut K) * Nat.card (Aut L)) :
    classMass (statWeight φ lam (B + B'))
        (Quotient.mk (relabelSetoid (B + B')) (dunion K L))
      = classMass (statWeight φ lam B) (Quotient.mk (relabelSetoid B) K)
        * classMass (statWeight φ lam B') (Quotient.mk (relabelSetoid B') L) := by
  rw [classMass_statWeight, classMass_statWeight, classMass_statWeight,
    φ.additive B B' K L, haut, pow_add]
  push_cast
  rw [div_mul_div_comm]

/-- Premise (ii) for the escape at one of the four families the derivation's `CarrierShuffle`
premise is actually stated at, instantiated to show the hypothesis of `statWeight_glues` is
really discharged somewhere and the theorem is not idle. -/
theorem statWeight_glues_at_dust_edge (φ : AdditiveStat) (lam : ℝ) (a : ℕ) :
    classMass (statWeight φ lam (a + 2))
        (Quotient.mk (relabelSetoid (a + 2)) (dunion (dust a) edge))
      = classMass (statWeight φ lam a) (Quotient.mk (relabelSetoid a) (dust a))
        * classMass (statWeight φ lam 2) (Quotient.mk (relabelSetoid 2) edge) :=
  statWeight_glues φ lam (dust a) edge (autMul_dust_edge a)

/-- **THEOREM (the escape fails the unrestricted premise, and for the intended measure's own
reason).**  No escape weight satisfies `GluesGenerally`, for any additive statistic and any
positive `lam`.  The failure is at `dust 1 ⊔ dust 1`, where the automorphism count does *not*
multiply: two isolated vertices can be exchanged, so `|Aut (dust 2)| = 2` while each part is
rigid.  The statistic contributes nothing to the discrepancy, since it adds on both sides; the
whole of it is the symmetry factor.

That is what "exactly where the intended measure fails it too" means, and it is not a figure of
speech: `lam = 1` is allowed here, and at `lam = 1` the escape *is* the Gibbs weight, so this
theorem also proves the RS measure fails unrestricted gluing.  Unrestricted gluing is therefore
not a hypothesis the derivation could have used, which is why `Gap2GluingDerivation` states
premise (ii) at eligible pairs only. -/
theorem statWeight_not_gluesGenerally (φ : AdditiveStat) {lam : ℝ} (hlam : 0 < lam) :
    ¬ GluesGenerally (statWeight φ lam) := by
  intro h
  have hEq := h (dust 1) (dust 1)
  rw [classMass_statWeight, classMass_statWeight, φ.additive 1 1 (dust 1) (dust 1)] at hEq
  have hA1 : Nat.card (Aut (dust 1)) = 1 := by
    rw [autCard_dust]; simp [Nat.factorial]
  have hA2 : Nat.card (Aut (dunion (dust 1) (dust 1))) = 2 := by
    rw [autCard_congr (dunion_dust_equivalent 1 1), autCard_dust]
    norm_num [Nat.factorial]
  rw [hA1, hA2, pow_add] at hEq
  push_cast at hEq
  have hX : (0 : ℝ) < lam ^ (φ.stat 1 (dust 1)) * lam ^ (φ.stat 1 (dust 1)) :=
    mul_pos (pow_pos hlam _) (pow_pos hlam _)
  linarith

/-! ### The two witnesses: same sizes, different loop counts -/

/-- Two loops at vertex `0`: sizes `(2,2,0)`. -/
def twoLoops : BoundedComplex 2 where
  nV := 2
  nE := 2
  nT := 0
  hV := le_refl 2
  hE := le_refl 2
  hT := Nat.zero_le 2
  edgeVerts := fun _ => (0, 0)
  tetVerts := fun t => t.elim0

/-- Two parallel non-loop edges `(0,1)`: sizes `(2,2,0)`, the same triple. -/
def twoBridges : BoundedComplex 2 where
  nV := 2
  nE := 2
  nT := 0
  hV := le_refl 2
  hE := le_refl 2
  hT := Nat.zero_le 2
  edgeVerts := fun _ => (0, 1)
  tetVerts := fun t => t.elim0

@[simp] theorem loopCount_twoLoops : loopCount twoLoops = 2 := by decide

@[simp] theorem loopCount_twoBridges : loopCount twoBridges = 0 := by decide

@[simp] theorem properEdgeCount_twoLoops : properEdgeCount twoLoops = 0 := by decide

@[simp] theorem properEdgeCount_twoBridges : properEdgeCount twoBridges = 2 := by decide

theorem twoLoops_sizes : twoLoops.nV = 2 ∧ twoLoops.nE = 2 ∧ twoLoops.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem twoBridges_sizes : twoBridges.nV = 2 ∧ twoBridges.nE = 2 ∧ twoBridges.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The two witnesses have the same three counts, so the loop count is not a function of
them.  This is the whole reason the escape exists. -/
theorem witnesses_same_sizes_different_loops :
    (twoLoops.nV = twoBridges.nV ∧ twoLoops.nE = twoBridges.nE ∧ twoLoops.nT = twoBridges.nT)
      ∧ loopCount twoLoops ≠ loopCount twoBridges := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  rw [loopCount_twoLoops, loopCount_twoBridges]
  decide

/-! ### Size-blindness, and the reach bound -/

/-- **Premise (i), size-blindness, as a relation rather than as a constructor.**  A weight
family is size-blind when it agrees on any two complexes, at any two caps, whose three index
sizes agree.  §5 proves this equivalent to being `sizeWeight f` for some `f`, which is the
constructor form the derivation uses. -/
def SizeBlind (w : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    K.nV = L.nV → K.nE = L.nE → K.nT = L.nT → w B K = w B' L

theorem sizeWeight_sizeBlind (f : ℕ → ℕ → ℕ → ℝ) :
    SizeBlind (fun _ K => sizeWeight f K) := by
  intro _ _ K L hv he ht
  simp only [sizeWeight, hv, he, ht]

/-- A positive real other than one has square other than one.  The only place the tilt's
nontriviality is used, extracted so both escapes share it. -/
theorem sq_ne_one_of_pos_ne_one {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) : lam ^ 2 ≠ 1 := by
  intro h2
  have hfac : (lam - 1) * (lam + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hfac with hz | hz
  · exact hne (by linarith)
  · linarith

/-- **THEOREM (the loop-count escape is not size-blind).** -/
theorem loopEscape_not_sizeBlind {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    ¬ SizeBlind (statWeight loopStat lam) := by
  intro h
  have hEq := h 2 2 twoLoops twoBridges rfl rfl rfl
  have hgib : gibbsWeight twoLoops = gibbsWeight twoBridges := rfl
  have hgpos : (0 : ℝ) < gibbsWeight twoBridges := gibbsWeight_positive twoBridges
  simp only [statWeight, loopStat, loopCount_twoLoops, loopCount_twoBridges, pow_zero,
    one_mul, hgib] at hEq
  have h2 : lam ^ 2 = 1 := by
    have hcanc : lam ^ 2 * gibbsWeight twoBridges = 1 * gibbsWeight twoBridges := by
      rw [one_mul]; exact hEq
    exact mul_right_cancel₀ (ne_of_gt hgpos) hcanc
  exact sq_ne_one_of_pos_ne_one hlam hne h2

/-- **THEOREM (the proper-edge escape is not size-blind).**  Same two witnesses, separated in
the other direction: `twoBridges` carries the tilt and `twoLoops` does not. -/
theorem properEscape_not_sizeBlind {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    ¬ SizeBlind (statWeight properStat lam) := by
  intro h
  have hEq := h 2 2 twoBridges twoLoops rfl rfl rfl
  have hgib : gibbsWeight twoBridges = gibbsWeight twoLoops := rfl
  have hgpos : (0 : ℝ) < gibbsWeight twoLoops := gibbsWeight_positive twoLoops
  simp only [statWeight, properStat, properEdgeCount_twoLoops, properEdgeCount_twoBridges,
    pow_zero, one_mul, hgib] at hEq
  have h2 : lam ^ 2 = 1 := by
    have hcanc : lam ^ 2 * gibbsWeight twoLoops = 1 * gibbsWeight twoLoops := by
      rw [one_mul]; exact hEq
    exact mul_right_cancel₀ (ne_of_gt hgpos) hcanc
  exact sq_ne_one_of_pos_ne_one hlam hne h2

/-! ### The three unit normalizations, and which escape survives them -/

/-- **The three unit normalizations, translated onto the labeled weight.**
`gibbs_of_unit_fugacities` assumes `f 1 0 0 = f 1 1 0 = f 1 0 1 = 1`.  Off the size function,
that is exactly this: the weight is `1` at every complex with one vertex and at most one
incidence, which are the three atoms and nothing else. -/
def NormalizedAtTheAtoms (w : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ (B : ℕ) (K : BoundedComplex B), K.nV = 1 → K.nE + K.nT ≤ 1 → w B K = 1

theorem gibbsWeight_eq_one_at_atoms (K : BoundedComplex B) (hv : K.nV = 1)
    (hi : K.nE + K.nT ≤ 1) : gibbsWeight K = 1 := by
  have hE : K.nE = 0 ∨ K.nE = 1 := by omega
  have hT : K.nT = 0 ∨ K.nT = 1 := by omega
  unfold gibbsWeight
  rcases hE with hE | hE <;> rcases hT with hT | hT <;>
    rw [hv, hE, hT] <;> norm_num [Nat.factorial]

/-- **THEOREM (the proper-edge escape satisfies the three unit normalizations).**  Its
statistic vanishes on every single-vertex complex, and the gauge volume is one there. -/
theorem properEscape_normalizedAtTheAtoms (lam : ℝ) :
    NormalizedAtTheAtoms (statWeight properStat lam) := by
  intro B K hv hi
  unfold statWeight
  have hs : properStat.stat B K = 0 :=
    properEdgeCount_eq_zero_of_nV_le_one K (by omega)
  rw [hs, pow_zero, one_mul, gibbsWeight_eq_one_at_atoms K hv hi]

/-- **THEOREM (the three normalizations kill the loop-count escape).**  At the single loop the
loop count is one, so the loop-count escape's weight there is `lam`.  The normalizations
therefore have real discriminating power, and the reach bound has to be carried by a statistic
that vanishes at the atoms, which is why `properStat` exists. -/
theorem loopEscape_fails_the_atoms {lam : ℝ} (hne : lam ≠ 1) :
    ¬ NormalizedAtTheAtoms (statWeight loopStat lam) := by
  intro h
  have hbad := h 2 (bouquet 1 0) rfl (by norm_num)
  have hloop : loopCount (bouquet 1 0) = 1 := by decide
  have hgib : gibbsWeight (bouquet 1 0) = 1 := by
    unfold gibbsWeight
    norm_num [Nat.factorial]
  simp only [statWeight, loopStat, hloop, hgib, pow_one, mul_one] at hbad
  exact hne hbad

/-- **Control for the reach bound, at every statistic.**  At `lam = 1` the escape weight *is* the
Gibbs weight and *is* size-blind, whichever statistic it was built from.  So the failure at
`lam ≠ 1` is a property of the tilt, not an artifact of the construction, and the two witnesses are
separating rather than merely different.  Without this the reach bound would be consistent with the
escape being malformed.  Stated for a general statistic so that it controls the proper-edge escape
the reach bound actually uses, not only the loop-count one. -/
theorem statWeight_sizeBlind_at_one (φ : AdditiveStat) : SizeBlind (statWeight φ 1) := by
  have h : ∀ (B : ℕ) (K : BoundedComplex B), statWeight φ 1 B K = gibbsWeight K := by
    intro B K
    simp [statWeight]
  intro B B' K L hv he ht
  rw [h, h]
  unfold gibbsWeight
  rw [hv, he, ht]

/-- The control at the loop-count statistic. -/
theorem loopEscape_sizeBlind_at_one : SizeBlind (statWeight loopStat 1) :=
  statWeight_sizeBlind_at_one loopStat

/-- The control at the proper-edge statistic, which is the one the reach bound uses. -/
theorem properEscape_sizeBlind_at_one : SizeBlind (statWeight properStat 1) :=
  statWeight_sizeBlind_at_one properStat

/-- **Every hypothesis the derivation places on the labeled weight except premise (i).**  Five
clauses: relabeling invariance, strict positivity, unit on the empty complex, unit at the three
atoms, and premise (ii) at every pair whose automorphism counts multiply.

The correspondence with `Gap2GluingDerivation`, stated exactly.  Its final theorem is
`CarrierShuffle.gibbs_of_unit_fugacities`, whose hypotheses are: the weight is `sizeWeight f`
for some `f` (premise (i)); `CarrierShuffle f`, which is `f` positive, `f 0 0 0 = 1`, and four
shuffle equations that `gluesAt_of_shuffle` shows are premise (ii) at four eligible families;
and `f 1 0 0 = f 1 1 0 = f 1 0 1 = 1`.  Clauses two through five are those, transported off the
size function so they can be stated without assuming premise (i).  Clause one is invariance,
which the class mass needs to be well defined at all.

**One asymmetry, stated rather than hidden.**  Clause five is premise (ii) at *every* eligible
pair, which is stronger than the four families the derivation consumes, so a weight satisfying
this bundle satisfies more than the derivation asks, not less. -/
def SatisfiesTheOtherHypotheses (w : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  (∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → w B K = w B K')
    ∧ (∀ (B : ℕ) (K : BoundedComplex B), 0 < w B K)
    ∧ (∀ B : ℕ, w B (emptyComplex B) = 1)
    ∧ NormalizedAtTheAtoms w
    ∧ (∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
        Nat.card (Aut (dunion K L)) = Nat.card (Aut K) * Nat.card (Aut L) →
          classMass (w (B + B')) (Quotient.mk (relabelSetoid (B + B')) (dunion K L))
            = classMass (w B) (Quotient.mk (relabelSetoid B) K)
              * classMass (w B') (Quotient.mk (relabelSetoid B') L))

theorem properEscape_satisfiesTheOtherHypotheses {lam : ℝ} (hlam : 0 < lam) :
    SatisfiesTheOtherHypotheses (statWeight properStat lam) :=
  ⟨fun _ _ _ h => statWeight_invariant properStat lam h,
    fun B K => statWeight_pos properStat hlam B K,
    fun B => statWeight_emptyComplex properStat lam B,
    properEscape_normalizedAtTheAtoms lam,
    fun _ _ K L haut => statWeight_glues properStat lam K L haut⟩

/-- **Control for the class-mass comparison.**  At `lam = 1` the very same formula returns the
RS measure exactly, for every complex.  So the inequality below measures the tilt and not a
mismatch of conventions between `classMass` and `mu`. -/
theorem classMass_statWeight_at_one (φ : AdditiveStat) (K : BoundedComplex B) :
    classMass (statWeight φ 1 B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  rw [classMass_statWeight]
  simp [mu]

/-- **THEOREM (the derivation's conclusion fails for the escape).**  The class mass of the
proper-edge escape at the two-bridge class is `lam²/|Aut|`, and the RS measure is `1/|Aut|`, so
they differ.  This is what makes the reach bound bite: not merely that the escape misses a
premise, but that the thing the derivation concludes is false of it. -/
theorem properEscape_classMass_ne_mu {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    classMass (statWeight properStat lam 2) (Quotient.mk (relabelSetoid 2) twoBridges)
      ≠ mu twoBridges := by
  rw [classMass_statWeight]
  unfold mu
  intro h
  have hA : (0 : ℝ) < (Nat.card (Aut twoBridges) : ℝ) := by
    exact_mod_cast autCard_pos twoBridges
  rw [div_eq_div_iff hA.ne' hA.ne'] at h
  have hkey : lam ^ (properStat.stat 2 twoBridges) = 1 := mul_right_cancel₀ hA.ne' h
  have hs : properStat.stat 2 twoBridges = 2 := properEdgeCount_twoBridges
  rw [hs] at hkey
  exact sq_ne_one_of_pos_ne_one hlam hne hkey

/-- **THE REACH BOUND.**  For each positive `lam ≠ 1` there is one fixed labeled weight that
satisfies *every* hypothesis the derivation places on the weight except premise (i), is not
size-blind, and whose class mass is not the RS measure.  So premise (i) is not redundant: it is
load-bearing for the conclusion.

The bundle it satisfies is already stronger than the derivation's, since its gluing clause
quantifies over every eligible pair rather than the four families `CarrierShuffle` names.  That is
the precise sense in which the other hypotheses cannot be blamed for premise (i); it is not a claim
about arbitrary strengthenings, some of which would obviously exclude this escape.

**Scope, and what this does not say.**  It does not say premise (ii) is empty; the sharper
statement of that is `gluing_alone_does_not_force_mu` in the derivation module, which exhibits a
weight satisfying gluing at *every* pair whose class mass is not `mu`.  It says premise (ii),
even conjoined with positivity, both normalizations and invariance, does not generate the
automorphism denominator that premise (i) alone already produces
(`classMass_sizeWeight_eq_fugacity_div_autCard`).  It does not characterize eligibility; no such
characterization exists in the library.

**It does not quantify over derivations.**  The statement is existential: one weight, satisfying
that bundle, not size-blind.  A reader may reasonably expect the stronger reading, that every
route to premise (i) must import a reason why incidence statistics do not appear, and that reading
is *not* proved here and is not provable from an existential.  What supports it, and only as
motivation, is that the escape mechanism runs for every additive incidence statistic
(`statWeight_glues`, `statWeight_pos`, `statWeight_invariant`) while the normalizations exclude
only the statistics that fail to vanish at the atoms (`loopEscape_fails_the_atoms`,
`properEdgeCount_eq_zero_of_nV_le_one`).  So the family of escapes is large, which is a fact about
the family and not a theorem about derivations. -/
theorem size_blindness_not_forced_by_the_other_hypotheses {lam : ℝ} (hlam : 0 < lam)
    (hne : lam ≠ 1) :
    SatisfiesTheOtherHypotheses (statWeight properStat lam)
      ∧ ¬ SizeBlind (statWeight properStat lam)
      ∧ classMass (statWeight properStat lam 2) (Quotient.mk (relabelSetoid 2) twoBridges)
          ≠ mu twoBridges :=
  ⟨properEscape_satisfiesTheOtherHypotheses hlam, properEscape_not_sizeBlind hlam hne,
    properEscape_classMass_ne_mu hlam hne⟩

/-! ## §4. Blindness to the posting alphabet, stated about the posting alphabet

`GaugeHistoryMeasure.PostingAlphabet K = Fin K.nV ⊕ Fin K.nE ⊕ Fin K.nT`, with the three
canonical injections `vertexPost`, `edgePost`, `tetPost`.  An equivalence of alphabets is
sort-respecting when it carries each kind of letter to the same kind. -/

/-- An equivalence of posting alphabets **respects the cell kinds** when it carries vertex
letters to vertex letters, edge letters to edge letters, and tetrahedron letters to
tetrahedron letters.

The condition is one-sided: it constrains the forward map and says nothing about the inverse.
That is deliberate and costs nothing, because the totals are already pinned by the equivalence.
Each kind injects into its partner, so each count is at most its partner's, and the three counts
sum to the same total; `exists_respectsKinds_iff_sizes` turns that into equality on all three.  A
two-sided definition would give the same theorem with more hypotheses to discharge. -/
def RespectsKinds {K : BoundedComplex B} {L : BoundedComplex B'}
    (e : GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L) :
    Prop :=
  (∀ v : Fin K.nV, ∃ v' : Fin L.nV, e (Sum.inl v) = Sum.inl v')
    ∧ (∀ x : Fin K.nE, ∃ x' : Fin L.nE, e (Sum.inr (Sum.inl x)) = Sum.inr (Sum.inl x'))
    ∧ (∀ t : Fin K.nT, ∃ t' : Fin L.nT, e (Sum.inr (Sum.inr t)) = Sum.inr (Sum.inr t'))

/-- A bare correspondence of posting alphabets exists exactly when the total cell counts
agree. -/
theorem postingAlphabet_equiv_iff_total (K : BoundedComplex B) (L : BoundedComplex B') :
    Nonempty (GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L)
      ↔ K.nV + K.nE + K.nT = L.nV + L.nE + L.nT := by
  have hK : Fintype.card (GaugeHistoryMeasure.PostingAlphabet K) = K.nV + K.nE + K.nT := by
    simp [GaugeHistoryMeasure.PostingAlphabet, Nat.add_assoc]
  have hL : Fintype.card (GaugeHistoryMeasure.PostingAlphabet L) = L.nV + L.nE + L.nT := by
    simp [GaugeHistoryMeasure.PostingAlphabet, Nat.add_assoc]
  constructor
  · intro ⟨e⟩
    have hc := Fintype.card_congr e
    rw [hK, hL] at hc
    exact hc
  · intro h
    exact ⟨Fintype.equivOfCardEq (by rw [hK, hL, h])⟩

/-- A sort-respecting correspondence sends each kind into the same kind injectively, so each
count is bounded by its partner. -/
theorem sizes_le_of_respectsKinds {K : BoundedComplex B} {L : BoundedComplex B'}
    {e : GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L}
    (h : RespectsKinds e) : K.nV ≤ L.nV ∧ K.nE ≤ L.nE ∧ K.nT ≤ L.nT := by
  classical
  obtain ⟨hv, he, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun v : Fin K.nV => (hv v).choose) := by
      intro a b hab
      have hkey : e (Sum.inl a) = e (Sum.inl b) := by
        rw [(hv a).choose_spec, (hv b).choose_spec]
        exact congrArg Sum.inl hab
      exact Sum.inl_injective (e.injective hkey)
    simpa using Fintype.card_le_of_injective _ hinj
  · have hinj : Function.Injective (fun x : Fin K.nE => (he x).choose) := by
      intro a b hab
      have hkey : e (Sum.inr (Sum.inl a)) = e (Sum.inr (Sum.inl b)) := by
        rw [(he a).choose_spec, (he b).choose_spec]
        exact congrArg (fun y => Sum.inr (Sum.inl y)) hab
      exact Sum.inl_injective (Sum.inr_injective (e.injective hkey))
    simpa using Fintype.card_le_of_injective _ hinj
  · have hinj : Function.Injective (fun t : Fin K.nT => (ht t).choose) := by
      intro a b hab
      have hkey : e (Sum.inr (Sum.inr a)) = e (Sum.inr (Sum.inr b)) := by
        rw [(ht a).choose_spec, (ht b).choose_spec]
        exact congrArg (fun y => Sum.inr (Sum.inr y)) hab
      exact Sum.inr_injective (Sum.inr_injective (e.injective hkey))
    simpa using Fintype.card_le_of_injective _ hinj

/-- **THEOREM.**  A sort-respecting correspondence of posting alphabets exists exactly when
the three cell counts agree.  Each count is bounded by its partner because the letters of
each kind inject, and the totals agree because the whole alphabet is in bijection; the two
together force equality. -/
theorem exists_respectsKinds_iff_sizes (K : BoundedComplex B) (L : BoundedComplex B') :
    (∃ e : GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L,
        RespectsKinds e)
      ↔ (K.nV = L.nV ∧ K.nE = L.nE ∧ K.nT = L.nT) := by
  constructor
  · intro ⟨e, h⟩
    obtain ⟨h1, h2, h3⟩ := sizes_le_of_respectsKinds h
    have htot := (postingAlphabet_equiv_iff_total K L).mp ⟨e⟩
    exact ⟨by omega, by omega, by omega⟩
  · intro ⟨hv, he, ht⟩
    refine ⟨Equiv.sumCongr (finCongr hv) (Equiv.sumCongr (finCongr he) (finCongr ht)), ?_, ?_, ?_⟩
    · intro v; exact ⟨finCongr hv v, rfl⟩
    · intro x; exact ⟨finCongr he x, rfl⟩
    · intro t; exact ⟨finCongr ht t, rfl⟩

/-- **Blind to everything but the posting alphabet read with its sorting into cell kinds.**
Stated against `GaugeHistoryMeasure.PostingAlphabet` itself. -/
def AlphabetBlindSorted (w : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    (∃ e : GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L,
        RespectsKinds e) → w B K = w B' L

theorem alphabetBlindSorted_iff_sizeBlind (w : ∀ B : ℕ, BoundedComplex B → ℝ) :
    AlphabetBlindSorted w ↔ SizeBlind w := by
  constructor
  · intro h B B' K L hv he ht
    exact h B B' K L ((exists_respectsKinds_iff_sizes K L).mpr ⟨hv, he, ht⟩)
  · intro h B B' K L hEq
    obtain ⟨hv, he, ht⟩ := (exists_respectsKinds_iff_sizes K L).mp hEq
    exact h B B' K L hv he ht

/-- The escape fails alphabet-blindness too, as it must. -/
theorem loopEscape_not_alphabetBlindSorted {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    ¬ AlphabetBlindSorted (statWeight loopStat lam) := by
  rw [alphabetBlindSorted_iff_sizeBlind]
  exact loopEscape_not_sizeBlind hlam hne

/-! ## §5. Against premise (i) exactly as the derivation states it

`Gap2GluingDerivation` states premise (i) not as a relation but as a constructor: the weight
*is* `sizeWeight f` for some `f` of three naturals.  Closing the equivalence needs a complex
at each realizable size triple, and needs the fact that the unrealizable triples are exactly
those with no vertex and some incidence, which `vertex_of_incidence` supplies. -/

/-- A canonical complex at each realizable size triple with at least one vertex: `a`
vertices, `b` loops at the first vertex, `c` tetrahedra degenerate at the first vertex. -/
def blob (a b c : ℕ) (h : 0 < a) : BoundedComplex (a + b + c) where
  nV := a
  nE := b
  nT := c
  hV := by omega
  hE := by omega
  hT := by omega
  edgeVerts := fun _ => (⟨0, h⟩, ⟨0, h⟩)
  tetVerts := fun _ _ => ⟨0, h⟩

/-- The size function read off a size-blind weight family.  Its value on the triples no
complex realizes, which are exactly those with no vertex and some incidence, is arbitrary
and never evaluated. -/
noncomputable def canonicalSizeFun (w : ∀ B : ℕ, BoundedComplex B → ℝ) (a b c : ℕ) : ℝ :=
  if h : 0 < a then w (a + b + c) (blob a b c h) else w 0 (emptyComplex 0)

theorem sizeBlind_eq_sizeWeight {w : ∀ B : ℕ, BoundedComplex B → ℝ} (hw : SizeBlind w)
    (B : ℕ) (K : BoundedComplex B) : w B K = sizeWeight (canonicalSizeFun w) K := by
  unfold sizeWeight canonicalSizeFun
  by_cases h : 0 < K.nV
  · rw [dif_pos h]
    exact hw B _ K (blob K.nV K.nE K.nT h) rfl rfl rfl
  · rw [dif_neg h]
    have hv : K.nV = 0 := by omega
    have hi : K.nE + K.nT = 0 := by
      by_contra hc
      have h1 : 1 ≤ K.nE + K.nT := by omega
      have := vertex_of_incidence K h1
      omega
    have hE : K.nE = 0 := by omega
    have hT : K.nT = 0 := by omega
    exact hw B 0 K (emptyComplex 0) (by simp [emptyComplex, hv])
      (by simp [emptyComplex, hE]) (by simp [emptyComplex, hT])

/-- Size-blindness as a relation and as a constructor are the same condition. -/
theorem sizeBlind_iff_exists_sizeFun (w : ∀ B : ℕ, BoundedComplex B → ℝ) :
    SizeBlind w
      ↔ ∃ f : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B), w B K = sizeWeight f K := by
  constructor
  · intro hw
    exact ⟨canonicalSizeFun w, sizeBlind_eq_sizeWeight hw⟩
  · intro ⟨f, hf⟩ B B' K L hv he ht
    rw [hf B K, hf B' L]
    exact sizeWeight_sizeBlind f B B' K L hv he ht

/-- **THEOREM.**  Premise (i) of `Gap2GluingDerivation`, that the labeled weight is
`sizeWeight f` for some size function `f`, holds exactly when the weight is blind to
everything but the substrate's posting alphabet read with its sorting into cell kinds.

**This is an equivalence, not a derivation.**  §6 proves the posting alphabet is itself a
function of the three counts, so the right-hand side is the left-hand side in other words.
The name says `iff` and means it. -/
theorem premise_one_iff_alphabetBlind (w : ∀ B : ℕ, BoundedComplex B → ℝ) :
    (∃ f : ℕ → ℕ → ℕ → ℝ, ∀ (B : ℕ) (K : BoundedComplex B), w B K = sizeWeight f K)
      ↔ AlphabetBlindSorted w :=
  (sizeBlind_iff_exists_sizeFun w).symm.trans (alphabetBlindSorted_iff_sizeBlind w).symm

/-! ## §6. The dichotomy: sufficient for premise (i) exactly when not weaker than it

§4 and §5 make precise the hope that premise (i) is simply what the posting alphabet says,
so that the premise moves off the measure and onto the substrate.  This section kills that
hope, and then generalizes the reason into a no-go covering every premise of that shape.

An **invariant** of complexes is any function of a complex, valued in any type.  A weight is
**blind to** an invariant when it agrees on any two complexes the invariant does not
separate.  Premise (i) is itself of this form: it is blindness to the size triple.  The
question is whether premise (i) follows from blindness to something *weaker*, and the answer
is no, for one of two reasons depending on which side of the dichotomy the invariant falls. -/

/-- A readout of a complex, valued in an arbitrary type.

**The name overstates the definition, deliberately.**  Nothing here requires relabeling invariance:
this is *any* function of a labeled complex, label-sensitive ones included.  The word is kept
because these are the objects a substrate would be said to resolve, and the looseness is what makes
the dichotomy exhaustive rather than restricted to well-behaved readouts.  Where invariance is
needed it is a hypothesis or a conclusion, never packed into the type: see
`sizeStatInvariant_invariant` for an instance that has it and the last clause of
`fine_invariant_blindness_does_not_imply_sizeBlind` for how the horn handles the case where it is
absent. -/
def Invariant (α : Type) : Type := ∀ B : ℕ, BoundedComplex B → α

/-- An invariant **resolves no more than the sizes** when any two complexes with the same
three cell counts receive the same value. -/
def ResolvesNoMoreThanSizes {α : Type} (I : Invariant α) : Prop :=
  ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    K.nV = L.nV → K.nE = L.nE → K.nT = L.nT → I B K = I B' L

/-- A weight is **blind to** an invariant when the invariant's value decides it. -/
def BlindTo {α : Type} (I : Invariant α) (w : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    I B K = I B' L → w B K = w B' L

/-- **Coarse horn.**  If an invariant resolves no more than the three cell counts, blindness
to it *implies* premise (i).  So assuming it is assuming premise (i) or more, and a
derivation of premise (i) from it is a restatement rather than a discharge. -/
theorem coarse_invariant_blindness_implies_sizeBlind {α : Type} (I : Invariant α)
    (hI : ResolvesNoMoreThanSizes I) (w : ∀ B : ℕ, BoundedComplex B → ℝ)
    (hw : BlindTo I w) : SizeBlind w := by
  intro B B' K L hv he ht
  exact hw B B' K L (hI B B' K L hv he ht)

/-- **Fine horn.**  If an invariant separates even one pair of complexes with the same three cell
counts, blindness to it does *not* imply premise (i).  The witness is the two-valued indicator of
one invariant value: strictly positive always, and relabeling-invariant whenever the invariant is,
which the last clause states as an implication rather than a hypothesis so that the horn applies to
**every** invariant, label-sensitive ones included.  That is what makes the dichotomy exhaustive.

The witness is not unit on the empty complex and says nothing about gluing;
`fine_horn_survives_the_other_hypotheses` supplies a witness that satisfies those too, at one
concrete invariant. -/
theorem fine_invariant_blindness_does_not_imply_sizeBlind {α : Type} (I : Invariant α)
    {B₀ B₀' : ℕ} (K₀ : BoundedComplex B₀) (L₀ : BoundedComplex B₀')
    (hv : K₀.nV = L₀.nV) (he : K₀.nE = L₀.nE) (ht : K₀.nT = L₀.nT)
    (hsep : I B₀ K₀ ≠ I B₀' L₀) :
    ∃ w : ∀ B : ℕ, BoundedComplex B → ℝ,
      BlindTo I w
        ∧ (∀ (B : ℕ) (K : BoundedComplex B), 0 < w B K)
        ∧ ¬ SizeBlind w
        ∧ ((∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → I B K = I B K') →
            ∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → w B K = w B K') := by
  classical
  refine ⟨fun B K => if I B K = I B₀ K₀ then 1 else 2, ?_, ?_, ?_, ?_⟩
  · intro B B' K L h
    simp only [h]
  · intro B K
    show (0 : ℝ) < if I B K = I B₀ K₀ then (1 : ℝ) else 2
    by_cases hc : I B K = I B₀ K₀
    · rw [if_pos hc]; norm_num
    · rw [if_neg hc]; norm_num
  · intro hsb
    have hbad : (if I B₀ K₀ = I B₀ K₀ then (1 : ℝ) else 2)
        = (if I B₀' L₀ = I B₀ K₀ then (1 : ℝ) else 2) := hsb B₀ B₀' K₀ L₀ hv he ht
    rw [if_pos (rfl : I B₀ K₀ = I B₀ K₀), if_neg (Ne.symm hsep)] at hbad
    norm_num at hbad
  · intro hIinv B K K' hEq
    simp only [hIinv B K K' hEq]

/-- **The two horns are exhaustive.**  By cases on whether the invariant is constant across
same-size pairs.

**This theorem has no content of its own.**  It is `P ∨ ¬P` with `¬P` unpacked into the witness it
asserts, so it excludes nothing and would hold for any predicate whatever.  It is stated because the
unpacking is what the horn theorems consume, and because a dichotomy claim should have its
exhaustiveness written down rather than assumed.  All the content is in the two horns and in
`blindness_forces_premise_one_iff_coarse`, which combines them.  Neither this theorem nor either
horn assumes the invariant is relabeling-invariant, so the coverage has no gap at label-sensitive
invariants. -/
theorem invariant_coarse_or_fine {α : Type} (I : Invariant α) :
    ResolvesNoMoreThanSizes I
      ∨ ∃ (B₀ B₀' : ℕ) (K₀ : BoundedComplex B₀) (L₀ : BoundedComplex B₀'),
          K₀.nV = L₀.nV ∧ K₀.nE = L₀.nE ∧ K₀.nT = L₀.nT ∧ I B₀ K₀ ≠ I B₀' L₀ := by
  classical
  by_cases h : ResolvesNoMoreThanSizes I
  · exact Or.inl h
  · right
    unfold ResolvesNoMoreThanSizes at h
    push_neg at h
    obtain ⟨B, B', K, L, hv, he, ht, hne⟩ := h
    exact ⟨B, B', K, L, hv, he, ht, hne⟩

/-- **THE DICHOTOMY, as one equivalence.**  Blindness to an invariant forces premise (i) **exactly
when** that invariant never separates two complexes with the same three counts.  The two horns are
the two directions, and this is the statement to cite: it is sharper than their conjunction, because
an equivalence cannot be read as leaving a third case open.

**What it rules out, stated as the contrapositive it is.**  Take any premise of the form *the weight
cannot separate complexes that agree on `X`* and ask it to yield premise (i) for every weight. Then
`X` resolves no more than the counts, and blindness to `X` is then sufficient for premise (i)
(`coarse_invariant_blindness_implies_sizeBlind`). So no premise of this shape is both strictly weaker
than premise (i) and sufficient for it. That is what kills the hope this module started from.

**It does not say the two conditions are interchangeable, and they are not.**  Sufficiency runs one
way only. A coarse invariant can be so coarse that blindness to it is *strictly stronger* than
premise (i), which is exactly what `unsorted_is_strictly_stronger` exhibits: the total cell count
resolves no more than the counts, yet a size-blind weight can fail blindness to it, and the Gibbs
weight does. So "blindness to `X` and premise (i) imply each other" is false in general, and an
earlier version of this docstring asserted it.

**Two things this does not say, both of which the word "circular" would wrongly suggest.**  It does
not say a coarse premise is premise (i) *renamed*: the coarse class contains conditions strictly
stronger than premise (i), and `unsorted_is_strictly_stronger` exhibits one, blindness to the total
cell count, which is outright inconsistent with the derivation's conclusion because the Gibbs weight
itself fails it. What is equivalent to
premise (i) is not the invariant but blindness to it, and only quantified over all weights. And it
does not quantify over derivations: a conjunction of several blindness premises, or a premise of
some other shape, is outside the statement, so premise (i) is not shown unprovable.

The escape's statistic witnesses the fine side (`fine_horn_survives_the_other_hypotheses`), the
posting alphabet the coarse side (`postingAlphabet_is_determined_by_the_sizes`), and the total cell
count the coarse side strictly (`unsorted_is_strictly_stronger`). -/
theorem blindness_forces_premise_one_iff_coarse {α : Type} (I : Invariant α) :
    (∀ w : ∀ B : ℕ, BoundedComplex B → ℝ, BlindTo I w → SizeBlind w)
      ↔ ResolvesNoMoreThanSizes I := by
  classical
  refine ⟨fun h => ?_, fun hI w hw => coarse_invariant_blindness_implies_sizeBlind I hI w hw⟩
  rcases invariant_coarse_or_fine I with hI | ⟨B₀, B₀', K₀, L₀, hv, he, ht, hsep⟩
  · exact hI
  · obtain ⟨w, hblind, -, hnsb, -⟩ :=
      fine_invariant_blindness_does_not_imply_sizeBlind I K₀ L₀ hv he ht hsep
    exact absurd (h w hblind) hnsb

/-- The dichotomy in horn form, as the two implications, for readers who want the witness the fine
side produces rather than only the equivalence.  Both sides quantify over the invariant's type, so
this is one statement covering every invariant of complexes. -/
theorem indistinguishability_premises_never_weaken_premise_one :
    (∀ (α : Type) (I : Invariant α), ResolvesNoMoreThanSizes I →
        ∀ w : ∀ B : ℕ, BoundedComplex B → ℝ, BlindTo I w → SizeBlind w)
      ∧ (∀ (α : Type) (I : Invariant α) (B₀ B₀' : ℕ) (K₀ : BoundedComplex B₀)
            (L₀ : BoundedComplex B₀'),
            K₀.nV = L₀.nV → K₀.nE = L₀.nE → K₀.nT = L₀.nT → I B₀ K₀ ≠ I B₀' L₀ →
              ∃ w : ∀ B : ℕ, BoundedComplex B → ℝ,
                BlindTo I w
                  ∧ (∀ (B : ℕ) (K : BoundedComplex B), 0 < w B K)
                  ∧ ¬ SizeBlind w
                  ∧ ((∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → I B K = I B K') →
                      ∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → w B K = w B K')) :=
  ⟨fun _ I hI w hw => coarse_invariant_blindness_implies_sizeBlind I hI w hw,
    fun _ I _ _ K₀ L₀ hv he ht hsep =>
      fine_invariant_blindness_does_not_imply_sizeBlind I K₀ L₀ hv he ht hsep⟩

/-! ### The fine horn is not an artifact of a degenerate witness

The abstract fine horn is witnessed by a two-valued indicator, which is positive and (when the
invariant is) relabeling-invariant, but is not unit on the empty complex and is silent about
gluing.  So a reader can still ask whether adding the derivation's remaining hypotheses rescues
the implication.  At one invariant it does not, and the escape of §3 is the witness: it is blind
to the invariant that reads the three counts together with the proper-edge count, an invariant
that separates a same-size pair, and it satisfies all five remaining hypotheses. -/

/-- The invariant that reads the three cell counts **and** the value of an additive statistic.
At `properStat` it separates the two witnesses of §3, so it is not on the coarse horn. -/
def sizeStatInvariant (φ : AdditiveStat) : Invariant (ℕ × ℕ × ℕ × ℕ) :=
  fun B K => (K.nV, K.nE, K.nT, φ.stat B K)

theorem sizeStatInvariant_invariant (φ : AdditiveStat) (B : ℕ) (K K' : BoundedComplex B)
    (h : Equivalent K K') : sizeStatInvariant φ B K = sizeStatInvariant φ B K' := by
  obtain ⟨r⟩ := h
  unfold sizeStatInvariant
  rw [size_v r, size_e r, size_t r, φ.invariant B K K' ⟨r⟩]

theorem sizeStatInvariant_separates_witnesses :
    sizeStatInvariant properStat 2 twoBridges ≠ sizeStatInvariant properStat 2 twoLoops := by
  intro h
  have h4 : properEdgeCount twoBridges = properEdgeCount twoLoops :=
    congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) h
  rw [properEdgeCount_twoBridges, properEdgeCount_twoLoops] at h4
  exact absurd h4 (by decide)

/-- An escape weight is a function of the three counts together with its own statistic, so it is
blind to that pairing. -/
theorem statWeight_blindTo_sizeStat (φ : AdditiveStat) (lam : ℝ) :
    BlindTo (sizeStatInvariant φ) (statWeight φ lam) := by
  intro B B' K L h
  have hv : K.nV = L.nV := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.1) h
  have he : K.nE = L.nE := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) h
  have ht : K.nT = L.nT := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) h
  have hs : φ.stat B K = φ.stat B' L := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) h
  unfold statWeight
  rw [hs]
  unfold gibbsWeight
  rw [hv, he, ht]

/-- **ONE FINE INVARIANT SURVIVES EVERY OTHER HYPOTHESIS.**  There is a relabeling-invariant
invariant that separates a same-size pair, hence is on the fine side, and a weight blind to it that
satisfies all five hypotheses the derivation places on the weight except premise (i), is not
size-blind, and whose class mass is not the RS measure.

**One invariant, and the name says so.**  This does *not* say the fine side in general survives the
other hypotheses.  The general fine horn
(`fine_invariant_blindness_does_not_imply_sizeBlind`) covers every invariant that separates a
same-size pair, but its witness carries only positivity and invariance, not the normalizations or
gluing.  What is settled here is: blindness to *this* fine invariant does not force premise (i) even
alongside every other hypothesis.  What is **not** settled, and is the open residual this module
leaves, is whether some *other* fine invariant might, conjoined with those hypotheses, force
premise (i); the conjunction is restrictive and the question is a real one.

**And the pair is matched by construction.**  The invariant reads the three counts together with the
statistic the weight is built from, so blindness is immediate rather than earned; the work is in the
weight satisfying the five hypotheses, not in the blindness clause.  A countermodel is allowed to be
constructed this way, and nothing here claims the invariant is one a substrate would supply. The
reason it is worth stating at all is that the five hypotheses are a genuine constraint: they already
exclude the loop-count version of exactly this construction
(`loopEscape_fails_the_atoms`). -/
theorem fine_horn_survives_the_other_hypotheses {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    (twoBridges.nV = twoLoops.nV ∧ twoBridges.nE = twoLoops.nE ∧ twoBridges.nT = twoLoops.nT)
      ∧ sizeStatInvariant properStat 2 twoBridges ≠ sizeStatInvariant properStat 2 twoLoops
      ∧ (∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' →
          sizeStatInvariant properStat B K = sizeStatInvariant properStat B K')
      ∧ BlindTo (sizeStatInvariant properStat) (statWeight properStat lam)
      ∧ SatisfiesTheOtherHypotheses (statWeight properStat lam)
      ∧ ¬ SizeBlind (statWeight properStat lam)
      ∧ classMass (statWeight properStat lam 2) (Quotient.mk (relabelSetoid 2) twoBridges)
          ≠ mu twoBridges :=
  ⟨⟨rfl, rfl, rfl⟩, sizeStatInvariant_separates_witnesses,
    sizeStatInvariant_invariant properStat, statWeight_blindTo_sizeStat properStat lam,
    properEscape_satisfiesTheOtherHypotheses hlam, properEscape_not_sizeBlind hlam hne,
    properEscape_classMass_ne_mu hlam hne⟩

/-- **Why the posting alphabet lands on the coarse horn.**  The posting alphabet is a
*function of* the three cell counts: any two complexes with the same counts have
sort-respecting equivalent posting alphabets, no matter how their cells are wired.  In
particular the two witnesses of §3, which differ only in incidence, have equivalent
alphabets.

So the alphabet carries no information about incidence to begin with, and asking a weight to
be blind to everything but the alphabet is asking for premise (i) under another name.  The
equivalence `premise_one_iff_alphabetBlind` is a reformulation, not a derivation.

**Scope.**  This is a statement about the posting *alphabet*, which is the only part of the
posting layer it touches.  That the wider posted-history layer adds no selecting information
is a separate and earlier result, recorded in the `PathSumMeasure` module header; this
theorem neither reproves nor needs it. -/
theorem postingAlphabet_is_determined_by_the_sizes :
    (∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
        K.nV = L.nV → K.nE = L.nE → K.nT = L.nT →
          ∃ e : GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L,
            RespectsKinds e)
      ∧ (∃ e : GaugeHistoryMeasure.PostingAlphabet twoLoops
              ≃ GaugeHistoryMeasure.PostingAlphabet twoBridges,
          RespectsKinds e)
      ∧ loopCount twoLoops ≠ loopCount twoBridges := by
  refine ⟨fun _ _ K L hv he ht => (exists_respectsKinds_iff_sizes K L).mpr ⟨hv, he, ht⟩,
    (exists_respectsKinds_iff_sizes twoLoops twoBridges).mpr ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [loopCount_twoLoops, loopCount_twoBridges]
  decide

/-! ### The one place the readings differ

Forgetting the sorting gives a strictly *stronger* condition, not a weaker one: a bare
correspondence of alphabets only forces the total cell count to agree, so unsorted blindness
forces the weight to depend on `nV + nE + nT` alone.  This shows the family of readings is
non-trivial.  It does not make any of them a derivation. -/

/-- **Blind to everything but the posting alphabet as a bare set.** -/
def AlphabetBlindUnsorted (w : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
    Nonempty (GaugeHistoryMeasure.PostingAlphabet K ≃ GaugeHistoryMeasure.PostingAlphabet L) →
      w B K = w B' L

/-- Three vertices and one edge: sizes `(3,1,0)`, total cell count `4`, the same total as
`twoBridges` at `(2,2,0)` and a different triple. -/
def threeVertsOneEdge : BoundedComplex 3 where
  nV := 3
  nE := 1
  nT := 0
  hV := le_refl 3
  hE := by norm_num
  hT := Nat.zero_le 3
  edgeVerts := fun _ => (0, 1)
  tetVerts := fun t => t.elim0

/-- **THEOREM (the sorting is load-bearing, and the intended measure needs it).**  Three parts.
Unsorted blindness implies the sorted form.  A size-blind weight can fail the unsorted form, at
the pair `(2,2,0)` and `(3,1,0)` whose totals agree.  And the failing weight is not a contrived
one: the Gibbs weight itself, which is what the derivation concludes, fails unsorted blindness at
that same pair, `1/4` against `1/6`.

**What the third part is for.**  It makes unsorted blindness and the derivation's conclusion jointly
unsatisfiable, so the coarse side of the dichotomy contains conditions strictly stronger than
premise (i) and not merely restatements of it.  Read as a conditional about substrates it would say:
*if* a substrate's posting alphabet were unsorted and *if* blindness to it were the right premise,
the two would contradict the conclusion.  Neither antecedent is proved anywhere; nothing here is a
theorem about what a substrate posts. -/
theorem unsorted_is_strictly_stronger :
    (∀ w : ∀ B : ℕ, BoundedComplex B → ℝ, AlphabetBlindUnsorted w → AlphabetBlindSorted w)
      ∧ (∃ w : ∀ B : ℕ, BoundedComplex B → ℝ, SizeBlind w ∧ ¬ AlphabetBlindUnsorted w)
      ∧ ¬ AlphabetBlindUnsorted (fun _ K => gibbsWeight K) := by
  have htot : twoBridges.nV + twoBridges.nE + twoBridges.nT
      = threeVertsOneEdge.nV + threeVertsOneEdge.nE + threeVertsOneEdge.nT := by
    norm_num [twoBridges, threeVertsOneEdge]
  refine ⟨?_, ?_, ?_⟩
  · intro w h B B' K L hEq
    obtain ⟨hv, he, ht⟩ := (exists_respectsKinds_iff_sizes K L).mp hEq
    exact h B B' K L ((postingAlphabet_equiv_iff_total K L).mpr (by rw [hv, he, ht]))
  · refine ⟨fun _ K => sizeWeight (fun a _ _ => (a : ℝ)) K, sizeWeight_sizeBlind _, ?_⟩
    intro h
    have hbad := h 2 3 twoBridges threeVertsOneEdge
      ((postingAlphabet_equiv_iff_total twoBridges threeVertsOneEdge).mpr htot)
    simp only [sizeWeight] at hbad
    norm_num [twoBridges, threeVertsOneEdge] at hbad
  · intro h
    have hbad := h 2 3 twoBridges threeVertsOneEdge
      ((postingAlphabet_equiv_iff_total twoBridges threeVertsOneEdge).mpr htot)
    unfold gibbsWeight at hbad
    norm_num [twoBridges, threeVertsOneEdge, Nat.factorial] at hbad

/-! ## §7. Index

The record below is a **navigation index**, not a certificate.  Its fields are assigned by
hand and its `rfl` projections prove nothing about the mathematics; the evidence is the named
theorems in each field's docstring. -/

/-- What this module contains, as a hand-assigned index.  Read the named theorems, not these
Booleans. -/
structure ReachIndex where
  /-- `size_blindness_not_forced_by_the_other_hypotheses`: all five remaining hypotheses hold
  of a weight that is not size-blind and whose class mass is not the measure. -/
  reachBoundCompiled : Bool
  /-- `loopEscape_fails_the_atoms`: the three unit normalizations do exclude something, namely
  the loop-count escape.  The reach bound is stated against a statistic that survives them. -/
  normalizationsAreNotIdle : Bool
  /-- `statWeight_sizeBlind_at_one` and `classMass_statWeight_at_one`: at `lam = 1` every escape,
  the proper-edge one included, is size-blind and its class mass is exactly `mu`, so the witness
  separates for the right reason. -/
  positiveControlCompiled : Bool
  /-- `premise_one_iff_alphabetBlind`: premise (i) as written is equivalent to blindness to
  the sorted posting alphabet. -/
  alphabetEquivalenceCompiled : Bool
  /-- `postingAlphabet_is_determined_by_the_sizes`: the alphabet is a function of the size
  triple, so the equivalence above is a reformulation. -/
  postingAlphabetIsCoarse : Bool
  /-- `blindness_forces_premise_one_iff_coarse`: blindness to an invariant forces premise (i)
  exactly when the invariant is coarse, so no premise of that shape is both strictly weaker than
  premise (i) and sufficient for it. -/
  dichotomyCompiled : Bool
  /-- `fine_horn_survives_the_other_hypotheses`: the fine side holds against all five remaining
  hypotheses together, at one concrete invariant and not in general. -/
  fineHornSurvivesOtherHypotheses : Bool
  /-- `unsorted_is_strictly_stronger`: the sorting in the alphabet is load-bearing. -/
  sortingLoadBearing : Bool
  /-- Premise (i) is NOT derived. -/
  sizeBlindnessDerived : Bool
  /-- NOT proved: that the escape residue is exactly one constant per connected component
  class.  That needs connectedness of a complex, which exists nowhere in the library. -/
  connectedComponentLawProved : Bool

/-- The state of play after this module. -/
def reachIndex : ReachIndex where
  reachBoundCompiled := true
  normalizationsAreNotIdle := true
  positiveControlCompiled := true
  alphabetEquivalenceCompiled := true
  postingAlphabetIsCoarse := true
  dichotomyCompiled := true
  fineHornSurvivesOtherHypotheses := true
  sortingLoadBearing := true
  sizeBlindnessDerived := false
  connectedComponentLawProved := false

theorem index_not_derived : reachIndex.sizeBlindnessDerived = false := rfl
theorem index_no_component_law : reachIndex.connectedComponentLawProved = false := rfl

end Gap2SizeBlindnessReach
end SevenGaps
end Gravity
end IndisputableMonolith
