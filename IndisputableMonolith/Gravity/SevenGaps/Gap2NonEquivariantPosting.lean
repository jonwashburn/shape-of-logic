import IndisputableMonolith.Gravity.SevenGaps.Gap2PostingLayerFloor

/-!
# Gap 2: the non-equivariant posting case, resolved by a witness

`Gap2PostingCostDerivation.equivariant_posts_mu_iff_numerator_one` closes the posting-cost route
for every *equivariant* letter cost: such a cost posts `mu` exactly when its Boltzmann numerator
`exp(-historyCost)` is identically one, so the cost layer contributes no factor to the measure.
Its docstring names one case it does not settle, and `Gap2PostingLayerFloor` §4 exhibits the class
that case lives in (`vertexIndexCost_not_equivariant`) without deciding it:

> whether a **non**-equivariant cost can post `mu` with a numerator that is not identically one,
> by having the orbit sum of its Boltzmann factors come out to the orbit count while the
> individual terms differ.

This module settles it, **in the witness direction**.  It can, and a one-parameter family does.

## §1, the sharp condition, and it holds for every cost

The first content is not the witness; it is the statement the witness is a witness *to*.  For an
arbitrary letter cost, with no equivariance hypothesis anywhere,

* `classMass_postedWeight`: the class mass of a posted weight is the Gibbs weight times the total
  of the numerator over the class, because the divisor is a function of the three sizes and every
  labeled complex presenting the class has those sizes;
* `mu_eq_orbitCard_mul_gibbsWeight`: `mu` is the orbit count times that same Gibbs weight;
* `posts_mu_iff_numeratorMass_eq_orbitCard`: therefore posting `mu` is **exactly** the condition
  that the numerator's total over each gauge class equals that class's orbit count, i.e. that the
  numerator has **orbit mean one**.

That is a strict weakening of "identically one", and naming it is what makes the open case
answerable rather than mysterious.  `orbitMeanOne_forces_one_of_invariant` then shows where
equivariance was doing its work: an equivariant cost has a numerator that is *constant* on each
orbit, and a constant with mean one is one.  So the equivariant theorem is mean one plus
constancy, and only constancy fails below.

## §2-§4, the witness: an edge-label transposition and a sign that flips under it

Mean one with non-constant terms needs a way to split an orbit into halves that cancel.  The
device is an involution of the *labeled* carrier that preserves gauge classes: `twist` relabels a
complex by transposing edge letters `0` and `1` (`edgeRelabel`, `swap01`).  Two facts make it
work.  It lands in the same class, since it is a relabeling (`twistRel`, `twist_class`), and it is
an involution on the nose (`twist_twist`), so it is a permutation of the carrier (`twistEquiv`).

`edgeSign` reads the two transposed letters and compares the endpoint keys of their incidence
pairs, returning `+1`, `-1` or `0`.  Transposing the letters swaps the two keys, and the
comparison is antisymmetric, so `edgeSign_twist`: the sign changes sign under the twist.  A
summand the twist negates cancels in pairs along each orbit, which is `classMass_of_twistOdd`,
proved by reindexing the class sum along `twistEquiv` and observing that the sum equals its own
negation.

The cost is then read off the numerator we want rather than guessed: `tiltedNumer t K =
1 + t * edgeSign K`, which is positive for `|t| < 1` and satisfies `tiltedNumer t (twist K) =
2 - tiltedNumer t K`, so its excess over one is twist-odd and cancels.  `tiltedCost t` charges
every letter of `K` an equal share of `-log (tiltedNumer t K)`, so its history cost is exactly
`-log (tiltedNumer t K)` (`historyCost_tiltedCost`) and its numerator is exactly `tiltedNumer t K`
(`exp_neg_historyCost_tiltedCost`).  Nothing here is baked: the numerator identity is a theorem
about a sum over the alphabet, and neither `gibbsWeight` nor `mu` appears in the definition of the
cost, the sign, or the twist.

## The result

`nonequivariant_cost_posts_mu_with_nonunit_numerator` (at `t = 1/2`) and
`nonequivariant_posting_family` (for every `|t| < 1`, `t ≠ 0`):

* the cost is not gauge-equivariant (`tiltedCost_not_equivariant`);
* its class mass is `mu` at **every** complex at **every** cap (`tiltedCost_posts_mu`);
* its numerator is `1 + t` at `loopAndBridge`, hence not identically one
  (`numerator_ne_one_at_loopAndBridge`).

So the forward direction of `equivariant_posts_mu_iff_numerator_one` **fails without the
equivariance hypothesis**, and the hypothesis is load-bearing rather than convenient
(`equivariance_is_load_bearing`).  This is a family, not one accident: distinct tilts give
distinct numerators at the same complex (`family_injective_at_loopAndBridge`), so a continuum of
letter costs posts `mu` exactly.

## What this does NOT show, stated before anyone reads it as more

**It does not derive the measure, and it does not weaken the uniqueness wall.**  It moves the
non-equivariant case from OPEN to underdetermined, which is the *opposite* of progress toward a
derivation: where the equivariant class contained exactly one posted numerator compatible with
`mu`, the full class contains a continuum.  The narrow true statement about determination: among
costs which post `mu`, the cost contributes no factor to the *class* mass; costs that fail to post
it exist and do constrain the measure (`Gap2PostingCostDerivation.incidencePosting_classMass_ne_mu`),
and the criterion `posts_mu_iff_numeratorMass_eq_orbitCard` discriminates the two.  What changes is
that the reason is no longer rigidity, and orbit-mean-one is a strictly weaker, hypothesis-free
target for any future premise-level selection principle on letter costs.

**It does not contradict `Gap2GaugeVolume.invariant_weight_gives_measure_iff`.**  That theorem
quantifies over relabeling-invariant labeled weights, and the witness's posted weight is not one
(`postedWeight_tiltedCost_not_invariant`): it is `(1+t)` times the Gibbs weight at `loopAndBridge`
and `(1-t)` times it at the twist, which are gauge-equivalent.  The witness escapes the class the
wall quantifies over; it does not breach the wall.

**It does not put a non-unit numerator anywhere the normalizations look.**  The sign vanishes
whenever a complex has fewer than two edge letters (`edgeSign_eq_zero_of_nE_le_one`), so the
numerator is one at the empty complex and at all three atoms, and the witness satisfies
`NormalizedAtTheAtoms` (`normalizedAtTheAtoms_tiltedCost`).  The non-unit values live only where
the sector group moves a complex to a *different* labeled complex in the same class, which is the
only place they could live: on a class whose orbit is a single labeled complex, mean one is
literally "the one term is one", for any cost whatever.

**It says nothing about what a substrate posts.**  `Equivariant` is the posting-layer form of
"labels are gauge"; a cost that fails it charges two labelings of one complex differently.
Whether the ledger does that is not a question any theorem here answers, and the premise the
measure rests on is still the one `Gap2GaugeVolume` named, unit sector fugacity, reducible to the
gluing law and not to anything proved here.

**It is a witness at one carrier cap for the non-unit half.**  The posting identity
`tiltedCost_posts_mu` is proved for every `B` and every complex; the non-unit numerator is
exhibited at `B = 3` on `loopAndBridge`.  One complex is all a counterexample needs, and no claim
is made that the sign is non-vanishing on most complexes: it is not.

## Honest tagging

Every declaration below is THEOREM (kernel-checked in this module).  The headline certificates,
the criterion, the witness, and the family injectivity are audited by `#print axioms` at the foot,
each at the base triple only.  The reading of `LetterCost` as a substrate charging rule, of `historyCost` as
ledger additivity over postings, and of the Boltzmann form, are the same three MODEL attachments
`Gap2PostingCostDerivation` names in its header; this module inherits them and adds none.

**Strength.**  The witness is an exact equality of reals at every complex and every cap, not an
agreement to a tolerance, and the family is a continuum rather than a single point.  The non-unit
claim is exact: the numerator at `loopAndBridge` is `1 + t`, so `3/2` at the tilt used in the
headline, against `1`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2NonEquivariantPosting

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation

noncomputable section

variable {B : ℕ}

/-! ## §0. Two pieces of bookkeeping

`sgnLt` is a comparison written as a difference of indicators rather than a nest of branches,
which is what makes its antisymmetry a `ring` step instead of a case analysis.  `classMass` is
linear, and the four lemmas that say so are used throughout. -/

/-- The comparison sign of two naturals, as a difference of indicators: `1` if `x < y`, `-1` if
`y < x`, `0` if neither.  Written this way on purpose: `sgnLt_swap` is then `ring`. -/
def sgnLt (x y : ℕ) : ℝ := (if x < y then (1 : ℝ) else 0) - (if y < x then (1 : ℝ) else 0)

/-- **The antisymmetry.**  Swapping the arguments negates the sign.  This is the whole mechanism
of the witness, and it is one `ring` call because the definition is a difference. -/
theorem sgnLt_swap (x y : ℕ) : sgnLt y x = -sgnLt x y := by
  unfold sgnLt
  ring

/-- The sign takes only three values, so a tilt of size less than one keeps `1 + t · sign`
positive. -/
theorem sgnLt_cases (x y : ℕ) : sgnLt x y = 1 ∨ sgnLt x y = -1 ∨ sgnLt x y = 0 := by
  unfold sgnLt
  split_ifs <;> norm_num

theorem classMass_zero (cl : TriangulationClass B) :
    classMass (fun _ : BoundedComplex B => (0 : ℝ)) cl = 0 := by
  classical
  unfold classMass
  exact Finset.sum_eq_zero fun K _ => by split_ifs <;> rfl

theorem classMass_add (D E : BoundedComplex B → ℝ) (cl : TriangulationClass B) :
    classMass (fun K => D K + E K) cl = classMass D cl + classMass E cl := by
  classical
  unfold classMass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun K _ => by split_ifs <;> simp

theorem classMass_neg (D : BoundedComplex B → ℝ) (cl : TriangulationClass B) :
    classMass (fun K => -D K) cl = -classMass D cl := by
  have h : classMass (fun K => D K + -D K) cl
      = classMass D cl + classMass (fun K => -D K) cl :=
    classMass_add D (fun K => -D K) cl
  have h0 : (fun K : BoundedComplex B => D K + -D K) = fun _ : BoundedComplex B => (0 : ℝ) := by
    funext K
    ring
  rw [h0, classMass_zero] at h
  linarith

/-- The class mass of the constant weight one is the orbit count. -/
theorem classMass_one (K : BoundedComplex B) :
    classMass (fun _ : BoundedComplex B => (1 : ℝ)) (Quotient.mk (relabelSetoid B) K)
      = (gaugeOrbitCard K : ℝ) := by
  have h := classMass_of_invariant (fun _ : BoundedComplex B => (1 : ℝ))
    (fun _ _ _ => rfl) (Quotient.mk (relabelSetoid B) K)
  simp only [orbitCardClass_mk, mul_one] at h
  exact h

/-! ## §1. The sharp condition for posting `mu`, with no equivariance hypothesis

`equivariant_posts_mu_iff_numerator_one` reads the collapse off
`Gap2GaugeVolume.invariant_weight_gives_measure_iff`, which needs invariance.  Underneath that
theorem there is an identity needing nothing: the divisor is a class function, so it factors out
of the class sum, and what is left is a condition on the numerator's *total* over the class.  That
total is the object the open case is about. -/

/-- The **numerator mass** of a letter cost: the total of its Boltzmann numerator over the labeled
complexes presenting a class.  Written with the module's own `classMass` functional so that no new
summation or decidability convention enters. -/
def numeratorMass (c : LetterCost) (B : ℕ) : TriangulationClass B → ℝ :=
  classMass (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K')))

/-- **THEOREM (the divisor factors out of every class sum).**  For an arbitrary letter cost, the
class mass of its posted weight is the Gibbs weight of any representative times the numerator
mass of the class.  No equivariance and no premise on the cost: the only input is that
`gibbsWeight` is a class function (`gibbsWeight_invariant`), which holds because it is a function
of the three sizes. -/
theorem classMass_postedWeight (c : LetterCost) (B : ℕ) (K : BoundedComplex B) :
    classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K)
      = gibbsWeight K * numeratorMass c B (Quotient.mk (relabelSetoid B) K) := by
  classical
  unfold numeratorMass classMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K' _ => ?_
  by_cases hc : Quotient.mk (relabelSetoid B) K' = Quotient.mk (relabelSetoid B) K
  · rw [if_pos hc, if_pos hc]
    unfold postedWeight
    rw [gibbsWeight_invariant (Quotient.exact hc)]
    ring
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- **THEOREM (`mu` is the orbit count times the gauge volume, in posted form).**  Recorded in the
shape the criterion below needs.  This is `Gap2GaugeVolume`'s orbit-stabilizer accounting read
through `classMass`, not a new fact. -/
theorem mu_eq_orbitCard_mul_gibbsWeight (K : BoundedComplex B) :
    mu K = (gaugeOrbitCard K : ℝ) * gibbsWeight K := by
  have h := classMass_of_invariant (fun K' : BoundedComplex B => gibbsWeight K')
    (fun _ _ hh => gibbsWeight_invariant hh) (Quotient.mk (relabelSetoid B) K)
  simp only [orbitCardClass_mk] at h
  rw [classMass_gibbsWeight_eq_mu K, gibbsWeight_invariant (equivalent_out K)] at h
  exact h

/-- **THEOREM (the sharp condition: orbit mean one).**  For **every** letter cost, equivariant or
not, the posted weight has class mass `mu` at a complex exactly when its Boltzmann numerator
totals that complex's orbit count over the class, i.e. exactly when the numerator has mean one on
that gauge orbit.

This is the statement `equivariant_posts_mu_iff_numerator_one` specializes.  Saying it in this
form is what turns the open case into a question with an answer: "identically one" is strictly
stronger than "mean one", and the gap between them is exactly the room a non-equivariant cost has
to move in. -/
theorem posts_mu_iff_numeratorMass_eq_orbitCard (c : LetterCost) (B : ℕ) (K : BoundedComplex B) :
    classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K
      ↔ numeratorMass c B (Quotient.mk (relabelSetoid B) K) = (gaugeOrbitCard K : ℝ) := by
  have hg : (0 : ℝ) < gibbsWeight K := gibbsWeight_positive K
  rw [classMass_postedWeight, mu_eq_orbitCard_mul_gibbsWeight]
  constructor
  · intro h
    have h' : gibbsWeight K * numeratorMass c B (Quotient.mk (relabelSetoid B) K)
        = gibbsWeight K * (gaugeOrbitCard K : ℝ) := by
      rw [h]; ring
    exact mul_left_cancel₀ (ne_of_gt hg) h'
  · intro h
    rw [h]
    ring

/-- **THEOREM (where equivariance was doing its work).**  If a cost's history cost is a class
function, which is what equivariance buys (`historyCost_invariant`), then its numerator is
constant on each orbit, and orbit mean one forces the value one.

So the equivariant collapse decomposes into two independent halves: mean one, which is forced by
`mu` for every cost, and constancy on orbits, which is forced only by invariance.  Everything
below attacks the second half. -/
theorem orbitMeanOne_forces_one_of_invariant (c : LetterCost) (B : ℕ)
    (hinv : ∀ K K' : BoundedComplex B, Equivalent K K' →
      historyCost c B K = historyCost c B K') (K : BoundedComplex B)
    (h : numeratorMass c B (Quotient.mk (relabelSetoid B) K) = (gaugeOrbitCard K : ℝ)) :
    Real.exp (-(historyCost c B K)) = 1 := by
  have hnum : ∀ K₁ K₂ : BoundedComplex B, Equivalent K₁ K₂ →
      Real.exp (-(historyCost c B K₁)) = Real.exp (-(historyCost c B K₂)) := by
    intro K₁ K₂ he
    rw [hinv K₁ K₂ he]
  have hc := classMass_of_invariant
    (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K'))) hnum
    (Quotient.mk (relabelSetoid B) K)
  simp only [orbitCardClass_mk] at hc
  unfold numeratorMass at h
  rw [hc, hnum _ K (equivalent_out K)] at h
  have horb : (0 : ℝ) < (gaugeOrbitCard K : ℝ) := by
    exact_mod_cast gaugeOrbitCard_pos K
  have h' : (gaugeOrbitCard K : ℝ) * Real.exp (-(historyCost c B K))
      = (gaugeOrbitCard K : ℝ) * 1 := by
    rw [mul_one]; exact h
  exact mul_left_cancel₀ (ne_of_gt horb) h'

/-! ## §2. The twist: transposing two edge letters is a class-preserving involution

The carrier permutation the cancellation runs on.  `edgeRelabel` renames the edge index set,
which is a gauge motion by construction; `swap01` is the transposition of `0` and `1` in `Fin n`,
the identity when `n < 2`; `twist` is their composite.  What has to be true, and is proved rather
than assumed, is that the twist stays inside the gauge class and squares to the identity. -/

/-- Transpose `0` and `1` in `Fin n`; the identity when there is no `1` to transpose.  Stated for a
bare `n` rather than for `K.nE` so that the twist of a twist reduces without dependent friction. -/
def swap01 (n : ℕ) : Equiv.Perm (Fin n) :=
  if h : 1 < n then Equiv.swap ⟨0, by omega⟩ ⟨1, h⟩ else Equiv.refl _

theorem swap01_involutive (n : ℕ) : Function.Involutive (swap01 n) := by
  intro e
  unfold swap01
  by_cases h : 1 < n
  · rw [dif_pos h]
    exact Equiv.swap_apply_self _ _ _
  · rw [dif_neg h]
    rfl

theorem swap01_trans_self (n : ℕ) : (swap01 n).trans (swap01 n) = Equiv.refl (Fin n) :=
  Equiv.ext fun e => swap01_involutive n e

theorem swap01_apply_zero {n : ℕ} (h : 1 < n) (h0 : 0 < n) : swap01 n ⟨0, h0⟩ = ⟨1, h⟩ := by
  unfold swap01
  rw [dif_pos h]
  exact Equiv.swap_apply_left _ _

theorem swap01_apply_one {n : ℕ} (h : 1 < n) (h0 : 0 < n) : swap01 n ⟨1, h⟩ = ⟨0, h0⟩ := by
  unfold swap01
  rw [dif_pos h]
  exact Equiv.swap_apply_right _ _

/-- Rename the edge index set of `K` by a permutation of it, keeping the incidence pairs and
everything else.  A gauge motion at the labeled level. -/
def edgeRelabel (K : BoundedComplex B) (σ : Equiv.Perm (Fin K.nE)) : BoundedComplex B where
  nV := K.nV
  nE := K.nE
  nT := K.nT
  hV := K.hV
  hE := K.hE
  hT := K.hT
  edgeVerts := fun e => K.edgeVerts (σ e)
  tetVerts := K.tetVerts

/-- **The twist**: the complex with its first two edge letters exchanged. -/
def twist (K : BoundedComplex B) : BoundedComplex B := edgeRelabel K (swap01 K.nE)

theorem twist_nE (K : BoundedComplex B) : (twist K).nE = K.nE := rfl

theorem twist_edgeVerts (K : BoundedComplex B) (e : Fin K.nE) :
    (twist K).edgeVerts e = K.edgeVerts (swap01 K.nE e) := rfl

/-- **THEOREM (the twist is an involution).**  Twisting twice composes the transposition with
itself, which is the identity permutation, and renaming by the identity is the complex itself. -/
theorem twist_twist (K : BoundedComplex B) : twist (twist K) = K := by
  have h1 : twist (twist K) = edgeRelabel K ((swap01 K.nE).trans (swap01 K.nE)) := rfl
  have h2 : edgeRelabel K (Equiv.refl (Fin K.nE)) = K := rfl
  rw [h1, swap01_trans_self, h2]

/-- The twist as a permutation of the labeled carrier: what the class sums are reindexed along. -/
def twistEquiv (B : ℕ) : BoundedComplex B ≃ BoundedComplex B where
  toFun := twist
  invFun := twist
  left_inv := twist_twist
  right_inv := twist_twist

theorem twistEquiv_apply (B : ℕ) (K : BoundedComplex B) : twistEquiv B K = twist K := rfl

/-- **THEOREM (the twist is a relabeling).**  The transposition of edge letters, with the identity
on vertices and tetrahedra, satisfies the incidence commutation conditions onto the twisted
complex.  This is what keeps the twist inside the gauge class. -/
def twistRel (K : BoundedComplex B) : Relabel K (twist K) where
  vEquiv := Equiv.refl _
  eEquiv := swap01 K.nE
  tEquiv := Equiv.refl _
  edge_comm := fun e => by
    show K.edgeVerts (swap01 K.nE (swap01 K.nE e)) = K.edgeVerts e
    rw [swap01_involutive K.nE e]
  tet_comm := fun _ _ => rfl

theorem twist_equivalent (K : BoundedComplex B) : Equivalent K (twist K) := ⟨twistRel K⟩

theorem twist_class (K : BoundedComplex B) :
    Quotient.mk (relabelSetoid B) (twist K) = Quotient.mk (relabelSetoid B) K :=
  (Quotient.sound (twist_equivalent K)).symm

/-! ## §3. Twist-odd functions have zero total on every class

The cancellation lemma.  Reindexing a class sum along the twist changes nothing, because the twist
preserves classes and permutes the carrier; so a summand the twist negates gives a sum equal to
its own negation. -/

/-- Reindexing a class sum along the twist leaves it unchanged. -/
theorem classMass_comp_twist (D : BoundedComplex B → ℝ) (cl : TriangulationClass B) :
    classMass (fun K => D (twist K)) cl = classMass D cl := by
  classical
  unfold classMass
  refine Fintype.sum_equiv (twistEquiv B) _ _ fun K => ?_
  rw [twistEquiv_apply, twist_class]

/-- **THEOREM (the cancellation lemma).**  A real function on labeled complexes that the twist
negates has total zero over every gauge class.  Two lines of content: the class sum is invariant
under reindexing by the twist, and the twist negates the summand, so the sum is its own
negation. -/
theorem classMass_of_twistOdd (D : BoundedComplex B → ℝ)
    (hodd : ∀ K : BoundedComplex B, D (twist K) = -D K) (cl : TriangulationClass B) :
    classMass D cl = 0 := by
  have h1 : classMass (fun K => D (twist K)) cl = classMass D cl := classMass_comp_twist D cl
  have h2 : (fun K : BoundedComplex B => D (twist K)) = fun K : BoundedComplex B => -D K :=
    funext hodd
  rw [h2, classMass_neg] at h1
  linarith

/-! ## §4. The sign that flips, and the cost built from it

The one thing left is a function of the labeled complex that the twist negates.  The twist
exchanges edge letters `0` and `1`, so anything that compares those two letters antisymmetrically
will do.  `keyAt` is the endpoint pair of a numbered edge letter, packed into one natural number
with the size cap as radix.  `edgeSign` compares letters `0` and `1`, and is silent wherever there
is no second letter. -/

/-- The endpoint pair of edge letter `i`, packed into one natural number; `0` when the complex has
no letter `i`.  Total in `i` by design. -/
def keyAt (K : BoundedComplex B) (i : ℕ) : ℕ :=
  if h : i < K.nE then (K.edgeVerts ⟨i, h⟩).1.val * B + (K.edgeVerts ⟨i, h⟩).2.val else 0

theorem keyAt_of_lt {K : BoundedComplex B} {i : ℕ} (h : i < K.nE) :
    keyAt K i = (K.edgeVerts ⟨i, h⟩).1.val * B + (K.edgeVerts ⟨i, h⟩).2.val :=
  dif_pos h

/-- Reading a key through the twist reads the transposed letter.  Stated for whichever pair of
letters the transposition exchanges, so the two directions below are one lemma applied twice. -/
theorem keyAt_twist {K : BoundedComplex B} {i j : ℕ} (hi : i < K.nE) (hj : j < K.nE)
    (hij : swap01 K.nE ⟨i, hi⟩ = ⟨j, hj⟩) : keyAt (twist K) i = keyAt K j := by
  have hi' : i < (twist K).nE := hi
  have e1 : keyAt (twist K) i
      = ((twist K).edgeVerts ⟨i, hi'⟩).1.val * B + ((twist K).edgeVerts ⟨i, hi'⟩).2.val :=
    keyAt_of_lt hi'
  have e2 : keyAt K j = (K.edgeVerts ⟨j, hj⟩).1.val * B + (K.edgeVerts ⟨j, hj⟩).2.val :=
    keyAt_of_lt hj
  have e3 : (twist K).edgeVerts ⟨i, hi'⟩ = K.edgeVerts ⟨j, hj⟩ := by
    have e4 : (twist K).edgeVerts ⟨i, hi'⟩ = K.edgeVerts (swap01 K.nE ⟨i, hi⟩) := rfl
    rw [e4, hij]
  rw [e1, e2, e3]

theorem keyAt_twist_zero {K : BoundedComplex B} (h : 1 < K.nE) :
    keyAt (twist K) 0 = keyAt K 1 := by
  have h0 : (0 : ℕ) < K.nE := by omega
  exact keyAt_twist h0 h (swap01_apply_zero h h0)

theorem keyAt_twist_one {K : BoundedComplex B} (h : 1 < K.nE) :
    keyAt (twist K) 1 = keyAt K 0 := by
  have h0 : (0 : ℕ) < K.nE := by omega
  exact keyAt_twist h h0 (swap01_apply_one h h0)

/-- The **sign of a labeled complex**: the comparison of the endpoint keys of its first two edge
letters, and `0` when it has fewer than two.  This is the only place the witness reads a label
rather than a class invariant, and it is what makes the cost non-equivariant. -/
def edgeSign (K : BoundedComplex B) : ℝ :=
  if 1 < K.nE then sgnLt (keyAt K 0) (keyAt K 1) else 0

theorem edgeSign_cases (K : BoundedComplex B) :
    edgeSign K = 1 ∨ edgeSign K = -1 ∨ edgeSign K = 0 := by
  unfold edgeSign
  by_cases h : 1 < K.nE
  · rw [if_pos h]
    exact sgnLt_cases _ _
  · rw [if_neg h]
    exact Or.inr (Or.inr rfl)

/-- The sign is silent on every complex with fewer than two edge letters, hence at the empty
complex and at all three atoms.  This is the scope clause of the whole construction: the witness
puts nothing non-unit where the normalizations look. -/
theorem edgeSign_eq_zero_of_nE_le_one (K : BoundedComplex B) (h : K.nE ≤ 1) : edgeSign K = 0 := by
  unfold edgeSign
  rw [if_neg (by omega : ¬ 1 < K.nE)]

/-- **THEOREM (the sign flips under the twist).**  The twist exchanges edge letters `0` and `1`,
so it exchanges their keys, and the comparison is antisymmetric.  The vanishing case is stable
because the twist preserves the edge count. -/
theorem edgeSign_twist (K : BoundedComplex B) : edgeSign (twist K) = -edgeSign K := by
  by_cases h : 1 < K.nE
  · have hT : 1 < (twist K).nE := h
    unfold edgeSign
    rw [if_pos hT, if_pos h, keyAt_twist_zero h, keyAt_twist_one h,
      sgnLt_swap (keyAt K 0) (keyAt K 1)]
  · have hT : (twist K).nE ≤ 1 := by
      have hEq : (twist K).nE = K.nE := twist_nE K
      omega
    rw [edgeSign_eq_zero_of_nE_le_one (twist K) hT,
      edgeSign_eq_zero_of_nE_le_one K (by omega), neg_zero]

/-! ### The numerator, and the cost that posts it -/

/-- The **tilted numerator**: one plus `t` times the sign.  This is the Boltzmann numerator the
witness is built to have, and the two facts it needs are that it is positive (so it is an
exponential of something real) and that it and its twist average to one. -/
def tiltedNumer (t : ℝ) (K : BoundedComplex B) : ℝ := 1 + t * edgeSign K

theorem tiltedNumer_pos {t : ℝ} (ht : |t| < 1) (K : BoundedComplex B) : 0 < tiltedNumer t K := by
  obtain ⟨h1, h2⟩ := abs_lt.mp ht
  unfold tiltedNumer
  rcases edgeSign_cases K with h | h | h <;> rw [h] <;> linarith

/-- **The cancellation identity.**  A complex and its twist carry numerators averaging to one.
Nothing about `mu` or `gibbsWeight` enters: this is `edgeSign_twist` and arithmetic. -/
theorem tiltedNumer_twist (t : ℝ) (K : BoundedComplex B) :
    tiltedNumer t (twist K) = 2 - tiltedNumer t K := by
  unfold tiltedNumer
  rw [edgeSign_twist]
  ring

theorem tiltedNumer_eq_one_of_nE_le_one (t : ℝ) (K : BoundedComplex B) (h : K.nE ≤ 1) :
    tiltedNumer t K = 1 := by
  unfold tiltedNumer
  rw [edgeSign_eq_zero_of_nE_le_one K h, mul_zero, add_zero]

/-- The **witness letter cost**: every letter of `K` is charged an equal share of
`-log (tiltedNumer t K)`.  The cost reads the labeling through `edgeSign`, which is exactly why it
is not equivariant. -/
def tiltedCost (t : ℝ) : LetterCost := fun _ K _ =>
  -(Real.log (tiltedNumer t K)) / ((K.nV + K.nE + K.nT : ℕ) : ℝ)

/-- **THEOREM (the history cost is what it was designed to be).**  Summing the shared charge over
the alphabet returns the whole of `-log (tiltedNumer t K)`, at every complex including the empty
one, where both sides vanish because a complex with no cells has no edge letters and hence unit
numerator.  This is the theorem that keeps the numerator claim from being an assumption. -/
theorem historyCost_tiltedCost (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (tiltedCost t) B K = -(Real.log (tiltedNumer t K)) := by
  have hcard : (Finset.univ : Finset (PostingAlphabet K)).card = K.nV + K.nE + K.nT := by
    rw [Finset.card_univ, card_postingAlphabet]
  unfold historyCost tiltedCost
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  by_cases hN : K.nV + K.nE + K.nT = 0
  · have h1 : tiltedNumer t K = 1 := tiltedNumer_eq_one_of_nE_le_one t K (by omega)
    rw [h1, Real.log_one, neg_zero, zero_div, mul_zero]
  · have hne : ((K.nV + K.nE + K.nT : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp

/-- **THEOREM (the Boltzmann numerator of the witness).**  Exactly `tiltedNumer t K`. -/
theorem exp_neg_historyCost_tiltedCost {t : ℝ} (ht : |t| < 1) (B : ℕ) (K : BoundedComplex B) :
    Real.exp (-(historyCost (tiltedCost t) B K)) = tiltedNumer t K := by
  rw [historyCost_tiltedCost, neg_neg, Real.exp_log (tiltedNumer_pos ht K)]

theorem postedWeight_tiltedCost {t : ℝ} (ht : |t| < 1) (B : ℕ) (K : BoundedComplex B) :
    postedWeight (tiltedCost t) B K = tiltedNumer t K * gibbsWeight K := by
  unfold postedWeight
  rw [exp_neg_historyCost_tiltedCost ht]

/-! ### The witness posts `mu` -/

/-- The numerator mass of the witness is the orbit count: the excess over one is twist-odd, so it
cancels, and what survives is the constant one summed over the class. -/
theorem numeratorMass_tiltedCost {t : ℝ} (ht : |t| < 1) (B : ℕ) (K : BoundedComplex B) :
    numeratorMass (tiltedCost t) B (Quotient.mk (relabelSetoid B) K)
      = (gaugeOrbitCard K : ℝ) := by
  have hodd : ∀ K' : BoundedComplex B,
      tiltedNumer t (twist K') - 1 = -(tiltedNumer t K' - 1) := by
    intro K'
    rw [tiltedNumer_twist]
    ring
  have hzero : classMass (fun K' : BoundedComplex B => tiltedNumer t K' - 1)
      (Quotient.mk (relabelSetoid B) K) = 0 :=
    classMass_of_twistOdd (fun K' : BoundedComplex B => tiltedNumer t K' - 1) hodd _
  have hsplit := classMass_add (fun _ : BoundedComplex B => (1 : ℝ))
    (fun K' : BoundedComplex B => tiltedNumer t K' - 1) (Quotient.mk (relabelSetoid B) K)
  have hfun : (fun K' : BoundedComplex B => Real.exp (-(historyCost (tiltedCost t) B K')))
      = fun K' : BoundedComplex B => (1 : ℝ) + (tiltedNumer t K' - 1) := by
    funext K'
    rw [exp_neg_historyCost_tiltedCost ht]
    ring
  unfold numeratorMass
  rw [hfun, hsplit, hzero, add_zero, classMass_one]

/-- **THEOREM (the witness posts the measure exactly).**  For every tilt of size less than one, at
every cap and every complex, the class mass of the witness's posted weight is `mu`. -/
theorem tiltedCost_posts_mu {t : ℝ} (ht : |t| < 1) (B : ℕ) (K : BoundedComplex B) :
    classMass (postedWeight (tiltedCost t) B) (Quotient.mk (relabelSetoid B) K) = mu K :=
  (posts_mu_iff_numeratorMass_eq_orbitCard (tiltedCost t) B K).mpr
    (numeratorMass_tiltedCost ht B K)

/-! ### The numerator is not identically one

`loopAndBridge` is `Gap2PostingCostDerivation`'s three-vertex complex with one loop `(0,0)` and
one proper edge `(1,2)`.  Its two edge letters carry different endpoint keys, `0` against `5`, so
the sign is `+1` and the numerator is `1 + t`. -/

theorem keyAt_loopAndBridge_zero : keyAt loopAndBridge 0 = 0 := by decide

theorem keyAt_loopAndBridge_one : keyAt loopAndBridge 1 = 5 := by decide

theorem edgeSign_loopAndBridge : edgeSign loopAndBridge = 1 := by
  unfold edgeSign
  rw [if_pos (show 1 < loopAndBridge.nE by decide),
    keyAt_loopAndBridge_zero, keyAt_loopAndBridge_one]
  unfold sgnLt
  norm_num

theorem tiltedNumer_loopAndBridge (t : ℝ) : tiltedNumer t loopAndBridge = 1 + t := by
  unfold tiltedNumer
  rw [edgeSign_loopAndBridge, mul_one]

/-- **THEOREM (a non-unit numerator).**  At `loopAndBridge` the witness's Boltzmann numerator is
`1 + t`, so for any nonzero tilt it is not one. -/
theorem numerator_ne_one_at_loopAndBridge {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    Real.exp (-(historyCost (tiltedCost t) 3 loopAndBridge)) ≠ 1 := by
  rw [exp_neg_historyCost_tiltedCost ht, tiltedNumer_loopAndBridge]
  intro h
  exact ht0 (by linarith)

/-! ### The witness is not equivariant

It cannot be, given the two theorems above: an equivariant cost with class mass `mu` has unit
numerator.  But the failure is exhibited directly rather than inferred, because the whole point is
that this cost lives outside the class the wall quantifies over. -/

/-- **THEOREM (the witness is label-asymmetric).**  Its history cost differs between
`loopAndBridge` and the twist of it, which are gauge-equivalent, so it is not equivariant. -/
theorem tiltedCost_not_equivariant {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    ¬ Equivariant (tiltedCost t) := by
  intro hc
  have h : historyCost (tiltedCost t) 3 loopAndBridge
      = historyCost (tiltedCost t) 3 (twist loopAndBridge) :=
    historyCost_invariant hc (twistRel loopAndBridge)
  have h2 : tiltedNumer t loopAndBridge = tiltedNumer t (twist loopAndBridge) := by
    rw [← exp_neg_historyCost_tiltedCost ht 3 loopAndBridge,
      ← exp_neg_historyCost_tiltedCost ht 3 (twist loopAndBridge), h]
  rw [tiltedNumer_twist, tiltedNumer_loopAndBridge] at h2
  exact ht0 (by linarith)

/-- **THEOREM (the witness escapes the uniqueness wall rather than breaching it).**  Its posted
weight is not a relabeling-invariant labeled weight: `loopAndBridge` and its twist are
gauge-equivalent and carry `(1+t)` and `(1-t)` times the same Gibbs weight.  So
`Gap2GaugeVolume.invariant_weight_gives_measure_iff`, which quantifies over invariant weights, is
untouched, and this module contradicts nothing in the library. -/
theorem postedWeight_tiltedCost_not_invariant {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    ¬ (∀ K K' : BoundedComplex 3, Equivalent K K' →
        postedWeight (tiltedCost t) 3 K = postedWeight (tiltedCost t) 3 K') := by
  intro hinv
  have hEq := hinv loopAndBridge (twist loopAndBridge) (twist_equivalent loopAndBridge)
  rw [postedWeight_tiltedCost ht, postedWeight_tiltedCost ht,
    gibbsWeight_invariant (twist_equivalent loopAndBridge)] at hEq
  have hg : (0 : ℝ) < gibbsWeight (twist loopAndBridge) := gibbsWeight_positive _
  have h2 : tiltedNumer t loopAndBridge = tiltedNumer t (twist loopAndBridge) :=
    mul_right_cancel₀ (ne_of_gt hg) hEq
  rw [tiltedNumer_twist, tiltedNumer_loopAndBridge] at h2
  exact ht0 (by linarith)

/-- **THEOREM (the witness meets the normalizations too).**  Its posted weight is one at the empty
complex and at all three atoms, because a complex with at most one edge letter has unit numerator
and unit gauge volume.  So the witness is not excluded by `NormalizedAtTheAtoms`, and the reason
is structural: the sign has nothing to compare there. -/
theorem normalizedAtTheAtoms_tiltedCost {t : ℝ} (ht : |t| < 1) :
    NormalizedAtTheAtoms (postedWeight (tiltedCost t)) := by
  intro B' K hv hi
  rw [postedWeight_tiltedCost ht, tiltedNumer_eq_one_of_nE_le_one t K (by omega), one_mul,
    gibbsWeight_eq_one_at_atoms K hv hi]

/-! ## §5. The open case, resolved -/

/-- **THE OPEN CASE, RESOLVED IN THE WITNESS DIRECTION.**  At tilt `1/2`: a letter cost that is
not gauge-equivariant, whose posted weight has class mass exactly `mu` at every complex at every
cap, and whose Boltzmann numerator at `loopAndBridge` is `3/2` rather than `1`.

This is the case `equivariant_posts_mu_iff_numerator_one` left open and `Gap2PostingLayerFloor` §4
showed inhabited without deciding.  It is now decided: orbit-sum cancellation is real, and the
forward implication of that theorem is false without its equivariance hypothesis. -/
theorem nonequivariant_cost_posts_mu_with_nonunit_numerator :
    ¬ Equivariant (tiltedCost (1/2))
      ∧ (∀ (B : ℕ) (K : BoundedComplex B),
          classMass (postedWeight (tiltedCost (1/2)) B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ∧ Real.exp (-(historyCost (tiltedCost (1/2)) 3 loopAndBridge)) = 3/2
      ∧ NormalizedAtTheAtoms (postedWeight (tiltedCost (1/2))) := by
  have ht : |(1/2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have ht0 : (1/2 : ℝ) ≠ 0 := by norm_num
  refine ⟨tiltedCost_not_equivariant ht ht0, fun B K => tiltedCost_posts_mu ht B K, ?_,
    normalizedAtTheAtoms_tiltedCost ht⟩
  rw [exp_neg_historyCost_tiltedCost ht, tiltedNumer_loopAndBridge]
  norm_num

/-- **THEOREM (the equivariance hypothesis is load-bearing).**  The equivalence
`equivariant_posts_mu_iff_numerator_one` fails when its hypothesis is dropped: there is a letter
cost posting `mu` at every complex of `BoundedComplex 3` whose numerator is not identically one.
Stated in exactly the shape of that theorem's two sides so the failure is checkable against it. -/
theorem equivariance_is_load_bearing :
    ∃ c : LetterCost,
      ¬ Equivariant c
        ∧ (∀ K : BoundedComplex 3,
            classMass (postedWeight c 3) (Quotient.mk (relabelSetoid 3) K) = mu K)
        ∧ ¬ (∀ K : BoundedComplex 3, Real.exp (-(historyCost c 3 K)) = 1) := by
  have ht : |(1/2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have ht0 : (1/2 : ℝ) ≠ 0 := by norm_num
  refine ⟨tiltedCost (1/2), tiltedCost_not_equivariant ht ht0,
    fun K => tiltedCost_posts_mu ht 3 K, ?_⟩
  intro hall
  exact numerator_ne_one_at_loopAndBridge ht ht0 (hall loopAndBridge)

/-- **THEOREM (a continuum, not an accident).**  Every tilt of size less than one gives a cost
posting `mu` exactly, and for nonzero tilt the cost is not equivariant and the numerator is not
identically one.  So the non-equivariant class does not contain one exceptional cost compatible
with the measure; it contains a one-parameter family. -/
theorem nonequivariant_posting_family {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    ¬ Equivariant (tiltedCost t)
      ∧ (∀ (B : ℕ) (K : BoundedComplex B),
          classMass (postedWeight (tiltedCost t) B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ∧ Real.exp (-(historyCost (tiltedCost t) 3 loopAndBridge)) = 1 + t :=
  ⟨tiltedCost_not_equivariant ht ht0, fun B K => tiltedCost_posts_mu ht B K, by
    rw [exp_neg_historyCost_tiltedCost ht, tiltedNumer_loopAndBridge]⟩

/-- The family is faithfully parametrized: distinct tilts give distinct numerators at the same
complex, so the costs above are genuinely different and the underdetermination is a continuum. -/
theorem family_injective_at_loopAndBridge {t s : ℝ}
    (h : tiltedNumer t loopAndBridge = tiltedNumer s loopAndBridge) : t = s := by
  rw [tiltedNumer_loopAndBridge, tiltedNumer_loopAndBridge] at h
  linarith

/-- **THEOREM (what the resolution changes, and what it does not).**  The five-part verdict.

1.  For every letter cost, equivariant or not, posting `mu` is exactly orbit mean one on the
    numerator (`posts_mu_iff_numeratorMass_eq_orbitCard`).
2.  Equivariance upgrades mean one to identically one only because it makes the numerator constant
    on orbits (`orbitMeanOne_forces_one_of_invariant`).
3.  Without it the upgrade fails: a label-reading cost posts `mu` with a non-unit numerator.
4.  That cost's posted weight is not relabeling-invariant, so the uniqueness wall is escaped, not
    breached.
5.  Its numerator is one wherever a complex has at most one edge letter, so the atom
    normalizations are met and the non-unit values sit only on classes the sector group moves. -/
theorem nonequivariant_case_verdict :
    (∀ (c : LetterCost) (B : ℕ) (K : BoundedComplex B),
        classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K
          ↔ numeratorMass c B (Quotient.mk (relabelSetoid B) K) = (gaugeOrbitCard K : ℝ))
      ∧ (∀ (c : LetterCost) (B : ℕ),
          (∀ K K' : BoundedComplex B, Equivalent K K' →
              historyCost c B K = historyCost c B K') →
            ∀ K : BoundedComplex B,
              numeratorMass c B (Quotient.mk (relabelSetoid B) K) = (gaugeOrbitCard K : ℝ) →
                Real.exp (-(historyCost c B K)) = 1)
      ∧ (∃ c : LetterCost, ¬ Equivariant c
          ∧ (∀ K : BoundedComplex 3,
              classMass (postedWeight c 3) (Quotient.mk (relabelSetoid 3) K) = mu K)
          ∧ ¬ (∀ K : BoundedComplex 3, Real.exp (-(historyCost c 3 K)) = 1))
      ∧ ¬ (∀ K K' : BoundedComplex 3, Equivalent K K' →
            postedWeight (tiltedCost (1/2)) 3 K = postedWeight (tiltedCost (1/2)) 3 K')
      ∧ (∀ (t : ℝ) (B : ℕ) (K : BoundedComplex B), K.nE ≤ 1 → tiltedNumer t K = 1) := by
  have ht : |(1/2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have ht0 : (1/2 : ℝ) ≠ 0 := by norm_num
  exact ⟨fun c B K => posts_mu_iff_numeratorMass_eq_orbitCard c B K,
    fun c B hinv K h => orbitMeanOne_forces_one_of_invariant c B hinv K h,
    equivariance_is_load_bearing,
    postedWeight_tiltedCost_not_invariant ht ht0,
    fun t _ K h => tiltedNumer_eq_one_of_nE_le_one t K h⟩

/-! ## §6. Navigation index

One flag flips relative to `Gap2PostingCostDerivation`: the non-equivariant case is settled.  The
flag it does **not** flip is the one that matters for the measure: the cost layer still contributes
no determination, and now for a second reason. -/

structure Index : Type where
  /-- Posting `mu` is orbit mean one on the numerator, for every letter cost. -/
  posting_mu_is_orbit_mean_one : Bool
  /-- Equivariance is exactly what turns mean one into identically one. -/
  equivariance_supplies_constancy : Bool
  /-- SETTLED (this module): a non-equivariant cost can post `mu` with a non-unit numerator. -/
  nonequivariant_numerator_settled : Bool
  /-- The witness is a one-parameter family, not one exceptional cost. -/
  witness_is_a_family : Bool
  /-- The witness's posted weight is not relabeling-invariant, so the uniqueness wall stands. -/
  uniqueness_wall_escaped_not_breached : Bool
  /-- NOT proved, and made worse rather than better: that the cost layer determines the measure.
  The equivariant class admitted one compatible numerator; the full class admits a continuum. -/
  cost_layer_determines_the_measure : Bool
  /-- NOT proved: that anything here derives the measure's premise (unit sector fugacity,
  reducible to the gluing law).  A witness that the collapse fails is not a derivation. -/
  measure_premise_derived : Bool

def index : Index where
  posting_mu_is_orbit_mean_one := true
  equivariance_supplies_constancy := true
  nonequivariant_numerator_settled := true
  witness_is_a_family := true
  uniqueness_wall_escaped_not_breached := true
  cost_layer_determines_the_measure := false
  measure_premise_derived := false

theorem index_nonequivariant_settled : index.nonequivariant_numerator_settled = true := rfl

theorem index_cost_layer_does_not_determine :
    index.cost_layer_determines_the_measure = false := rfl

theorem index_premise_still_open : index.measure_premise_derived = false := rfl

end

#print axioms classMass_postedWeight
#print axioms family_injective_at_loopAndBridge
#print axioms mu_eq_orbitCard_mul_gibbsWeight
#print axioms posts_mu_iff_numeratorMass_eq_orbitCard
#print axioms orbitMeanOne_forces_one_of_invariant
#print axioms twist_twist
#print axioms twist_class
#print axioms classMass_of_twistOdd
#print axioms edgeSign_twist
#print axioms historyCost_tiltedCost
#print axioms exp_neg_historyCost_tiltedCost
#print axioms numeratorMass_tiltedCost
#print axioms tiltedCost_posts_mu
#print axioms numerator_ne_one_at_loopAndBridge
#print axioms tiltedCost_not_equivariant
#print axioms postedWeight_tiltedCost_not_invariant
#print axioms normalizedAtTheAtoms_tiltedCost
#print axioms nonequivariant_cost_posts_mu_with_nonunit_numerator
#print axioms equivariance_is_load_bearing
#print axioms nonequivariant_posting_family
#print axioms nonequivariant_case_verdict

end Gap2NonEquivariantPosting
end SevenGaps
end Gravity
end IndisputableMonolith
