import IndisputableMonolith.Loom.Grammar
import IndisputableMonolith.Loom.Readings
import IndisputableMonolith.Loom.Semantics
import IndisputableMonolith.Loom.CertificateData

/-!
# The separation witness, checked by the kernel

Two pieces of content:

* A. every door has some key that opens it, and one master key locks every door,
* B. every door has some key that locks it, and one master key opens every door.

The second is a security hole and the first is not. They assert the same two relations
under the same two quantifier patterns and differ only in which relation gets the
universal power, so a multiset of ground facts holds the same entries for both, and the
codebook was chosen by exhaustive search so that both cost the same number of one bit
acts with the same per loop length multiset. Counting cannot tell them apart.

What this module proves, with no hypothesis left dangling and nothing taken on trust
except the provenance of the automorphism action:

* `weave_witnessA`, `weave_witnessB`: the Lean weaver reproduces the two utterances the
  Python encoder emitted, letter for letter. Everything below is therefore about the
  grammar in `Grammar.lean` and not about opaque data.
* `depth_one_is_blind`, `abelianised_is_blind`: the loop by loop reading and the
  abelianised reading are IDENTICAL on the pair. Every carrier that stops at depth one
  conflates them, and this is what makes the separation nontrivial rather than a
  restatement of a length difference.
* `depth_two_separates`: the commutator reading differs.
* `no_gauge_image_of_A_is_B`: for every one of the forty eight automorphisms of the
  recognition window, every basepoint move, a simultaneous reversal or not, any
  respelling and any reordering of the loops, the image of A is not B. So the two are
  different meanings and not two spellings of one.

The strength of the separation, stated in the terms the institute requires: the gauge
group quotiented over has order 96 times the free choice of basepoint word, the check
covers all 48 automorphism images exactly (`autSubst_length`), and the two invariants
differ in one coordinate of twenty one, which is the smallest possible margin and is
exact rather than within a tolerance, because the invariant lands in a finite set.
-/

namespace IndisputableMonolith
namespace Loom
namespace Certificate

-- ---------------------------------------------------------------------------
-- the content, as content
-- ---------------------------------------------------------------------------

/-- The four shared names, as codebook indices. -/
def door : Nat := 0
def key : Nat := 1
def opens : Nat := 2
def locks : Nat := 3

/-- The codebook the search chose: it is the one under which no length statistic can
separate the pair, which makes the test harder rather than easier. Which codebook is
used is a free convention, and `invariant_substConfig` is why. Taken from the emitted
certificate rather than written out here, because the search rechooses it whenever the
encoder changes. -/
def cb : Codebook := cbData

def opensKeyDoor : Expr := .atom opens [key, door] false
def locksKeyDoor : Expr := .atom locks [key, door] false

/-- Every door has some key that opens it. -/
def everyDoorSomeKeyOpens : Expr := .quant true door (.quant false key opensKeyDoor)
/-- One master key opens every door. -/
def someKeyEveryDoorOpens : Expr := .quant false key (.quant true door opensKeyDoor)
/-- Every door has some key that locks it. -/
def everyDoorSomeKeyLocks : Expr := .quant true door (.quant false key locksKeyDoor)
/-- One master key locks every door. -/
def someKeyEveryDoorLocks : Expr := .quant false key (.quant true door locksKeyDoor)

/-- Safe: keys open doors one at a time, and one master key locks up. -/
def witnessA : Expr := .conj everyDoorSomeKeyOpens someKeyEveryDoorLocks
/-- Unsafe: one master key opens every door. -/
def witnessB : Expr := .conj everyDoorSomeKeyLocks someKeyEveryDoorOpens

/-- The weaver in `Grammar.lean` produces exactly the utterance the Python encoder
produced, so the certificate below is about the grammar and not about a coincidence of
transcription. -/
theorem weave_witnessA : weave cb witnessA = cfgA := by decide
theorem weave_witnessB : weave cb witnessB = cfgB := by decide

/-- Both utterances pass the checker. -/
theorem wellFormed_A : wellFormed cfgA = true := by
  rw [← weave_witnessA]; exact wellFormed_weave cb witnessA
theorem wellFormed_B : wellFormed cfgB = true := by
  rw [← weave_witnessB]; exact wellFormed_weave cb witnessB

-- ---------------------------------------------------------------------------
-- the homomorphism is a homomorphism
-- ---------------------------------------------------------------------------

/-- The five generator images really are inverse pairs of determinant one, so `base` is
a homomorphism from the free group of rank five into `SL(2, ZMod 3)`. Decided, not
assumed. -/
theorem base_ok : Table.ok base = true := by decide

/-- And so is every one of its forty eight relabellings, for free, from
`ok_tableOfSubst`. No table beyond `base` is trusted data: Lean computes each
composite itself from the automorphism's action on the generators. -/
theorem tableOfSubst_ok (σ : Subst) : Table.ok (tableOfSubst base σ) = true :=
  ok_tableOfSubst base base_ok σ

/-- All forty eight automorphisms of the window are covered. -/
theorem autSubst_length : autSubst.length = 48 := by decide

/-- The composite tables the Python search reported agree, matrix for matrix, with the
ones Lean computes from the substitution words. Two independent routes to the same
forty eight homomorphisms. -/
theorem autTables_eq : autTables = autSubst.map (tableOfSubst base) := by decide

-- ---------------------------------------------------------------------------
-- what the shallow readings see, and what they do not
-- ---------------------------------------------------------------------------

/-- The loop by loop reading is BLIND: identical on the pair. Any carrier whose reading
of an utterance is a multiset of per loop quantities conflates A with B. -/
theorem depth_one_is_blind : (invariant base cfgA).1 = (invariant base cfgB).1 := by
  decide

/-- The abelianised reading is blind too. This is the unique canonical quotient a bag of
relations performs, so the conflation is not an artifact of one implementation. -/
theorem abelianised_is_blind : abelBag cfgA = abelBag cfgB := by decide

/-- Depth two separates. One coordinate of twenty one, exactly, in a finite set. -/
theorem depth_two_separates : (invariant base cfgA).2 ≠ (invariant base cfgB).2 := by
  decide

theorem invariant_separates : invariant base cfgA ≠ invariant base cfgB := by
  intro h
  exact depth_two_separates (congrArg Prod.snd h)

-- ---------------------------------------------------------------------------
-- the gauge group, and the theorem
-- ---------------------------------------------------------------------------

/-- A gauge image of an utterance: relabel the generators by an automorphism of the
window, optionally reverse every loop at once, move the shared basepoint by one word,
and respell everything freely. Reordering the loops is handled by the permutation
hypothesis of the theorem below, because an utterance is a multiset. -/
def gaugeImage (σ : Subst) (flip : Bool) (g : Word) (c : Config) : Config :=
  reduceConfig
    ((if flip then (substConfig σ c).map invWord else substConfig σ c).map (conjWord g))

theorem invariant_gaugeImage (σ : Subst) (flip : Bool) (g : Word) (c : Config) :
    invariant base (gaugeImage σ flip g c) = invariant (tableOfSubst base σ) c := by
  rw [gaugeImage, invariant_reduceConfig base base_ok,
    invariant_conjWord base base_ok]
  cases flip with
  | false => rw [if_neg (by simp), invariant_substConfig]
  | true =>
    rw [if_pos rfl, invariant_map_invWord base base_ok, invariant_substConfig]

/-- The check: under every one of the forty eight relabellings, the invariant of A stays
different from the invariant of B. -/
def separatesEverywhere : Bool :=
  autSubst.all fun σ => invariant (tableOfSubst base σ) cfgA != invariant base cfgB

theorem separates_everywhere : separatesEverywhere = true := by decide

/-- THE SEPARATION THEOREM. No gauge transformation of A is B: not a relabelling by any
automorphism of the recognition window, not a reversal of every loop, not a move of the
shared basepoint, not a respelling, and not a reordering. So A and B are two meanings
and not two spellings of one, while every depth one reading of them is identical. -/
theorem no_gauge_image_of_A_is_B (σ : Subst) (hσ : σ ∈ autSubst) (flip : Bool)
    (g : Word) (c : Config) (hc : List.Perm c (gaugeImage σ flip g cfgA)) :
    invariant base c ≠ invariant base cfgB := by
  rw [invariant_perm base hc, invariant_gaugeImage]
  have h := List.all_eq_true.mp separates_everywhere σ hσ
  simpa only [bne_iff_ne, ne_eq] using h

/-- The same statement about the utterances themselves. -/
theorem gauge_image_ne_B (σ : Subst) (hσ : σ ∈ autSubst) (flip : Bool) (g : Word)
    (c : Config) (hc : List.Perm c (gaugeImage σ flip g cfgA)) : c ≠ cfgB := by
  intro h
  exact no_gauge_image_of_A_is_B σ hσ flip g c hc (by rw [h])

/-- And the whole thing as one statement about CONTENT: the two formulas receive
utterances that no gauge transformation identifies, though every depth one reading of
them agrees. -/
theorem witnesses_separated (σ : Subst) (hσ : σ ∈ autSubst) (flip : Bool) (g : Word)
    (c : Config) (hc : List.Perm c (gaugeImage σ flip g (weave cb witnessA))) :
    c ≠ weave cb witnessB := by
  rw [weave_witnessA] at hc
  rw [weave_witnessB]
  exact gauge_image_ne_B σ hσ flip g c hc

-- ---------------------------------------------------------------------------
-- the second witness: the rival readings are defined here and proved blind
-- ---------------------------------------------------------------------------

/-! The flagship above is conflated by a multiset of ground facts, which is the honest
shape of a relational message, but it IS seen by a stronger rival that also carries every
parent to child label of the parse tree. So the flagship does not settle the question
against that rival, and this second pair does.

The pair, with `door` and `key` as the two bound names:

* C. some door locks every key, and every door opens every key,
* D. some door opens every key, and every door locks every key.

Which relation is asserted of everything and which only of one thing: the same question the
flagship asks, put so that a labelled tree cannot answer it either. The atom in each branch
hangs off a `forall key` node, so the multiset of parent to child label pairs is identical
and the two atoms are exchangeable between the branches.

Unlike the flagship, this pair is separated under EVERY one of the 384 codebooks, while act
count and the amplitude reading separate it under NONE of them. The codebook below is the
one that also equalises the per loop length multiset, so both utterances cost 88 acts with
the same multiset of loop lengths. -/

def cb2 : Codebook := cbData2

def opensDoorKey : Expr := .atom opens [door, key] false
def locksDoorKey : Expr := .atom locks [door, key] false

/-- Some door locks every key. -/
def someDoorLocksEveryKey : Expr := .quant false door (.quant true key locksDoorKey)
/-- Some door opens every key. -/
def someDoorOpensEveryKey : Expr := .quant false door (.quant true key opensDoorKey)
/-- Every door opens every key. -/
def everyDoorOpensEveryKey : Expr := .quant true door (.quant true key opensDoorKey)
/-- Every door locks every key. -/
def everyDoorLocksEveryKey : Expr := .quant true door (.quant true key locksDoorKey)

def witnessC : Expr := .conj someDoorLocksEveryKey everyDoorOpensEveryKey
def witnessD : Expr := .conj someDoorOpensEveryKey everyDoorLocksEveryKey

theorem weave_witnessC : weave cb2 witnessC = cfgC := by decide
theorem weave_witnessD : weave cb2 witnessD = cfgD := by decide

/-- The two differ as trees. Necessary and nowhere near sufficient, since two formulas can
differ as trees and agree as claims; the model below is what settles it. -/
theorem witnessC_ne_witnessD : witnessC ≠ witnessD := by decide

/-- THE TWO ARE DIFFERENT CLAIMS, and on the plainest reading there is: one universe of
two elements shared by both bound names, `opens` holding of every pair, `locks` holding of
`(0,0)` and `(0,1)`. Then C holds, because door 0 locks both keys and everything opens
everything, and D fails, because it needs door 1 to lock key 0 and it does not.

This is the theorem that keeps the separation from being an embarrassment. Had the two been
logically equivalent, separating them would show the language drawing a distinction the
logic does not, which is a defect and not a witness. Note what is NOT assumed: the two
names range over the same universe, so nothing here rests on doors and keys being different
kinds of thing. -/
def witnessModel : Model 2 where
  holds p args :=
    if p = opens then true
    else if p = locks then
      match args with
      | [x, _] => x = 0
      | _ => false
    else false

theorem witnessC_and_D_are_different_claims :
    SeparatedBy witnessModel (fun _ => 0) witnessC witnessD := by decide

/-- Spelled out: the first holds and the second fails. -/
theorem witnessC_holds : evalExpr witnessModel (fun _ => 0) witnessC = true := by decide
theorem witnessD_fails : evalExpr witnessModel (fun _ => 0) witnessD = false := by decide

/-- RIVAL ONE IS BLIND. The multiset of ground facts and binder occurrences is the same
for both. Stated as a permutation, which is equality of multisets. -/
theorem groundBag_blind : List.Perm (groundBag witnessC) (groundBag witnessD) := by decide

/-- RIVAL TWO IS BLIND, and this is the one the flagship failed against. Every parent to
child label pair of the parse tree, with denial folded into the atom labels, is the same
for both. So no reading of this content as a collection of locally labelled facts can tell
the two apart. -/
theorem adjacencyBag_blind :
    List.Perm (adjacencyBag witnessC) (adjacencyBag witnessD) := by decide

/-- And the depth one reading of the two utterances is blind as well, so nothing that
reads loop by loop separates them either. -/
theorem depth_one_is_blind2 : (invariant base cfgC).1 = (invariant base cfgD).1 := by
  decide

theorem abelianised_is_blind2 : abelBag cfgC = abelBag cfgD := by decide

/-- Depth two separates, under the same single homomorphism that certifies the flagship. -/
theorem depth_two_separates2 : (invariant base cfgC).2 ≠ (invariant base cfgD).2 := by
  decide

theorem wellFormed_C : wellFormed cfgC = true := by
  rw [← weave_witnessC]; exact wellFormed_weave cb2 witnessC
theorem wellFormed_D : wellFormed cfgD = true := by
  rw [← weave_witnessD]; exact wellFormed_weave cb2 witnessD

def separatesEverywhere2 : Bool :=
  autSubst.all fun σ => invariant (tableOfSubst base σ) cfgC != invariant base cfgD

theorem separates_everywhere2 : separatesEverywhere2 = true := by decide

/-- THE SECOND SEPARATION THEOREM, and the strongest statement in this file. Two pieces of
content that every reading of content as locally labelled facts identifies, and that no
gauge transformation of the utterance identifies. -/
theorem no_gauge_image_of_C_is_D (σ : Subst) (hσ : σ ∈ autSubst) (flip : Bool)
    (g : Word) (c : Config) (hc : List.Perm c (gaugeImage σ flip g cfgC)) :
    invariant base c ≠ invariant base cfgD := by
  rw [invariant_perm base hc, invariant_gaugeImage]
  have h := List.all_eq_true.mp separates_everywhere2 σ hσ
  simpa only [bne_iff_ne, ne_eq] using h

theorem gauge_image_ne_D (σ : Subst) (hσ : σ ∈ autSubst) (flip : Bool) (g : Word)
    (c : Config) (hc : List.Perm c (gaugeImage σ flip g cfgC)) : c ≠ cfgD := by
  intro h
  exact no_gauge_image_of_C_is_D σ hσ flip g c hc (by rw [h])

theorem witnesses2_separated (σ : Subst) (hσ : σ ∈ autSubst) (flip : Bool) (g : Word)
    (c : Config) (hc : List.Perm c (gaugeImage σ flip g (weave cb2 witnessC))) :
    c ≠ weave cb2 witnessD := by
  rw [weave_witnessC] at hc
  rw [weave_witnessD]
  exact gauge_image_ne_D σ hσ flip g c hc

/-!
## A conjecture, tagged as one

Ken's ninth judgment `recognize_ne_defeq` is held open. The loop language suggests a
witness: a trivial loop, one that freely reduces to the empty word, is a walk that
returns without distinguishing anything, and that is exactly the shape of definitional
equality, while a nontrivial loop is a closed walk that cannot be contracted and so
records a distinction that had to be made. If that reading is right then
`reduceWord w = []` is the decidable side of `defeq` and any `w` with
`reduceWord w ≠ []` witnesses `recognize_ne_defeq`. CONJECTURE: not proved here, and
the gap is that nothing in this module connects the free group to Ken's judgment types.
-/

#print axioms weave_witnessA
#print axioms weave_witnessB
#print axioms base_ok
#print axioms autTables_eq
#print axioms depth_one_is_blind
#print axioms abelianised_is_blind
#print axioms depth_two_separates
#print axioms separates_everywhere
#print axioms no_gauge_image_of_A_is_B
#print axioms witnesses_separated
#print axioms weave_witnessC
#print axioms witnessC_ne_witnessD
#print axioms witnessC_and_D_are_different_claims
#print axioms witnessC_holds
#print axioms witnessD_fails
#print axioms groundBag_blind
#print axioms adjacencyBag_blind
#print axioms depth_one_is_blind2
#print axioms depth_two_separates2
#print axioms separates_everywhere2
#print axioms no_gauge_image_of_C_is_D
#print axioms witnesses2_separated

end Certificate
end Loom
end IndisputableMonolith
