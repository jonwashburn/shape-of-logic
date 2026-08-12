import IndisputableMonolith.Loom.Core

/-!
# The grammar: content in, an utterance out

`Expr` is the inductive type of content the language accepts, and `weave` is the total
function that turns a piece of content into a configuration of closed walks. Five
production rules, each one forced by asking which operation on configurations has the
algebraic properties the content operator has:

* a relation applied to roles in order is an ordered PRODUCT of letters, opened and
  closed by the relation's own letter,
* denial is INVERSION, the only involution the group offers,
* conjunction is MULTISET UNION, the only unordered idempotent join,
* a universal is a BINDER LOOP with the body CONJUGATED BY THAT SAME ORIENTED LOOP,
  because "inside" is conjugation and the body sits inside the binder as uttered,
* an existential is the same with the binder reversed, which is not a second choice but
  a consequence: `not (forall x (not B))` gives back exactly that.

Conjugating by the binder's own oriented loop rather than by the bare letter is what makes
a quantifier's TYPE visible from inside its scope: an atom's loop then records whether each
binder above it was universal or existential, not merely which name it bound. The bare
letter loses that, and when two conjuncts bind the same names in the same order it lets
atoms be exchanged between a universal and an existential branch without moving the
utterance. Measured on 3,800 pieces of irredundant content, the bare letter conflates 860
pairs of genuinely different content and this rule conflates 1, which is a pair with no
separating model and so is correctly conflated.

Two rules make an utterance rather than a fragment. Every utterance carries the FRAME
loop, the walk that closes the complete recognition window, because with a single loop
there is nothing to be oriented against and denial would be inexpressible. And every
loop is freely reduced, because spelling is not content.

`Expr` is already in negation normal form: denial rides on the atom. That is not a
preprocessing convenience, it is what the algebra does. Inverting a binder loop flips
its sign, which turns a denied universal into an existential, so the carrier represents
every formula it accepts in this form. The denial of a conjunction is therefore outside
the language, since inverting a multiset of loops denies each loop separately, giving
"neither" rather than "not both". There is no join on configurations, so the language
has no disjunction, and `Expr` cannot express one: the refusal is structural rather
than a runtime error.
-/

namespace IndisputableMonolith
namespace Loom

/-- Content the language accepts. Names are indices into a shared codebook, so nothing
anonymous and nothing per-claim is ever named. -/
inductive Expr where
  /-- A relation applied to role fillers in role order, denied or not. -/
  | atom (pred : Nat) (args : List Nat) (denied : Bool) : Expr
  /-- Both, unordered. -/
  | conj (a b : Expr) : Expr
  /-- A quantifier over a shared name: universal when the flag is true. -/
  | quant (universal : Bool) (binder : Nat) (body : Expr) : Expr
deriving DecidableEq, Repr

/-- Which signed generator each shared name is attached to. This is the whole of what
sender and receiver must already share. It is *not* pure gauge, contrary to what this
comment said until 2026-07-28: `Loom.Attachment.six_atoms_not_forced` shows the gauge
group is too small to act transitively on the labellings, and `fourteen_orbits_insufficient`
with `fifteen_orbits_suffice` pin the minimum at fifteen orbits. So a codebook carries a
residue of real choice that no relabelling removes. -/
abbrev Codebook := List Int

def letterOf (cb : Codebook) (n : Nat) : Int := cb.getD n 0

/-- The five production rules, as one total function. -/
def weaveBody (cb : Codebook) : Expr → Config
  | .atom pred args denied =>
      let p := letterOf cb pred
      let w := reduceWord (p :: (args.map (letterOf cb) ++ [p]))
      [if denied then invWord w else w]
  | .conj a b => weaveBody cb a ++ weaveBody cb b
  | .quant universal binder body =>
      let q := letterOf cb binder
      let marker : Word := if universal then [q] else [-q]
      marker :: (weaveBody cb body).map (conjWord marker)

/-- Content to utterance: the body, framed and freely reduced. Total, and every
question about its output is answerable in linear time. -/
def weave (cb : Codebook) (e : Expr) : Config :=
  reduceConfig ([frameGen] :: weaveBody cb e)

/-- SOUNDNESS of the weaver against the checker: everything the grammar produces is
well formed, so the checker never has to reject an honest utterance. -/
theorem wellFormed_weave (cb : Codebook) (e : Expr) : wellFormed (weave cb e) = true :=
  wellFormed_reduceConfig_frame _

/-- The invariant of a woven utterance does not depend on how its loops are spelled. -/
theorem invariant_weave_reduce (T : Table) (hT : Table.ok T = true) (cb : Codebook)
    (e : Expr) :
    invariant T (weave cb e) = invariant T ([frameGen] :: weaveBody cb e) :=
  invariant_reduceConfig T hT _

/-- Depth one cannot see nesting. Every loop of a quantified body is a conjugate of the
corresponding loop of the body itself, so the loop traces of the two agree pointwise;
only the commutators of the loops with each other move. This is the theorem behind the
measured fact that loop traces alone fail to separate the witness. -/
theorem trN_weaveBody_quant (T : Table) (hT : Table.ok T = true) (cb : Codebook)
    (universal : Bool) (binder : Nat) (body : Expr) :
    ((weaveBody cb (.quant universal binder body)).tail.map
        (fun w => Mat.trN (evalWord T w)))
      = (weaveBody cb body).map (fun w => Mat.trN (evalWord T w)) := by
  simp only [weaveBody, List.tail_cons, List.map_map]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, trN_conjWord T hT]

#print axioms wellFormed_weave
#print axioms trN_weaveBody_quant

end Loom
end IndisputableMonolith
