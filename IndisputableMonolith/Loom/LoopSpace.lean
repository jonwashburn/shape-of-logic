import Mathlib
import IndisputableMonolith.Patterns

/-!
# Loom: the recognition potential is blind to every closed walk

`IndisputableMonolith/Chain.lean` states T3 as `Conserves`: a closed chain has
zero flux under the ledger potential `phi = debit - credit`.  This module makes
the reason explicit and then measures what it costs.

A recognition history on one window is a walk on `Patterns.Pattern d`, the
`d`-cube, whose steps flip one bit.  A per-state amplitude reading of such a
history is a potential `phi : Pattern d → ℤ` summed along the walk.  The first
theorem is that this sum **telescopes**:

    readWalk phi w = phi (endpoint w) - phi (start w)

so the entire amplitude reading of a history is a function of two states and
nothing else.  It cannot see the interior of the walk at all.  For a closed walk
the two states coincide, so the reading is `0` for *every* potential
(`readWalk_closed`).  That is T3, and it means the amplitude reading is a
**constant function on the set of balanced histories**: it maps all of them to
zero.

The rest of the module exhibits what that constant hides, at two depths.

* Depth one, the bag of words.  Fixing the Gray path as a spanning tree, the
  five edges outside it index the loop coordinates.  `loopCoord` reads the signed
  traversal count of one such edge.  `potential_reading_not_injective_on_closed`
  gives two closed walks that every potential reads identically and that a loop
  coordinate separates.
* Depth two, the order.  `muCoord` is the antisymmetric degree-two Magnus
  coefficient of a pair of loop coordinates: how often one loop is traversed
  before the other, signed.  `witness14` is a fourteen-act closed history, found
  by exhaustive census, on which **every potential reads zero and every loop
  coordinate reads zero**, and whose `muCoord` is `-2`.  So it is a statement
  that an amplitude carrier cannot distinguish from silence, that a word-counting
  carrier cannot distinguish from silence, and that is provably not silence.

Fourteen is the exact floor: the census enumerated every closed walk to length
twenty and found no shorter witness (`Loom/census/q3_loop_census.py`, and note
that this is *not* the sixteen-step floor holography measured for spatial
linking, which is a different invariant).

Tier: THEOREM.  Nothing here is a claim about nature; it is a claim about what a
coboundary can see.  Scoped verdict at `LoopSpaceCert`.
-/

namespace IndisputableMonolith
namespace Loom

open IndisputableMonolith.Patterns

/-! ## Walks on the cube -/

/-- Flip one axis of a recognition state.  This is the elementary act. -/
def flip {d : ℕ} (p : Pattern d) (i : Fin d) : Pattern d :=
  fun j => if j = i then !p j else p j

/-- A recognition history: a start state and the axes flipped, in order. -/
structure Walk (d : ℕ) where
  start : Pattern d
  steps : List (Fin d)

namespace Walk

/-- The state reached after running the history. -/
def endpoint {d : ℕ} (w : Walk d) : Pattern d :=
  w.steps.foldl flip w.start

/-- A history is closed when it returns, which by T3 is when it balances. -/
def Closed {d : ℕ} (w : Walk d) : Prop := w.endpoint = w.start

/-- Length is the number of elementary acts, which is the integer cost. -/
def length {d : ℕ} (w : Walk d) : ℕ := w.steps.length

end Walk

/-- `Patterns.Pattern` is a `def`, so instance search needs this spelled out.
Same reason `Patterns.instFintypePattern` exists. -/
instance instDecidableEqPattern (d : ℕ) : DecidableEq (Pattern d) := by
  dsimp [Pattern]; infer_instance

/-- Closedness is decidable, which is what makes the witnesses machine-checkable
rather than hand-verified. -/
instance instDecidableClosed {d : ℕ} (w : Walk d) : Decidable w.Closed := by
  unfold Walk.Closed; infer_instance

/-! ## The amplitude reading telescopes -/

/-- A per-state amplitude profile: what a chord, a token table, or any
state-indexed carrier supplies. -/
abbrev Potential (d : ℕ) := Pattern d → ℤ

/-- The reading a potential gives to a history: the sum of its step differences.
This is the edge-chain pairing written without mentioning chains. -/
def potentialReading {d : ℕ} (phi : Potential d) (start : Pattern d) :
    List (Fin d) → ℤ
  | [] => 0
  | a :: rest =>
      (phi (flip start a) - phi start) + potentialReading phi (flip start a) rest

/-- **The reading depends only on the endpoints.**  Every amplitude reading of a
history telescopes to the difference of the potential at its two ends, so it is
blind to the entire interior of the history. -/
theorem potentialReading_telescopes {d : ℕ} (phi : Potential d) :
    ∀ (steps : List (Fin d)) (start : Pattern d),
      potentialReading phi start steps
        = phi (steps.foldl flip start) - phi start := by
  intro steps
  induction steps with
  | nil => intro start; simp [potentialReading]
  | cons a rest ih =>
      intro start
      simp only [potentialReading, List.foldl_cons, ih (flip start a)]
      ring

/-- The reading of a whole history. -/
def readWalk {d : ℕ} (phi : Potential d) (w : Walk d) : ℤ :=
  potentialReading phi w.start w.steps

theorem readWalk_eq_endpoints {d : ℕ} (phi : Potential d) (w : Walk d) :
    readWalk phi w = phi w.endpoint - phi w.start := by
  simpa [readWalk, Walk.endpoint] using
    potentialReading_telescopes phi w.steps w.start

/-- **T3, made explicit.**  Every potential reads every balanced history as zero.
This is `Chain.Conserves` with the coboundary structure exposed: the reading is a
difference of endpoint values, and a closed history has one endpoint. -/
theorem readWalk_closed {d : ℕ} (phi : Potential d) {w : Walk d} (h : w.Closed) :
    readWalk phi w = 0 := by
  rw [readWalk_eq_endpoints, h]
  ring

/-- **The amplitude carrier is constant on balanced histories.**  Any two closed
histories get the same reading from every potential, so no amplitude profile can
distinguish one balanced statement from another, nor any of them from silence. -/
theorem readWalk_constant_on_closed {d : ℕ} (phi : Potential d) {w₁ w₂ : Walk d}
    (h₁ : w₁.Closed) (h₂ : w₂.Closed) :
    readWalk phi w₁ = readWalk phi w₂ := by
  rw [readWalk_closed phi h₁, readWalk_closed phi h₂]

/-! ## Depth one: the loop coordinates

The Gray path `000 001 011 010 110 111 101 100` is a spanning tree of the
three-cube, so the five edges outside it index the loop coordinates.  We need
only that the signed traversal count of one named edge is a well defined integer
function of a history. -/

/-- State code of a three-bit pattern, bit `i` being axis `i`. -/
def code (p : Pattern 3) : ℕ :=
  (if p 0 then 1 else 0) + (if p 1 then 2 else 0) + (if p 2 then 4 else 0)

/-- The unordered edge between a state and its neighbour along one axis, named by
the pair of state codes. -/
def edgeOf (p : Pattern 3) (a : Fin 3) : ℕ × ℕ :=
  let q := flip p a
  if code p ≤ code q then (code p, code q) else (code q, code p)

/-- `+1` when the step crosses this edge upward in code, `-1` downward, `0`
when it is a different edge. -/
def stepSign (e : ℕ × ℕ) (p : Pattern 3) (a : Fin 3) : ℤ :=
  if edgeOf p a = e then (if code p < code (flip p a) then 1 else -1) else 0

/-- Signed traversal count of one named edge along a history. -/
def cotreeCount (e : ℕ × ℕ) (start : Pattern 3) : List (Fin 3) → ℤ
  | [] => 0
  | a :: rest => stepSign e start a + cotreeCount e (flip start a) rest

/-- The depth-one coordinate of a history at one loop: how many times it went
round, signed.  The vector of these over the five loops is the bag of words. -/
def loopCoord (e : ℕ × ℕ) (w : Walk 3) : ℤ :=
  cotreeCount e w.start w.steps

/-- The five edges outside the Gray path, which index the five loops. -/
def gen₁ : ℕ × ℕ := (0, 2)
def gen₂ : ℕ × ℕ := (0, 4)
def gen₃ : ℕ × ℕ := (1, 5)
def gen₄ : ℕ × ℕ := (3, 7)
def gen₅ : ℕ × ℕ := (4, 6)

/-! ## Depth two: the order

The antisymmetric degree-two Magnus coefficient of a pair of loops: how often the
first is traversed before the second, minus the reverse.  Zero for every history
whose loops all commute, and the first thing a bag of words cannot see. -/

/-- Accumulate the depth-two coefficient while carrying the two running depth-one
counts. -/
def muAux (e₁ e₂ : ℕ × ℕ) (start : Pattern 3) (a₁ a₂ acc : ℤ) :
    List (Fin 3) → ℤ
  | [] => acc
  | a :: rest =>
      let s₁ := stepSign e₁ start a
      let s₂ := stepSign e₂ start a
      muAux e₁ e₂ (flip start a) (a₁ + s₁) (a₂ + s₂) (acc + a₁ * s₂ - a₂ * s₁) rest

/-- The depth-two coordinate of a history at a pair of loops. -/
def muCoord (e₁ e₂ : ℕ × ℕ) (w : Walk 3) : ℤ :=
  muAux e₁ e₂ w.start 0 0 0 w.steps

/-! ## Witnesses -/

/-- The all-false state. -/
def o : Pattern 3 := fun _ => false

/-- Silence: the empty history. -/
def silence : Walk 3 := ⟨o, []⟩

/-- One face of the cube, traversed one way. -/
def faceForward : Walk 3 := ⟨o, [1, 0, 1, 0]⟩

/-- The same face, traversed the other way. -/
def faceReverse : Walk 3 := ⟨o, [0, 1, 0, 1]⟩

/-- **The census witness.**  Fourteen acts.  Every potential reads it as zero and
every loop coordinate reads it as zero, yet it is not silence.  Found by
exhaustive enumeration of every closed walk to length twenty; fourteen is the
floor. -/
def witness14 : Walk 3 := ⟨o, [0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2]⟩

/-! ## The theorems -/

theorem silence_closed : silence.Closed := by decide

theorem faceForward_closed : faceForward.Closed := by decide

theorem faceReverse_closed : faceReverse.Closed := by decide

theorem witness14_closed : witness14.Closed := by decide

/-- **Depth one is enough to beat the amplitude carrier.**  Two closed histories
that every potential reads identically, separated by a loop coordinate.  So the
amplitude reading is not injective on balanced histories, and here is a witness
to the loss. -/
theorem potential_reading_not_injective_on_closed :
    (∀ phi : Potential 3, readWalk phi faceForward = readWalk phi faceReverse)
      ∧ loopCoord gen₁ faceForward ≠ loopCoord gen₁ faceReverse := by
  refine ⟨fun phi => readWalk_constant_on_closed phi faceForward_closed faceReverse_closed, ?_⟩
  decide

/-- **The census witness has an empty bag of words.**  All five loop coordinates
vanish, exactly as they do for silence. -/
theorem witness14_depth_one_is_silent :
    loopCoord gen₁ witness14 = 0 ∧ loopCoord gen₂ witness14 = 0
      ∧ loopCoord gen₃ witness14 = 0 ∧ loopCoord gen₄ witness14 = 0
      ∧ loopCoord gen₅ witness14 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **And it is not silence.**  Its depth-two coordinate at the first pair of
loops is `-2`. -/
theorem witness14_depth_two_speaks : muCoord gen₁ gen₂ witness14 = -2 := by
  decide

/-- Silence is silent at depth two as well, so the separation below is real. -/
theorem silence_depth_two_silent : muCoord gen₁ gen₂ silence = 0 := by
  decide

/-- **The crown.**  There is a fourteen-act balanced history that

* every amplitude profile reads as zero, exactly as it reads silence,
* every loop coordinate reads as zero, exactly as it reads silence,
* and a depth-two coordinate separates from silence.

Two carriers cannot tell this statement from saying nothing.  It is not nothing.
That gap is the syntax layer, and its floor is fourteen acts. -/
theorem depth_two_is_the_first_invisible_layer :
    (∀ phi : Potential 3, readWalk phi witness14 = readWalk phi silence)
      ∧ (loopCoord gen₁ witness14 = loopCoord gen₁ silence
          ∧ loopCoord gen₂ witness14 = loopCoord gen₂ silence
          ∧ loopCoord gen₃ witness14 = loopCoord gen₃ silence
          ∧ loopCoord gen₄ witness14 = loopCoord gen₄ silence
          ∧ loopCoord gen₅ witness14 = loopCoord gen₅ silence)
      ∧ muCoord gen₁ gen₂ witness14 ≠ muCoord gen₁ gen₂ silence := by
  refine ⟨fun phi => readWalk_constant_on_closed phi witness14_closed silence_closed, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · decide

/-! ## Certificate -/

/-- What this module licenses, in one object.

* `telescopes` — every amplitude reading of a history is a difference of endpoint
  values, hence blind to the interior;
* `blind_on_closed` — every potential reads every balanced history as zero (T3);
* `constant_on_closed` — so the reading cannot separate any two of them;
* `depth_one_separates` — a loop coordinate can, with a four-act witness;
* `depth_two_separates` — and there is a fourteen-act balanced history that both
  the amplitude reading and the whole bag of words read as silence, and that a
  depth-two coordinate does not.

Scoped verdict.  CLAIM: a per-state amplitude carrier cannot distinguish any two
balanced histories, and a bag-of-loops carrier cannot distinguish the fourteen-act
witness from silence.  DOMAIN: walks on `Pattern d` with one-bit steps; `d = 3`
for the witnesses.  PREMISES: `flip` steps; `ℤ`-valued potentials; the Gray path
as spanning tree.  REACH: licenses moving the message carrier off the amplitude
profile, and licenses the claim that order is not a convention but the first
content a bag cannot hold.  DOES NOT LICENSE: that any particular replacement
carrier is useful (a separate measurement), or that fourteen is a floor for
any invariant other than this one. -/
structure LoopSpaceCert : Prop where
  telescopes : ∀ (phi : Potential 3) (w : Walk 3),
    readWalk phi w = phi w.endpoint - phi w.start
  blind_on_closed : ∀ (phi : Potential 3) (w : Walk 3), w.Closed → readWalk phi w = 0
  constant_on_closed : ∀ (phi : Potential 3) (w₁ w₂ : Walk 3),
    w₁.Closed → w₂.Closed → readWalk phi w₁ = readWalk phi w₂
  depth_one_separates :
    (∀ phi : Potential 3, readWalk phi faceForward = readWalk phi faceReverse)
      ∧ loopCoord gen₁ faceForward ≠ loopCoord gen₁ faceReverse
  depth_two_separates :
    (∀ phi : Potential 3, readWalk phi witness14 = readWalk phi silence)
      ∧ (loopCoord gen₁ witness14 = loopCoord gen₁ silence
          ∧ loopCoord gen₂ witness14 = loopCoord gen₂ silence
          ∧ loopCoord gen₃ witness14 = loopCoord gen₃ silence
          ∧ loopCoord gen₄ witness14 = loopCoord gen₄ silence
          ∧ loopCoord gen₅ witness14 = loopCoord gen₅ silence)
      ∧ muCoord gen₁ gen₂ witness14 ≠ muCoord gen₁ gen₂ silence

theorem loopSpaceCert_holds : LoopSpaceCert where
  telescopes := fun phi w => readWalk_eq_endpoints phi w
  blind_on_closed := fun phi _ h => readWalk_closed phi h
  constant_on_closed := fun phi _ _ h₁ h₂ => readWalk_constant_on_closed phi h₁ h₂
  depth_one_separates := potential_reading_not_injective_on_closed
  depth_two_separates := depth_two_is_the_first_invisible_layer

#print axioms loopSpaceCert_holds
#print axioms potentialReading_telescopes
#print axioms readWalk_closed
#print axioms depth_two_is_the_first_invisible_layer
#print axioms witness14_depth_two_speaks

end Loom
end IndisputableMonolith
