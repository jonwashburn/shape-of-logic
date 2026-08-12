import IndisputableMonolith.Gravity.SevenGaps.Gap2LedgerCohomology

/-!
# Gap 2 / C10: parity of the incidence class under reversal involutions

The C10 parity audit of the Track D observable program (panel receipt
`state/panel/qg-track-d-observable-20260731_20260731_140423.json`): does the
ledger incidence complex admit an orientation or letter-reversal involution `ι`
under which the genuine incidence class is parity-ODD, `ι*[c] = −[c]`?  The C9
birefringence bet needs exactly such a sign: a holonomy read off refinement
histories must flip sign when the history is reversed.

## Verdict: NO.  The class is even under every involution the ledger supports,
and no self-map of the complex space pulls it back to its negative.

The genuine class is `incidenceCost 1`, whose C18 history at `K` is the count
`properEdgeCount K` (kernel theorem `historyCost_incidenceCost`).  Parity is
read at the level of history functions, because two C18 classes agree exactly
when their histories agree at every complex (a ledger coboundary is a
history-zero cost).  The library's objects supply three families of candidate
involutions, and each is EVEN on the class:

1. **Letter permutations**, including the serial-name reversal
   `letterReversal K` below: pulling a cost back along a permutation of the
   posting alphabet re-indexes the history sum, which changes nothing
   (`Equiv.sum_comp`).  Every class is even under every letter permutation,
   involutive or not, and no equivariance hypothesis is needed.
2. **Relabelings**: the class is gauge-equivariant
   (`incidenceCost_equivariant`), so its history is invariant
   (`historyCost_invariant`).
3. **Edge-orientation reversal** `edgeReverse`: swap the two endpoints of every
   edge.  The carrier's `edgeVerts` is an ordered pair with no ordering
   constraint, so this is a genuine self-map of `BoundedComplex B`; it is
   involutive, and it is NOT a relabeling (the label-erasure module records
   that reversing a directed edge lies outside `Aut`).  But the loop/proper
   dichotomy is symmetric in the two endpoints (`ne_comm`), so
   `properEdgeCount` is invariant: the class is even here too.

The odd alternative is excluded outright (`no_odd_pullback_of_incidence_class`):
for `t ≠ 0` there is no self-map `F` of the bounded-complex space, involutive
or not, with `historyCost (incidenceCost t) B (F B K)` equal to
`− historyCost (incidenceCost t) B K` at every `K`.  At `twoBridges` the class
has history `2t`; any pullback re-evaluates the same non-negative count
`t · properEdgeCount (F 2 twoBridges)` at another complex, and that can never
equal `−2t`.  The involution requirement never even enters: a non-negative
count that is positive somewhere cannot be odd under any pullback, because a
pullback is still an evaluation of that same count.

## Scope notes

* The scalar map `c ↦ −c` on cochains would make every class of every theory
  odd trivially; it is a coefficient operation, not an orientation or letter
  reversal of the ledger's objects, so it is not a candidate the question
  admits, and adding it would be observable shopping.
* A28 (`Gap2GaugeTransport`) concerns configuration-level count-functionals.
  This lane is history/class level: the pairing is the C18 history of a letter
  cost, and the kill mechanism is the sign of a count, not the A28 washout.
  A28 is neither used nor contradicted here.
* Consequence: the C9 birefringence lane closes on the scope of the genuine
  incidence class (the exhibited H^1 generator), and the C10 leg of the panel's
  frozen signing condition is SATISFIED permanently by the even/absent verdict.
  The banking sentence stays unsigned because C11 returned a nonzero branch
  (the class is visible to ratio probes) and the C2 audit is still out.
  The transgression
  question on 1-cycles is moot: there is no odd class to transgress.
  No flag moves; `FullTheoryLedger` is not imported.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2IncidenceParity

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Gap2LetterCostDichotomy Gap2LedgerCohomology

noncomputable section

variable {B : ℕ}

/-! ## §1. The letter-reversal involution -/

/-- **Letter reversal**: reverse the serial-name order within each letter kind
(`Fin.revPerm` on vertices, edges, and tetrahedra), transported across the
posting alphabet by the library's own `postingAlphEquiv`.  This is the
letter-reversal involution the question names: it permutes which letter sits
at which serial position, reversing the posting order. -/
def letterReversal (K : BoundedComplex B) : Equiv.Perm (PostingAlphabet K) :=
  postingAlphEquiv Fin.revPerm Fin.revPerm Fin.revPerm

/-- Letter reversal is an involution: reversing the serial names twice returns
every letter to itself. -/
theorem letterReversal_involutive (K : BoundedComplex B) :
    Function.Involutive (letterReversal K) := by
  intro a
  rcases a with v | (e | t)
  · exact congrArg Sum.inl (Fin.rev_involutive v)
  · exact congrArg (Sum.inr ∘ Sum.inl) (Fin.rev_involutive e)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Fin.rev_involutive t)

/-- Pullback of a letter cost along a family of letter permutations:
precomposition on the posting alphabet. -/
def letterPullback (c : LetterCost)
    (π : ∀ (B : ℕ) (K : BoundedComplex B), Equiv.Perm (PostingAlphabet K)) :
    LetterCost :=
  fun B K a => c B K (π B K a)

/-- Every letter permutation is EVEN on every class: re-indexing a finite sum
changes nothing.  No equivariance hypothesis is needed. -/
theorem historyCost_letterPullback (c : LetterCost)
    (π : ∀ (B : ℕ) (K : BoundedComplex B), Equiv.Perm (PostingAlphabet K))
    (B : ℕ) (K : BoundedComplex B) :
    historyCost (letterPullback c π) B K = historyCost c B K :=
  Equiv.sum_comp (π B K) (fun a => c B K a)

/-- **The genuine incidence class is even under letter reversal.** -/
theorem incidence_class_even_under_letterReversal
    (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (letterPullback (incidenceCost t) (fun _ K' => letterReversal K')) B K
      = historyCost (incidenceCost t) B K :=
  historyCost_letterPullback _ _ _ _

/-! ## §2. The edge-orientation reversal involution -/

/-- **Orientation reversal**: swap the two endpoints of every edge.  The
carrier is directed and ordered (`edgeVerts e : Fin nV × Fin nV`, loops
allowed, no ordering constraint), so swapping endpoints yields another bounded
complex with the same letters. -/
def edgeReverse (K : BoundedComplex B) : BoundedComplex B where
  nV := K.nV
  nE := K.nE
  nT := K.nT
  hV := K.hV
  hE := K.hE
  hT := K.hT
  edgeVerts := fun e => (K.edgeVerts e).swap
  tetVerts := K.tetVerts

/-- Swapping a pair twice returns it.  (Stated locally so the involution
proofs do not depend on Mathlib lemma roulette.) -/
private theorem swap_swap {α β : Type*} (p : α × β) : Prod.swap (Prod.swap p) = p := by
  cases p
  rfl

/-- Orientation reversal is an involution on the incidence data: swapping both
endpoints of every edge twice returns every edge to itself. -/
theorem edgeReverse_edgeVerts_involutive (K : BoundedComplex B) (e : Fin K.nE) :
    (edgeReverse (edgeReverse K)).edgeVerts e = K.edgeVerts e :=
  swap_swap _

/-- Orientation reversal is an involution of the complex itself. -/
theorem edgeReverse_involutive (B : ℕ) :
    Function.Involutive (edgeReverse (B := B)) := by
  intro K
  cases K
  congr

/-- Orientation reversal as a permutation of the labeled carrier. -/
def edgeReverseEquiv (B : ℕ) : Equiv.Perm (BoundedComplex B) where
  toFun := edgeReverse
  invFun := edgeReverse
  left_inv := edgeReverse_involutive B
  right_inv := edgeReverse_involutive B

/-- `properEdgeCount` is invariant under orientation reversal: the loop/proper
dichotomy `v₁ ≠ v₂` is symmetric in the two endpoints. -/
theorem properEdgeCount_edgeReverse (K : BoundedComplex B) :
    properEdgeCount (edgeReverse K) = properEdgeCount K := by
  unfold properEdgeCount
  exact congrArg Finset.card (Finset.filter_congr (fun i _ => ne_comm))

/-- **The genuine incidence class is even under orientation reversal.**  The
pullback re-evaluates the history at the reversed complex, and the history is
unchanged because `properEdgeCount` is invariant. -/
theorem incidence_class_even_under_edgeReverse (t : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (incidenceCost t) B (edgeReverse K)
      = historyCost (incidenceCost t) B K := by
  rw [historyCost_incidenceCost, historyCost_incidenceCost,
    properEdgeCount_edgeReverse]

/-- **The genuine incidence class is even under every relabeling**: gauge
equivariance of `incidenceCost`, restated at the level of the class. -/
theorem incidence_class_even_under_relabel (t : ℝ) {K K' : BoundedComplex B}
    (r : Relabel K K') :
    historyCost (incidenceCost t) B K = historyCost (incidenceCost t) B K' :=
  historyCost_invariant (incidenceCost_equivariant t) r

/-! ## §3. No odd pullback exists -/

/-- **C10 headline: the incidence class admits no odd pullback.**  For `t ≠ 0`
there is no self-map `F` of the bounded-complex space, involutive or not,
pulling `[incidenceCost t]` back to its negative.  The parity-odd equation
fails at `twoBridges`: the class has history `2t` there, while any pullback
re-evaluates the same non-negative count `t · properEdgeCount (F 2 twoBridges)`
at another complex, which cannot equal `−2t`.  Equality of C18 classes is
equality of history functions (a ledger coboundary is exactly a history-zero
cost), so the class-level odd equation fails already as a function equation. -/
theorem no_odd_pullback_of_incidence_class {t : ℝ} (ht : t ≠ 0) :
    ¬ ∃ F : (B : ℕ) → BoundedComplex B → BoundedComplex B,
        ∀ (B : ℕ) (K : BoundedComplex B),
          historyCost (incidenceCost t) B (F B K)
            = - historyCost (incidenceCost t) B K := by
  rintro ⟨F, hF⟩
  have h := hF 2 twoBridges
  rw [historyCost_incidenceCost, historyCost_incidenceCost,
    properEdgeCount_twoBridges] at h
  have h2 : t * (properEdgeCount (F 2 twoBridges) : ℝ) = t * (-2) := by
    rw [h]
    ring
  have h3 : (properEdgeCount (F 2 twoBridges) : ℝ) = -2 := mul_left_cancel₀ ht h2
  have hnonneg : (0 : ℝ) ≤ (properEdgeCount (F 2 twoBridges) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **No odd involution exists** (the C10 question at the genuine class
`incidenceCost 1`).  Every self-map of the complex space, and so every
involution, pulls the class's history back to a non-negative count, never to
its negative. -/
theorem no_odd_involution_exists :
    ¬ ∃ F : (B : ℕ) → BoundedComplex B → BoundedComplex B,
        ∀ (B : ℕ) (K : BoundedComplex B),
          historyCost (incidenceCost (1 : ℝ)) B (F B K)
            = - historyCost (incidenceCost (1 : ℝ)) B K :=
  no_odd_pullback_of_incidence_class one_ne_zero

/-! ## §4. Verdict package -/

/-- **C10 parity verdict.**  The genuine incidence class is EVEN under every
involution the ledger's objects support (letter reversal, edge-orientation
reversal, and every relabeling), and it admits no odd pullback at all.  The C9
birefringence lane, which needed a sign-changing holonomy on refinement
histories, has no substrate in the incidence complex; the unsigned banking
sentence's C10 condition fails.  Flag unmoved. -/
theorem incidence_parity_verdict (t : ℝ) (ht : t ≠ 0) :
    (∀ (K : BoundedComplex B), Function.Involutive (letterReversal K))
      ∧ Function.Involutive (edgeReverse (B := B))
      ∧ (∀ (K : BoundedComplex B),
          historyCost (incidenceCost t) B (edgeReverse K)
            = historyCost (incidenceCost t) B K)
      ∧ ¬ ∃ F : (B : ℕ) → BoundedComplex B → BoundedComplex B,
            ∀ (B : ℕ) (K : BoundedComplex B),
              historyCost (incidenceCost t) B (F B K)
                = - historyCost (incidenceCost t) B K :=
  ⟨letterReversal_involutive, edgeReverse_involutive B,
    fun K => incidence_class_even_under_edgeReverse t _ K,
    no_odd_pullback_of_incidence_class ht⟩

end

/-! ## Axiom audit -/

#print axioms letterReversal_involutive
#print axioms historyCost_letterPullback
#print axioms incidence_class_even_under_letterReversal
#print axioms edgeReverse_edgeVerts_involutive
#print axioms edgeReverse_involutive
#print axioms properEdgeCount_edgeReverse
#print axioms incidence_class_even_under_edgeReverse
#print axioms incidence_class_even_under_relabel
#print axioms no_odd_pullback_of_incidence_class
#print axioms no_odd_involution_exists
#print axioms incidence_parity_verdict

end Gap2IncidenceParity
end SevenGaps
end Gravity
end IndisputableMonolith
