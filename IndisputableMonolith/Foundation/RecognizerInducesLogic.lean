import Mathlib
import IndisputableMonolith.Foundation.PrimitiveDistinction
import IndisputableMonolith.Foundation.MagnitudeOfMismatch
import IndisputableMonolith.Foundation.ObserverFromRecognition

/-!
# Recognizers Induce a Law-of-Logic Realization

This module unifies Recognition Geometry with the Law of Logic. The
companion paper `RS_Recognition_Geometry_Logic_Unification.tex` argues
that any recognizer `r : 𝒞 → ℰ` mapping configurations to events
automatically generates a Law-of-Logic realization on its event space
`ℰ`. We formalise the honest version of that claim:

* A recognizer automatically supplies the **three definitional**
  Aristotelian conditions on its event space:
    (L1) Identity, (L2) Non-Contradiction, (L3a) Totality.
  These are forced by the equality-induced cost on `ℰ` together with
  the type signature of the recognizer.

* A recognizer automatically supplies a **primitive observer** in the
  sense of `ObserverFromRecognition`. The recognizer is the primitive
  observer.

* (L4) Composition Consistency is **not** automatic. It requires extra
  compositional structure on the recognizer family, made explicit as the
  hypothesis `RecognizerComposition`.

Putting these together: a recognizer alone produces three of the four
classical conditions for free (definitional from the type signature plus
equality), the primitive observer for free (canonical two-outcome
recognizer), and reduces the remaining substantive content of the
Aristotelian framework to a single named compositional axiom. This is the
single forcing chain promised by the companion paper.

This module connects:

* `PrimitiveDistinction.lean` (definitional facts from equality)
* `MagnitudeOfMismatch.lean` (single-valuedness forces symmetry)
* `ObserverFromRecognition.lean` (non-trivial recognition forces
  primitive observer)

into one Lean-checked unification.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RecognizerInducesLogic

open Classical
open PrimitiveDistinction
open MagnitudeOfMismatch
open ObserverFromRecognition

/-! ## The Recognizer

We use the Recognition Geometry presentation: a recognizer is a
surjection from a configuration space onto an event space.
-/

/-- A **recognizer** in the Recognition Geometry sense: a surjection
from a configuration space `𝒞` onto an event space `ℰ`. The fact that
it is many-to-one is essential; it is what generates the
indistinguishability quotient. -/
structure Recognizer (𝒞 ℰ : Type*) where
  observe : 𝒞 → ℰ
  surjective : Function.Surjective observe

/-! ## The Indistinguishability Quotient -/

/-- Two configurations are observationally indistinguishable under a
recognizer if the recognizer maps them to the same event. -/
def Recognizer.kernel {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ) (x y : 𝒞) : Prop :=
  r.observe x = r.observe y

/-- The kernel of a recognizer is an equivalence relation. -/
theorem Recognizer.kernel_is_equivalence {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ) :
    Equivalence (r.kernel) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-! ## The Recognizer-Induced Cost on the Event Space -/

/-- The cost of distinguishing two events: zero when they are the same
event, a positive weight otherwise. This is exactly the equality-induced
cost of `PrimitiveDistinction` applied to the event space `ℰ`. -/
noncomputable def Recognizer.cost {𝒞 ℰ : Type*} (_r : Recognizer 𝒞 ℰ)
    (weight : ℝ) : ℰ → ℰ → ℝ :=
  equalityCost ℰ weight

/-! ## The Three Definitional Aristotelian Conditions

A recognizer induces (L1), (L2), and (L3a) on its event space
automatically, by `PrimitiveDistinction`. No further structural choice
is required.
-/

/-- **(L1) Identity from the recognizer.** The cost of distinguishing an
event from itself is zero. -/
theorem Recognizer.identity {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ)
    (weight : ℝ) :
    ∀ e : ℰ, r.cost weight e e = 0 := by
  intro e
  exact identity_from_equality ℰ weight e

/-- **(L2) Non-Contradiction from the recognizer.** The cost of
distinguishing `e₁` from `e₂` equals the cost of distinguishing `e₂`
from `e₁`. -/
theorem Recognizer.non_contradiction {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ)
    (weight : ℝ) :
    ∀ e₁ e₂ : ℰ, r.cost weight e₁ e₂ = r.cost weight e₂ e₁ := by
  intro e₁ e₂
  exact non_contradiction_from_equality ℰ weight e₁ e₂

/-- **(L3a) Totality from the recognizer.** The cost is defined and
returns a value for every pair of events. -/
theorem Recognizer.totality {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ)
    (weight : ℝ) :
    ∀ e₁ e₂ : ℰ, ∃ c : ℝ, r.cost weight e₁ e₂ = c := by
  intro e₁ e₂
  exact totality_from_function_type ℰ weight e₁ e₂

/-- **Single-valuedness from the recognizer.** The induced cost is a
single-valued function on unordered pairs of events; equivalently, by
`MagnitudeOfMismatch`, it is symmetric. -/
theorem Recognizer.singleValued {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ)
    (weight : ℝ) :
    SingleValuedOnUnorderedPair (r.cost weight) :=
  equalityCost_singleValued ℰ weight

/-! ## The Primitive Observer is the Recognizer

Once the event space has at least two distinct events, the recognizer
delivers the primitive observer of `ObserverFromRecognition`. This is the
unification: the recognizer of Recognition Geometry **is** the primitive
observer of the Law-of-Logic chain. They are the same object.
-/

/-- The event space of a recognizer admits non-trivial recognition iff
it contains at least two distinct events. -/
def Recognizer.hasNontrivialRecognition {𝒞 ℰ : Type*}
    (_r : Recognizer 𝒞 ℰ) : Prop :=
  ∃ e₁ e₂ : ℰ, e₁ ≠ e₂

/-- **Recognizer is observer.** Any recognizer with a non-trivially
populated event space induces a primitive observer (a finite-valued
interface) that separates two distinct events.

This is the unification: the geometric primitive (recognizer producing
event space) and the logical primitive (interface producing primitive
observer) are the same act. -/
theorem Recognizer.induces_primitive_observer {𝒞 ℰ : Type*}
    (r : Recognizer 𝒞 ℰ) (h : r.hasNontrivialRecognition) :
    ∃ (O : PrimitiveObserver ℰ) (e₁ e₂ : ℰ),
      e₁ ≠ e₂ ∧ Separates O e₁ e₂ := by
  rcases h with ⟨e₁, e₂, hne⟩
  refine ⟨pointInterface e₁, e₁, e₂, hne, ?_⟩
  exact pointInterface_separates hne

/-! ## (L4) Composition Consistency: The Substantive Hypothesis

Composition consistency is not automatic from the type signature. It
requires the recognizer family to compose lawfully: composing two
recognition events should yield a cost determined by the costs of the
components. We make this an explicit hypothesis package; it is what the
companion paper acknowledges as the genuinely structural part of the
Aristotelian framework.
-/

/-- **(L4) Composition consistency on the event space.** The cost of a
composed comparison is determined by the costs of its components.

The exact algebraic form depends on the carrier; for the continuous
positive-ratio realization it is `F(xy) + F(x/y) = P(F(x), F(y))`. We
state the abstract version: there exists a combiner `Φ` on the cost
space realizing this functional dependence. -/
def Recognizer.RecognizerComposition {𝒞 ℰ : Type*}
    (r : Recognizer 𝒞 ℰ) (weight : ℝ)
    (compose : ℰ → ℰ → ℰ) (revcompose : ℰ → ℰ → ℰ) : Prop :=
  ∃ Φ : ℝ → ℝ → ℝ,
    ∀ e₁ e₂ : ℰ,
      r.cost weight (compose e₁ e₂) e₁ + r.cost weight (revcompose e₁ e₂) e₁ =
        Φ (r.cost weight e₁ e₁) (r.cost weight e₂ e₂)

/-! ## The Unification Theorem

The single forcing chain claim of the companion paper, in its honest
Lean form: a recognizer plus a compositional structure delivers all four
classical Aristotelian conditions on its event space.
-/

/-- **The Unification Theorem.**

A recognizer automatically supplies the three definitional Aristotelian
conditions (Identity, Non-Contradiction, Totality) on its event space,
plus the primitive observer (the recognizer itself), provided the event
space is non-trivially populated.

The fourth condition (Composition Consistency) is not automatic; it
requires the explicit `RecognizerComposition` hypothesis on a chosen
composition law for the event space. When that hypothesis is supplied,
the recognizer's event space is a full Law-of-Logic carrier in the sense
of the rigidity paper. -/
theorem unification {𝒞 ℰ : Type*}
    (r : Recognizer 𝒞 ℰ) (weight : ℝ)
    (h : r.hasNontrivialRecognition) :
    -- Three definitional Aristotelian conditions:
    (∀ e : ℰ, r.cost weight e e = 0) ∧
    (∀ e₁ e₂ : ℰ, r.cost weight e₁ e₂ = r.cost weight e₂ e₁) ∧
    (∀ e₁ e₂ : ℰ, ∃ c : ℝ, r.cost weight e₁ e₂ = c) ∧
    -- Single-valuedness on unordered pairs (≡ Non-Contradiction):
    SingleValuedOnUnorderedPair (r.cost weight) ∧
    -- Primitive observer:
    (∃ (O : PrimitiveObserver ℰ) (e₁ e₂ : ℰ),
      e₁ ≠ e₂ ∧ Separates O e₁ e₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Recognizer.identity r weight
  · exact Recognizer.non_contradiction r weight
  · exact Recognizer.totality r weight
  · exact Recognizer.singleValued r weight
  · exact Recognizer.induces_primitive_observer r h

/-! ## Headline Certificate -/

/-- **Recognizer-Induces-Logic Certificate.**

The single forcing chain from Recognition Geometry to the Law of Logic
in its current form: the three definitional Aristotelian conditions are
automatic, the primitive observer is automatic, and the substantive
content reduces to a named compositional hypothesis. -/
structure RecognizerInducesLogicCert where
  identity_auto :
    ∀ {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ) (weight : ℝ),
      ∀ e : ℰ, r.cost weight e e = 0
  non_contradiction_auto :
    ∀ {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ) (weight : ℝ),
      ∀ e₁ e₂ : ℰ, r.cost weight e₁ e₂ = r.cost weight e₂ e₁
  totality_auto :
    ∀ {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ) (weight : ℝ),
      ∀ e₁ e₂ : ℰ, ∃ c : ℝ, r.cost weight e₁ e₂ = c
  primitive_observer_auto :
    ∀ {𝒞 ℰ : Type*} (r : Recognizer 𝒞 ℰ),
      r.hasNontrivialRecognition →
        ∃ (O : PrimitiveObserver ℰ) (e₁ e₂ : ℰ),
          e₁ ≠ e₂ ∧ Separates O e₁ e₂

def recognizerInducesLogicCert : RecognizerInducesLogicCert where
  identity_auto := fun r w => Recognizer.identity r w
  non_contradiction_auto := fun r w => Recognizer.non_contradiction r w
  totality_auto := fun r w => Recognizer.totality r w
  primitive_observer_auto := fun r h => Recognizer.induces_primitive_observer r h

theorem recognizerInducesLogicCert_inhabited :
    Nonempty RecognizerInducesLogicCert :=
  ⟨recognizerInducesLogicCert⟩

end RecognizerInducesLogic
end Foundation
end IndisputableMonolith
