import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection
import IndisputableMonolith.Foundation.RecognitionSignatureGauge
import IndisputableMonolith.Foundation.ObserverFromRecognition
import IndisputableMonolith.Foundation.RecognizerInducesLogic
import IndisputableMonolith.Foundation.MultiplicativeRecognizerL4
import IndisputableMonolith.Foundation.RecognitionLatticeFromRecognizer
import IndisputableMonolith.RecogGeom.Composition
import IndisputableMonolith.RecogGeom.FiniteResolution

/-!
# Recognition Core — the shape of logic at the recognizer / signature layer

This public aggregator exposes the recognition-geometry core that sits at the
T0 / T4 layer of the forcing chain: the recognizer, its indistinguishability
quotient, the full recognition signature, and the completeness condition under
which the signature determines all physically relevant states.

It is the formal answer to "a single Boolean observable is atomic, not complete;
the physical content is carried by the admitted recognizer family." Every
declaration below is proved in Lean with no `sorry` and no project-local axiom.

## Public citation targets

* `forced_quotient_iff` — the full signature determines the state up to the
  indistinguishability quotient (unconditional).
* `gauge_from_indistinguishability` — the physically forced quotient is exactly
  indistinguishability under the admitted family; gauge is the absence of a
  distinguishing recognition act.
* `signature_complete_iff_separating` — completeness (injective physical
  quotient) holds iff the family separates points. Necessary and sufficient.
* `one_bit_not_complete_boundary` — one Boolean coordinate is atomic, not
  complete; a separating family reconstructs the state; scalar-cost completeness
  is a separate hypothesis.
* `recognizer_refinement` — composing recognizers refines the quotient; more
  recognizers give a finer observable structure.
* `recognizer_forces_observer` — non-trivial recognition forces a primitive
  observer.
* `recognizer_induces_logic` — a recognizer supplies the three definitional
  Aristotelian conditions plus the primitive observer for free.
* `multiplicative_recognizer_L4` — composition consistency (the d'Alembert law)
  is derived, not assumed, on the multiplicative event space.
* `recognition_lattice` — a recognizer's kernel classes are the first
  recognition lattice; same-kernel interfaces give canonically equivalent
  lattices.
-/

namespace IndisputableMonolith
namespace RecognitionCore

/-! ## Signature, quotient, and completeness -/

/-- The full recognition signature determines the state up to the
indistinguishability quotient, with no hypothesis. -/
abbrev forced_quotient_iff :=
  @Foundation.PrimitiveRecognitionCalculus.QuotientSelection.forced_iff

/-- The physically forced quotient is exactly indistinguishability under the
admitted observable family; observables descend; a separating family collapses
the quotient to the identity. -/
abbrev gauge_from_indistinguishability :=
  @Foundation.PrimitiveRecognitionCalculus.QuotientSelection.gauge_from_indistinguishability

/-- Signature equality is the physical quotient. -/
abbrev signature_forced_quotient_iff :=
  @Foundation.RecognitionSignatureGauge.signature_forced_quotient_iff

/-- Completeness: a separating recognition signature gives an injective physical
quotient. This is the exact necessary-and-sufficient completeness condition. -/
abbrev signature_complete_iff_separating :=
  @Foundation.RecognitionSignatureGauge.signature_projection_injective_of_separating

/-- The corrected T0 boundary: one Boolean coordinate is atomic not complete; a
separating family reconstructs the state; scalar-cost completeness needs an extra
hypothesis. -/
abbrev one_bit_not_complete_boundary :=
  Foundation.RecognitionSignatureGauge.booleanShadowCompletenessBoundary_holds

/-! ## Recognizer family: generation and refinement -/

/-- Composing recognizers refines the quotient: more recognizers give a finer
observable structure. -/
abbrev recognizer_refinement :=
  @RecogGeom.refinement_theorem

/-- Non-trivial recognition forces a primitive observer (finite interface). -/
abbrev recognizer_forces_observer :=
  Foundation.ObserverFromRecognition.observerFromRecognitionCert

/-- A recognizer supplies the three definitional Aristotelian conditions plus
the primitive observer automatically on its event space. -/
abbrev recognizer_induces_logic :=
  @Foundation.RecognizerInducesLogic.unification

/-- Composition consistency (the d'Alembert law) is derived, not assumed, on the
positive multiplicative event space. -/
abbrev multiplicative_recognizer_L4 :=
  @Foundation.MultiplicativeRecognizerL4.MultiplicativeRecognizer.l4DerivableCert_inhabited

/-- A recognizer's kernel classes are the first recognition lattice. -/
abbrev recognition_lattice :=
  @Foundation.RecognitionLatticeFromRecognizer.recognitionLatticeCert_inhabited

end RecognitionCore
end IndisputableMonolith
