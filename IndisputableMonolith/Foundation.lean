import IndisputableMonolith.Foundation.NothingToDistinction
import IndisputableMonolith.Foundation.TMinus1ToT8Bridge
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.LinkingFromHierarchy
import IndisputableMonolith.Foundation.RecognitionToLinkingSeam
import IndisputableMonolith.Foundation.RecognitionLinkingPositiveID
import IndisputableMonolith.Foundation.RecognitionProducedEmbedding
import IndisputableMonolith.Foundation.LinkingNumbers

/-!
# Shape of Logic Core Foundation

This public aggregator is intentionally narrow.  It exposes the T-2 through T8
core theory, the Mathlib circle-H1 T8 closure, and the Recognition-to-detector
seam (`LinkingNecessity`, `RecognitionToLinkingSeam`,
`RecognitionProducedEmbedding`). It does not re-export later physics or
private application layers.
-/

namespace IndisputableMonolith
namespace Foundation

open NothingToDistinction
open TMinus1ToT8Bridge

/-! ## Public Core Exports -/

/-- T-2 to T-1: the Lean encoding of absolute nothing forces distinction. -/
abbrev tminus2_to_tminus1_certificate :=
  NothingToDistinction.nothingToDistinctionCert

/-- Public T-2 through T8 certificate. -/
abbrev complete_tminus2_to_t8 :=
  TMinus1ToT8Bridge.complete_forcing_chain_tminus2_to_t8

/-! The carrier-threaded T0 through T8 spine from one object-level distinction. -/

/-- T8's Mathlib circle-H1 nonvanishing replacement is closed unconditionally. -/
theorem circle_h1_nonzero : MathlibCohomologyBridge.circleH1ZNonzero :=
  TMinus1ToT8Bridge.complete_forcing_chain_tminus2_to_t8.{0,0,0,0,0,0,0}.circle_h1_nonzero

/-- The stronger `H_1(S^1; Z) ≅ Z` target is also closed unconditionally. -/
theorem circle_h1_iso_int : MathlibCohomologyBridge.circleH1ZIsoInt :=
  TMinus1ToT8Bridge.complete_forcing_chain_tminus2_to_t8.{0,0,0,0,0,0,0}.circle_h1_iso_int

end Foundation
end IndisputableMonolith
