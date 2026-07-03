import Mathlib
import IndisputableMonolith.Core

/-!
README (Executable Manifest) — Proven Architecture of Reality

To verify in seconds (no knobs), run:
  #eval IndisputableMonolith.URCAdapters.routeA_end_to_end_demo
  #eval IndisputableMonolith.URCAdapters.routeB_closure_report
  #eval IndisputableMonolith.URCAdapters.lambda_report
  #eval IndisputableMonolith.URCAdapters.grand_manifest

These confirm: A (axioms→bridge) ⇒ C; B (generators→bridge) ⇒ C; λ_rec uniqueness holds.
-/

open Classical Function
open Real Complex
open scoped BigOperators

namespace IndisputableMonolith

/-- Entry point for the Indisputable Monolith verification system.
    This module serves as the documentation and entry point for all
    verification components that have been extracted into separate modules. -/
def manifest : String :=
  "IndisputableMonolith: Proven Architecture of Reality
   All components extracted and verified. Run individual module tests for details."

end IndisputableMonolith
