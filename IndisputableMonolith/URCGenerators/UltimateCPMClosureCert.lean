import Mathlib
import IndisputableMonolith.URCGenerators.CPMClosureCert
import IndisputableMonolith.Verification.PhiPinnedCert

namespace IndisputableMonolith
namespace URCGenerators

/-!
# Ultimate + CPM Closure Certificate

Bundles the existence/uniqueness of the pinned scale `φ` from
`PhiPinnedCert` together with the standalone CPM method closure
certificate (generic CPM A/B/C + a toy-model consistency witness).

This serves as a more comprehensive top‑level certificate that
combines RS φ-pinning with CPM method closure.
-/

/-- Combined certificate for UltimateClosure ∧ CPMClosure. -/
structure UltimateCPMClosureCert where
  deriving Repr

/-- Verification predicate: asserts both
    (1) unique `φ` satisfying `PhiSelection`, and
    (2) CPM method closure (standalone CPM certificate).

NOTE: We intentionally do **not** import the repo-wide `NonCircularityCert` here.
That larger bundle pulls in many WIP subprojects (astrophysics, applied modules, etc.)
and should be audited/compiled as a separate target, not as part of the CI smoke surface. -/
@[simp] def UltimateCPMClosureCert.verified (_c : UltimateCPMClosureCert) : Prop :=
  IndisputableMonolith.Verification.PhiPinned.PhiPinnedCert.verified {} ∧
  IndisputableMonolith.URCGenerators.CPMClosureCert.verified {}

/-- Top‑level theorem: the combined certificate verifies. -/
@[simp] theorem UltimateCPMClosureCert.verified_any (c : UltimateCPMClosureCert) :
  UltimateCPMClosureCert.verified c := by
  refine And.intro ?_ ?_
  · exact IndisputableMonolith.Verification.PhiPinned.PhiPinnedCert.verified_any {}
  · exact IndisputableMonolith.URCGenerators.CPMClosureCert.verified_any {}

end URCGenerators
end IndisputableMonolith
