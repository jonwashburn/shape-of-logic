import IndisputableMonolith.Gravity.Track1BCorrectedQuadratic

namespace IndisputableMonolith
namespace Gravity
namespace Track1BCompilerTrustStatus

/-!
# Compiler-Trust Status for the Track 1.B Corrected Gate

This module records, in a machine-checkable structure `CompilerTrustStatus`,
that the Track 1.B corrected-quadratic gate at `N = 5`
(`Track1BCorrectedQuadratic.correctedTrack1BGateAtN5_closed`) relies on
`native_decide` and therefore extends the kernel basis.

The extra axioms introduced are:
- `Lean.ofReduceBool`: allows the kernel to trust the compiler's reduction
  of boolean expressions.
- `Lean.trustCompiler`: grants general compiler trust for native computation.

The `N = 5` gate itself is closed (`gate_open = false` in
`correctedTrack1BStatus`), but the all-cardinality generalization remains open.
-/

/-- Machine-checkable record of the basis and open-problem status
for a theorem whose proof relies on `native_decide`. -/
structure CompilerTrustStatus where
  /-- Whether the proof uses `native_decide`. -/
  uses_native_decide : Bool
  /-- Extra axioms beyond the standard Lean basis. -/
  extra_axioms : List String
  /-- The standard Lean kernel basis. -/
  standard_basis : List String
  /-- Whether the all-cardinality generalization remains open. -/
  all_cardinality_open : Bool

/-- The compiler-trust status of the Track 1.B corrected gate at `N = 5`.
The gate is closed via `native_decide` (see
`Track1BCorrectedQuadratic.correctedTrack1BGateAtN5_closed`), so the kernel
basis is extended by `Lean.ofReduceBool` and `Lean.trustCompiler` on top of
the standard `propext / Classical.choice / Quot.sound` basis. The
all-cardinality generalization remains open. -/
def track1BCompilerTrustStatus : CompilerTrustStatus where
  uses_native_decide := true
  extra_axioms := ["Lean.ofReduceBool", "Lean.trustCompiler"]
  standard_basis := ["propext", "Classical.choice", "Quot.sound"]
  all_cardinality_open := true

/-- **Anchoring theorem.** The trust-status record is anchored to the real
result: the corrected Track 1.B gate at `N = 5` is closed
(`gate_open = false` in `correctedTrack1BStatus`), discharged by
`native_decide` via `correctedTrack1BGateAtN5_closed`, and the trust status
correctly records `uses_native_decide = true`. -/
theorem track1BCompilerTrustStatus_anchors_closed_gate :
    track1BCompilerTrustStatus.uses_native_decide = true ∧
    Track1BCorrectedQuadratic.correctedTrack1BStatus.gate_open = false := by
  exact ⟨rfl, rfl⟩

end Track1BCompilerTrustStatus
end Gravity
end IndisputableMonolith