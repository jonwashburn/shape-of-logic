import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Bases

/-! # Hilbert Space for Recognition Science QM Bridge -/

namespace IndisputableMonolith.Quantum

/-- A separable Hilbert space structure -/
class RSHilbertSpace (H : Type*) extends
  SeminormedAddCommGroup H,
  InnerProductSpace ℂ H,
  CompleteSpace H,
  TopologicalSpace.SeparableSpace H

/-- Normalized state (unit vector) -/
structure NormalizedState (H : Type*) [RSHilbertSpace H] where
  vec : H
  norm_one : ‖vec‖ = 1

end IndisputableMonolith.Quantum
