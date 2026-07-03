import Mathlib
import IndisputableMonolith.Verification.CPT.Core

/-!
# CPT Window Identifiability

This module formalizes the matrix-level identifiability core used in the CPT window
arguments:

- injective reconstruction from finite window measurements,
- equivalence with trivial kernel of the measurement map,
- equivalence with a "full-column-rank" predicate (defined as injectivity here),
- zero-detection under identifiability.

The "generic/nondegenerate" layer is represented explicitly by a named hypothesis
bundle (`NonvanishingMinorHypothesis`) to keep claim strength explicit.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace WindowIdentifiability

open scoped Classical

abbrev Vec (ι : Type) := ι → ℝ

variable {m n : Type} [Fintype n] [DecidableEq n]

/-- Linear measurement map induced by the window matrix. -/
noncomputable def measurementLinear (A : Matrix m n ℝ) :
    Vec n →ₗ[ℝ] Vec m :=
  Matrix.toLin' A

/-- Window identifiability: the measurement map is injective. -/
def Identifiable (A : Matrix m n ℝ) : Prop :=
  Function.Injective (measurementLinear A)

/-- Trivial-kernel formulation of identifiability. -/
def TrivialKernel (A : Matrix m n ℝ) : Prop :=
  LinearMap.ker (measurementLinear A) = ⊥

/-- "Full column rank" in the finite-data reconstruction sense:
injectivity of the matrix-induced linear map. -/
def FullColumnRank (A : Matrix m n ℝ) : Prop :=
  Function.Injective (measurementLinear A)

theorem identifiable_iff_trivialKernel (A : Matrix m n ℝ) :
    Identifiable A ↔ TrivialKernel A := by
  simpa [Identifiable, TrivialKernel] using
    (LinearMap.ker_eq_bot (f := measurementLinear A)).symm

theorem identifiable_iff_fullColumnRank (A : Matrix m n ℝ) :
    Identifiable A ↔ FullColumnRank A := by
  rfl

theorem trivialKernel_iff_fullColumnRank (A : Matrix m n ℝ) :
    TrivialKernel A ↔ FullColumnRank A := by
  constructor
  · intro h
    exact (identifiable_iff_fullColumnRank A).mp ((identifiable_iff_trivialKernel A).mpr h)
  · intro h
    exact (identifiable_iff_trivialKernel A).mp ((identifiable_iff_fullColumnRank A).mpr h)

/-- Under identifiability, observing zero output forces the input to be zero. -/
theorem zero_detection_of_identifiable (A : Matrix m n ℝ)
    (hId : Identifiable A) (x : Vec n) :
    measurementLinear A x = 0 → x = 0 := by
  intro hx
  apply hId
  calc
    measurementLinear A x = 0 := hx
    _ = measurementLinear A 0 := by simp

/-- Explicit bridge hypothesis for the paper's generic/nondegenerate regime:
we assume the relevant maximal-minor nonvanishing condition has already been
verified and expose only its identifiability consequence at this layer. -/
structure NonvanishingMinorHypothesis (A : Matrix m n ℝ) : Prop where
  fullColumnRank : FullColumnRank A

theorem generic_identifiability_assuming_nonvanishing_minor
    (A : Matrix m n ℝ)
    (hMinor : NonvanishingMinorHypothesis A) :
    Identifiable A :=
  hMinor.fullColumnRank

end WindowIdentifiability
end CPT
end Verification
end IndisputableMonolith
