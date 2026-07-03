import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace FactorizationForcing

/-!
# Factorization and Associativity Gate

This module formalizes the algebraic core used by the B2 closure program.

The hard analytic step in the paper is the passage from factorization plus
three-way compatibility to the statement that the combiner is affine in its
second argument. Once that affine response is available, the remaining forcing
is pure algebra:

- symmetry,
- the boundary law `P(u,0) = 2u`,
- and the canonical normalization `P(1,1) = 6`

together force the RCL polynomial exactly.
-/

/-- Packaged combiner gate used by the factorization/associativity bridge. -/
structure FactorizationAssociativityGate (P : ℝ → ℝ → ℝ) : Prop where
  symmetric : ∀ u v, P u v = P v u
  rightAffine : ∀ u, ∃ α β, ∀ v, P u v = α * v + β
  zeroBoundary : ∀ u, P u 0 = 2 * u
  unitDiagonal : P 1 1 = 6

/-- The canonical RCL combiner. -/
def rclCombiner (u v : ℝ) : ℝ :=
  2 * u * v + 2 * u + 2 * v

/-- The canonical RCL polynomial satisfies the full factorization gate. -/
theorem rclCombiner_satisfies_gate :
    FactorizationAssociativityGate rclCombiner where
  symmetric := by
    intro u v
    unfold rclCombiner
    ring
  rightAffine := by
    intro u
    refine ⟨2 * u + 2, 2 * u, ?_⟩
    intro v
    unfold rclCombiner
    ring
  zeroBoundary := by
    intro u
    unfold rclCombiner
    ring
  unitDiagonal := by
    unfold rclCombiner
    norm_num

/-- Once the affine-response step is known, symmetry and the boundary law force
    the entire bilinear family. -/
theorem gate_forces_bilinear_family (P : ℝ → ℝ → ℝ)
    (hGate : FactorizationAssociativityGate P) :
    ∃ c : ℝ, ∀ u v, P u v = c * u * v + 2 * u + 2 * v := by
  classical
  choose α β hAffine using hGate.rightAffine
  have hβ : ∀ u, β u = 2 * u := by
    intro u
    have h0 : P u 0 = α u * 0 + β u := hAffine u 0
    rw [hGate.zeroBoundary u] at h0
    linarith
  let c : ℝ := α 1 - 2
  refine ⟨c, ?_⟩
  intro u v
  have hsym1 : P u 1 = P 1 u := hGate.symmetric u 1
  have hαu : α u = c * u + 2 := by
    dsimp [c]
    have hcalc : α u * 1 + β u = α 1 * u + β 1 := by
      calc
        α u * 1 + β u = P u 1 := by symm; exact hAffine u 1
        _ = P 1 u := hGate.symmetric u 1
        _ = α 1 * u + β 1 := hAffine 1 u
    rw [hβ u, hβ 1] at hcalc
    linarith
  calc
    P u v = α u * v + β u := hAffine u v
    _ = (c * u + 2) * v + 2 * u := by rw [hαu, hβ u]
    _ = c * u * v + 2 * u + 2 * v := by ring

/-- Canonical normalization selects the RCL member of the bilinear family. -/
theorem gate_forces_rcl (P : ℝ → ℝ → ℝ)
    (hGate : FactorizationAssociativityGate P) :
    ∀ u v, P u v = 2 * u * v + 2 * u + 2 * v := by
  obtain ⟨c, hc⟩ := gate_forces_bilinear_family P hGate
  have hc_two : c = 2 := by
    have h11 : P 1 1 = c * 1 * 1 + 2 * 1 + 2 * 1 := by
      simpa using hc 1 1
    linarith [hGate.unitDiagonal, h11]
  intro u v
  calc
    P u v = c * u * v + 2 * u + 2 * v := hc u v
    _ = 2 * u * v + 2 * u + 2 * v := by rw [hc_two]

/-- Exact gate characterization: the factorization gate is equivalent to being
the canonical RCL combiner. -/
theorem factorization_gate_iff_rcl (P : ℝ → ℝ → ℝ) :
    FactorizationAssociativityGate P ↔ ∀ u v, P u v = rclCombiner u v := by
  constructor
  · intro hGate u v
    rw [gate_forces_rcl P hGate u v]
    rfl
  · intro hP
    refine {
      symmetric := ?_
      rightAffine := ?_
      zeroBoundary := ?_
      unitDiagonal := ?_
    }
    · intro u v
      rw [hP u v, hP v u]
      unfold rclCombiner
      ring
    · intro u
      refine ⟨2 * u + 2, 2 * u, ?_⟩
      intro v
      rw [hP u v]
      unfold rclCombiner
      ring
    · intro u
      rw [hP u 0]
      unfold rclCombiner
      ring
    · rw [hP 1 1]
      unfold rclCombiner
      norm_num

end FactorizationForcing
end DAlembert
end Foundation
end IndisputableMonolith
