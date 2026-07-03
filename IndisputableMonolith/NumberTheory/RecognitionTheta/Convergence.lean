import IndisputableMonolith.NumberTheory.RecognitionTheta

/-!
  RecognitionTheta/Convergence.lean

  Track C, sub-conjecture A.1.

  The current `RecognitionThetaConvergence` statement asks for summability of
  the Recognition Theta term for every `t > 0`. This module proves the general
  comparison theorem needed to discharge it: if the terms admit a summable
  nonnegative majorant for each positive `t`, then A.1 follows.

  The remaining mathematical content is not hidden here. It is the construction
  of such a majorant from lower bounds on `costSpectrumValue n` and upper
  bounds on the phi-rung weight.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace RecognitionTheta
namespace Convergence

noncomputable section

/-- A summable nonnegative majorant for the Recognition Theta terms at each
positive time. -/
structure RecognitionThetaMajorant where
  majorant : ℝ → ℕ → ℝ
  summable_majorant :
    ∀ t : ℝ, 0 < t → Summable (majorant t)
  term_norm_le :
    ∀ t : ℝ, 0 < t →
      ∀ n : ℕ, ‖recognitionThetaTerm t n‖ ≤ majorant t n

/-- A majorant package proves Recognition Theta convergence. -/
theorem recognitionThetaConvergence_of_majorant
    (maj : RecognitionThetaMajorant) :
    RecognitionThetaConvergence where
  summable := by
    intro t ht
    exact (maj.summable_majorant t ht).of_norm_bounded
      (maj.term_norm_le t ht)

/-- A reusable sufficient condition: domination by a geometric sequence. -/
structure RecognitionThetaGeometricMajorant where
  C : ℝ
  q : ℝ
  C_nonneg : 0 ≤ C
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  term_norm_le :
    ∀ t : ℝ, 0 < t →
      ∀ n : ℕ, ‖recognitionThetaTerm t n‖ ≤ C * q ^ n

/-- A geometric majorant is a summable majorant. -/
def majorant_of_geometric
    (geo : RecognitionThetaGeometricMajorant) :
    RecognitionThetaMajorant where
  majorant := fun _ n => geo.C * geo.q ^ n
  summable_majorant := by
    intro _t _ht
    exact Summable.mul_left geo.C
      (summable_geometric_of_lt_one geo.q_nonneg geo.q_lt_one)
  term_norm_le := geo.term_norm_le

/-- A geometric majorant proves Recognition Theta convergence. -/
theorem recognitionThetaConvergence_of_geometricMajorant
    (geo : RecognitionThetaGeometricMajorant) :
    RecognitionThetaConvergence :=
  recognitionThetaConvergence_of_majorant (majorant_of_geometric geo)

/-! ## Current A.1 attack surface -/

/-- Machine-readable A.1 status: the comparison theorem is proved; the remaining
input is a summable majorant, ideally geometric after finitely many terms. -/
structure RecognitionThetaConvergenceAttackSurface where
  comparison :
    RecognitionThetaMajorant → RecognitionThetaConvergence
  geometric_comparison :
    RecognitionThetaGeometricMajorant → RecognitionThetaConvergence

def recognitionThetaConvergenceAttackSurface :
    RecognitionThetaConvergenceAttackSurface where
  comparison := recognitionThetaConvergence_of_majorant
  geometric_comparison := recognitionThetaConvergence_of_geometricMajorant

end

end Convergence
end RecognitionTheta
end NumberTheory
end IndisputableMonolith
