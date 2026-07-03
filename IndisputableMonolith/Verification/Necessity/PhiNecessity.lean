import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport.Lemmas

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace PhiNecessity

/-- Minimal self-similarity structure sufficient for the inevitability pipeline. -/
structure HasSelfSimilarity (StateSpace : Type) where
  preferred_scale : ℝ
  scale_gt_one : 1 < preferred_scale
  level0 : ℝ
  level1 : ℝ
  level2 : ℝ
  level0_pos : 0 < level0
  level1_ratio : level1 = preferred_scale * level0
  level2_ratio : level2 = preferred_scale * level1
  level2_recurrence : level2 = level1 + level0

namespace HasSelfSimilarity

@[simp]
lemma preferred_scale_pos {StateSpace : Type} (hSim : HasSelfSimilarity StateSpace) :
    0 < hSim.preferred_scale :=
  lt_trans (show (0 : ℝ) < 1 by norm_num) hSim.scale_gt_one

end HasSelfSimilarity

/-- **SCAFFOLD**: Canonical self-similarity witness constructed by directly
    inserting φ. This does NOT derive self-similarity from zero parameters alone;
    it assumes the conclusion by building a witness from the known answer.

    The genuine derivation chain is:
    1. ZeroParameterComparisonLedger → HasMultilevelComposition (structural)
    2. HasMultilevelComposition + no_free_knobs → UniformScaleLadder (HierarchyForcing)
    3. UniformScaleLadder + local binary recurrence + minimality → Fibonacci (HierarchyDynamics)
    4. Fibonacci → φ (HierarchyEmergence)

    See `IndisputableMonolith.Foundation.HierarchyDynamics.bridge_T5_T6` for the
    sorry-free derivation of the Fibonacci recurrence from primitive axioms.

    This scaffold constructor is retained for backward compatibility
    with the existing exclusivity pipeline. -/
noncomputable def self_similarity_from_discrete
    (StateSpace : Type)
    [Inhabited StateSpace]
    (_levels : ℤ → StateSpace)
    (_surj : Function.Surjective _levels) :
    HasSelfSimilarity StateSpace :=
  { preferred_scale := Constants.phi
  , scale_gt_one := IndisputableMonolith.PhiSupport.one_lt_phi
  , level0 := 1
  , level1 := Constants.phi
  , level2 := Constants.phi ^ 2
  , level0_pos := by norm_num
  , level1_ratio := by simp
  , level2_ratio := by
      simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  , level2_recurrence := IndisputableMonolith.PhiSupport.phi_squared }

/-- Self-similarity data forces the preferred scale to satisfy the golden-ratio polynomial. -/
lemma preferred_scale_fixed_point
    {StateSpace : Type} [Inhabited StateSpace]
    (hSim : HasSelfSimilarity StateSpace) :
    hSim.preferred_scale ^ 2 = hSim.preferred_scale + 1 := by
  classical
  have h₀ : hSim.level0 ≠ 0 := ne_of_gt hSim.level0_pos
  have h_eq :
      hSim.preferred_scale ^ 2 * hSim.level0 = (hSim.preferred_scale + 1) * hSim.level0 := by
    calc
      hSim.preferred_scale ^ 2 * hSim.level0
          = hSim.preferred_scale * (hSim.preferred_scale * hSim.level0) := by
            simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
      _ = hSim.preferred_scale * hSim.level1 := by
            simpa [hSim.level1_ratio, mul_comm, mul_left_comm, mul_assoc]
      _ = hSim.level2 := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hSim.level2_ratio.symm
      _ = hSim.level1 + hSim.level0 := hSim.level2_recurrence
      _ = (hSim.preferred_scale + 1) * hSim.level0 := by
            simpa [hSim.level1_ratio, right_distrib, add_comm, add_left_comm, add_assoc]
  have hScaled := congrArg (fun t => t / hSim.level0) h_eq
  simpa [h₀, mul_comm, mul_left_comm, mul_assoc] using hScaled

/-- Core consequence: any self-similarity witness satisfies the golden-ratio identities. -/
private lemma phi_result
    {StateSpace : Type} [Inhabited StateSpace]
    (hSim : HasSelfSimilarity StateSpace) :
    hSim.preferred_scale = Constants.phi ∧
    hSim.preferred_scale ^ 2 = hSim.preferred_scale + 1 ∧
    hSim.preferred_scale > 0 := by
  have hPos : 0 < hSim.preferred_scale := HasSelfSimilarity.preferred_scale_pos hSim
  have hFixed := preferred_scale_fixed_point (StateSpace:=StateSpace) hSim
  have hEq :=
    (IndisputableMonolith.PhiSupport.phi_unique_pos_root hSim.preferred_scale).mp
      ⟨hFixed, hPos⟩
  exact ⟨hEq, hFixed, hPos⟩

/-- Golden-ratio necessity when discrete levels are available. -/
theorem self_similarity_forces_phi
    {StateSpace : Type} [Inhabited StateSpace]
    (hSim : HasSelfSimilarity StateSpace)
    (_hDiscrete : ∃ levels : ℤ → StateSpace, Function.Surjective levels) :
    hSim.preferred_scale = Constants.phi ∧
    hSim.preferred_scale ^ 2 = hSim.preferred_scale + 1 ∧
    hSim.preferred_scale > 0 :=
  phi_result hSim

/-- Golden-ratio necessity from the polynomial identity alone. -/
theorem phi_is_mathematically_necessary
    (φ : ℝ) (h_gt : 1 < φ) (h_fix : φ ^ 2 = φ + 1) :
    φ = Constants.phi :=
  (IndisputableMonolith.PhiSupport.phi_unique_pos_root φ).mp
    ⟨h_fix, lt_trans (show (0 : ℝ) < 1 by norm_num) h_gt⟩

end PhiNecessity
end Necessity
end Verification
end IndisputableMonolith
