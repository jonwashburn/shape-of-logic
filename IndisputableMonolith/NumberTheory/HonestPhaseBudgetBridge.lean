import Mathlib
import IndisputableMonolith.NumberTheory.DefectSampledTrace
import IndisputableMonolith.NumberTheory.MeromorphicCircleOrder

/-!
# Honest Phase Budget Bridge

This module packages a concrete kind of extra analytic input beyond pure
completed-ξ symmetry: a perturbation witness for an actual phase family.

Such a witness does not by itself prove RH, but it is exactly the
Euler/Hadamard-style quantitative control needed to turn an honest phase family
into bounded annular excess data on the sampled side.
-/

namespace IndisputableMonolith
namespace NumberTheory

noncomputable section

/-- The current `zetaDerivedPhaseFamily` sits exactly on the topological floor:
its annular excess is identically zero on every mesh depth. -/
theorem zetaDerivedPhaseFamily_excess_zero
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge)
    (N : ℕ) :
    annularExcess ((zetaDerivedPhaseFamily sensor qlf horder).toSampledFamily.mesh N) = 0 := by
  let dpf := zetaDerivedPhaseFamily sensor qlf horder
  unfold annularExcess annularCost annularTopologicalFloor
  rw [sub_eq_zero]
  apply Finset.sum_congr rfl
  intro n _
  have hconst :
      ∀ j : Fin (8 * (n.val + 1)),
        (((dpf.toSampledFamily).mesh N).rings n).increments j =
          -(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
            (8 * (n.val + 1) : ℝ) := by
    intro j
    have hinc :
        (((dpf.toSampledFamily).mesh N).rings n).increments j =
          defectPhasePureIncrement dpf (n.val + 1) := by
      simpa [dpf, zetaDerivedPhasePerturbationWitness] using
        (zetaDerivedPhasePerturbationWitness sensor qlf horder).increment_eq
          (n.val + 1) (Nat.succ_pos n.val) j
    have hpure :
        defectPhasePureIncrement dpf (n.val + 1) =
          -(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
            (8 * (n.val + 1) : ℝ) := by
      simp [dpf, defectPhasePureIncrement, DefectPhaseFamily.toSampledFamily,
        defectAnnularMesh]
    rw [hinc, hpure]
  calc
    ringCost (((dpf.toSampledFamily).mesh N).rings n)
        = ∑ j : Fin (8 * (n.val + 1)),
            phiCost (-(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
              (8 * (n.val + 1) : ℝ)) := by
            unfold ringCost
            apply Finset.sum_congr rfl
            intro j _
            rw [hconst j]
    _ = topologicalFloor (n.val + 1) (((dpf.toSampledFamily).mesh N).charge) := by
          unfold topologicalFloor
          simp [Finset.sum_const, nsmul_eq_mul]

/-- A perturbation witness for any defect phase family induces the ring-level
perturbation-control package needed by the annular-cost machinery. -/
noncomputable def phaseFamily_ringPerturbationControl
    (dpf : DefectPhaseFamily) (hw : DefectPhasePerturbationWitness dpf) :
    RingPerturbationControl (dpf.toSampledFamily) := by
  refine { small := ?_, total_bounded := ?_ }
  · intro N n j
    have hsmall := regular_perturbation_small hw (n.val + 1) (Nat.succ_pos n.val) j
    have hinc :
        (((dpf.toSampledFamily).mesh N).rings n).increments j =
          defectPhasePureIncrement dpf (n.val + 1) +
            hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j := by
      simpa [DefectPhaseFamily.toSampledFamily, defectAnnularMesh,
        ContinuousPhaseData.toAnnularRingSample] using
        regular_factor_increment_decomposition hw (n.val + 1) (Nat.succ_pos n.val) j
    have hpure :
        defectPhasePureIncrement dpf (n.val + 1) =
          -(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
            (8 * (n.val + 1) : ℝ) := by
      simp [defectPhasePureIncrement, DefectPhaseFamily.toSampledFamily,
        defectAnnularMesh]
    rw [hinc, hpure]
    simpa using hsmall
  obtain ⟨K₁, hK₁⟩ := regular_perturbation_linear_term_bounded hw
  obtain ⟨K₂, hK₂⟩ := regular_perturbation_quadratic_term_bounded hw
  refine ⟨K₁ + K₂, ?_⟩
  intro N
  have hterm :
      ∀ n : Fin N,
        realizedRingPerturbationError (dpf.toSampledFamily) N n =
          phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
            ∑ j : Fin (8 * (n.val + 1)),
              |hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j| +
          phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
            ∑ j : Fin (8 * (n.val + 1)),
              (hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2 := by
    intro n
    dsimp [realizedRingPerturbationError]
    have hpure :
        defectPhasePureIncrement dpf (n.val + 1) =
          -(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
            (8 * (n.val + 1) : ℝ) := by
      simp [defectPhasePureIncrement, DefectPhaseFamily.toSampledFamily,
        defectAnnularMesh]
    rw [hpure]
    have hlinSum :
        ∑ j : Fin (8 * (n.val + 1)),
          |(((dpf.toSampledFamily).mesh N).rings n).increments j -
            (-(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
              (8 * (n.val + 1) : ℝ))| =
        ∑ j : Fin (8 * (n.val + 1)),
          |hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j| := by
      apply Finset.sum_congr rfl
      intro j _
      have hinc :
          (((dpf.toSampledFamily).mesh N).rings n).increments j =
            defectPhasePureIncrement dpf (n.val + 1) +
              hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j := by
        simpa [DefectPhaseFamily.toSampledFamily, defectAnnularMesh,
          ContinuousPhaseData.toAnnularRingSample] using
          regular_factor_increment_decomposition hw (n.val + 1) (Nat.succ_pos n.val) j
      rw [hinc, hpure]
      ring_nf
    have hquadSum :
        ∑ j : Fin (8 * (n.val + 1)),
          ((((dpf.toSampledFamily).mesh N).rings n).increments j -
            (-(2 * Real.pi * (((dpf.toSampledFamily).mesh N).charge : ℝ)) /
              (8 * (n.val + 1) : ℝ))) ^ 2 =
        ∑ j : Fin (8 * (n.val + 1)),
          (hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      have hinc :
          (((dpf.toSampledFamily).mesh N).rings n).increments j =
            defectPhasePureIncrement dpf (n.val + 1) +
              hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j := by
        simpa [DefectPhaseFamily.toSampledFamily, defectAnnularMesh,
          ContinuousPhaseData.toAnnularRingSample] using
          regular_factor_increment_decomposition hw (n.val + 1) (Nat.succ_pos n.val) j
      rw [hinc, hpure]
      ring_nf
    rw [hlinSum, hquadSum]
  calc
    ∑ n : Fin N, realizedRingPerturbationError (dpf.toSampledFamily) N n
        = ∑ n : Fin N,
            (phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                |hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j| +
             phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                (hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2) := by
            apply Finset.sum_congr rfl
            intro n _
            exact hterm n
    _ = (∑ n : Fin N,
            phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                |hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j|) +
          ∑ n : Fin N,
            phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                (hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2 := by
            rw [Finset.sum_add_distrib]
    _ ≤ K₁ + K₂ := by
          linarith [hK₁ N, hK₂ N]

/-- Hence a perturbation witness gives bounded annular excess for the sampled
family attached to that phase family. -/
theorem phaseFamily_excess_bounded_of_perturbationWitness
    (dpf : DefectPhaseFamily) (hw : DefectPhasePerturbationWitness dpf) :
    RealizedDefectAnnularExcessBounded (dpf.toSampledFamily) := by
  exact realizedDefectAnnularExcessBounded_of_ringRegularErrorBound _
    (ringRegularErrorBound_of_ringPerturbationControl _
      (phaseFamily_ringPerturbationControl dpf hw))

/-- Specialization to the honest zeta-derived phase package. This makes the
missing Euler/Hadamard-style upgrade explicit: a perturbation witness for the
honest phase family is enough to produce bounded annular excess data. -/
theorem honestPhaseFamily_excess_bounded_of_perturbationWitness
    (zfd : ZetaPhaseFamilyData)
    (hw : DefectPhasePerturbationWitness zfd.phaseFamily) :
    RealizedDefectAnnularExcessBounded (zfd.phaseFamily.toSampledFamily) := by
  exact phaseFamily_excess_bounded_of_perturbationWitness zfd.phaseFamily hw

/-- The current honest zeta-derived phase package already supplies its canonical
zero-perturbation witness. -/
noncomputable def honestPhaseFamily_perturbationWitness
    (zfd : ZetaPhaseFamilyData) :
    DefectPhasePerturbationWitness zfd.phaseFamily :=
  zfd.perturbationWitness

/-- The sampled family attached to honest phase data has zero annular excess on
every mesh depth. -/
theorem honestPhaseFamily_excess_zero
    (zfd : ZetaPhaseFamilyData) (N : ℕ) :
    annularExcess (zfd.phaseFamily.toSampledFamily.mesh N) = 0 := by
  simpa [zfd.family_derived] using
    zetaDerivedPhaseFamily_excess_zero zfd.sensor zfd.witness zfd.witness_order N

/-- Therefore the sampled family attached to the current honest phase package
has bounded annular excess. The remaining analytic gap is no longer the
perturbation witness itself, but upgrading this excess control to the charge-zero
conclusion required by `AnalyticTrace`. -/
theorem honestPhaseFamily_excess_bounded
    (zfd : ZetaPhaseFamilyData) :
    RealizedDefectAnnularExcessBounded (zfd.phaseFamily.toSampledFamily) := by
  refine ⟨0, ?_⟩
  intro N
  rw [honestPhaseFamily_excess_zero zfd N]

/-- If the sampled family attached to honest phase data also has bounded total
annular cost, then the corresponding sensor charge must vanish. This isolates
the remaining topological/budget upgrade needed by the analytic route. -/
theorem honestPhaseFamily_charge_zero_of_costBounded
    (zfd : ZetaPhaseFamilyData)
    (hcost : RealizedDefectAnnularCostBounded (zfd.phaseFamily.toSampledFamily)) :
    zfd.sensor.charge = 0 := by
  have hzero :=
    (realizedDefectCostBounded_iff_charge_zero_and_excessBounded
      (zfd.phaseFamily.toSampledFamily)).mp hcost
  simpa [DefectPhaseFamily.toSampledFamily, zfd.family_sensor] using hzero.1

/-- For the current honest phase package, bounded total cost is equivalent to
zero charge. The perturbation/excess part is already proved; only the bounded-cost
upgrade remains genuinely open. -/
theorem honestPhaseFamily_cost_bounded_iff_charge_zero
    (zfd : ZetaPhaseFamilyData) :
    RealizedDefectAnnularCostBounded (zfd.phaseFamily.toSampledFamily) ↔
      zfd.sensor.charge = 0 := by
  constructor
  · intro hcost
    exact honestPhaseFamily_charge_zero_of_costBounded zfd hcost
  · intro hzero
    have hzero' : (zfd.phaseFamily.toSampledFamily).sensor.charge = 0 := by
      simpa [DefectPhaseFamily.toSampledFamily, zfd.family_sensor] using hzero
    exact realizedDefectCostBounded_of_charge_zero_and_excessBounded
      (zfd.phaseFamily.toSampledFamily) hzero'
      (honestPhaseFamily_excess_bounded zfd)

end

end NumberTheory
end IndisputableMonolith
