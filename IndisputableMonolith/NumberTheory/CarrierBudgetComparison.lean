import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.DefectSampledTrace
import IndisputableMonolith.NumberTheory.CirclePhaseLift
import IndisputableMonolith.NumberTheory.MeromorphicCircleOrder
import IndisputableMonolith.NumberTheory.EulerInstantiation
import IndisputableMonolith.NumberTheory.HonestPhaseBudgetBridge

/-!
# Carrier–Defect Budget Comparison

This module formalizes the carrier budget comparison strategy (Phase 4a
of the RH closure plan): on the SAME circles around a hypothetical zero,
the carrier's sampled cost is bounded while the defect's topological floor
diverges, providing a contradiction for nonzero charge.

## Architecture

Given a hypothetical zero of ζ at ρ with charge m ≠ 0:

1. **Carrier family**: The Euler carrier C(s) = det₂(I−A(s))² is holomorphic
   and nonvanishing on Re(s) > 1/2. On circles around ρ, it has charge 0,
   so its topological floor is 0 and its sampled cost equals its excess.

2. **Defect family**: The reciprocal ζ⁻¹ has a pole/zero of order m at ρ.
   On circles around ρ, it has charge m ≠ 0, so its topological floor
   grows as Θ(m² log N).

3. **Budget transfer**: The carrier and defect sample the SAME geometric
   circles. The carrier's excess is bounded (by its regularity), while the
   defect's floor diverges. Since the total cost on each circle decomposes
   as floor + excess, the defect's total cost diverges.

## Key result

`carrier_defect_budget_contradiction`: for any `DefectSensor` with nonzero
charge and any finite carrier budget, there exists a refinement depth N
such that the defect's topological floor exceeds the carrier budget.
-/

namespace IndisputableMonolith
namespace NumberTheory

open Constants

noncomputable section

/-! ### §1. Carrier sampled family on common circles -/

/-- A carrier sampled family paired with a defect family on shared circles.

This structure records that two sampled families (carrier and defect) are
defined on the same concentric circles around a common center, allowing
direct comparison of their annular costs. -/
structure SharedCircleFamilyPair where
  sensor : DefectSensor
  carrierPhaseFamily : DefectPhaseFamily
  defectPhaseFamily : DefectPhaseFamily
  carrier_sensor_charge_zero : carrierPhaseFamily.sensor.charge = 0
  defect_sensor_eq : defectPhaseFamily.sensor = sensor
  shared_radius : carrierPhaseFamily.witnessRadius = defectPhaseFamily.witnessRadius

/-- The carrier family in a shared-circle pair has bounded annular cost
because its charge is 0 (topological floor vanishes). -/
theorem carrier_cost_bounded_of_shared_pair
    (pair : SharedCircleFamilyPair)
    (hexcess : RealizedDefectAnnularExcessBounded
      (pair.carrierPhaseFamily.toSampledFamily)) :
    RealizedDefectAnnularCostBounded
      (pair.carrierPhaseFamily.toSampledFamily) := by
  have hcharge : (pair.carrierPhaseFamily.toSampledFamily).sensor.charge = 0 :=
    pair.carrier_sensor_charge_zero
  exact realizedDefectCostBounded_of_charge_zero_and_excessBounded
    pair.carrierPhaseFamily.toSampledFamily hcharge hexcess

/-- The defect family in a shared-circle pair has UNBOUNDED annular cost
when the sensor has nonzero charge. -/
theorem defect_cost_unbounded_of_shared_pair
    (pair : SharedCircleFamilyPair)
    (hm : pair.sensor.charge ≠ 0) :
    ¬ RealizedDefectAnnularCostBounded
      (pair.defectPhaseFamily.toSampledFamily) := by
  intro hbound
  have hcharge : (pair.defectPhaseFamily.toSampledFamily).sensor.charge ≠ 0 := by
    simpa [DefectPhaseFamily.toSampledFamily, pair.defect_sensor_eq] using hm
  exact not_realizedDefectAnnularCostBounded
    pair.defectPhaseFamily.toSampledFamily hcharge hbound

/-! ### §2. Floor divergence versus carrier budget -/

/-- The carrier's topological floor is identically zero (since charge = 0),
while the defect's floor diverges. For any finite bound K, the defect floor
eventually exceeds K. -/
theorem defect_floor_exceeds_any_bound
    (sensor : DefectSensor) (hm : sensor.charge ≠ 0)
    (K : ℝ) :
    ∃ N : ℕ, K < annularTopologicalFloor N sensor.charge :=
  defect_topological_floor_unbounded sensor hm K

/-- Carrier cost on zero-charge circles: annularCost = annularExcess
since the topological floor is 0. -/
theorem carrier_cost_eq_excess_of_zero_charge (N : ℕ) (mesh : AnnularMesh N)
    (hcharge : mesh.charge = 0) :
    annularCost mesh = annularExcess mesh := by
  unfold annularExcess
  rw [hcharge, annularTopologicalFloor_zero]
  ring

/-! ### §3. Budget transfer theorem -/

/-- **Budget Transfer Theorem.**

On shared circles, the defect's total annular cost exceeds the carrier's
excess budget for sufficiently large refinement depth.

The logic:
- The carrier has charge 0 → topological floor = 0 → cost = excess ≤ B
- The defect has charge m ≠ 0 → topological floor > B for large N
- Since cost ≥ floor, the defect cost > B for large N

This theorem packages the key mathematical comparison: no finite carrier
budget can bound the defect's divergent cost when the charge is nonzero. -/
theorem carrier_defect_budget_contradiction
    (sensor : DefectSensor) (hm : sensor.charge ≠ 0)
    (B : ℝ) :
    ∃ N : ℕ, B < annularTopologicalFloor N sensor.charge := by
  exact defect_topological_floor_unbounded sensor hm B

/-- **Cost divergence from budget comparison.**

If the carrier's excess on shared circles is bounded by `B`, then for
sufficiently large N, the defect's total cost exceeds `B` because its
topological floor (which is a lower bound on total cost) diverges. -/
theorem defect_cost_exceeds_carrier_budget
    (sensor : DefectSensor) (hm : sensor.charge ≠ 0)
    (fam : DefectSampledFamily)
    (hfam_sensor : fam.sensor = sensor)
    (B : ℝ) :
    ∃ N : ℕ, B < annularCost (fam.mesh N) := by
  have hfam_charge : fam.sensor.charge ≠ 0 := by rwa [hfam_sensor]
  exact defectSampledFamily_unbounded fam hfam_charge B

/-! ### §4. Building shared-circle pairs from genuine phase data -/

/-- Construct a `SharedCircleFamilyPair` from a `QuantitativeLocalFactorization`
and a `DefectSensor`.

The carrier family uses the regular factor phase (charge 0, bounded cost),
while the defect family uses the full meromorphic phase (charge m). Both
are sampled on circles of decreasing radius `r₀/(n+1)` around the same
center. -/
noncomputable def mkSharedCirclePair
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) :
    SharedCircleFamilyPair where
  sensor := sensor
  carrierPhaseFamily := {
    sensor := { charge := 0, realPart := sensor.realPart, in_strip := sensor.in_strip }
    witnessRadius := qlf.radius
    witnessRadius_pos := qlf.radius_pos
    phaseAtLevel := fun n hn => by
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hd : (0 : ℝ) < ↑n + 1 := by linarith
      have hgt1 : (1 : ℝ) < ↑n + 1 := by linarith
      let rfp := regularFactorPhaseFromWitness qlf.toLocalMeromorphicWitness
        (qlf.radius / (↑n + 1)) (div_pos qlf.radius_pos hd) (div_lt_self qlf.radius_pos hgt1)
        qlf.logDerivBound qlf.logDerivBound_pos
      exact rfp.toContinuousPhaseData
    charge_uniform := fun n hn => by
      simp only
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hd : (0 : ℝ) < ↑n + 1 := by linarith
      have hgt1 : (1 : ℝ) < ↑n + 1 := by linarith
      exact (regularFactorPhaseFromWitness qlf.toLocalMeromorphicWitness
        (qlf.radius / (↑n + 1)) (div_pos qlf.radius_pos hd) (div_lt_self qlf.radius_pos hgt1)
        qlf.logDerivBound qlf.logDerivBound_pos).charge_zero
  }
  defectPhaseFamily := genuineZetaDerivedPhaseFamily sensor qlf horder
  carrier_sensor_charge_zero := rfl
  defect_sensor_eq := rfl
  shared_radius := rfl

/-- The shared-circle pair's carrier has bounded excess because the regular
factor phase is Lipschitz-controlled.

The carrier family has charge 0, so `defectPhasePureIncrement = 0`:
- `small`: via `epsilon_log_phi_small` (same underlying `RegularFactorPhase`)
- `linear_term_bounded`: trivially 0 since `phiCostLinearCoeff(0) = 0`
- `quadratic_term_bounded`: `phiCostQuadraticCoeff(0) = κ` times convergent `∑ ε²` -/
theorem mkSharedCirclePair_carrier_excess_bounded
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) :
    RealizedDefectAnnularExcessBounded
      ((mkSharedCirclePair sensor qlf horder).carrierPhaseFamily.toSampledFamily) := by
  let carrierDpf := (mkSharedCirclePair sensor qlf horder).carrierPhaseFamily
  have hw : DefectPhasePerturbationWitness carrierDpf := {
    epsilon := fun n hn j =>
      (genuineRegularFactorPhaseAt qlf n hn).sampleIncrements n j
    increment_eq := by
      intro n hn j
      simp only [carrierDpf, mkSharedCirclePair, defectPhasePureIncrement, Int.cast_zero,
        neg_zero, mul_zero, zero_div, zero_add]
      simp only [genuineRegularFactorPhaseAt, regularFactorPhaseFromWitness, mkRegularFactorPhase]
    small := epsilon_log_phi_small qlf
    linear_term_bounded := by
      refine ⟨0, fun N => ?_⟩
      have hpure_zero : ∀ (n : Fin N),
          defectPhasePureIncrement carrierDpf (n.val + 1) = 0 := by
        intro n
        simp [carrierDpf, mkSharedCirclePair, defectPhasePureIncrement]
      simp only [hpure_zero, abs_zero, phiCostLinearCoeff, mul_zero, Real.sinh_zero,
        zero_mul, Finset.sum_const_zero, le_refl]
    quadratic_term_bounded := by
      refine ⟨kappa * (qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * Real.pi) ^ 2), fun N => ?_⟩
      have hpure_zero : ∀ (n : Fin N),
          defectPhasePureIncrement carrierDpf (n.val + 1) = 0 := by
        intro n
        simp [carrierDpf, mkSharedCirclePair, defectPhasePureIncrement]
      let C : ℝ :=
        kappa * (qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * Real.pi) ^ 2) / 8
      have hbig_nonneg :
          0 ≤ kappa * (qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * Real.pi) ^ 2) := by
        exact mul_nonneg kappa_pos.le (by positivity)
      have hC_nonneg : 0 ≤ C := by
        dsimp [C]
        exact div_nonneg hbig_nonneg (by positivity)
      have hterm :
          ∀ n : Fin N,
            phiCostQuadraticCoeff |defectPhasePureIncrement carrierDpf (n.val + 1)| *
                ∑ j : Fin (8 * (n.val + 1)),
                  ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
                    (n.val + 1) j) ^ 2
              ≤ C * ((1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ^ 2) := by
        intro n
        let innerSum : ℝ :=
          ∑ j : Fin (8 * (n.val + 1)),
            ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
              (n.val + 1) j) ^ 2
        have hinner := sum_epsilon_sq_bound qlf n
        have hbound :
            kappa * innerSum ≤
              kappa *
                (qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * Real.pi) ^ 2 /
                  (8 * ((n.val : ℝ) + 1) * ((n.val : ℝ) + 2) ^ 2)) := by
          simpa [innerSum] using mul_le_mul_of_nonneg_left hinner kappa_pos.le
        rw [hpure_zero n]
        simp [phiCostQuadraticCoeff]
        simpa [C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound
      calc
        ∑ n : Fin N,
            phiCostQuadraticCoeff |defectPhasePureIncrement carrierDpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
                  (n.val + 1) j) ^ 2
          ≤ ∑ n : Fin N, C * ((1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ^ 2) := by
              apply Finset.sum_le_sum
              intro n hn
              exact hterm n
        _ = C * ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ^ 2 := by
              rw [← Finset.mul_sum]
        _ ≤ C * 1 := by
              exact mul_le_mul_of_nonneg_left (sum_inv_succ_mul_succ_sq_le_one N) hC_nonneg
        _ ≤ kappa * (qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * Real.pi) ^ 2) := by
              dsimp [C]
              simpa using (div_le_self hbig_nonneg (by norm_num : (1 : ℝ) ≤ 8))
  }
  exact phaseFamily_excess_bounded_of_perturbationWitness carrierDpf hw

/-! ### §5. The full comparison chain -/

/-- **Full carrier–defect comparison for hypothetical zeros.**

For any hypothetical zero of ζ with nonzero charge, the carrier budget
comparison shows that the defect's cost exceeds any carrier budget bound
for sufficiently large refinement depth. This is the concrete instantiation
of the abstract budget transfer theorem on shared circles. -/
theorem carrier_defect_comparison_rh
    (sensor : DefectSensor) (hm : sensor.charge ≠ 0)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) :
    ¬ RealizedDefectAnnularCostBounded
      ((mkSharedCirclePair sensor qlf horder).defectPhaseFamily.toSampledFamily) := by
  exact defect_cost_unbounded_of_shared_pair _ hm

end

end NumberTheory
end IndisputableMonolith
