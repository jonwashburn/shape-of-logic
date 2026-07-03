import Mathlib
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.MeromorphicCircleOrder

/-!
# Defect Sampled Trace

Realized annular meshes attached to the phase-sampling construction for a
hypothetical zeta defect.

## Why this layer is needed

After eliminating Axiom 1, the remaining bottleneck is Axiom 2. The previous
formal statement quantified over *all* `AnnularMesh` values with the right
charge, which is stronger than the intended analytic statement. What one really
needs to bound is the cost of the **canonical sampled family** coming from the
phase of `ζ⁻¹` near the hypothetical defect.

This module packages that realized family:

* `defectAnnularMesh` — sample one `DefectPhaseFamily` at depth `N`
* `DefectSampledFamily` — a full refinement family of realized meshes
* `canonicalDefectSampledFamily` — the chosen family attached to a sensor
* `defectSampledFamily_unbounded` — nonzero charge still forces cost → ∞

The last theorem is the key bridge for the refined Axiom 2: any uniform upper
bound on the cost of the realized sampled family contradicts annular coercivity.
-/

namespace IndisputableMonolith
namespace NumberTheory

noncomputable section

/-! ### §1. Sampling a phase family into annular meshes -/

/-- Build an `AnnularMesh` from a `DefectPhaseFamily` by sampling each ring at
the canonical `8n` equispaced angles. -/
def defectAnnularMesh (dpf : DefectPhaseFamily) (N : ℕ) : AnnularMesh N where
  rings := fun k =>
    (dpf.phaseAtLevel (k.val + 1) (Nat.succ_pos k.val)).toAnnularRingSample
      (k.val + 1) (Nat.succ_pos k.val)
  charge := dpf.sensor.charge
  uniform_charge := fun k =>
    dpf.charge_uniform (k.val + 1) (Nat.succ_pos k.val)

/-- The mesh obtained from phase sampling has the correct total charge. -/
theorem defectAnnularMesh_charge (dpf : DefectPhaseFamily) (N : ℕ) :
    (defectAnnularMesh dpf N).charge = dpf.sensor.charge :=
  rfl

/-! ### §2. Realized sampled families -/

/-- A realized sampled family of annular meshes attached to one defect sensor.

Unlike a bare `AnnularTrace`, this object is intended to arise from the actual
phase-sampling construction for `ζ⁻¹`, not from an arbitrary synthetic mesh
family. -/
structure DefectSampledFamily where
  sensor : DefectSensor
  mesh : ∀ N : ℕ, AnnularMesh N
  charge_spec : ∀ N : ℕ, (mesh N).charge = sensor.charge

/-- Convert a `DefectPhaseFamily` to its realized sampled annular family. -/
def DefectPhaseFamily.toSampledFamily (dpf : DefectPhaseFamily) :
    DefectSampledFamily where
  sensor := dpf.sensor
  mesh := defectAnnularMesh dpf
  charge_spec := defectAnnularMesh_charge dpf

/-- Choose one phase family attached to a hypothetical defect sensor.

This uses the strengthened existential package
`defect_phase_family_with_perturbation_exists`, so the chosen family comes with
the perturbation witness needed downstream for the annular excess argument. -/
noncomputable def chosenDefectPhaseFamily (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) : DefectPhaseFamily :=
  Classical.choose (defect_phase_family_with_perturbation_exists sensor hm)

/-- The chosen phase family is attached to the requested sensor. -/
theorem chosenDefectPhaseFamily_sensor (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    (chosenDefectPhaseFamily sensor hm).sensor = sensor :=
  (Classical.choose_spec (defect_phase_family_with_perturbation_exists sensor hm)).1

/-- The chosen phase family also carries the regular-factor perturbation witness
needed to build the ring perturbation control package. -/
noncomputable def chosenDefectPhasePerturbationWitness (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    DefectPhasePerturbationWitness (chosenDefectPhaseFamily sensor hm) :=
  Classical.choice ((Classical.choose_spec
    (defect_phase_family_with_perturbation_exists sensor hm)).2)

/-- The canonical realized sampled family attached to a hypothetical defect. -/
noncomputable def canonicalDefectSampledFamily (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) : DefectSampledFamily :=
  (chosenDefectPhaseFamily sensor hm).toSampledFamily

/-- The canonical sampled family remembers the requested sensor. -/
theorem canonicalDefectSampledFamily_sensor (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    (canonicalDefectSampledFamily sensor hm).sensor = sensor :=
  chosenDefectPhaseFamily_sensor sensor hm

/-- Every mesh in the canonical sampled family has the requested sensor charge. -/
theorem canonicalDefectSampledFamily_charge (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) (N : ℕ) :
    ((canonicalDefectSampledFamily sensor hm).mesh N).charge = sensor.charge := by
  simpa [canonicalDefectSampledFamily_sensor sensor hm] using
    ((canonicalDefectSampledFamily sensor hm).charge_spec N)

/-! ### §3. Refined bounded-cost proposition -/

/-- The annular cost of a realized sampled family is bounded independently of
mesh refinement. This is the realizable replacement for the previous
over-strong quantification over arbitrary `AnnularMesh` values. -/
def RealizedDefectAnnularCostBounded (fam : DefectSampledFamily) : Prop :=
  ∃ K : ℝ, ∀ N : ℕ, annularCost (fam.mesh N) ≤ K

/-- The annular excess of a realized sampled family is bounded independently of
mesh refinement. This is the quantitatively plausible part of the defect-cost
story: after removing the topological floor, only the regular remainder should
need analytic control. -/
def RealizedDefectAnnularExcessBounded (fam : DefectSampledFamily) : Prop :=
  ∃ K : ℝ, ∀ N : ℕ, annularExcess (fam.mesh N) ≤ K

/-! ### §3a. Ring-level regular-part error control -/

/-- A ring-level regular-part error package for a realized sampled family.

For each depth `N` and ring `n`, the sampled ring cost is bounded by the
topological floor for its charge sector plus an error term coming from the
regular factor in the local meromorphic factorization. The total error across
all rings is uniformly bounded in `N`.

This is the exact quantitative input needed to prove bounded annular excess. -/
structure RingRegularErrorBound (fam : DefectSampledFamily) where
  error : ∀ N : ℕ, Fin N → ℝ
  ring_estimate : ∀ N : ℕ, ∀ n : Fin N,
    ringCost ((fam.mesh N).rings n) ≤
      topologicalFloor (n.val + 1) ((fam.mesh N).charge) + error N n
  total_error_bounded : ∃ K : ℝ, ∀ N : ℕ, ∑ n : Fin N, error N n ≤ K

/-- The explicit linear-plus-quadratic perturbation error on one realized ring.

This is the error term delivered by
`ringCost_le_topologicalFloor_add_linear_quadratic_error` once the ring
increments are written as the pure winding increment plus a regular
perturbation. -/
noncomputable def realizedRingPerturbationError (fam : DefectSampledFamily)
    (N : ℕ) (n : Fin N) : ℝ :=
  let u : ℝ := -(2 * Real.pi * ((fam.mesh N).charge : ℝ)) / (8 * (n.val + 1) : ℝ)
  phiCostLinearCoeff |u| *
      ∑ j : Fin (8 * (n.val + 1)),
        |((fam.mesh N).rings n).increments j - u| +
    phiCostQuadraticCoeff |u| *
      ∑ j : Fin (8 * (n.val + 1)),
        (((fam.mesh N).rings n).increments j - u) ^ 2

/-- Quantitative perturbation control for a realized sampled family.

The `small` field says each sampled increment stays within the unit-scale
perturbative regime of `phiCost` once expressed as

`Δ_j = (pure winding increment) + ε_j`.

The `total_bounded` field says the resulting linear-plus-quadratic error sums
are uniformly bounded across refinement depth `N`. This is exactly the remaining
analytic input needed after the perturbative `phiCost` reduction. -/
structure RingPerturbationControl (fam : DefectSampledFamily) where
  small : ∀ N : ℕ, ∀ n : Fin N, ∀ j : Fin (8 * (n.val + 1)),
    |Real.log Constants.phi *
        (((fam.mesh N).rings n).increments j -
          (-(2 * Real.pi * ((fam.mesh N).charge : ℝ)) / (8 * (n.val + 1) : ℝ)))| ≤ 1
  total_bounded : ∃ K : ℝ, ∀ N : ℕ,
    ∑ n : Fin N, realizedRingPerturbationError fam N n ≤ K

/-- A perturbation-control package yields the ring-regular-error package needed
for bounded annular excess. -/
noncomputable def ringRegularErrorBound_of_ringPerturbationControl
    (fam : DefectSampledFamily) (hctrl : RingPerturbationControl fam) :
    RingRegularErrorBound fam := by
  refine
    { error := realizedRingPerturbationError fam
      ring_estimate := ?_
      total_error_bounded := hctrl.total_bounded }
  intro N n
  have hcharge : ((fam.mesh N).rings n).winding = (fam.mesh N).charge := by
    rw [((fam.mesh N).uniform_charge n)]
  have hsmall_ring :
      ∀ j : Fin (8 * n.val.succ),
        |Real.log Constants.phi *
            (((fam.mesh N).rings n).increments j -
              (-(2 * Real.pi * ((((fam.mesh N).rings n).winding : ℤ) : ℝ)) /
                (8 * n.val.succ : ℝ)))| ≤ 1 := by
    intro j
    have hj := hctrl.small N n j
    simpa [hcharge, Nat.succ_eq_add_one] using hj
  have hring :=
    ringCost_le_topologicalFloor_add_linear_quadratic_error
      (Nat.succ_pos n.val) ((fam.mesh N).rings n) hsmall_ring
  rw [hcharge] at hring
  simpa [realizedRingPerturbationError, add_assoc] using hring

/-- Summing the ring-level estimate yields a bound for annular excess.

This is the unconditional algebraic step:

`ringCost ≤ topologicalFloor + regularError`

on each ring implies

`annularExcess ≤ ∑ regularError`

on the full annulus. -/
theorem annularExcess_le_sum_of_ringCost_le_topologicalFloor_plus_regularError
    (fam : DefectSampledFamily) (hreg : RingRegularErrorBound fam) (N : ℕ) :
    annularExcess (fam.mesh N) ≤ ∑ n : Fin N, hreg.error N n := by
  have hsum :
      annularCost (fam.mesh N) ≤
        annularTopologicalFloor N ((fam.mesh N).charge) + ∑ n : Fin N, hreg.error N n := by
    calc
      annularCost (fam.mesh N)
          = ∑ n : Fin N, ringCost ((fam.mesh N).rings n) := by
              rfl
      _ ≤ ∑ n : Fin N,
            (topologicalFloor (n.val + 1) ((fam.mesh N).charge) + hreg.error N n) := by
              apply Finset.sum_le_sum
              intro n _
              exact hreg.ring_estimate N n
      _ = (∑ n : Fin N, topologicalFloor (n.val + 1) ((fam.mesh N).charge)) +
            ∑ n : Fin N, hreg.error N n := by
              rw [Finset.sum_add_distrib]
      _ = annularTopologicalFloor N ((fam.mesh N).charge) + ∑ n : Fin N, hreg.error N n := by
              rfl
  unfold annularExcess
  linarith

/-- A uniform ring-level regular-part error bound implies bounded annular
excess for the realized family. -/
theorem realizedDefectAnnularExcessBounded_of_ringRegularErrorBound
    (fam : DefectSampledFamily) (hreg : RingRegularErrorBound fam) :
    RealizedDefectAnnularExcessBounded fam := by
  obtain ⟨K, hK⟩ := hreg.total_error_bounded
  refine ⟨K, ?_⟩
  intro N
  exact le_trans
    (annularExcess_le_sum_of_ringCost_le_topologicalFloor_plus_regularError fam hreg N)
    (hK N)

/-- A uniform total-cost bound immediately gives a uniform excess bound, since
the topological floor is nonnegative. -/
theorem realizedDefectAnnularExcessBounded_of_costBounded
    (fam : DefectSampledFamily)
    (hcost : RealizedDefectAnnularCostBounded fam) :
    RealizedDefectAnnularExcessBounded fam := by
  obtain ⟨K, hK⟩ := hcost
  refine ⟨K, ?_⟩
  intro N
  unfold annularExcess
  have hfloor : 0 ≤ annularTopologicalFloor N (fam.sensor.charge) :=
    annularTopologicalFloor_nonneg N fam.sensor.charge
  have hcostN : annularCost (fam.mesh N) ≤ K := hK N
  rw [fam.charge_spec N]
  linarith

/-- If the sensor charge is zero, then bounded excess is equivalent to bounded
total cost because the topological floor vanishes identically. -/
theorem realizedDefectCostBounded_of_charge_zero_and_excessBounded
    (fam : DefectSampledFamily)
    (hzero : fam.sensor.charge = 0)
    (hexcess : RealizedDefectAnnularExcessBounded fam) :
    RealizedDefectAnnularCostBounded fam := by
  obtain ⟨K, hK⟩ := hexcess
  refine ⟨K, ?_⟩
  intro N
  have hfloor : annularTopologicalFloor N (fam.sensor.charge) = 0 := by
    rw [hzero, annularTopologicalFloor_zero]
  have hexN : annularExcess (fam.mesh N) ≤ K := hK N
  unfold annularExcess at hexN
  rw [fam.charge_spec N, hfloor] at hexN
  simpa using hexN

/-- For a realized sampled family, bounded total cost is exactly the conjunction
of:
1. zero charge, and
2. bounded excess above the topological floor.

This theorem isolates the remaining mathematical task cleanly: after the
realized-family refactor, the analytically natural target is no longer a bound
on arbitrary meshes, but a proof that the realized family has bounded excess
and hence can only occur with zero charge. -/
theorem realizedDefectCostBounded_iff_charge_zero_and_excessBounded
    (fam : DefectSampledFamily) :
    RealizedDefectAnnularCostBounded fam ↔
      fam.sensor.charge = 0 ∧ RealizedDefectAnnularExcessBounded fam := by
  constructor
  · intro hcost
    have hzero : fam.sensor.charge = 0 := by
      by_cases hm : fam.sensor.charge = 0
      · exact hm
      · obtain ⟨K, hK⟩ := hcost
        obtain ⟨N, hN⟩ := defect_cost_unbounded fam.sensor hm K
        have hcharge : ∀ n, ((fam.mesh N).rings n).winding = fam.sensor.charge := by
          intro n
          rw [((fam.mesh N).uniform_charge n), fam.charge_spec N]
        exact False.elim (not_lt_of_ge (hK N) (hN (fam.mesh N) hcharge))
    exact ⟨hzero, realizedDefectAnnularExcessBounded_of_costBounded fam hcost⟩
  · rintro ⟨hzero, hexcess⟩
    exact realizedDefectCostBounded_of_charge_zero_and_excessBounded fam hzero hexcess

/-- **Quantitative target for the Axiom 2 attack.**

The canonical realized defect family should have bounded excess above the
topological floor. This is the theorem that the current complex-analysis stack
ought to prove from local factorization `ζ⁻¹ = (z-ρ)^{-m} g(z)` together with a
log-derivative bound on the regular factor `g`.

Once proved, `realizedDefectCostBounded_iff_charge_zero_and_excessBounded`
shows that Axiom 2 reduces exactly to forcing zero charge. -/
noncomputable def canonicalDefectSampledFamily_ringPerturbationControl
    (sensor : DefectSensor) (hm : sensor.charge ≠ 0) :
    RingPerturbationControl (canonicalDefectSampledFamily sensor hm) := by
  let dpf := chosenDefectPhaseFamily sensor hm
  let hw := chosenDefectPhasePerturbationWitness sensor hm
  refine { small := ?_, total_bounded := ?_ }
  · intro N n j
    have hsmall := regular_perturbation_small hw (n.val + 1) (Nat.succ_pos n.val) j
    have hinc :
        (((canonicalDefectSampledFamily sensor hm).mesh N).rings n).increments j =
          defectPhasePureIncrement dpf (n.val + 1) +
            hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j := by
      simpa [canonicalDefectSampledFamily, chosenDefectPhaseFamily, dpf,
        defectAnnularMesh, ContinuousPhaseData.toAnnularRingSample] using
        regular_factor_increment_decomposition hw (n.val + 1) (Nat.succ_pos n.val) j
    have hpure :
        defectPhasePureIncrement dpf (n.val + 1) =
          -(2 * Real.pi * (((canonicalDefectSampledFamily sensor hm).mesh N).charge : ℝ)) /
            (8 * (n.val + 1) : ℝ) := by
      simp [defectPhasePureIncrement, canonicalDefectSampledFamily_charge,
        chosenDefectPhaseFamily_sensor, dpf]
    rw [hinc, hpure]
    simpa using hsmall
  obtain ⟨K₁, hK₁⟩ := regular_perturbation_linear_term_bounded hw
  obtain ⟨K₂, hK₂⟩ := regular_perturbation_quadratic_term_bounded hw
  refine ⟨K₁ + K₂, ?_⟩
  intro N
  have hlin := hK₁ N
  have hquad := hK₂ N
  have hterm :
      ∀ n : Fin N,
        realizedRingPerturbationError (canonicalDefectSampledFamily sensor hm) N n =
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
          -(2 * Real.pi * (((canonicalDefectSampledFamily sensor hm).mesh N).charge : ℝ)) /
            (8 * (n.val + 1) : ℝ) := by
      simp [defectPhasePureIncrement, canonicalDefectSampledFamily_charge,
        chosenDefectPhaseFamily_sensor, dpf]
    rw [hpure]
    have hlinSum :
        ∑ j : Fin (8 * (n.val + 1)),
          |(((canonicalDefectSampledFamily sensor hm).mesh N).rings n).increments j -
            (-(2 * Real.pi * (((canonicalDefectSampledFamily sensor hm).mesh N).charge : ℝ)) /
              (8 * (n.val + 1) : ℝ))| =
        ∑ j : Fin (8 * (n.val + 1)),
          |hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j| := by
      apply Finset.sum_congr rfl
      intro j _
      have hinc :
          (((canonicalDefectSampledFamily sensor hm).mesh N).rings n).increments j =
            defectPhasePureIncrement dpf (n.val + 1) +
              hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j := by
        simpa [canonicalDefectSampledFamily, chosenDefectPhaseFamily, dpf,
          defectAnnularMesh, ContinuousPhaseData.toAnnularRingSample] using
          regular_factor_increment_decomposition hw (n.val + 1) (Nat.succ_pos n.val) j
      rw [hinc, hpure]
      ring_nf
    have hquadSum :
        ∑ j : Fin (8 * (n.val + 1)),
          ((((canonicalDefectSampledFamily sensor hm).mesh N).rings n).increments j -
            (-(2 * Real.pi * (((canonicalDefectSampledFamily sensor hm).mesh N).charge : ℝ)) /
              (8 * (n.val + 1) : ℝ))) ^ 2 =
        ∑ j : Fin (8 * (n.val + 1)),
          (hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      have hinc :
          (((canonicalDefectSampledFamily sensor hm).mesh N).rings n).increments j =
            defectPhasePureIncrement dpf (n.val + 1) +
              hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j := by
        simpa [canonicalDefectSampledFamily, chosenDefectPhaseFamily, dpf,
          defectAnnularMesh, ContinuousPhaseData.toAnnularRingSample] using
          regular_factor_increment_decomposition hw (n.val + 1) (Nat.succ_pos n.val) j
      rw [hinc, hpure]
      ring_nf
    rw [hlinSum, hquadSum]
  calc
    ∑ n : Fin N, realizedRingPerturbationError (canonicalDefectSampledFamily sensor hm) N n
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
          linarith

/-- The canonical perturbation-control package yields the regular-error package
needed for bounded annular excess. -/
noncomputable def canonicalDefectSampledFamily_ringRegularErrorBound (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    RingRegularErrorBound (canonicalDefectSampledFamily sensor hm) := by
  exact ringRegularErrorBound_of_ringPerturbationControl _
    (canonicalDefectSampledFamily_ringPerturbationControl sensor hm)

theorem canonicalDefectSampledFamily_excess_bounded (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    RealizedDefectAnnularExcessBounded
      (canonicalDefectSampledFamily sensor hm) := by
  exact realizedDefectAnnularExcessBounded_of_ringRegularErrorBound _
    (canonicalDefectSampledFamily_ringRegularErrorBound sensor hm)

/-- Nonzero charge forces the realized sampled family cost to exceed any bound.

This is just `defect_cost_unbounded` specialized to the meshes of one realized
family. The theorem is completely unconditional. -/
theorem defectSampledFamily_unbounded (fam : DefectSampledFamily)
    (hm : fam.sensor.charge ≠ 0) :
    ∀ B : ℝ, ∃ N : ℕ, B < annularCost (fam.mesh N) := by
  intro B
  obtain ⟨N, hN⟩ := defect_cost_unbounded fam.sensor hm B
  refine ⟨N, ?_⟩
  have hcharge : ∀ n, ((fam.mesh N).rings n).winding = fam.sensor.charge := by
    intro n
    rw [((fam.mesh N).uniform_charge n), fam.charge_spec N]
  exact hN (fam.mesh N) hcharge

/-- A realized sampled family with nonzero charge can never have bounded annular
cost. This is the contradiction theorem underlying the refined Axiom 2. -/
theorem not_realizedDefectAnnularCostBounded (fam : DefectSampledFamily)
    (hm : fam.sensor.charge ≠ 0) :
    ¬ RealizedDefectAnnularCostBounded fam := by
  intro hbound
  obtain ⟨K, hK⟩ := hbound
  obtain ⟨N, hN⟩ := defectSampledFamily_unbounded fam hm K
  exact not_lt_of_ge (hK N) hN

end

end NumberTheory
end IndisputableMonolith
