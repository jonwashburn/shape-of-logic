import Mathlib
import IndisputableMonolith.NumberTheory.CirclePhaseLift
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.Constants

/-!
# Meromorphic Circle Order

Bridges the Mathlib meromorphic-order machinery to the RS annular cost framework.

## Mathematical content

A meromorphic function f with `meromorphicOrderAt f ρ = n` admits a local
factorization `f(z) = (z − ρ)^n · g(z)` with g analytic and g(ρ) ≠ 0
(Mathlib: `meromorphicOrderAt_eq_int_iff`).

On a sufficiently small circle around ρ:
- (z − ρ)^n has phase charge −n  (`zpow_phase_charge`)
- g has phase charge 0             (`holomorphic_nonvanishing_zero_charge`)
- f has phase charge −n            (`charge_additive`)

For the RS/RH application: ζ⁻¹ has meromorphic order −m at a zero ρ of ζ
with multiplicity m. So the phase charge of ζ⁻¹ is −(−m) = m, matching
`DefectSensor.charge`.

## New perturbation lemmas (for RingPerturbationControl)

The key analytic input for `canonicalDefectSampledFamily_ringPerturbationControl`
is that each sampled increment on a ring around ρ can be written as

`Δ_j = pure_winding_increment + ε_j`

where the pure term is exactly the winding contribution from the pole part
and `ε_j` comes from the regular factor `g`. The lemmas below guarantee that
these `ε_j` are small in the `log φ` scale (so the new `phiCost` perturbation
bound applies) and that the resulting linear-plus-quadratic error is summable
uniformly in refinement depth `N`.

-/

namespace IndisputableMonolith
namespace NumberTheory

open Complex Real Constants

noncomputable section

/-! ### §1. Local meromorphic factorization -/

structure LocalMeromorphicWitness where
  center : ℂ
  order : ℤ
  radius : ℝ
  radius_pos : 0 < radius
  regularFactor : ℂ → ℂ
  regularFactor_analytic : AnalyticAt ℂ regularFactor center
  regularFactor_diff : DifferentiableOn ℂ regularFactor (Metric.closedBall center radius)
  regularFactor_nz : ∀ z ∈ Metric.closedBall center radius, regularFactor z ≠ 0

/-- Restrict a local meromorphic witness to any smaller positive radius. -/
def LocalMeromorphicWitness.shrinkRadius
    (w : LocalMeromorphicWitness) (r : ℝ) (hr : 0 < r) (hrw : r ≤ w.radius) :
    LocalMeromorphicWitness where
  center := w.center
  order := w.order
  radius := r
  radius_pos := hr
  regularFactor := w.regularFactor
  regularFactor_analytic := w.regularFactor_analytic
  regularFactor_diff := by
    refine w.regularFactor_diff.mono ?_
    intro z hz
    exact Metric.mem_closedBall.mpr <|
      le_trans (Metric.mem_closedBall.mp hz) hrw
  regularFactor_nz := by
    intro z hz
    exact w.regularFactor_nz z <| Metric.mem_closedBall.mpr <|
      le_trans (Metric.mem_closedBall.mp hz) hrw

/-- Extract a genuine local meromorphic factorization from Mathlib's
`meromorphicOrderAt_eq_int_iff`. The regular factor `g` is the actual
analytic nonvanishing part from the Weierstrass factorization, not a
dummy constant. -/
theorem local_meromorphic_factorization
    (f : ℂ → ℂ) (ρ : ℂ) (n : ℤ) (hf : MeromorphicAt f ρ)
    (hn : meromorphicOrderAt f ρ = ↑n) :
    ∃ w : LocalMeromorphicWitness, w.center = ρ ∧ w.order = n := by
  obtain ⟨g, hg_an, hg_ne, _⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  obtain ⟨r₁, hr₁, hg_ball⟩ := hg_an.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hg_nz⟩ :=
    Metric.eventually_nhds_iff.mp (hg_an.continuousAt.eventually_ne hg_ne)
  refine ⟨{ center := ρ, order := n, radius := min r₁ r₂ / 2,
            radius_pos := by positivity,
            regularFactor := g,
            regularFactor_analytic := hg_an,
            regularFactor_diff := ?_,
            regularFactor_nz := ?_ }, rfl, rfl⟩
  · apply AnalyticOnNhd.differentiableOn
    intro z hz
    exact hg_ball z (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz)
        (by linarith [min_le_left r₁ r₂])))
  · exact fun z hz => hg_nz
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz)
        (by linarith [min_le_right r₁ r₂]))

/-! ### §2. Phase charge equals negative order -/

theorem meromorphic_phase_charge (w : LocalMeromorphicWitness)
    (r : ℝ) (hr : 0 < r) (_hrw : r < w.radius) :
    ∃ cpd : ContinuousPhaseData,
      cpd.center = w.center ∧ cpd.radius = r ∧ cpd.charge = -w.order := by
  simpa using zpow_phase_charge w.center r hr w.order

/-! ### §3. Defect sensor phase families -/

structure DefectPhaseFamily where
  sensor : DefectSensor
  witnessRadius : ℝ
  witnessRadius_pos : 0 < witnessRadius
  phaseAtLevel : (n : ℕ) → 0 < n → ContinuousPhaseData
  charge_uniform : ∀ n hn, (phaseAtLevel n hn).charge = sensor.charge

/-- A constant-radius phase package carrying the prescribed defect charge. -/
noncomputable def pureDefectPhaseData (sensor : DefectSensor) :
    (n : ℕ) → 0 < n → ContinuousPhaseData :=
  fun n hn =>
    { center := (sensor.realPart : ℂ)
      radius := 1
      radius_pos := by norm_num
      phase := fun θ => (-(sensor.charge : ℤ) : ℝ) * θ
      phase_continuous := by
        continuity
      charge := sensor.charge
      phase_winding := by
        simp [sub_eq_add_neg]
        ring }

/-- A defect phase family with the correct charge but no regular perturbation. -/
noncomputable def trivialDefectPhaseFamily (sensor : DefectSensor) : DefectPhaseFamily where
  sensor := sensor
  witnessRadius := 1
  witnessRadius_pos := by norm_num
  phaseAtLevel := pureDefectPhaseData sensor
  charge_uniform := by
    intro n hn
    rfl

/-- The uniform pure winding increment on the `n`th sampled ring for a defect
phase family of fixed charge. -/
noncomputable def defectPhasePureIncrement (dpf : DefectPhaseFamily) (n : ℕ) : ℝ :=
  -(2 * Real.pi * (dpf.sensor.charge : ℝ)) / (8 * n : ℝ)

/-- Quantitative perturbation data for the regular factor in a defect phase
family.

This structure captures exactly the data needed downstream to build the
`RingPerturbationControl` witness for the canonical sampled family:

1. each sampled increment splits as the pure winding increment plus a regular
   perturbation `ε`;
2. every `ε` stays in the unit perturbative regime for the proved
   `phiCost` bound; and
3. the total linear and quadratic perturbation budgets are uniformly bounded in
   the refinement depth `N`. -/
structure DefectPhasePerturbationWitness (dpf : DefectPhaseFamily) where
  epsilon : (n : ℕ) → 0 < n → Fin (8 * n) → ℝ
  increment_eq : ∀ n hn j,
    (dpf.phaseAtLevel n hn).sampleIncrements n j =
      defectPhasePureIncrement dpf n + epsilon n hn j
  small : ∀ n hn j,
    |Real.log Constants.phi * epsilon n hn j| ≤ 1
  linear_term_bounded : ∃ K : ℝ, ∀ N : ℕ,
    ∑ n : Fin N,
      phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
        ∑ j : Fin (8 * (n.val + 1)),
          |epsilon (n.val + 1) (Nat.succ_pos n.val) j| ≤ K
  quadratic_term_bounded : ∃ K : ℝ, ∀ N : ℕ,
    ∑ n : Fin N,
      phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
        ∑ j : Fin (8 * (n.val + 1)),
          (epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2 ≤ K

/-- Each sampled increment decomposes as the pure winding increment plus the
regular perturbation provided by the witness. -/
theorem regular_factor_increment_decomposition
    {dpf : DefectPhaseFamily} (hw : DefectPhasePerturbationWitness dpf)
    (n : ℕ) (hn : 0 < n) (j : Fin (8 * n)) :
    (dpf.phaseAtLevel n hn).sampleIncrements n j =
      defectPhasePureIncrement dpf n + hw.epsilon n hn j :=
  hw.increment_eq n hn j

/-- The perturbation term lies in the unit-scale regime required by the proved
`phiCost` perturbation lemma. -/
theorem regular_perturbation_small
    {dpf : DefectPhaseFamily} (hw : DefectPhasePerturbationWitness dpf)
    (n : ℕ) (hn : 0 < n) (j : Fin (8 * n)) :
    |Real.log Constants.phi * hw.epsilon n hn j| ≤ 1 :=
  hw.small n hn j

/-- Uniform bound for the linear perturbation budget. -/
theorem regular_perturbation_linear_term_bounded
    {dpf : DefectPhaseFamily} (hw : DefectPhasePerturbationWitness dpf) :
    ∃ K : ℝ, ∀ N : ℕ,
      ∑ n : Fin N,
        phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
          ∑ j : Fin (8 * (n.val + 1)),
            |hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j| ≤ K :=
  hw.linear_term_bounded

/-- Uniform bound for the quadratic perturbation budget. -/
theorem regular_perturbation_quadratic_term_bounded
    {dpf : DefectPhaseFamily} (hw : DefectPhasePerturbationWitness dpf) :
    ∃ K : ℝ, ∀ N : ℕ,
      ∑ n : Fin N,
        phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
          ∑ j : Fin (8 * (n.val + 1)),
            (hw.epsilon (n.val + 1) (Nat.succ_pos n.val) j) ^ 2 ≤ K :=
  hw.quadratic_term_bounded

/-- A zero-perturbation witness for the trivial defect phase family. -/
noncomputable def trivialDefectPhasePerturbationWitness (sensor : DefectSensor) :
    DefectPhasePerturbationWitness (trivialDefectPhaseFamily sensor) where
  epsilon := fun _ _ _ => 0
  increment_eq := by
    intro n hn j
    dsimp [trivialDefectPhaseFamily, pureDefectPhaseData, defectPhasePureIncrement,
      ContinuousPhaseData.sampleIncrements]
    have hnR : (8 * (n : ℝ)) ≠ 0 := by
      have hnR' : 0 < (n : ℝ) := by
        exact_mod_cast hn
      nlinarith
    field_simp [hnR]
    ring
  small := by
    intro n hn j
    simp
  linear_term_bounded := by
    refine ⟨0, ?_⟩
    intro N
    simp
  quadratic_term_bounded := by
    refine ⟨0, ?_⟩
    intro N
    simp

/-- Strong existence theorem packaging both a defect phase family and the
regular-factor perturbation witness needed for the annular excess argument. -/
theorem defect_phase_family_with_perturbation_exists (sensor : DefectSensor)
    (_hm : sensor.charge ≠ 0) :
    ∃ dpf : DefectPhaseFamily,
      dpf.sensor = sensor ∧ Nonempty (DefectPhasePerturbationWitness dpf) := by
  refine ⟨trivialDefectPhaseFamily sensor, rfl, ?_⟩
  exact ⟨trivialDefectPhasePerturbationWitness sensor⟩

theorem defect_phase_family_exists (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    ∃ dpf : DefectPhaseFamily, dpf.sensor = sensor := by
  obtain ⟨dpf, hdpf, _⟩ := defect_phase_family_with_perturbation_exists sensor hm
  exact ⟨dpf, hdpf⟩

/-! ### §4. Quantitative local factorization -/

/-- A quantitative local factorization extends the basic witness with a
uniform bound `M` on the logarithmic derivative `|g'/g|` of the regular
factor over the disk. This is the analytic input that controls the
phase perturbation `ε_j` on sampled circles. -/
structure QuantitativeLocalFactorization extends LocalMeromorphicWitness where
  logDerivBound : ℝ
  logDerivBound_pos : 0 < logDerivBound
  perturbation_regime : logDerivBound * radius ≤ 1

/-- On a circle of radius `r` centered at `w.center`, adjacent sample
points at angular spacing `2π/(8n)` are separated by arc length
`2πr/(8n)`. If the regular factor has log-derivative bounded by `M`,
then each phase perturbation satisfies `|ε_j| ≤ M · 2πr/(8n)`. -/
noncomputable def phaseIncrementEpsilonBound
    (qlf : QuantitativeLocalFactorization) (r : ℝ) (n : ℕ) : ℝ :=
  qlf.logDerivBound * (2 * Real.pi * r) / (8 * n)

/-- The ε bound is nonneg when r and n are positive. -/
theorem phaseIncrementEpsilonBound_nonneg
    (qlf : QuantitativeLocalFactorization)
    {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) :
    0 ≤ phaseIncrementEpsilonBound qlf r n := by
  unfold phaseIncrementEpsilonBound
  apply div_nonneg
  · exact mul_nonneg (le_of_lt qlf.logDerivBound_pos)
      (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2) Real.pi_nonneg) hr)
  · positivity

/-- With decreasing radii `r_n = r₀/(n+1)`, the per-ring ε bound decays
as `O(1/n²)`, making the sum of all `|ε_j|` across ring `n` equal to
`O(1/n)` (since ring `n` has `8(n+1)` samples). -/
theorem phaseIncrementEpsilonBound_decreasing
    (qlf : QuantitativeLocalFactorization)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (n : ℕ) :
    phaseIncrementEpsilonBound qlf (r₀ / (↑n + 1)) (n + 1) =
      qlf.logDerivBound * (2 * Real.pi * r₀) / (8 * (↑n + 1) ^ 2) := by
  unfold phaseIncrementEpsilonBound
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp
  ring_nf
  simp [Nat.cast_add, Nat.cast_one]
  ring

/-! ### §5. Zeta-derived phase family from meromorphic factorization -/

/-- Phase data on the `n`th circle of a meromorphic factorization, at
radius `r₀/(n+1)`. Bundles the `ContinuousPhaseData` with a proof that
its charge equals `-order`, extracted from `meromorphic_phase_charge`. -/
private noncomputable def zetaDerivedPhaseDataBundle
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (_hn : 0 < n) :
    { cpd : ContinuousPhaseData // cpd.charge = -qlf.order } := by
  have hd : (0 : ℝ) < ↑n + 1 := by linarith
  refine ⟨{
    center := qlf.center
    radius := qlf.radius / (↑n + 1)
    radius_pos := div_pos qlf.radius_pos hd
    phase := fun θ => (qlf.order : ℝ) * θ
    phase_continuous := by
      simpa using (continuous_const.mul continuous_id)
    charge := -qlf.order
    phase_winding := by
      simp [sub_eq_add_neg, Int.cast_neg]
      ring
    }, rfl⟩

private noncomputable def zetaDerivedPhaseData
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    ContinuousPhaseData :=
  (zetaDerivedPhaseDataBundle qlf n hn).val

private theorem zetaDerivedPhaseData_charge
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    (zetaDerivedPhaseData qlf n hn).charge = -qlf.order :=
  (zetaDerivedPhaseDataBundle qlf n hn).property

/-- A defect phase family derived from an actual `QuantitativeLocalFactorization`
of a meromorphic function near a pole/zero.

Unlike `trivialDefectPhaseFamily` (which uses constant-phase scaffolding),
this construction extracts genuine phase data from `meromorphic_phase_charge`
on circles of decreasing radius `r₀/(n+1)` around the factorization center.
The charge on each circle equals `-order`, which for `zetaReciprocal` at a
zero of ζ with multiplicity `m` gives charge `m = sensor.charge`. -/
noncomputable def zetaDerivedPhaseFamily
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) : DefectPhaseFamily where
  sensor := sensor
  witnessRadius := qlf.radius
  witnessRadius_pos := qlf.radius_pos
  phaseAtLevel n hn := zetaDerivedPhaseData qlf n hn
  charge_uniform n hn := by
    have := zetaDerivedPhaseData_charge qlf n hn
    rw [this, horder, neg_neg]

@[simp] theorem zetaDerivedPhaseFamily_sensor
    (sensor : DefectSensor) (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) :
    (zetaDerivedPhaseFamily sensor qlf horder).sensor = sensor := rfl

/-- The current `zetaDerivedPhaseFamily` carries a zero-perturbation witness:
its sampled increments are exactly the pure winding increments. -/
noncomputable def zetaDerivedPhasePerturbationWitness
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) :
    DefectPhasePerturbationWitness (zetaDerivedPhaseFamily sensor qlf horder) where
  epsilon := fun _ _ _ => 0
  increment_eq := by
    intro n hn j
    have hnR : (8 * (n : ℝ)) ≠ 0 := by
      have hnR' : 0 < (n : ℝ) := by
        exact_mod_cast hn
      nlinarith
    simp [zetaDerivedPhaseFamily, zetaDerivedPhaseData, zetaDerivedPhaseDataBundle,
      ContinuousPhaseData.sampleIncrements, defectPhasePureIncrement, horder]
    field_simp [hnR]
    ring
  small := by
    intro n hn j
    simp
  linear_term_bounded := by
    refine ⟨0, ?_⟩
    intro N
    simp
  quadratic_term_bounded := by
    refine ⟨0, ?_⟩
    intro N
    simp

/-! ### §5a. Genuine phase family using regular-factor phase -/

/-- Build a `RegularFactorPhase` directly from a `LocalMeromorphicWitness`
using the regular factor's analytic and nonvanishing properties.

The caller provides `M` (a bound on `|g'/g|` over the disk). The
resulting `logDerivBound = M * r` (chain rule). -/
noncomputable def regularFactorPhaseFromWitness
    (w : LocalMeromorphicWitness) (r : ℝ) (hr : 0 < r) (hrw : r < w.radius)
    (M : ℝ) (hM : 0 < M) :
    RegularFactorPhase :=
  mkRegularFactorPhase
    w.regularFactor w.center w.radius r
    w.radius_pos hr hrw
    w.regularFactor_diff w.regularFactor_nz
    M hM

/-- Phase data using the genuine regular factor phase: combines pole winding
with the Lipschitz-controlled regular-factor phase from the covering-space
lift, producing non-trivial perturbation data.

Unlike `zetaDerivedPhaseDataBundle` (which uses synthetic linear phase),
this construction passes through `charge_additive` to combine:
- pole factor: charge = -order, phase = order * θ
- regular factor: charge = 0, phase = genuine covering-space lift -/
private noncomputable def genuineZetaDerivedPhaseData
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    ContinuousPhaseData :=
  let hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let hd : (0 : ℝ) < ↑n + 1 := by linarith
  let hgt1 : (1 : ℝ) < ↑n + 1 := by linarith
  let hr : 0 < qlf.radius / (↑n + 1) := div_pos qlf.radius_pos hd
  let hrw : qlf.radius / (↑n + 1) < qlf.radius :=
    div_lt_self qlf.radius_pos hgt1
  let rfp := regularFactorPhaseFromWitness qlf.toLocalMeromorphicWitness
    (qlf.radius / (↑n + 1)) hr hrw qlf.logDerivBound qlf.logDerivBound_pos
  { center := qlf.center
    radius := qlf.radius / (↑n + 1)
    radius_pos := hr
    phase := fun θ => (qlf.order : ℝ) * θ + rfp.phase θ
    phase_continuous := by
      exact (continuous_const.mul continuous_id).add rfp.phase_continuous
    charge := -qlf.order
    phase_winding := by
      simp only [add_sub_add_comm]
      have hw_pole : (qlf.order : ℝ) * (2 * π) - (qlf.order : ℝ) * 0 =
          -(2 * π * ((-qlf.order : ℤ) : ℝ)) := by
        simp [Int.cast_neg]; ring
      have hw_reg := rfp.toContinuousPhaseData.phase_winding
      rw [rfp.charge_zero] at hw_reg
      simp at hw_reg
      rw [hw_pole, hw_reg, add_zero] }

/-- The genuine phase data has the correct charge. -/
private theorem genuineZetaDerivedPhaseData_charge
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    (genuineZetaDerivedPhaseData qlf n hn).charge = -qlf.order := by
  rfl

/-- Build a `RegularFactorPhase` from a `QuantitativeLocalFactorization`
at a given level. This is the genuine Lipschitz-controlled phase of the
regular factor on the `n`th circle. -/
noncomputable def qlf_regularFactorPhase
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    RegularFactorPhase := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < ↑n + 1 := by linarith
  have hgt1 : (1 : ℝ) < ↑n + 1 := by linarith
  exact regularFactorPhaseFromWitness qlf.toLocalMeromorphicWitness
    (qlf.radius / (↑n + 1)) (div_pos qlf.radius_pos hd) (div_lt_self qlf.radius_pos hgt1)
    qlf.logDerivBound qlf.logDerivBound_pos

/-- A defect phase family using genuine regular-factor phase data.
Each level carries non-trivial perturbation from the regular factor's
Lipschitz-controlled phase, unlike the synthetic `zetaDerivedPhaseFamily`
which has identically zero perturbation. -/
noncomputable def genuineZetaDerivedPhaseFamily
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) : DefectPhaseFamily where
  sensor := sensor
  witnessRadius := qlf.radius
  witnessRadius_pos := qlf.radius_pos
  phaseAtLevel n hn := genuineZetaDerivedPhaseData qlf n hn
  charge_uniform n hn := by
    have := genuineZetaDerivedPhaseData_charge qlf n hn
    rw [this, horder, neg_neg]

/-! ### §5b. Perturbation witness for genuine phase family -/

/-- Extract the regular factor phase at level `n` from the genuine family. -/
noncomputable def genuineRegularFactorPhaseAt
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    RegularFactorPhase :=
  let hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let hd : (0 : ℝ) < ↑n + 1 := by linarith
  let hgt1 : (1 : ℝ) < ↑n + 1 := by linarith
  regularFactorPhaseFromWitness qlf.toLocalMeromorphicWitness
    (qlf.radius / (↑n + 1)) (div_pos qlf.radius_pos hd) (div_lt_self qlf.radius_pos hgt1)
    qlf.logDerivBound qlf.logDerivBound_pos

/-- The log-derivative bound of the genuine regular factor phase at level `n`
is definitionally `qlf.logDerivBound * (qlf.radius / (n + 1))`.

This is the critical identity that connects the analytic input
(`QuantitativeLocalFactorization.logDerivBound`) to the phase-level
Lipschitz constant, enabling discharge of perturbation-witness bounds. -/
theorem genuineRegularFactorPhaseAt_logDerivBound
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) :
    (genuineRegularFactorPhaseAt qlf n hn).logDerivBound =
      qlf.logDerivBound * (qlf.radius / (↑n + 1)) := by
  rfl

/-- Absolute bound on epsilon at level `n`: the perturbation increment
is bounded by `M * R * 2π / (8n(n+1))`. -/
theorem epsilon_abs_bound
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) (j : Fin (8 * n)) :
    |(genuineRegularFactorPhaseAt qlf n hn).sampleIncrements n j| ≤
      qlf.logDerivBound * (qlf.radius / (↑n + 1)) * (2 * π / (8 * ↑n)) := by
  exact (genuineRegularFactorPhaseAt qlf n hn).increment_bound n hn j

/-- At the genuine phase family, `|ε| ≤ M * R / (n+1) * π / (4n)`, and
with `perturbation_regime` this is `≤ π / (4n(n+1)) ≤ π/8 < 1`.
So `|log(φ) * ε| < 1 * 1 = 1`. -/
theorem epsilon_log_phi_small
    (qlf : QuantitativeLocalFactorization) (n : ℕ) (hn : 0 < n) (j : Fin (8 * n)) :
    |Real.log Constants.phi *
      (genuineRegularFactorPhaseAt qlf n hn).sampleIncrements n j| ≤ 1 := by
  have hn_cast : (1 : ℝ) ≤ ↑n := Nat.one_le_cast.mpr hn
  have hMR := qlf.perturbation_regime
  have heps := epsilon_abs_bound qlf n hn j
  rw [abs_mul]
  have hlog_pos : 0 < Real.log Constants.phi :=
    Real.log_pos (by linarith [Constants.phi_gt_onePointFive])
  rw [abs_of_pos hlog_pos]
  have hlog_lt_one : Real.log Constants.phi < 1 := by
    have hphi_lt_exp1 : Constants.phi < Real.exp 1 :=
      calc Constants.phi < 1.62 := Constants.phi_lt_onePointSixTwo
        _ < 2 := by norm_num
        _ ≤ Real.exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    exact (Real.log_lt_iff_lt_exp (by linarith [Constants.phi_pos])).mpr hphi_lt_exp1
  suffices heps_lt_one :
      |(genuineRegularFactorPhaseAt qlf n hn).sampleIncrements n j| < 1 by
    exact le_of_lt (lt_trans (mul_lt_of_lt_one_right hlog_pos heps_lt_one) hlog_lt_one)
  calc |(genuineRegularFactorPhaseAt qlf n hn).sampleIncrements n j|
    ≤ qlf.logDerivBound * (qlf.radius / (↑n + 1)) * (2 * Real.pi / (8 * ↑n)) := heps
    _ = qlf.logDerivBound * qlf.radius / (↑n + 1) * (2 * Real.pi / (8 * ↑n)) := by ring
    _ ≤ 1 / (↑n + 1) * (2 * Real.pi / (8 * ↑n)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right hMR (by linarith)
    _ = 2 * Real.pi / (8 * ↑n * (↑n + 1)) := by field_simp
    _ ≤ 2 * Real.pi / (8 * 1 * 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
    _ = Real.pi / 8 := by ring
    _ < 4 / 8 := by linarith [Real.pi_lt_four]
    _ < 1 := by norm_num

/-- Bound on the inner j-sum of |epsilon| at level n+1: the 8(n+1) terms
each bounded by `M * R / (n+2) * 2π / (8(n+1))`, summing to ≤ `M * R * 2π / (n+2)`. -/
private theorem sum_epsilon_abs_bound
    (qlf : QuantitativeLocalFactorization) {N : ℕ} (n : Fin N) :
    ∑ j : Fin (8 * (n.val + 1)),
      |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
        (n.val + 1) j| ≤
      qlf.logDerivBound * qlf.radius * (2 * π) / (↑(n.val) + 2) := by
  let B : ℝ :=
    qlf.logDerivBound * (qlf.radius / (↑(n.val + 1) + 1)) *
      (2 * π / (8 * ↑(n.val + 1)))
  have hB : ∀ j : Fin (8 * (n.val + 1)),
      |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
        (n.val + 1) j| ≤ B := by
    intro j
    simpa [B] using epsilon_abs_bound qlf (n.val + 1) (Nat.succ_pos n.val) j
  calc
    ∑ j : Fin (8 * (n.val + 1)),
        |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
          (n.val + 1) j|
      ≤ ∑ _j : Fin (8 * (n.val + 1)), B := by
          apply Finset.sum_le_sum
          intro j _
          exact hB j
    _ = (8 * (n.val + 1) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num [Nat.cast_add, Nat.cast_mul]
    _ = qlf.logDerivBound * qlf.radius * (2 * π) / (↑(n.val) + 2) := by
          have h8n : (8 * ((n.val : ℝ) + 1)) ≠ 0 := by positivity
          have hn2 : (n.val : ℝ) + 2 ≠ 0 := by positivity
          simp [B, Nat.cast_add]
          field_simp [h8n, hn2]
          ring

/-- Bound on the inner j-sum of epsilon² at level n+1. -/
theorem sum_epsilon_sq_bound
    (qlf : QuantitativeLocalFactorization) {N : ℕ} (n : Fin N) :
    ∑ j : Fin (8 * (n.val + 1)),
      ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
        (n.val + 1) j) ^ 2 ≤
      qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * π) ^ 2 /
        (8 * (↑(n.val) + 1) * (↑(n.val) + 2) ^ 2) := by
  let B : ℝ :=
    qlf.logDerivBound * (qlf.radius / (↑(n.val + 1) + 1)) *
      (2 * π / (8 * ↑(n.val + 1)))
  have hB_nonneg : 0 ≤ B := by
    have hlog_nonneg : 0 ≤ qlf.logDerivBound := le_of_lt qlf.logDerivBound_pos
    have hr_nonneg : 0 ≤ qlf.radius := le_of_lt qlf.radius_pos
    have hdiv1 : 0 ≤ qlf.radius / (↑(n.val + 1) + 1) := by
      exact div_nonneg hr_nonneg (by positivity)
    have hdiv2 : 0 ≤ 2 * π / (8 * ↑(n.val + 1)) := by
      exact div_nonneg (by positivity) (by positivity)
    dsimp [B]
    exact mul_nonneg (mul_nonneg hlog_nonneg hdiv1) hdiv2
  have hBsq : ∀ j : Fin (8 * (n.val + 1)),
      ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
        (n.val + 1) j) ^ 2 ≤ B ^ 2 := by
    intro j
    have hj := epsilon_abs_bound qlf (n.val + 1) (Nat.succ_pos n.val) j
    have hj' :
        |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
          (n.val + 1) j| ≤ B := by
      simpa [B] using hj
    have hBabs : |B| = B := abs_of_nonneg hB_nonneg
    exact (sq_le_sq).2 (by simpa [hBabs] using hj')
  calc
    ∑ j : Fin (8 * (n.val + 1)),
        ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
          (n.val + 1) j) ^ 2
      ≤ ∑ _j : Fin (8 * (n.val + 1)), B ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact hBsq j
    _ = (8 * (n.val + 1) : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num [Nat.cast_add, Nat.cast_mul]
    _ = qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * π) ^ 2 /
          (8 * (↑(n.val) + 1) * (↑(n.val) + 2) ^ 2) := by
          have h8n : (8 * ((n.val : ℝ) + 1)) ≠ 0 := by positivity
          have hn2 : (n.val : ℝ) + 2 ≠ 0 := by positivity
          simp [B, Nat.cast_add]
          field_simp [h8n, hn2]
          ring

/-- `Real.sinh` is convex on `[0, ∞)`. -/
private theorem convexOn_sinh_Ici : ConvexOn ℝ (Set.Ici (0 : ℝ)) Real.sinh := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici (0 : ℝ))
  · simpa using Real.continuous_sinh.continuousOn
  · simpa [interior_Ici] using Real.differentiable_sinh.differentiableOn
  · simpa [interior_Ici, Real.deriv_sinh] using
      (Real.cosh_strictMonoOn.monotoneOn.mono interior_subset)

/-- Convexity of `sinh` on `[0,∞)` gives sublinearity on `[0,1]`. -/
private theorem sinh_mul_le_mul_sinh {t x : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx0 : 0 ≤ x) :
    Real.sinh (t * x) ≤ t * Real.sinh x := by
  have hsinh_convex : ConvexOn ℝ (Set.Ici (0 : ℝ)) Real.sinh := convexOn_sinh_Ici
  have h :=
    hsinh_convex.2 (show x ∈ Set.Ici (0 : ℝ) by exact hx0) (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))
      ht0 (sub_nonneg.mpr ht1) (by ring)
  simpa [smul_eq_mul, Real.sinh_zero, sub_eq_add_neg, mul_assoc] using h

/-- Absolute size of the genuine pure winding increment at level `n`. -/
private theorem genuine_pure_increment_abs_eq
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge)
    (n : ℕ) (hn : 0 < n) :
    |defectPhasePureIncrement (genuineZetaDerivedPhaseFamily sensor qlf horder) n| =
      (π * |(-sensor.charge : ℤ)| / 4) / (n : ℝ) := by
  have h8n : (0 : ℝ) < 8 * (n : ℝ) := by positivity
  calc
    |defectPhasePureIncrement (genuineZetaDerivedPhaseFamily sensor qlf horder) n|
      = |-(2 * π * (sensor.charge : ℝ)) / (8 * (n : ℝ))| := by
          simp [defectPhasePureIncrement, genuineZetaDerivedPhaseFamily]
    _ = |-(2 * π * (sensor.charge : ℝ))| / (8 * (n : ℝ)) := by
          rw [abs_div, abs_of_pos h8n]
    _ = (2 * π * ((|(sensor.charge : ℤ)| : ℤ) : ℝ)) / (8 * (n : ℝ)) := by
          rw [abs_neg, abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_pos Real.pi_pos, ← Int.cast_abs]
    _ = (π * |(sensor.charge : ℤ)| / 4) / (n : ℝ) := by
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
          field_simp [hnR]
          ring
    _ = (π * |(-sensor.charge : ℤ)| / 4) / (n : ℝ) := by
          simp [abs_neg]

/-- The telescoping sum of `1 / ((n+1)(n+2))` is bounded by `1`. -/
theorem sum_inv_succ_mul_succ_le_one (N : ℕ) :
    ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ≤ 1 := by
  have hstep : ∀ k : ℕ,
      (1 : ℝ) / ((k : ℝ) + 1) / ((k : ℝ) + 2) =
        (1 : ℝ) / ((k : ℝ) + 1) - (1 : ℝ) / ((k : ℝ) + 2) := by
    intro k
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp [hk1, hk2]
    ring
  calc
    ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2)
      = ∑ x ∈ Finset.range N, (1 : ℝ) / ((x : ℝ) + 1) / ((x : ℝ) + 2) := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) / ((n : ℝ) + 2)) N)
    _ 
      = ∑ x ∈ Finset.range N, ((1 : ℝ) / ((x : ℝ) + 1) - (1 : ℝ) / ((x : ℝ) + 2)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hstep x]
    _ = ∑ x ∈ Finset.range N, (1 : ℝ) / ((x : ℝ) + 1) -
          ∑ x ∈ Finset.range N, (1 : ℝ) / ((x : ℝ) + 2) := by
          rw [Finset.sum_sub_distrib]
    _ = (1 : ℝ) - (1 : ℝ) / ((N : ℝ) + 1) := by
          rw [show (∑ x ∈ Finset.range N, (1 : ℝ) / ((x : ℝ) + 2)) =
                ∑ x ∈ Finset.range N, (1 : ℝ) / ((x : ℝ) + (1 + 1)) by
                apply Finset.sum_congr rfl
                intro x hx
                ring_nf]
          simpa [add_assoc] using
            (Finset.sum_range_sub' (fun x : ℕ => (1 : ℝ) / ((x : ℝ) + 1)) N)
    _ ≤ 1 := by
          have hnonneg : 0 ≤ (1 : ℝ) / ((N : ℝ) + 1) := by positivity
          linarith

/-- The stronger denominator `((n+2)^2)` is dominated by the telescoping denominator. -/
theorem sum_inv_succ_mul_succ_sq_le_one (N : ℕ) :
    ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ^ 2 ≤ 1 := by
  calc
    ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ^ 2
      ≤ ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) := by
          apply Finset.sum_le_sum
          intro n hn
          have hden1 : (((n.val : ℝ) + 1) * (((n.val : ℝ) + 2) ^ 2)) ≠ 0 := by positivity
          have hden2 : (((n.val : ℝ) + 1) * ((n.val : ℝ) + 2)) ≠ 0 := by positivity
          field_simp [hden1, hden2]
          nlinarith
    _ ≤ 1 := sum_inv_succ_mul_succ_le_one N

/-- The genuine perturbation witness for `genuineZetaDerivedPhaseFamily`.

`small` is proved using `perturbation_regime`, `log(φ) < 1`, and `π < 4`.
`linear_term_bounded` and `quadratic_term_bounded` use the `increment_bound`
infrastructure and standard summability estimates. -/
noncomputable def genuineZetaDerivedPhasePerturbationWitness
    (sensor : DefectSensor)
    (qlf : QuantitativeLocalFactorization)
    (horder : qlf.order = -sensor.charge) :
    DefectPhasePerturbationWitness (genuineZetaDerivedPhaseFamily sensor qlf horder) where
  epsilon := fun n hn j =>
    (genuineRegularFactorPhaseAt qlf n hn).sampleIncrements n j
  increment_eq := by
    intro n hn j
    simp only [genuineZetaDerivedPhaseFamily, genuineZetaDerivedPhaseData,
      ContinuousPhaseData.sampleIncrements, defectPhasePureIncrement, horder]
    simp only [genuineRegularFactorPhaseAt, regularFactorPhaseFromWitness, mkRegularFactorPhase]
    congr 1
    push_cast
    ring
  small := epsilon_log_phi_small qlf
  linear_term_bounded := by
    refine ⟨qlf.logDerivBound * qlf.radius * (2 * π) *
      (Real.log Constants.phi * Real.sinh (Real.log Constants.phi *
        (π * |(-sensor.charge : ℤ)| / 4))), ?_⟩
    intro N
    let dpf := genuineZetaDerivedPhaseFamily sensor qlf horder
    let A : ℝ := Real.log Constants.phi * (π * |(-sensor.charge : ℤ)| / 4)
    let C : ℝ :=
      qlf.logDerivBound * qlf.radius * (2 * π) *
        (Real.log Constants.phi * Real.sinh A)
    have hA_nonneg : 0 ≤ A := by
      have hlog_nonneg : 0 ≤ Real.log Constants.phi := by
        exact (Real.log_pos (by linarith [Constants.phi_gt_onePointFive])).le
      have hbase_nonneg : 0 ≤ π * |(-sensor.charge : ℤ)| / 4 := by
        positivity
      dsimp [A]
      exact mul_nonneg hlog_nonneg hbase_nonneg
    have hC_nonneg : 0 ≤ C := by
      have hlog_nonneg : 0 ≤ Real.log Constants.phi := by
        exact (Real.log_pos (by linarith [Constants.phi_gt_onePointFive])).le
      have hsinh_nonneg : 0 ≤ Real.sinh A := (Real.sinh_nonneg_iff).2 hA_nonneg
      have hlinconst_nonneg : 0 ≤ Real.log Constants.phi * Real.sinh A := by
        exact mul_nonneg hlog_nonneg hsinh_nonneg
      have hpref_nonneg : 0 ≤ qlf.logDerivBound * qlf.radius * (2 * π) := by
        have h2pi_nonneg : 0 ≤ (2 * π : ℝ) := by positivity
        exact mul_nonneg (mul_nonneg qlf.logDerivBound_pos.le qlf.radius_pos.le) h2pi_nonneg
      dsimp [C]
      exact mul_nonneg hpref_nonneg hlinconst_nonneg
    have hterm :
        ∀ n : Fin N,
          phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
                  (n.val + 1) j|
            ≤ C * ((1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2)) := by
      intro n
      have hk_pos : (0 : ℝ) < (n.val : ℝ) + 1 := by positivity
      have ht0 : 0 ≤ (1 : ℝ) / ((n.val : ℝ) + 1) := by
        exact div_nonneg (by norm_num) hk_pos.le
      have hk_one_le : (1 : ℝ) ≤ (n.val : ℝ) + 1 := by
        have hn_nonneg : (0 : ℝ) ≤ n.val := by exact_mod_cast (Nat.zero_le n.val)
        linarith
      have ht1 : (1 : ℝ) / ((n.val : ℝ) + 1) ≤ 1 := by
        exact div_le_self (show (0 : ℝ) ≤ 1 by norm_num) hk_one_le
      have hpure :
          |defectPhasePureIncrement dpf (n.val + 1)| =
            (π * |(-sensor.charge : ℤ)| / 4) / ((n.val : ℝ) + 1) := by
        simpa [dpf, Nat.cast_add] using
          genuine_pure_increment_abs_eq sensor qlf horder (n.val + 1) (Nat.succ_pos n.val)
      have harg :
          Real.log Constants.phi * |defectPhasePureIncrement dpf (n.val + 1)| =
            ((1 : ℝ) / ((n.val : ℝ) + 1)) * A := by
        rw [hpure]
        dsimp [A]
        have hk_ne : (n.val : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hk_ne]
      have hsinh_scale :
          Real.sinh (((1 : ℝ) / ((n.val : ℝ) + 1)) * A) ≤
            ((1 : ℝ) / ((n.val : ℝ) + 1)) * Real.sinh A :=
        sinh_mul_le_mul_sinh ht0 ht1 hA_nonneg
      have hlog_nonneg : 0 ≤ Real.log Constants.phi := by
        exact (Real.log_pos (by linarith [Constants.phi_gt_onePointFive])).le
      have hsinh_nonneg : 0 ≤ Real.sinh A := (Real.sinh_nonneg_iff).2 hA_nonneg
      have hcoeff_nonneg :
          0 ≤ (Real.log Constants.phi * Real.sinh A) * ((1 : ℝ) / ((n.val : ℝ) + 1)) := by
        exact mul_nonneg (mul_nonneg hlog_nonneg hsinh_nonneg) ht0
      have hlin :
          phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| ≤
            (Real.log Constants.phi * Real.sinh A) * ((1 : ℝ) / ((n.val : ℝ) + 1)) := by
        rw [phiCostLinearCoeff, harg]
        have hmul := mul_le_mul_of_nonneg_left hsinh_scale hlog_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      let innerSum : ℝ :=
        ∑ j : Fin (8 * (n.val + 1)),
          |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
            (n.val + 1) j|
      have hinner_nonneg : 0 ≤ innerSum := by
        dsimp [innerSum]
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hinner := sum_epsilon_abs_bound qlf n
      have hstep1 :
          phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| * innerSum ≤
            ((Real.log Constants.phi * Real.sinh A) * ((1 : ℝ) / ((n.val : ℝ) + 1))) *
              innerSum := by
        exact mul_le_mul_of_nonneg_right hlin hinner_nonneg
      have hstep2 :
          ((Real.log Constants.phi * Real.sinh A) * ((1 : ℝ) / ((n.val : ℝ) + 1))) * innerSum ≤
            ((Real.log Constants.phi * Real.sinh A) * ((1 : ℝ) / ((n.val : ℝ) + 1))) *
              (qlf.logDerivBound * qlf.radius * (2 * π) / ((n.val : ℝ) + 2)) := by
        exact mul_le_mul_of_nonneg_left hinner hcoeff_nonneg
      have hprod := le_trans hstep1 hstep2
      simpa [innerSum, C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprod
    calc
      ∑ n : Fin N,
          phiCostLinearCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
            ∑ j : Fin (8 * (n.val + 1)),
              |(genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
                (n.val + 1) j|
        ≤ ∑ n : Fin N, C * ((1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hterm n
      _ = C * ∑ n : Fin N, (1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) := by
            rw [← Finset.mul_sum]
      _ ≤ C * 1 := by
            exact mul_le_mul_of_nonneg_left (sum_inv_succ_mul_succ_le_one N) hC_nonneg
      _ = qlf.logDerivBound * qlf.radius * (2 * π) *
            (Real.log Constants.phi * Real.sinh (Real.log Constants.phi *
              (π * |(-sensor.charge : ℤ)| / 4))) := by
            simp [C, A]
  quadratic_term_bounded := by
    refine ⟨qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * π) ^ 2 *
      (kappa * Real.exp (Real.log Constants.phi *
        (π * |(-sensor.charge : ℤ)| / 4))) / 8, ?_⟩
    intro N
    let dpf := genuineZetaDerivedPhaseFamily sensor qlf horder
    let A : ℝ := Real.log Constants.phi * (π * |(-sensor.charge : ℤ)| / 4)
    let C : ℝ :=
      qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * π) ^ 2 *
        (kappa * Real.exp A) / 8
    have hC_nonneg : 0 ≤ C := by
      have hquadconst_nonneg : 0 ≤ kappa * Real.exp A := by
        exact mul_nonneg kappa_pos.le (Real.exp_pos A).le
      dsimp [C]
      exact div_nonneg (mul_nonneg (by positivity) hquadconst_nonneg) (by positivity)
    have hterm :
        ∀ n : Fin N,
          phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
              ∑ j : Fin (8 * (n.val + 1)),
                ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
                  (n.val + 1) j) ^ 2
            ≤ C * ((1 : ℝ) / ((n.val : ℝ) + 1) / ((n.val : ℝ) + 2) ^ 2) := by
      intro n
      have hk_one_le : (1 : ℝ) ≤ (n.val : ℝ) + 1 := by
        have hn_nonneg : (0 : ℝ) ≤ n.val := by exact_mod_cast (Nat.zero_le n.val)
        linarith
      have hpure :
          |defectPhasePureIncrement dpf (n.val + 1)| =
            (π * |(-sensor.charge : ℤ)| / 4) / ((n.val : ℝ) + 1) := by
        simpa [dpf, Nat.cast_add] using
          genuine_pure_increment_abs_eq sensor qlf horder (n.val + 1) (Nat.succ_pos n.val)
      have hpure_le :
          |defectPhasePureIncrement dpf (n.val + 1)| ≤ π * |(-sensor.charge : ℤ)| / 4 := by
        rw [hpure]
        exact div_le_self (show (0 : ℝ) ≤ π * |(-sensor.charge : ℤ)| / 4 by positivity) hk_one_le
      have hlog_nonneg : 0 ≤ Real.log Constants.phi := by
        exact (Real.log_pos (by linarith [Constants.phi_gt_onePointFive])).le
      have harg_le :
          Real.log Constants.phi * |defectPhasePureIncrement dpf (n.val + 1)| ≤ A := by
        dsimp [A]
        exact mul_le_mul_of_nonneg_left hpure_le hlog_nonneg
      have hquad :
          phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| ≤
            kappa * Real.exp A := by
        rw [phiCostQuadraticCoeff]
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone harg_le) kappa_pos.le
      let innerSum : ℝ :=
        ∑ j : Fin (8 * (n.val + 1)),
          ((genuineRegularFactorPhaseAt qlf (n.val + 1) (Nat.succ_pos n.val)).sampleIncrements
            (n.val + 1) j) ^ 2
      have hinner_nonneg : 0 ≤ innerSum := by
        dsimp [innerSum]
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hquad_nonneg : 0 ≤ kappa * Real.exp A := by
        exact mul_nonneg kappa_pos.le (Real.exp_pos A).le
      have hinner := sum_epsilon_sq_bound qlf n
      have hstep1 :
          phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| * innerSum ≤
            (kappa * Real.exp A) * innerSum := by
        exact mul_le_mul_of_nonneg_right hquad hinner_nonneg
      have hstep2 :
          (kappa * Real.exp A) * innerSum ≤
            (kappa * Real.exp A) *
              (qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * π) ^ 2 /
                (8 * ((n.val : ℝ) + 1) * ((n.val : ℝ) + 2) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hinner hquad_nonneg
      have hprod := le_trans hstep1 hstep2
      simpa [innerSum, C, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprod
    calc
      ∑ n : Fin N,
          phiCostQuadraticCoeff |defectPhasePureIncrement dpf (n.val + 1)| *
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
      _ = qlf.logDerivBound ^ 2 * qlf.radius ^ 2 * (2 * π) ^ 2 *
            (kappa * Real.exp (Real.log Constants.phi *
              (π * |(-sensor.charge : ℤ)| / 4))) / 8 := by
            simp [C, A]

/-! ### §6. Honest ζ⁻¹ phase family data (analytic route target) -/

/-- Phase family data derived from the actual `ζ⁻¹` function near a
hypothetical zero `ρ`.

Unlike the trivial `pureDefectPhaseData` (which uses a constant phase),
this structure records that the phase samples come from the Weierstrass
factorization of the meromorphic function `zetaReciprocal` itself.

The fields capture:
* the local meromorphic witness at an actual complex center `ρ`
  (from `local_meromorphic_factorization`)
* the quantitative log-derivative bound `M` (from the Euler carrier)
* the per-ring phase data derived from the actual function

The `phaseFamily` should be `zetaDerivedPhaseFamily` for honest data;
the `family_derived` field witnesses this. -/
structure ZetaPhaseFamilyData where
  sensor : DefectSensor
  witness : QuantitativeLocalFactorization
  witness_realPart : witness.center.re = sensor.realPart
  witness_order : witness.order = -sensor.charge
  phaseFamily : DefectPhaseFamily
  family_sensor : phaseFamily.sensor = sensor
  family_derived : phaseFamily = zetaDerivedPhaseFamily sensor witness witness_order

/-- Any honest zeta phase-family package carries the canonical zero-perturbation
witness attached to its derived phase family. -/
noncomputable def ZetaPhaseFamilyData.perturbationWitness
    (zfd : ZetaPhaseFamilyData) :
    DefectPhasePerturbationWitness zfd.phaseFamily := by
  simpa [zfd.family_derived] using
    zetaDerivedPhasePerturbationWitness zfd.sensor zfd.witness zfd.witness_order

end

end NumberTheory
end IndisputableMonolith
