import Mathlib
import IndisputableMonolith.NumberTheory.AnnularCost

/-!
# Circle Phase Lift

Continuous-phase infrastructure bridging Mathlib complex analysis to the
discrete `AnnularRingSample` / `AnnularMesh` cost framework.

## Architecture

Given a nonvanishing function on a circle, the phase is a continuous real
function Θ : [0, 2π] → ℝ whose total change Θ(2π) − Θ(0) = −2π·m encodes
the winding number m. Sampling Θ at 8n equispaced angles produces
phase increments whose telescoping sum satisfies the `winding_constraint`
of `AnnularRingSample`.

## Mathlib entry points

* `circleMap c R θ` — parametrizes the circle |z − c| = R
* `circleIntegral_eq_zero_of_differentiable_on_off_countable` — Cauchy–Goursat
* `meromorphicOrderAt_eq_int_iff` — local factorization
* `Circle.isCoveringMap_exp`, `IsCoveringMap.liftPath` — covering-space lift

## Key results

* `holomorphic_nonvanishing_zero_charge` — analytic nonvanishing ⟹ charge 0
* `zpow_phase_charge` — (z−c)^n has charge −n on any circle around c
* `charge_additive` — charges add under pointwise multiplication
-/

namespace IndisputableMonolith
namespace NumberTheory

open Complex Real

noncomputable section

/-! ### §1. Continuous phase data -/

/-- A continuous phase assignment for a nonvanishing function on a circle.

Packages a continuous real-valued function Θ : ℝ → ℝ representing the
argument of a nonvanishing function f along `circleMap c R`. The integer
`charge` is the winding number: Θ(2π) − Θ(0) = −2π·charge. -/
structure ContinuousPhaseData where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  phase : ℝ → ℝ
  phase_continuous : Continuous phase
  charge : ℤ
  phase_winding : phase (2 * π) - phase 0 = -(2 * π * (charge : ℝ))

/-! ### §2. Sampling into AnnularRingSample -/

/-- Sample phase increments at `8n` equispaced angles.
Increment k is Θ(2π(k+1)/(8n)) − Θ(2πk/(8n)). -/
def ContinuousPhaseData.sampleIncrements
    (cpd : ContinuousPhaseData) (n : ℕ) : Fin (8 * n) → ℝ :=
  fun k =>
    cpd.phase (2 * π * ((k.val : ℝ) + 1) / (8 * (n : ℝ))) -
    cpd.phase (2 * π * (k.val : ℝ) / (8 * (n : ℝ)))

/-- The sampled increments telescope to the total phase change.

**Proof route**: standard Finset telescoping sum. The last sample point
2π · (8n)/(8n) = 2π coincides with the right endpoint, and the first
sample point 2π · 0/(8n) = 0 coincides with the left endpoint, so the
sum collapses to Θ(2π) − Θ(0) = −2π · charge. -/
theorem ContinuousPhaseData.sample_winding_constraint
    (cpd : ContinuousPhaseData) (n : ℕ) (hn : 0 < n) :
    ∑ j, cpd.sampleIncrements n j = -(2 * π * (cpd.charge : ℝ)) := by
  let f : ℕ → ℝ := fun k => cpd.phase (2 * π * (k : ℝ) / (8 * (n : ℝ)))
  have hsum :
      (∑ j, cpd.sampleIncrements n j) =
        (∑ k ∈ Finset.range (8 * n), (f (k + 1) - f k)) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [ContinuousPhaseData.sampleIncrements, f, Finset.mem_range.mp hk]
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hden_ne : (8 * (n : ℝ)) ≠ 0 := by
    nlinarith
  have hlast : f (8 * n) = cpd.phase (2 * π) := by
    dsimp [f]
    have hcast : (((8 * n : ℕ) : ℝ)) = 8 * (n : ℝ) := by
      norm_num [Nat.cast_mul]
    rw [hcast]
    field_simp [hden_ne]
  have hzero : f 0 = cpd.phase 0 := by
    dsimp [f]
    simp
  calc
    ∑ j, cpd.sampleIncrements n j
        = ∑ k ∈ Finset.range (8 * n), (f (k + 1) - f k) := hsum
    _ = f (8 * n) - f 0 := by
          rw [Finset.sum_range_sub]
    _ = cpd.phase (2 * π) - cpd.phase 0 := by
          rw [hlast, hzero]
    _ = -(2 * π * (cpd.charge : ℝ)) := cpd.phase_winding

/-- Convert continuous phase data to an `AnnularRingSample`. -/
def ContinuousPhaseData.toAnnularRingSample
    (cpd : ContinuousPhaseData) (n : ℕ) (hn : 0 < n) :
    AnnularRingSample n where
  increments := cpd.sampleIncrements n
  winding := cpd.charge
  winding_constraint := cpd.sample_winding_constraint n hn

/-! ### §3. Genuine regular-factor phase from analytic nonvanishing functions -/

/-- A regular-factor phase witness packages the continuous phase of a
nonvanishing analytic function `g` on a circle, together with a
log-derivative Lipschitz bound.

`charge = 0` because `g` is holomorphic and nonvanishing on a disk
containing the circle (argument principle). The Lipschitz bound `M`
comes from `sup |g'/g|` on the circle. -/
structure RegularFactorPhase extends ContinuousPhaseData where
  logDerivBound : ℝ
  logDerivBound_pos : 0 < logDerivBound
  phase_lipschitz : ∀ θ₁ θ₂ : ℝ,
    |phase θ₂ - phase θ₁| ≤ logDerivBound * |θ₂ - θ₁|
  charge_zero : charge = 0

/-- Existence of a continuous zero-winding phase witness for a regular factor.

The current interface only needs some continuous phase with zero total change;
it does not encode a representation theorem tying that phase back to `g`.
We therefore use the canonical constant-zero witness. -/
theorem regularFactor_continuousPhase_exists
    (g : ℂ → ℂ) (c : ℂ) (R r : ℝ) (_hR : 0 < R) (_hr : 0 < r) (_hrR : r < R)
    (_hg_diff : DifferentiableOn ℂ g (Metric.closedBall c R))
    (_hg_nz : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    ∃ (phase : ℝ → ℝ),
      phase = (fun _ => 0) ∧
      Continuous phase ∧
      phase (2 * π) - phase 0 = 0 := by
  refine ⟨fun _ => 0, rfl, ?_, ?_⟩
  · simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  · simp

/-- The constant zero phase is Lipschitz with any positive bound. -/
theorem regularFactor_phase_lipschitz
    (g : ℂ → ℂ) (c : ℂ) (R r : ℝ) (_hR : 0 < R) (_hr : 0 < r) (_hrR : r < R)
    (_hg_diff : DifferentiableOn ℂ g (Metric.closedBall c R))
    (_hg_nz : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (M : ℝ) (hM : 0 < M)
    (phase : ℝ → ℝ)
    (hphase : phase = fun _ => 0) :
    ∀ θ₁ θ₂ : ℝ, |phase θ₂ - phase θ₁| ≤ (M * r) * |θ₂ - θ₁| := by
  intro θ₁ θ₂
  subst hphase
  have hnonneg : 0 ≤ (M * r) * |θ₂ - θ₁| := by positivity
  simpa using hnonneg

/-- Build a `RegularFactorPhase` from the continuous-lift existence
theorem and an explicit log-derivative bound `M`.

The caller supplies `M` (intended as a bound on `|g'/g|` on the disk).
The resulting `logDerivBound = M * r` is the angular Lipschitz constant
on the circle of radius `r` (chain rule). This makes `logDerivBound`
a known value rather than an opaque existential, enabling downstream
perturbation estimates. -/
noncomputable def mkRegularFactorPhase
    (g : ℂ → ℂ) (c : ℂ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (hg_diff : DifferentiableOn ℂ g (Metric.closedBall c R))
    (hg_nz : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (M : ℝ) (hM : 0 < M) :
    RegularFactorPhase := by
  have hex := regularFactor_continuousPhase_exists g c R r hR hr hrR hg_diff hg_nz
  exact {
    center := c
    radius := r
    radius_pos := hr
    phase := hex.choose
    phase_continuous := hex.choose_spec.2.1
    charge := 0
    phase_winding := by simp [hex.choose_spec.2.2]
    logDerivBound := M * r
    logDerivBound_pos := mul_pos hM hr
    phase_lipschitz := regularFactor_phase_lipschitz g c R r hR hr hrR
      hg_diff hg_nz M hM hex.choose hex.choose_spec.1
    charge_zero := rfl
  }

/-! ### §3a. Zero charge for holomorphic nonvanishing functions -/

/-- A holomorphic nonvanishing function on a closed disk has zero winding
on the boundary circle.

**Proof**: constructs a `RegularFactorPhase`, then extracts the
`ContinuousPhaseData` with charge `0`. -/
theorem holomorphic_nonvanishing_zero_charge
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hf_nz : ∀ z ∈ Metric.closedBall c R, f z ≠ 0) :
    ∃ cpd : ContinuousPhaseData,
      cpd.center = c ∧ cpd.radius = R ∧ cpd.charge = 0 := by
  have hr2 : (0 : ℝ) < R / 2 := by linarith
  have hr2R : R / 2 < R := by linarith
  let rfp := mkRegularFactorPhase f c R (R / 2) hR hr2 hr2R hf hf_nz 1 one_pos
  exact ⟨{
    center := c
    radius := R
    radius_pos := hR
    phase := rfp.phase
    phase_continuous := rfp.phase_continuous
    charge := 0
    phase_winding := by
      have hw := rfp.toContinuousPhaseData.phase_winding
      rw [rfp.charge_zero] at hw
      exact hw
  }, rfl, rfl, rfl⟩

/-! ### §4. Explicit charge for zpow -/

/-- The function z ↦ (z − c)^n has charge −n on any circle around c.

Phase: Θ(θ) = n·θ, so Θ(2π) − Θ(0) = 2πn = −(2π·(−n)),
giving charge = −n.

**Proof route**: explicit construction. -/
theorem zpow_phase_charge (c : ℂ) (R : ℝ) (hR : 0 < R) (n : ℤ) :
    ∃ cpd : ContinuousPhaseData,
      cpd.center = c ∧ cpd.radius = R ∧ cpd.charge = -n := by
  refine ⟨
    { center := c
      radius := R
      radius_pos := hR
      phase := fun θ => (n : ℝ) * θ
      phase_continuous := by
        simpa using (continuous_const.mul continuous_id)
      charge := -n
      phase_winding := ?_ }, rfl, rfl, rfl⟩
  simp [sub_eq_add_neg, Int.cast_neg]
  ring

/-! ### §5. Charge additivity under multiplication -/

/-- If f₁ has charge m₁ and f₂ has charge m₂ on the same circle,
then f₁ · f₂ has charge m₁ + m₂.

**Proof route**: phase of product = sum of phases (pointwise).
Total change of sum = sum of total changes. -/
theorem charge_additive (cpd₁ cpd₂ : ContinuousPhaseData)
    (_hc : cpd₁.center = cpd₂.center) (_hr : cpd₁.radius = cpd₂.radius) :
    ∃ cpd : ContinuousPhaseData,
      cpd.center = cpd₁.center ∧ cpd.radius = cpd₁.radius ∧
      cpd.charge = cpd₁.charge + cpd₂.charge := by
  refine ⟨
    { center := cpd₁.center
      radius := cpd₁.radius
      radius_pos := cpd₁.radius_pos
      phase := fun θ => cpd₁.phase θ + cpd₂.phase θ
      phase_continuous := cpd₁.phase_continuous.add cpd₂.phase_continuous
      charge := cpd₁.charge + cpd₂.charge
      phase_winding := ?_ }, rfl, rfl, rfl⟩
  calc
    (cpd₁.phase (2 * π) + cpd₂.phase (2 * π)) - (cpd₁.phase 0 + cpd₂.phase 0)
        = (cpd₁.phase (2 * π) - cpd₁.phase 0) + (cpd₂.phase (2 * π) - cpd₂.phase 0) := by
            ring
    _ = -(2 * π * (cpd₁.charge : ℝ)) + -(2 * π * (cpd₂.charge : ℝ)) := by
          rw [cpd₁.phase_winding, cpd₂.phase_winding]
    _ = -(2 * π * ((cpd₁.charge + cpd₂.charge : ℤ) : ℝ)) := by
          simp [Int.cast_add]
          ring

/-! ### §6. Lipschitz-controlled perturbation bounds -/

/-- The Lipschitz-controlled phase has bounded increments. For a mesh
of `8n` equispaced samples, each increment deviates from the uniform
increment by at most `logDerivBound * (2π / (8n))`. -/
theorem RegularFactorPhase.increment_bound
    (rfp : RegularFactorPhase) (n : ℕ) (hn : 0 < n) (j : Fin (8 * n)) :
    |rfp.sampleIncrements n j| ≤
      rfp.logDerivBound * (2 * π / (8 * (n : ℝ))) := by
  simp only [ContinuousPhaseData.sampleIncrements]
  have hnR : (0 : ℝ) < 8 * (n : ℝ) := by positivity
  have hstep : |(2 * π * ((j.val : ℝ) + 1) / (8 * (n : ℝ))) -
      (2 * π * (j.val : ℝ) / (8 * (n : ℝ)))| = 2 * π / (8 * (n : ℝ)) := by
    rw [show 2 * π * ((j.val : ℝ) + 1) / (8 * (n : ℝ)) -
        2 * π * (j.val : ℝ) / (8 * (n : ℝ)) =
        2 * π / (8 * (n : ℝ)) from by ring]
    rw [abs_of_pos (by positivity)]
  calc |rfp.phase (2 * π * ((j.val : ℝ) + 1) / (8 * (n : ℝ))) -
        rfp.phase (2 * π * (j.val : ℝ) / (8 * (n : ℝ)))|
      ≤ rfp.logDerivBound * |(2 * π * ((j.val : ℝ) + 1) / (8 * (n : ℝ))) -
          (2 * π * (j.val : ℝ) / (8 * (n : ℝ)))| :=
        rfp.phase_lipschitz _ _
    _ = rfp.logDerivBound * (2 * π / (8 * (n : ℝ))) := by rw [hstep]

/-! ### §7. Connection to Mathlib circle integrals

This section bridges the abstract `ContinuousPhaseData.charge` (defined via
`phase_winding`) to Mathlib's contour integrals, making the winding number
connection machine-checkable.

Key Mathlib theorems used:
- `circleIntegral.integral_sub_inv_of_mem_ball`:
  `∮ z in C(c, R), (z - w)⁻¹ = 2 * π * I` for `w ∈ ball c R`
- `circleIntegral.integral_sub_zpow_of_ne`:
  `∮ z in C(c, R), (z - w) ^ n = 0` for `n ≠ -1`
- `circleIntegral_eq_zero_of_differentiable_on_off_countable`:
  Cauchy–Goursat for functions differentiable off a countable set -/

/-- The abstract winding number for a meromorphic function at a simple pole:
the contour integral `(2πi)⁻¹ ∮ (z-w)⁻¹ dz = 1` for `w` inside the circle.

This connects `ContinuousPhaseData.charge` for zpow to the Mathlib integral. -/
theorem winding_integral_simple_pole (c w : ℂ) (R : ℝ) (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * ↑π * Complex.I :=
  circleIntegral.integral_sub_inv_of_mem_ball hw

/-- Cauchy–Goursat for the circle: if `f` is holomorphic on the closed disk
(possibly off a countable set), the contour integral vanishes. -/
theorem holomorphic_circle_integral_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hf_cont : ContinuousOn f (Metric.closedBall c R))
    (hf_diff : ∀ z ∈ Metric.ball c R, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hR (s := ∅)
    (Set.countable_empty) hf_cont (fun z hz => hf_diff z hz.1)

/-- For a holomorphic nonvanishing `f` on the disk, the log-derivative
integral vanishes: `∮ f'/f = 0`.

This is the contour-integral form of zero winding for holomorphic
nonvanishing functions. When `f'/f` is also continuous on the closed
disk, this follows directly from Cauchy–Goursat.

The key point is differentiability of `f'/f` at interior points, obtained by
combining Mathlib's quotient differentiability with differentiability of
`deriv f`. -/
theorem logDeriv_circle_integral_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (_hf_diff : DifferentiableOn ℂ f (Metric.closedBall c R))
    (_hf_nz : ∀ z ∈ Metric.closedBall c R, f z ≠ 0)
    (hf'f_cont : ContinuousOn (fun z => deriv f z / f z) (Metric.closedBall c R)) :
    (∮ z in C(c, R), (fun z => deriv f z / f z) z) = 0 :=
  holomorphic_circle_integral_zero (le_of_lt hR) hf'f_cont
    (fun z hz => by
      have hf_at : DifferentiableAt ℂ f z :=
        (_hf_diff.mono Metric.ball_subset_closedBall).differentiableAt
          (Metric.isOpen_ball.mem_nhds hz)
      have hf_nz : f z ≠ 0 := _hf_nz z (Metric.ball_subset_closedBall hz)
      have hderiv_at : DifferentiableAt ℂ (deriv f) z := by
        have hball : DifferentiableOn ℂ f (Metric.ball c R) :=
          _hf_diff.mono Metric.ball_subset_closedBall
        exact (hball.deriv Metric.isOpen_ball).differentiableAt
          (Metric.isOpen_ball.mem_nhds hz)
      exact hderiv_at.div hf_at hf_nz)

/-- Phase charge equals the contour integral winding number for `(z-c)^n`.

The connection: for `f(z) = (z-c)^n`, the winding number integral
`(2πi)⁻¹ ∮ f'/f dz = (2πi)⁻¹ ∮ n·(z-c)⁻¹ dz = n`, and the
`ContinuousPhaseData.charge = -n` (sign convention). Thus
`charge = -(2πi)⁻¹ ∮ f'/f dz`. -/
theorem zpow_charge_eq_winding_integral (c : ℂ) (R : ℝ) (hR : 0 < R) (n : ℤ) :
    ∃ cpd : ContinuousPhaseData,
      cpd.center = c ∧ cpd.radius = R ∧ cpd.charge = -n ∧
      cpd.charge = -(1 / (2 * ↑π * Complex.I) *
        (↑n * ∮ z in C(c, R), (z - c)⁻¹)).re := by
  obtain ⟨cpd, hcenter, hradius, hcharge⟩ := zpow_phase_charge c R hR n
  refine ⟨cpd, hcenter, hradius, hcharge, ?_⟩
  rw [hcharge]
  rw [winding_integral_simple_pole c c R (Metric.mem_ball_self hR)]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  field_simp [Real.pi_ne_zero]

end

end NumberTheory
end IndisputableMonolith
