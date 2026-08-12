import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureFunctionBlocker

/-!
# Wave C2 R0+R1: dynamic structure-function bracket on two sites

Closes the first two typed residuals of
`plans/QG_WaveC2_Gap5_Residual_DAG_Draft_20260722.txt`:

* **R0 (decoy).** The naive lookalike that plugs `g x` into the frozen
  `HamW` slot and reuses the frozen partials (`pderivQ_HamW`) fails: the
  configuration partial picks up an uncompensated `∂g/∂q` term.
* **R1.** The same candidate Hamiltonian, once its Frechet derivative is
  computed honestly (including `∂g/∂q`), inhabits
  `PhaseSpaceDependentHamiltonianConstruction concreteDynamicInverseMetric`
  at `n = 2`. The extra derivative terms cancel in the Hamiltonian–Hamiltonian
  bracket, so `ham_ham` recovers the target dynamic structure function.

Does **not** flip `gap5_constraint_recovery`. Continuum and HKT residuals
remain OPEN.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DynamicStructureBracket

open HypersurfaceDeformation WeightedHypersurfaceBracket DynamicStructureFunctionBlocker

noncomputable section

open Finset

/-! ## Candidate: naive dynamic HamW lookalike -/

/-- MODEL. The lookalike that substitutes the phase-space-dependent inverse
metric into the `HamW` density pointwise:
`ham N x := HamW (concreteDynamicInverseMetric x) N x`. -/
def naiveDynamicHamW (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  HamW (concreteDynamicInverseMetric x) N x

/-- Unfolded form used for Frechet calculus. -/
def HamDyn (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ i : ZMod 2, (N i / 2) *
    (x.2 i * x.2 i +
      (1 + x.1 i * x.1 i) *
        ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)))

theorem HamDyn_eq_naive (N : ZMod 2 → ℝ) :
    HamDyn N = naiveDynamicHamW N := by
  funext x
  unfold HamDyn naiveDynamicHamW HamW concreteDynamicInverseMetric
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## R0 witness data -/

/-- Explicit witness phase point: unit configuration and unit momentum at
site `0`, zero at site `1`. Gradient and `∂g/∂q` are both nonzero at site
`0`. -/
def decoyPhasePoint : PhaseSpace 2 :=
  (fun j : ZMod 2 => if j = (0 : ZMod 2) then (1 : ℝ) else 0,
    fun j : ZMod 2 => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

/-- Lapse supported at site `0`. -/
def decoyLapse : ZMod 2 → ℝ :=
  fun j => if j = (0 : ZMod 2) then (1 : ℝ) else 0

private lemma decoyLapse_zero : decoyLapse (0 : ZMod 2) = 1 := by
  simp [decoyLapse]

private lemma decoyLapse_one : decoyLapse (1 : ZMod 2) = 0 := by
  simp [decoyLapse]

private lemma decoy_q_zero : decoyPhasePoint.1 (0 : ZMod 2) = 1 := by
  simp [decoyPhasePoint]

private lemma decoy_q_one : decoyPhasePoint.1 (1 : ZMod 2) = 0 := by
  simp [decoyPhasePoint]

private lemma zmod2_zero_sub_one : (0 : ZMod 2) - 1 = 1 := by
  decide

private lemma zmod2_zero_add_one : (0 : ZMod 2) + 1 = 1 := by
  decide

/-! ## Frechet derivative (honest; includes ∂g/∂q) -/

/-- Frechet derivative of `HamDyn N`. The final summand carries `0 + …`
so that it matches `HasFDerivAt.const.add` from the metric factor. -/
def HamDynD (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  ∑ i : ZMod 2,
    (N i / 2) •
      ((x.2 i • coordP i + x.2 i • coordP i) +
        ((1 + x.1 i * x.1 i) •
            ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i) +
              (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)) +
          ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)) •
            (0 + (x.1 i • coordQ i + x.1 i • coordQ i))))

lemma hasFDerivAt_HamDyn (N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (HamDyn N) (HamDynD N x) x := by
  unfold HamDyn HamDynD
  exact HasFDerivAt.fun_sum fun i _ =>
    ((((hasFDerivAt_coord_snd i x).mul (hasFDerivAt_coord_snd i x)).add
      (((hasFDerivAt_const (1 : ℝ) x).add
          ((hasFDerivAt_coord_fst i x).mul (hasFDerivAt_coord_fst i x))).mul
        (((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x)).mul
          ((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x))))).const_mul
      (N i / 2))

/-- THEOREM. Momentum partial: kinetic slot unchanged by `g`. -/
theorem pderivP_HamDyn (N : ZMod 2 → ℝ) (j : ZMod 2) (x : PhaseSpace 2) :
    pderivP (HamDyn N) j x = N j * x.2 j := by
  rw [pderivP, (hasFDerivAt_HamDyn N x).fderiv, HamDynD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod 2,
      (((N i / 2) •
          ((x.2 i • coordP i + x.2 i • coordP i) +
            ((1 + x.1 i * x.1 i) •
                ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i) +
                  (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)) +
              ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)) •
                (0 + (x.1 i • coordQ i + x.1 i • coordQ i)))) :
            PhaseSpace 2 →L[ℝ] ℝ))
        ((0, Pi.single j 1) : PhaseSpace 2)
      = (N i * x.2 i) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]

/-- THEOREM. Honest configuration partial: frozen `HamW` contribution plus
the `∂g/∂q` correction `N_j q_j (Δq_j)²`. -/
theorem pderivQ_HamDyn (N : ZMod 2 → ℝ) (j : ZMod 2) (x : PhaseSpace 2) :
    pderivQ (HamDyn N) j x
      = N (j - 1) * ((1 + x.1 (j - 1) * x.1 (j - 1)) * (x.1 j - x.1 (j - 1)))
        - N j * ((1 + x.1 j * x.1 j) * (x.1 (j + 1) - x.1 j))
        + N j * (x.1 j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) := by
  rw [pderivQ, (hasFDerivAt_HamDyn N x).fderiv, HamDynD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod 2,
      (((N i / 2) •
          ((x.2 i • coordP i + x.2 i • coordP i) +
            ((1 + x.1 i * x.1 i) •
                ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i) +
                  (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)) +
              ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)) •
                (0 + (x.1 i • coordQ i + x.1 i • coordQ i)))) :
            PhaseSpace 2 →L[ℝ] ℝ))
        ((Pi.single j 1, 0) : PhaseSpace 2)
      = (N i * ((1 + x.1 i * x.1 i) * (x.1 (i + 1) - x.1 i))) *
            (if i + 1 = j then (1 : ℝ) else 0)
        - (N i * ((1 + x.1 i * x.1 i) * (x.1 (i + 1) - x.1 i))) *
            (if i = j then (1 : ℝ) else 0)
        + (N i * (x.1 i * ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)))) *
            (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply, mul_sub]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_mul_ite_add
      (fun i => N i * ((1 + x.1 i * x.1 i) * (x.1 (i + 1) - x.1 i))) 1 j,
    sum_mul_ite
      (fun i => N i * ((1 + x.1 i * x.1 i) * (x.1 (i + 1) - x.1 i))) j,
    sum_mul_ite
      (fun i => N i * (x.1 i * ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)))) j]
  have e : j - 1 + 1 = j := by ring
  simp only [e]

/-- THEOREM (R0 decoy). The naive lookalike fails the frozen-partial
construction reading: at `decoyPhasePoint`, with lapse `decoyLapse` and site
`0`, the honest `pderivQ` differs from the frozen `pderivQ_HamW` evaluation
at `w := g x` by the uncompensated `∂g/∂q` term. -/
theorem TypedResidual_naive_dynamic_HamW_decoy_fails :
    pderivQ (HamDyn decoyLapse) (0 : ZMod 2) decoyPhasePoint
      ≠ pderivQ (HamW (concreteDynamicInverseMetric decoyPhasePoint) decoyLapse)
          (0 : ZMod 2) decoyPhasePoint := by
  have hHonest :
      pderivQ (HamDyn decoyLapse) (0 : ZMod 2) decoyPhasePoint = (3 : ℝ) := by
    rw [pderivQ_HamDyn, zmod2_zero_sub_one, zmod2_zero_add_one,
      decoyLapse_zero, decoyLapse_one, decoy_q_zero, decoy_q_one]
    norm_num
  have hFrozen :
      pderivQ (HamW (concreteDynamicInverseMetric decoyPhasePoint) decoyLapse)
          (0 : ZMod 2) decoyPhasePoint = (2 : ℝ) := by
    rw [pderivQ_HamW]
    rw [zmod2_zero_sub_one, zmod2_zero_add_one, decoyLapse_zero, decoyLapse_one,
      decoy_q_zero, decoy_q_one]
    simp only [concreteDynamicInverseMetric, decoy_q_zero, pow_two]
    norm_num
  rw [hHonest, hFrozen]
  norm_num

theorem differentiable_HamDyn (N : ZMod 2 → ℝ) :
    Differentiable ℝ (HamDyn N) :=
  fun x => (hasFDerivAt_HamDyn N x).differentiableAt

/-- THEOREM (R1 headline). Exact dynamic structure-function identity for the
two-site concrete inverse metric. -/
theorem bracket_HamDyn_HamDyn (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (HamDyn N) (HamDyn M) x
      = ∑ j : ZMod 2, (N j * M (j + 1) - M j * N (j + 1)) *
          (concreteDynamicInverseMetric x j *
            (x.2 (j + 1) * (x.1 (j + 1) - x.1 j))) := by
  simp only [bracket, pderivQ_HamDyn, pderivP_HamDyn, concreteDynamicInverseMetric]
  have step1 :
      (∑ j : ZMod 2,
          ((N (j - 1) * ((1 + x.1 (j - 1) * x.1 (j - 1)) * (x.1 j - x.1 (j - 1)))
              - N j * ((1 + x.1 j * x.1 j) * (x.1 (j + 1) - x.1 j))
              + N j * (x.1 j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))) *
            (M j * x.2 j)
            - (N j * x.2 j) *
              (M (j - 1) * ((1 + x.1 (j - 1) * x.1 (j - 1)) * (x.1 j - x.1 (j - 1)))
                - M j * ((1 + x.1 j * x.1 j) * (x.1 (j + 1) - x.1 j))
                + M j * (x.1 j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))))))
        = ∑ j : ZMod 2,
            (N (j - 1) * M j - M (j - 1) * N j) *
              ((1 + x.1 (j - 1) * x.1 (j - 1)) *
                (x.2 j * (x.1 j - x.1 (j - 1)))) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [step1]
  refine sum_reindex 1
    (fun k =>
      (N (k - 1) * M k - M (k - 1) * N k) *
        ((1 + x.1 (k - 1) * x.1 (k - 1)) *
          (x.2 k * (x.1 k - x.1 (k - 1))))) _
    fun j => ?_
  have e1 : j + 1 - 1 = j := by ring
  simp only [e1]
  ring

/-- THEOREM (R1). Inhabitant of the phase-space-dependent Hamiltonian
construction for `concreteDynamicInverseMetric` at `n = 2`. -/
def concreteDynamicHamiltonianConstruction :
    PhaseSpaceDependentHamiltonianConstruction concreteDynamicInverseMetric where
  ham := HamDyn
  ham_differentiable := differentiable_HamDyn
  ham_ham := bracket_HamDyn_HamDyn

/-- Equivalent residual Prop named in the Wave C2 DAG. -/
def TypedResidual_dynamic_bracket_concrete_two_site : Prop :=
  Nonempty (PhaseSpaceDependentHamiltonianConstruction concreteDynamicInverseMetric)

theorem typedResidual_dynamic_bracket_concrete_two_site :
    TypedResidual_dynamic_bracket_concrete_two_site :=
  ⟨concreteDynamicHamiltonianConstruction⟩

/-- Immediate hard-core corollary (DAG R2, folded into R1 for `n = 2`). -/
theorem phaseSpaceDependentDiracPremise_two_site :
    PhaseSpaceDependentDiracPremise 2 :=
  ⟨concreteDynamicInverseMetric,
    concreteDynamicInverseMetric_not_constant,
    ⟨concreteDynamicHamiltonianConstruction⟩⟩

/-! ### Axiom receipts -/

#print axioms TypedResidual_naive_dynamic_HamW_decoy_fails
#print axioms bracket_HamDyn_HamDyn
#print axioms typedResidual_dynamic_bracket_concrete_two_site
#print axioms phaseSpaceDependentDiracPremise_two_site

end
end DynamicStructureBracket
end SevenGaps
end Gravity
end IndisputableMonolith
