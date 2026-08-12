import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureFunctionBlocker

/-!
# Wave C2 R4 repair Step 2: general-`n` dynamic structure bracket

Generalizes `DynamicStructureBracket.HamDyn` / `bracket_HamDyn_HamDyn` from
`n = 2` to arbitrary `n` with `[NeZero n]`. The Frechet bookkeeping
(`HamDynD`, `∂g/∂q` correction, Kronecker collapse, periodic reindex) is
the same pattern as the two-site proof; ZMod wraparound is periodic, so
there is no boundary term.

True general RHS (derived from the calculus, matching the `n = 2` case):

```
bracket (HamDynN N) (HamDynN M) x
  = ∑ j, (N j * M (j+1) - M j * N (j+1))
      * ((1 + (x.1 j)^2) * (x.2 (j+1) * (x.1 (j+1) - x.1 j)))
```

Structure factor `g_j = 1 + (x.1 j)^2` sits at the left split point `j`
(same placement as `HamW`'s background weight `w j`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DynamicStructureBracketN

open HypersurfaceDeformation WeightedHypersurfaceBracket
open DynamicStructureFunctionBlocker DynamicStructureBracket

noncomputable section

open Finset

variable {n : ℕ} [NeZero n]

/-! ## General-`n` dynamic Hamiltonian -/

/-- MODEL. Exact shape of `HamDyn` at general `n`: kinetic slot unweighted,
stiffness slot carries `g x j = 1 + (x.1 j)^2`. -/
def HamDynN (N : ZMod n → ℝ) (x : PhaseSpace n) : ℝ :=
  ∑ i : ZMod n, (N i / 2) *
    (x.2 i * x.2 i +
      (1 + x.1 i * x.1 i) *
        ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)))

/-- Consistency: at `n = 2`, `HamDynN` is definitionally `HamDyn`. -/
theorem HamDynN_eq_HamDyn (N : ZMod 2 → ℝ) :
    HamDynN (n := 2) N = HamDyn N :=
  rfl

/-- Inverse-metric factor used in the structure slot. -/
def dynamicInverseMetricN (x : PhaseSpace n) (j : ZMod n) : ℝ :=
  1 + (x.1 j) ^ 2

omit [NeZero n] in
theorem dynamicInverseMetricN_eq (x : PhaseSpace n) (j : ZMod n) :
    dynamicInverseMetricN x j = 1 + x.1 j * x.1 j := by
  simp [dynamicInverseMetricN, pow_two]

/-! ## Frechet derivative (honest; includes ∂g/∂q) -/

/-- Frechet derivative of `HamDynN N`. Final summand carries `0 + …` to match
`HasFDerivAt.const.add` from the metric factor (same as `HamDynD`). -/
def HamDynND (N : ZMod n → ℝ) (x : PhaseSpace n) : PhaseSpace n →L[ℝ] ℝ :=
  ∑ i : ZMod n,
    (N i / 2) •
      ((x.2 i • coordP i + x.2 i • coordP i) +
        ((1 + x.1 i * x.1 i) •
            ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i) +
              (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)) +
          ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)) •
            (0 + (x.1 i • coordQ i + x.1 i • coordQ i))))

lemma hasFDerivAt_HamDynN (N : ZMod n → ℝ) (x : PhaseSpace n) :
    HasFDerivAt (HamDynN N) (HamDynND N x) x := by
  unfold HamDynN HamDynND
  exact HasFDerivAt.fun_sum fun i _ =>
    ((((hasFDerivAt_coord_snd i x).mul (hasFDerivAt_coord_snd i x)).add
      (((hasFDerivAt_const (1 : ℝ) x).add
          ((hasFDerivAt_coord_fst i x).mul (hasFDerivAt_coord_fst i x))).mul
        (((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x)).mul
          ((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x))))).const_mul
      (N i / 2))

/-- THEOREM. Momentum partial: kinetic slot unchanged by `g`. -/
theorem pderivP_HamDynN (N : ZMod n → ℝ) (j : ZMod n) (x : PhaseSpace n) :
    pderivP (HamDynN N) j x = N j * x.2 j := by
  rw [pderivP, (hasFDerivAt_HamDynN N x).fderiv, HamDynND, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (((N i / 2) •
          ((x.2 i • coordP i + x.2 i • coordP i) +
            ((1 + x.1 i * x.1 i) •
                ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i) +
                  (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)) +
              ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)) •
                (0 + (x.1 i • coordQ i + x.1 i • coordQ i)))) :
            PhaseSpace n →L[ℝ] ℝ))
        ((0, Pi.single j 1) : PhaseSpace n)
      = (N i * x.2 i) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]

/-- THEOREM. Honest configuration partial: frozen `HamW`-style contribution
plus the `∂g/∂q` correction `N_j q_j (Δq_j)²`. -/
theorem pderivQ_HamDynN (N : ZMod n → ℝ) (j : ZMod n) (x : PhaseSpace n) :
    pderivQ (HamDynN N) j x
      = N (j - 1) * ((1 + x.1 (j - 1) * x.1 (j - 1)) * (x.1 j - x.1 (j - 1)))
        - N j * ((1 + x.1 j * x.1 j) * (x.1 (j + 1) - x.1 j))
        + N j * (x.1 j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) := by
  rw [pderivQ, (hasFDerivAt_HamDynN N x).fderiv, HamDynND, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (((N i / 2) •
          ((x.2 i • coordP i + x.2 i • coordP i) +
            ((1 + x.1 i * x.1 i) •
                ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i) +
                  (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)) +
              ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)) •
                (0 + (x.1 i • coordQ i + x.1 i • coordQ i)))) :
            PhaseSpace n →L[ℝ] ℝ))
        ((Pi.single j 1, 0) : PhaseSpace n)
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

theorem differentiable_HamDynN (N : ZMod n → ℝ) :
    Differentiable ℝ (HamDynN N) :=
  fun x => (hasFDerivAt_HamDynN N x).differentiableAt

/-- THEOREM (headline). Exact dynamic structure-function identity at general
`n`. Structure factor at left split point `j`. The `∂g/∂q` corrections cancel
in the Hamiltonian–Hamiltonian bracket (same telescoping as `n = 2`). -/
theorem bracket_HamDynN_HamDynN (N M : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (HamDynN N) (HamDynN M) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1)) *
          ((1 + x.1 j * x.1 j) *
            (x.2 (j + 1) * (x.1 (j + 1) - x.1 j))) := by
  simp only [bracket, pderivQ_HamDynN, pderivP_HamDynN]
  have step1 :
      (∑ j : ZMod n,
          ((N (j - 1) * ((1 + x.1 (j - 1) * x.1 (j - 1)) * (x.1 j - x.1 (j - 1)))
              - N j * ((1 + x.1 j * x.1 j) * (x.1 (j + 1) - x.1 j))
              + N j * (x.1 j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))) *
            (M j * x.2 j)
            - (N j * x.2 j) *
              (M (j - 1) * ((1 + x.1 (j - 1) * x.1 (j - 1)) * (x.1 j - x.1 (j - 1)))
                - M j * ((1 + x.1 j * x.1 j) * (x.1 (j + 1) - x.1 j))
                + M j * (x.1 j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))))))
        = ∑ j : ZMod n,
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

/-- Equivalent form with `dynamicInverseMetricN`. -/
theorem bracket_HamDynN_HamDynN' (N M : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (HamDynN N) (HamDynN M) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1)) *
          (dynamicInverseMetricN x j *
            (x.2 (j + 1) * (x.1 (j + 1) - x.1 j))) := by
  simpa [dynamicInverseMetricN, pow_two] using bracket_HamDynN_HamDynN N M x

/-- Consistency: at `n = 2`, recovers `bracket_HamDyn_HamDyn`. -/
theorem bracket_HamDynN_HamDynN_eq_two
    (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (HamDynN (n := 2) N) (HamDynN (n := 2) M) x
      = bracket (HamDyn N) (HamDyn M) x := by
  rw [HamDynN_eq_HamDyn, HamDynN_eq_HamDyn]

theorem bracket_HamDynN_recovers_bracket_HamDyn
    (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (HamDynN (n := 2) N) (HamDynN (n := 2) M) x
      = ∑ j : ZMod 2, (N j * M (j + 1) - M j * N (j + 1)) *
          (concreteDynamicInverseMetric x j *
            (x.2 (j + 1) * (x.1 (j + 1) - x.1 j))) := by
  rw [bracket_HamDynN_HamDynN_eq_two, bracket_HamDyn_HamDyn]

/-! ### Axiom receipts -/

#print axioms hasFDerivAt_HamDynN
#print axioms pderivP_HamDynN
#print axioms pderivQ_HamDynN
#print axioms differentiable_HamDynN
#print axioms bracket_HamDynN_HamDynN
#print axioms bracket_HamDynN_recovers_bracket_HamDyn

end
end DynamicStructureBracketN
end SevenGaps
end Gravity
end IndisputableMonolith
