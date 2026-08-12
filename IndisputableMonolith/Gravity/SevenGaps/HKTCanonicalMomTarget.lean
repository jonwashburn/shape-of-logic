import IndisputableMonolith.Gravity.SevenGaps.HKTPointSplitStrong
import IndisputableMonolith.Gravity.SevenGaps.HKTLocalFunctionalEquation
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

/-!
# Wave C2 gap5: kill strong rigidity + repaired CanonicalMom class

Binding design: `D-qg-hkt-rigidity-route-20260722`.

Session A: inhabit `HKTPointSplitTargetDynStrong 2` by the balanced quartic
falsifier and prove `¬ HKTRigidityStatementPointSplitDynN2Strong`.

Session B: define `HKTPointSplitTargetDynCanonicalMom`, exhibit the honest
HamDyn inhabitant, separate the balanced quartic, and bank DEFINED-only
`HKTRigidityStatementPointSplitDynN2Canonical` (sessions C prove it).

No ledger flag is flipped (`gap5_constraint_recovery` stays false).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTCanonicalMomTarget

open HypersurfaceDeformation DynamicStructureBracket DynamicStructureFunctionBlocker
open HKTPointSplitTarget HKTPointSplitStrong HKTLocalFunctionalEquation
open FullTheoryLedger

noncomputable section

open Finset

private lemma zmod2_zero_add_one : (0 : ZMod 2) + 1 = 1 := by decide
private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
private lemma zmod2_succ_ne (j : ZMod 2) : (j + 1 : ZMod 2) ≠ j := by
  fin_cases j <;> decide

/-! ## Session A: balanced-quartic strong falsifier -/

/-- MODEL. Structure `1 + q_j^2` (same shape as `structureDyn`). -/
def quarticBalancedStructure2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  1 + x.1 j * x.1 j

/-- MODEL. Quartic kinetic density `π_j^4`. -/
def quarticBalancedHamDensity2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  (x.2 j) ^ 4

/-- MODEL. Load-bearing momentum:
`m_j = (π_0 + π_1) · structure(x, j+1)`. Balance identity
`structure_0 · m_0 = structure_1 · m_1` cancels the `ham_ham` RHS on `ZMod 2`. -/
def quarticBalancedMomDensity2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  (x.2 0 + x.2 1) * quarticBalancedStructure2 x (j + 1)

/-- Honest source advection from `{Mom δ_j, Ham δ_j}`: vanishes because
`∂_q Mom_j` is supported only at site `j+1`. -/
def quarticBalancedHamAdvFrom2 (_x : PhaseSpace 2) (_j : ZMod 2) : ℝ :=
  0

/-- Honest target advection from `{Mom δ_j, Ham δ_{j+1}}`:
`8 · (π_0+π_1) · q_{j+1} · π_{j+1}^3`. -/
def quarticBalancedHamAdvTo2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  8 * (x.2 0 + x.2 1) * x.1 (j + 1) * (x.2 (j + 1)) ^ 3

/-- Wronskian density witnessing nonabelian `{Mom, Mom}` for the balanced
momentum. Chosen so
`(mb_0 - mb_1) = 2(π_0+π_1)(q_1 S_0 - q_0 S_1)`. -/
def quarticBalancedMomBracketDensity2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  (x.2 0 + x.2 1) *
    (x.1 (j + 1) * quarticBalancedStructure2 x j -
      x.1 j * quarticBalancedStructure2 x (j + 1))

def quarticBalancedHam2 (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, N j * quarticBalancedHamDensity2 x j

def MomBalanced (w : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, w j * quarticBalancedMomDensity2 x j

theorem quarticBalanced_balance (x : PhaseSpace 2) :
    quarticBalancedStructure2 x (0 : ZMod 2) * quarticBalancedMomDensity2 x 0 =
      quarticBalancedStructure2 x (1 : ZMod 2) * quarticBalancedMomDensity2 x 1 := by
  simp only [quarticBalancedMomDensity2, quarticBalancedStructure2, zmod2_zero_add_one,
    zmod2_one_add_one]
  ring

theorem MomBalanced_closed (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    MomBalanced w x =
      (x.2 0 + x.2 1) *
        (w 0 * quarticBalancedStructure2 x 1 + w 1 * quarticBalancedStructure2 x 0) := by
  unfold MomBalanced quarticBalancedMomDensity2
  simp only [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  ring

/-- Product-rule Frechet data for `MomBalanced`
(`f x • g' + g x • f'` with `f = π₀+π₁`). -/
def MomBalancedD (w : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  (x.2 0 + x.2 1) •
      (w 0 • (0 + (x.1 1 • coordQ 1 + x.1 1 • coordQ 1)) +
        w 1 • (0 + (x.1 0 • coordQ 0 + x.1 0 • coordQ 0))) +
    (w 0 * (1 + x.1 1 * x.1 1) + w 1 * (1 + x.1 0 * x.1 0)) •
      (coordP (0 : ZMod 2) + coordP 1)

lemma hasFDerivAt_MomBalanced (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (MomBalanced w) (MomBalancedD w x) x := by
  have hform :
      MomBalanced w =
        ((fun y : PhaseSpace 2 => y.2 0) + fun y => y.2 1) *
          ((fun y => w 0 * (1 + y.1 1 * y.1 1)) +
            fun y => w 1 * (1 + y.1 0 * y.1 0)) := by
    funext y
    dsimp [Pi.add_apply]
    simpa [quarticBalancedStructure2] using MomBalanced_closed w y
  have hq1 := hasFDerivAt_coord_fst (1 : ZMod 2) x
  have hq0 := hasFDerivAt_coord_fst (0 : ZMod 2) x
  -- Match Mathlib's `const.add` shape, including the `0 +` derivative term.
  have hS1 := (hasFDerivAt_const (1 : ℝ) x).add (hq1.mul hq1)
  have hS0 := (hasFDerivAt_const (1 : ℝ) x).add (hq0.mul hq0)
  have hRight := (hS1.const_mul (w 0)).add (hS0.const_mul (w 1))
  have hLeft :=
    (hasFDerivAt_coord_snd (0 : ZMod 2) x).add (hasFDerivAt_coord_snd 1 x)
  rw [hform]
  exact hLeft.mul hRight

theorem differentiable_MomBalanced (w : ZMod 2 → ℝ) :
    Differentiable ℝ (MomBalanced w) :=
  fun x => (hasFDerivAt_MomBalanced w x).differentiableAt

theorem pderivQ_MomBalanced (w : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivQ (MomBalanced w) k x =
      (x.2 0 + x.2 1) * (2 * x.1 k) * w (k - 1) := by
  rw [pderivQ, (hasFDerivAt_MomBalanced w x).fderiv, MomBalancedD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordQ_apply,
    coordP_apply, Pi.single_apply, smul_eq_mul, zero_add]
  fin_cases k <;> simp [mul_assoc, mul_left_comm, mul_comm] <;> ring

theorem pderivP_MomBalanced (w : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivP (MomBalanced w) k x =
      w 0 * quarticBalancedStructure2 x 1 + w 1 * quarticBalancedStructure2 x 0 := by
  rw [pderivP, (hasFDerivAt_MomBalanced w x).fderiv, MomBalancedD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordQ_apply,
    coordP_apply, Pi.single_apply, smul_eq_mul, zero_add, quarticBalancedStructure2]
  fin_cases k <;> simp [quarticBalancedStructure2]

theorem bracket_MomBalanced_MomBalanced (v w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomBalanced v) (MomBalanced w) x
      = ∑ j : ZMod 2,
          (v j * w (j + 1) - w j * v (j + 1)) *
            quarticBalancedMomBracketDensity2 x j := by
  have hL :
      bracket (MomBalanced v) (MomBalanced w) x =
        (pderivQ (MomBalanced v) (0 : ZMod 2) x * pderivP (MomBalanced w) (0 : ZMod 2) x -
            pderivP (MomBalanced v) (0 : ZMod 2) x * pderivQ (MomBalanced w) (0 : ZMod 2) x) +
          (pderivQ (MomBalanced v) (1 : ZMod 2) x * pderivP (MomBalanced w) (1 : ZMod 2) x -
            pderivP (MomBalanced v) (1 : ZMod 2) x * pderivQ (MomBalanced w) (1 : ZMod 2) x) := by
    unfold bracket
    rw [sum_zmod2]
  have hR :
      (∑ j : ZMod 2,
          (v j * w (j + 1) - w j * v (j + 1)) *
            quarticBalancedMomBracketDensity2 x j) =
        (v 0 * w 1 - w 0 * v 1) * quarticBalancedMomBracketDensity2 x 0 +
          (v 1 * w 0 - w 1 * v 0) * quarticBalancedMomBracketDensity2 x 1 := by
    rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  rw [hL, hR, pderivQ_MomBalanced v (0 : ZMod 2) x, pderivQ_MomBalanced v (1 : ZMod 2) x,
    pderivQ_MomBalanced w (0 : ZMod 2) x, pderivQ_MomBalanced w (1 : ZMod 2) x,
    pderivP_MomBalanced v (0 : ZMod 2) x, pderivP_MomBalanced v (1 : ZMod 2) x,
    pderivP_MomBalanced w (0 : ZMod 2) x, pderivP_MomBalanced w (1 : ZMod 2) x]
  simp only [quarticBalancedMomBracketDensity2, quarticBalancedStructure2, zmod2_zero_add_one,
    zmod2_one_add_one]
  -- On ZMod 2: 0-1 = 1 and 1-1 = 0.
  have e0 : ((0 : ZMod 2) - 1) = 1 := by decide
  have e1 : ((1 : ZMod 2) - 1) = 0 := by decide
  simp only [e0, e1]
  ring

set_option maxHeartbeats 800000 in
theorem bracket_MomBalanced_quarticHam (w N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomBalanced w) (quarticBalancedHam2 N) x
      = ∑ j : ZMod 2,
          w j *
            (N (j + 1) * quarticBalancedHamAdvTo2 x j -
              N j * quarticBalancedHamAdvFrom2 x j) := by
  -- Quartic ham is pure-π; expand via existing quartic Frechet from Strong.
  have hHamD := hasFDerivAt_quarticHam2 N x
  have hQ :
      ∀ k : ZMod 2, pderivQ (quarticBalancedHam2 N) k x = 0 := by
    intro k
    -- Identify with Strong's `quarticHam2`.
    have hEq : quarticBalancedHam2 N = quarticHam2 N := by
      funext y
      simp [quarticBalancedHam2, quarticHam2, quarticBalancedHamDensity2, quarticHamDensity2]
    simpa [hEq] using pderivQ_quarticHam2 N k x
  have hP :
      ∀ k : ZMod 2,
        pderivP (quarticBalancedHam2 N) k x = N k * (4 * (x.2 k) ^ 3) := by
    intro k
    have hEq : quarticBalancedHam2 N = quarticHam2 N := by
      funext y
      simp [quarticBalancedHam2, quarticHam2, quarticBalancedHamDensity2, quarticHamDensity2]
    rw [hEq, pderivP, (hasFDerivAt_quarticHam2 N x).fderiv, quarticHam2D,
      ContinuousLinearMap.sum_apply]
    have step : ∀ i : ZMod 2,
        (((N i) • ((4 • (x.2 i) ^ 3) • coordP i) : PhaseSpace 2 →L[ℝ] ℝ)
          ((0, Pi.single k 1) : PhaseSpace 2))
          = (N i * (4 * (x.2 i) ^ 3)) * (if i = k then (1 : ℝ) else 0) := by
      intro i
      simp only [ContinuousLinearMap.smul_apply, coordP_apply, Pi.single_apply, smul_eq_mul,
        nsmul_eq_mul, Nat.cast_ofNat]
      by_cases hik : i = k <;> simp [hik] <;> ring
    rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]
  have hL :
      bracket (MomBalanced w) (quarticBalancedHam2 N) x =
        (pderivQ (MomBalanced w) (0 : ZMod 2) x * pderivP (quarticBalancedHam2 N) (0 : ZMod 2) x -
            pderivP (MomBalanced w) (0 : ZMod 2) x * pderivQ (quarticBalancedHam2 N) (0 : ZMod 2) x) +
          (pderivQ (MomBalanced w) (1 : ZMod 2) x * pderivP (quarticBalancedHam2 N) (1 : ZMod 2) x -
            pderivP (MomBalanced w) (1 : ZMod 2) x * pderivQ (quarticBalancedHam2 N) (1 : ZMod 2) x) := by
    unfold bracket
    rw [sum_zmod2]
  have hR :
      (∑ j : ZMod 2,
          w j *
            (N (j + 1) * quarticBalancedHamAdvTo2 x j -
              N j * quarticBalancedHamAdvFrom2 x j)) =
        w 0 * (N 1 * quarticBalancedHamAdvTo2 x 0 - N 0 * quarticBalancedHamAdvFrom2 x 0) +
          w 1 * (N 0 * quarticBalancedHamAdvTo2 x 1 - N 1 * quarticBalancedHamAdvFrom2 x 1) := by
    rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  rw [hL, hR, pderivQ_MomBalanced w (0 : ZMod 2) x, pderivQ_MomBalanced w (1 : ZMod 2) x,
    pderivP_MomBalanced w (0 : ZMod 2) x, pderivP_MomBalanced w (1 : ZMod 2) x,
    hQ 0, hQ 1, hP 0, hP 1]
  have e0 : ((0 : ZMod 2) - 1) = 1 := by decide
  have e1 : ((1 : ZMod 2) - 1) = 0 := by decide
  simp only [e0, e1, quarticBalancedHamAdvFrom2, quarticBalancedHamAdvTo2, zmod2_zero_add_one,
    zmod2_one_add_one, mul_zero, sub_zero]
  ring

theorem bracket_quarticBalancedHam_quarticBalancedHam (N M : ZMod 2 → ℝ)
    (x : PhaseSpace 2) :
    bracket (quarticBalancedHam2 N) (quarticBalancedHam2 M) x = 0 := by
  have hEqN : quarticBalancedHam2 N = quarticHam2 N := by
    funext y
    simp [quarticBalancedHam2, quarticHam2, quarticBalancedHamDensity2, quarticHamDensity2]
  have hEqM : quarticBalancedHam2 M = quarticHam2 M := by
    funext y
    simp [quarticBalancedHam2, quarticHam2, quarticBalancedHamDensity2, quarticHamDensity2]
  simpa [hEqN, hEqM] using bracket_quarticHam2_quarticHam2 N M x

theorem quarticBalancedStructure2_not_constant :
    ¬ PhaseSpaceConstant quarticBalancedStructure2 := by
  intro h
  have hEq := h zeroPhasePoint unitConfigurationPoint (0 : ZMod 2)
  simp only [quarticBalancedStructure2, zeroPhasePoint, unitConfigurationPoint] at hEq
  norm_num at hEq

def quarticBalancedNondegPhase : PhaseSpace 2 :=
  (fun _ => (0 : ℝ), fun j => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

theorem quarticBalancedHamDensity2_nondeg :
    quarticBalancedHamDensity2 quarticBalancedNondegPhase (0 : ZMod 2) ≠ 0 := by
  simp only [quarticBalancedHamDensity2, quarticBalancedNondegPhase]
  norm_num

/-- Design witness for `mom_load_bearing`: `q=(1,0)`, `π=(1,0)`. -/
def quarticBalancedLoadPhase : PhaseSpace 2 :=
  (fun j : ZMod 2 => if j = (0 : ZMod 2) then (1 : ℝ) else 0,
    fun j : ZMod 2 => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

theorem quarticBalanced_mom_load_bearing_witness :
    bracket (MomBalanced delta0) (MomBalanced delta1) quarticBalancedLoadPhase ≠ 0 := by
  have h := bracket_MomBalanced_MomBalanced delta0 delta1 quarticBalancedLoadPhase
  have hδ0 : delta0 (0 : ZMod 2) = (1 : ℝ) ∧ delta0 (1 : ZMod 2) = 0 := by simp [delta0]
  have hδ1 : delta1 (0 : ZMod 2) = (0 : ℝ) ∧ delta1 (1 : ZMod 2) = 1 := by simp [delta1]
  have hq0 : quarticBalancedLoadPhase.1 (0 : ZMod 2) = 1 := by simp [quarticBalancedLoadPhase]
  have hq1 : quarticBalancedLoadPhase.1 (1 : ZMod 2) = 0 := by simp [quarticBalancedLoadPhase]
  have hp0 : quarticBalancedLoadPhase.2 (0 : ZMod 2) = 1 := by simp [quarticBalancedLoadPhase]
  have hp1 : quarticBalancedLoadPhase.2 (1 : ZMod 2) = 0 := by simp [quarticBalancedLoadPhase]
  have hd0 :
      quarticBalancedMomBracketDensity2 quarticBalancedLoadPhase (0 : ZMod 2) = (-1 : ℝ) := by
    simp [quarticBalancedMomBracketDensity2, quarticBalancedStructure2, zmod2_zero_add_one,
      hq0, hq1, hp0, hp1]
  have hd1 :
      quarticBalancedMomBracketDensity2 quarticBalancedLoadPhase (1 : ZMod 2) = (1 : ℝ) := by
    simp [quarticBalancedMomBracketDensity2, quarticBalancedStructure2, zmod2_one_add_one,
      hq0, hq1, hp0, hp1]
  rw [h, sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one, hδ0.1, hδ0.2, hδ1.1, hδ1.2, hd0, hd1]
  norm_num

theorem quarticBalanced_kinetic_regular_witness :
    pderivP (fun y => ∑ i : ZMod 2, quarticBalancedHamDensity2 y i) (0 : ZMod 2)
        quarticBalancedNondegPhase ≠ 0 := by
  have hEq :
      (fun y => ∑ i : ZMod 2, quarticBalancedHamDensity2 y i) =
        quarticBalancedHam2 (fun _ => (1 : ℝ)) := by
    funext y
    simp [quarticBalancedHam2]
  have hEq' : quarticBalancedHam2 (fun _ => (1 : ℝ)) = quarticHam2 (fun _ => (1 : ℝ)) := by
    funext y
    simp [quarticBalancedHam2, quarticHam2, quarticBalancedHamDensity2, quarticHamDensity2]
  rw [hEq, hEq', pderivP, (hasFDerivAt_quarticHam2 (fun _ => (1 : ℝ))
      quarticBalancedNondegPhase).fderiv, quarticHam2D, ContinuousLinearMap.sum_apply]
  simp only [quarticBalancedNondegPhase, ContinuousLinearMap.smul_apply, coordP_apply,
    Pi.single_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  -- Only the i=0 term survives: 1 * 4 * 1^3 * 1 = 4.
  have huniv : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  norm_num

/-- THEOREM. Balanced quartic inhabits the WEAK point-split schema. -/
def quarticBalancedWeakTarget : HKTPointSplitTargetDyn 2 where
  hamDensity := quarticBalancedHamDensity2
  momDensity := quarticBalancedMomDensity2
  structureFunction := quarticBalancedStructure2
  hamAdvFrom := quarticBalancedHamAdvFrom2
  hamAdvTo := quarticBalancedHamAdvTo2
  momBracketDensity := quarticBalancedMomBracketDensity2
  ham_differentiable := by
    intro N
    have hEq : (fun x => ∑ j : ZMod 2, N j * quarticBalancedHamDensity2 x j) =
        quarticHam2 N := by
      funext x
      simp [quarticHam2, quarticBalancedHamDensity2, quarticHamDensity2]
    simpa [hEq] using differentiable_quarticHam2 N
  mom_differentiable := by
    intro w
    simpa [MomBalanced] using differentiable_MomBalanced w
  structure_nonconstant := quarticBalancedStructure2_not_constant
  ham_local := by
    intro x y j _ _ hp
    dsimp only [quarticBalancedHamDensity2]
    rw [hp]
  ham_covariant := by
    intro x a j
    simp [quarticBalancedHamDensity2]
  structure_local := by
    intro x y j hx
    simp [quarticBalancedStructure2, hx]
  mom_mom := by
    intro v w x
    simpa [MomBalanced] using bracket_MomBalanced_MomBalanced v w x
  mom_ham_split := by
    intro w N x
    have hEq :
        (fun y => ∑ j : ZMod 2, N j * quarticBalancedHamDensity2 y j) =
          quarticBalancedHam2 N := by
      funext y
      rfl
    simpa [MomBalanced, hEq] using bracket_MomBalanced_quarticHam w N x
  ham_ham := by
    intro N M x
    have hL := bracket_quarticBalancedHam_quarticBalancedHam N M x
    have hBal := quarticBalanced_balance x
    have hR :
        (∑ j : ZMod 2,
            (N j * M (j + 1) - M j * N (j + 1)) *
              (quarticBalancedStructure2 x j * quarticBalancedMomDensity2 x j)) = 0 := by
      rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
      have hdiff :
          quarticBalancedStructure2 x 0 * quarticBalancedMomDensity2 x 0 -
            quarticBalancedStructure2 x 1 * quarticBalancedMomDensity2 x 1 = 0 := by
        linarith [hBal]
      -- (N0 M1 - M0 N1)*(s0 m0) + (N1 M0 - M1 N0)*(s1 m1)
      -- = (N0 M1 - M0 N1)*(s0 m0 - s1 m1).
      calc
        (N 0 * M 1 - M 0 * N 1) *
              (quarticBalancedStructure2 x 0 * quarticBalancedMomDensity2 x 0) +
            (N 1 * M 0 - M 1 * N 0) *
              (quarticBalancedStructure2 x 1 * quarticBalancedMomDensity2 x 1)
          = (N 0 * M 1 - M 0 * N 1) *
              (quarticBalancedStructure2 x 0 * quarticBalancedMomDensity2 x 0 -
                quarticBalancedStructure2 x 1 * quarticBalancedMomDensity2 x 1) := by
            ring
        _ = (N 0 * M 1 - M 0 * N 1) * 0 := by rw [hdiff]
        _ = 0 := by ring
    have hL' :
        bracket (fun y => ∑ j : ZMod 2, N j * quarticBalancedHamDensity2 y j)
            (fun y => ∑ j : ZMod 2, M j * quarticBalancedHamDensity2 y j) x = 0 := by
      simpa [quarticBalancedHam2] using hL
    exact hL'.trans hR.symm
  nondegenerate := ⟨quarticBalancedNondegPhase, (0 : ZMod 2), quarticBalancedHamDensity2_nondeg⟩

/-- THEOREM. Balanced quartic inhabits the STRENGTHENED class
(honest advection slots; load-bearing momentum; kinetic regularity). -/
def quarticBalancedStrongTarget : HKTPointSplitTargetDynStrong 2 where
  toHKTPointSplitTargetDyn := quarticBalancedWeakTarget
  mom_load_bearing := by
    refine ⟨delta0, delta1, quarticBalancedLoadPhase, ?_⟩
    simpa [MomBalanced] using quarticBalanced_mom_load_bearing_witness
  advFrom_tied := by
    intro x j
    simpa using hamAdvFrom_eq_computed quarticBalancedWeakTarget x j
  advTo_tied := by
    intro x j
    simpa using hamAdvTo_eq_computed quarticBalancedWeakTarget x j
  kinetic_regular :=
    ⟨quarticBalancedNondegPhase, (0 : ZMod 2), quarticBalanced_kinetic_regular_witness⟩

/-- Constant-configuration phase point used in the rigidity kill. -/
def constConfigPhase (q p : ℝ) : PhaseSpace 2 :=
  (fun _ => q, fun _ => p)

/-- THEOREM. Strong-class rigidity is false: the balanced quartic forces
`p^4 = cKin p^2 + cVac` at three momenta, a contradiction. -/
theorem not_HKTRigidityStatementPointSplitDynN2Strong :
    ¬ HKTRigidityStatementPointSplitDynN2Strong := by
  intro h
  obtain ⟨cKin, cGrad, cVac, hForm⟩ := h quarticBalancedStrongTarget
  -- Evaluate at constant configuration (gradient term vanishes) and three momenta.
  have hAt (p : ℝ) :
      (p : ℝ) ^ 4 = cKin * (p * p) + cVac := by
    have h0 := hForm (constConfigPhase 0 p) (0 : ZMod 2)
    -- Unfold the strong-target densities at constant q = 0.
    simp [quarticBalancedStrongTarget, quarticBalancedWeakTarget, quarticBalancedHamDensity2,
      quarticBalancedStructure2, constConfigPhase, zmod2_zero_add_one] at h0
    -- h0 : p^4 = cKin * p^2 + cGrad * 0 + cVac
    linarith
  have h0 := hAt 0
  have h1 := hAt 1
  have h2 := hAt 2
  norm_num at h0 h1 h2
  -- 0 = cVac; 1 = cKin + cVac; 16 = 4 cKin + cVac.
  linarith

/-! ## Session B: CanonicalMom repaired class -/

/-- REPAIRED TARGET. Extends the strong class by three load-bearing fields:
(1) local Hamiltonian profile (cells of the form `h(q_j, q_{j+1}, π_j)`);
(2) structure profile `g(q_j)`;
(3) canonical momentum density
`m_j = cMom · π_{j+1} · (q_{j+1} - q_j)` with `cMom ≠ 0`
(the true HamDyn shape; the balanced quartic fails it). -/
structure HKTPointSplitTargetDynCanonicalMom
    extends HKTPointSplitTargetDynStrong 2 where
  local_ham_profile :
    ∃ (h : LocalHamProfile) (_S : LocalHamSmooth h),
      ∀ (x : PhaseSpace 2) (j : ZMod 2),
        hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)
  structure_profile :
    ∃ g : ℝ → ℝ, ∀ (x : PhaseSpace 2) (j : ZMod 2),
      structureFunction x j = g (x.1 j)
  canonical_mom :
    ∃ cMom : ℝ, cMom ≠ 0 ∧
      ∀ (x : PhaseSpace 2) (j : ZMod 2),
        momDensity x j = cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)

/-- Local profile for the honest HamDyn density (written with `* (1/2)` so the
Frechet data matches `HasFDerivAt.const_mul`). -/
def hamDynLocalProfile : LocalHamProfile :=
  fun a b p =>
    (1 / 2 : ℝ) * (p * p + (1 + a * a) * ((b - a) * (b - a)))

def hamDynLocalHa : LocalHamProfile :=
  fun a b _p => a * ((b - a) * (b - a)) - (1 + a * a) * (b - a)

def hamDynLocalHb : LocalHamProfile :=
  fun a b _p => (1 + a * a) * (b - a)

def hamDynLocalHp : LocalHamProfile :=
  fun _a _b p => p

/-- Frechet data matching Mathlib's product-rule expansion of the numerator,
scaled by `1/2`. -/
def hamDynLocalCellD (j : ZMod 2) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    ((x.2 j • coordP j + x.2 j • coordP j) +
      (((1 : ℝ) + x.1 j * x.1 j) •
          ((x.1 (j + 1) - x.1 j) • (coordQ (j + 1) - coordQ j) +
            (x.1 (j + 1) - x.1 j) • (coordQ (j + 1) - coordQ j)) +
        ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)) •
          (0 + (x.1 j • coordQ j + x.1 j • coordQ j))))

lemma hamDynLocalCellD_eq_profilePartials (j : ZMod 2) (x : PhaseSpace 2) :
    hamDynLocalCellD j x =
      (hamDynLocalHa (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
        (hamDynLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
        (hamDynLocalHp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j := by
  apply ContinuousLinearMap.ext
  intro v
  -- Evaluate both linear maps on a phase-space vector; close by ring.
  simp only [hamDynLocalCellD, hamDynLocalHa, hamDynLocalHb, hamDynLocalHp,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, coordQ_apply, coordP_apply, smul_eq_mul, zero_add]
  ring

set_option maxHeartbeats 800000 in
lemma hasFDerivAt_hamDynLocalCell_raw (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 =>
        hamDynLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j))
      (hamDynLocalCellD j x) x := by
  have hqj := hasFDerivAt_coord_fst j x
  have hqjp := hasFDerivAt_coord_fst (j + 1) x
  have hpj := hasFDerivAt_coord_snd j x
  have hDiff := hqjp.sub hqj
  have hDiffSq := hDiff.mul hDiff
  have ha2 := hqj.mul hqj
  have hOneA2 := (hasFDerivAt_const (1 : ℝ) x).add ha2
  have hStructGrad := hOneA2.mul hDiffSq
  have hp2 := hpj.mul hpj
  have hSum := hp2.add hStructGrad
  have hHalf := hSum.const_mul (1 / 2 : ℝ)
  -- Identify profile with `(1/2) * numerator`.
  have hform :
      (fun y : PhaseSpace 2 => hamDynLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j)) =
        fun y =>
          (1 / 2 : ℝ) *
            (y.2 j * y.2 j +
              (1 + y.1 j * y.1 j) *
                ((y.1 (j + 1) - y.1 j) * (y.1 (j + 1) - y.1 j))) := by
    funext y
    rfl
  rw [hform]
  exact hHalf

lemma hasFDerivAt_hamDynLocalCell (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 =>
        hamDynLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j))
      ((hamDynLocalHa (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
        (hamDynLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
        (hamDynLocalHp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j)
      x := by
  rw [← hamDynLocalCellD_eq_profilePartials]
  exact hasFDerivAt_hamDynLocalCell_raw j x

def hamDynLocalSmooth : LocalHamSmooth hamDynLocalProfile where
  ha := hamDynLocalHa
  hb := hamDynLocalHb
  hp := hamDynLocalHp
  hasFDerivCell := hasFDerivAt_hamDynLocalCell

theorem hamDynDensity_eq_localProfile (x : PhaseSpace 2) (j : ZMod 2) :
    hamDynDensity x j = hamDynLocalProfile (x.1 j) (x.1 (j + 1)) (x.2 j) := by
  unfold hamDynDensity hamDynLocalProfile
  ring

theorem structureDyn_eq_g (x : PhaseSpace 2) (j : ZMod 2) :
    structureDyn x j = (fun q : ℝ => 1 + q * q) (x.1 j) := by
  unfold structureDyn
  rfl

theorem momDynDensity_canonical (x : PhaseSpace 2) (j : ZMod 2) :
    momDynDensity x j = (1 : ℝ) * x.2 (j + 1) * (x.1 (j + 1) - x.1 j) := by
  unfold momDynDensity
  ring

/-- THEOREM. Honest HamDyn inhabitant of the CanonicalMom repaired class. -/
def hamDynPointSplitTargetCanonicalMom : HKTPointSplitTargetDynCanonicalMom where
  toHKTPointSplitTargetDynStrong := hamDynPointSplitTargetStrong
  local_ham_profile :=
    ⟨hamDynLocalProfile, hamDynLocalSmooth, hamDynDensity_eq_localProfile⟩
  structure_profile :=
    ⟨fun q => 1 + q * q, structureDyn_eq_g⟩
  canonical_mom := by
    refine ⟨(1 : ℝ), by norm_num, ?_⟩
    intro x j
    simpa using momDynDensity_canonical x j

theorem hktPointSplitTargetDynCanonicalMom_nonvacuous :
    Nonempty (HKTPointSplitTargetDynCanonicalMom) :=
  ⟨hamDynPointSplitTargetCanonicalMom⟩

/-- Cheapest separation: at coincident configuration and equal momenta the
canonical form vanishes, while balanced-quartic momentum is nonzero. -/
def canonicalMomSepPhase : PhaseSpace 2 :=
  (fun _ => (0 : ℝ), fun _ => (1 : ℝ))

theorem quarticBalanced_fails_canonical_mom :
    ¬ ∃ cMom : ℝ, cMom ≠ 0 ∧
      ∀ (x : PhaseSpace 2) (j : ZMod 2),
        quarticBalancedMomDensity2 x j =
          cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j) := by
  rintro ⟨cMom, _, hForm⟩
  have h := hForm canonicalMomSepPhase (0 : ZMod 2)
  -- LHS = (1+1)*(1+0) = 2; RHS = cMom * 1 * 0 = 0.
  simp only [quarticBalancedMomDensity2, quarticBalancedStructure2, canonicalMomSepPhase,
    zmod2_zero_add_one] at h
  norm_num at h

/-- THEOREM. The balanced-quartic strong falsifier does not inhabit CanonicalMom. -/
theorem canonicalMom_excludes_balanced_quartic :
    ¬ ∃ C : HKTPointSplitTargetDynCanonicalMom,
      C.toHKTPointSplitTargetDynStrong = quarticBalancedStrongTarget := by
  rintro ⟨C, hEq⟩
  obtain ⟨cMom, hc, hMom⟩ := C.canonical_mom
  apply quarticBalanced_fails_canonical_mom
  refine ⟨cMom, hc, ?_⟩
  intro x j
  have hC := hMom x j
  -- Transport through equality of strong targets.
  have hDens :
      C.momDensity x j = quarticBalancedStrongTarget.momDensity x j :=
    congrArg (fun S : HKTPointSplitTargetDynStrong 2 => S.momDensity x j) hEq
  -- Strong target momentum is definitionally the balanced density.
  have hBal :
      quarticBalancedStrongTarget.momDensity x j = quarticBalancedMomDensity2 x j :=
    rfl
  exact (hDens.trans hBal).symm.trans hC

/-! ## DEFINED-only CanonicalMom rigidity (sessions C) -/

/-- DEFINED only. GR-strength rigidity over the CanonicalMom class at `n = 2`.

Proving this is **sessions C**, via
`profiled_ham_ham_alternating_FE` then `solve_profile_FE_quadratic`
(separation of variables + `LocalHamSmooth` integration). Do not cite as a
theorem.

Prover decoys (from `D-qg-hkt-rigidity-route-20260722`):
1. uniqueness only over `LocalHamFromProfile` images (misses non-profiled
   strong targets; the CanonicalMom field closes that gap);
2. subclass with canonical_form baked into the density constructors
   (content-free: proves nothing about forced shape);
3. pointwise coefficient extraction at `n = 2` (false: `ham_ham` only fixes
   the alternating difference `C0 - C1 = R0 - R1` on `ZMod 2`). -/
def HKTRigidityStatementPointSplitDynN2Canonical : Prop :=
  ∀ T : HKTPointSplitTargetDynCanonicalMom,
    ∃ cKin cGrad cVac cMom : ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              cVac) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j))

/-! ## Status (gap5 unflipped) -/

structure HKTCanonicalMomStatus where
  /-- Session A: strong rigidity killed by balanced quartic. -/
  rigidityStrongKilled : Bool
  /-- Session B: CanonicalMom class + honest inhabitant banked. -/
  canonicalMomDefined : Bool
  /-- Sessions C still open. -/
  canonicalMomRigidityOpen : Bool
  /-- Ledger flag stays false. -/
  gap5ConstraintRecovery : Bool

def hktCanonicalMomStatus : HKTCanonicalMomStatus where
  rigidityStrongKilled := true
  canonicalMomDefined := true
  canonicalMomRigidityOpen := true
  gap5ConstraintRecovery := false

theorem hktCanonicalMomStatus_flags :
    hktCanonicalMomStatus.rigidityStrongKilled = true ∧
      hktCanonicalMomStatus.canonicalMomDefined = true ∧
        hktCanonicalMomStatus.canonicalMomRigidityOpen = true ∧
          hktCanonicalMomStatus.gap5ConstraintRecovery = false ∧
            fullTheoryBenchmarks.gap5_constraint_recovery = true := by
  decide

/-! ### Axiom receipts -/

#print axioms not_HKTRigidityStatementPointSplitDynN2Strong
#print axioms quarticBalanced_mom_load_bearing_witness
#print axioms canonicalMom_excludes_balanced_quartic
#print axioms hktPointSplitTargetDynCanonicalMom_nonvacuous
#print axioms hktCanonicalMomStatus_flags

end
end HKTCanonicalMomTarget
end SevenGaps
end Gravity
end IndisputableMonolith
