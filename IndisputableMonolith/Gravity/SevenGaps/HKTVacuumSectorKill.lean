import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidityPDE
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

/-!
# Wave C3 gap5: vacuum-sector kill of unconditioned CanonicalMom rigidity

Binding: `D-qg-hkt-rigidity-gauge-scope-20260723` (Codex cross-family
adjudication 2026-07-23; fork resolved as branch A).

The unconditioned Prop `HKTRigidityStatementPointSplitDynN2Canonical` is
FALSE. Killer: vacuum-shift density at `n = 2`

  h(a,b,p) = (1/2)·(p² + (1+a²)(b-a)²) + a²
  g(a) = 1 + a²
  mⱼ = π_{j+1}·(q_{j+1}-qⱼ), cMom = 1

The ham_ham alternating FE is blind to the zero-gradient vacuum term `a²`;
tied advection slots record the computed Mom–Ham brackets (contentless as a
constraint); `mom_mom`, `mom_load_bearing`, `kinetic_regular`, and
`structure_nonconstant` hold as for HamDyn. The rigidity conclusion forces a
constant vacuum `cVac`, while this density evaluates at coincident
configurations to `q²` (nonconstant).

`sqrtAffineProfile` does **not** lift to CanonicalMom (its FE forces `g`
constant, violating `structure_nonconstant`); it is not the kill.

Repaired terminal (DEFINED only): `HKTRigidityModVacuumStatementN2`.
Whether `structure_nonconstant` + FE forces the kinetic/gradient sectors
remains OPEN mathematics.

Do NOT flip `gap5_constraint_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTVacuumSectorKill

open HypersurfaceDeformation DynamicStructureBracket DynamicStructureFunctionBlocker
open HKTPointSplitTarget HKTPointSplitStrong HKTLocalFunctionalEquation
open HKTCanonicalMomTarget HKTCanonicalMomRigidity FullTheoryLedger

noncomputable section

open Finset

private lemma zmod2_zero_add_one : (0 : ZMod 2) + 1 = 1 := by decide
private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-! ## Vacuum-shift densities -/

/-- MODEL. HamDyn density plus vacuum shift `qⱼ²`. -/
def vacuumShiftHamDensity (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  hamDynDensity x j + x.1 j * x.1 j

/-- Local profile: `h(a,b,p) = (1/2)·(p² + (1+a²)(b-a)²) + a²`. -/
def vacuumShiftLocalProfile : LocalHamProfile :=
  fun a b p => hamDynLocalProfile a b p + a * a

def vacuumShiftLocalHa : LocalHamProfile :=
  fun a b p => hamDynLocalHa a b p + (2 : ℝ) * a

def vacuumShiftLocalHb : LocalHamProfile := hamDynLocalHb

def vacuumShiftLocalHp : LocalHamProfile := hamDynLocalHp

/-- Source advection unchanged by the vacuum shift (Vac has vanishing π-partial). -/
def vacuumShiftHamAdvFrom (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  hamDynAdvFrom x j

/-- Target advection: HamDyn slot plus vacuum correction
`-2 · (q_{j+1}-qⱼ) · q_{j+1}`. -/
def vacuumShiftHamAdvTo (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  hamDynAdvTo x j - (2 : ℝ) * (x.1 (j + 1) - x.1 j) * x.1 (j + 1)

theorem vacuumShiftDensity_eq_localProfile (x : PhaseSpace 2) (j : ZMod 2) :
    vacuumShiftHamDensity x j =
      vacuumShiftLocalProfile (x.1 j) (x.1 (j + 1)) (x.2 j) := by
  unfold vacuumShiftHamDensity vacuumShiftLocalProfile hamDynDensity hamDynLocalProfile
  ring

/-! ## Vacuum smear and Frechet data -/

def VacSmear (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, N j * (x.1 j * x.1 j)

def VacSmearD (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  ∑ j : ZMod 2, (N j) • (x.1 j • coordQ j + x.1 j • coordQ j)

lemma hasFDerivAt_VacSmear (N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (VacSmear N) (VacSmearD N x) x := by
  unfold VacSmear VacSmearD
  exact HasFDerivAt.fun_sum fun j _ =>
    ((hasFDerivAt_coord_fst j x).mul (hasFDerivAt_coord_fst j x)).const_mul (N j)

theorem pderivQ_VacSmear (N : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivQ (VacSmear N) k x = (2 : ℝ) * N k * x.1 k := by
  rw [pderivQ, (hasFDerivAt_VacSmear N x).fderiv, VacSmearD,
    ContinuousLinearMap.sum_apply]
  have step : ∀ j : ZMod 2,
      (((N j) • (x.1 j • coordQ j + x.1 j • coordQ j) : PhaseSpace 2 →L[ℝ] ℝ)
          ((Pi.single k 1, 0) : PhaseSpace 2))
        = ((2 : ℝ) * N j * x.1 j) * (if j = k then (1 : ℝ) else 0) := by
    intro j
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, coordQ_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases hjk : j = k <;> (simp [hjk]; try ring)
  rw [Finset.sum_congr rfl fun j _ => step j, sum_mul_ite]

theorem pderivP_VacSmear (N : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivP (VacSmear N) k x = 0 := by
  rw [pderivP, (hasFDerivAt_VacSmear N x).fderiv, VacSmearD,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [coordQ]

def HamVac (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, N j * vacuumShiftHamDensity x j

theorem HamVac_eq_HamDyn_add_Vac (N : ZMod 2 → ℝ) :
    HamVac N = fun x => HamDyn N x + VacSmear N x := by
  funext x
  unfold HamVac VacSmear vacuumShiftHamDensity
  have hsum :
      (∑ j : ZMod 2, N j * (hamDynDensity x j + x.1 j * x.1 j)) =
        (∑ j : ZMod 2, N j * hamDynDensity x j) +
          ∑ j : ZMod 2, N j * (x.1 j * x.1 j) := by
    simp only [mul_add, sum_add_distrib]
  rw [hsum]
  have hDyn : (∑ j : ZMod 2, N j * hamDynDensity x j) = HamDyn N x := by
    simpa using (congrArg (fun F : PhaseSpace 2 → ℝ => F x) (hamDynDensity_smear N))
  rw [hDyn]

theorem differentiable_HamVac (N : ZMod 2 → ℝ) :
    Differentiable ℝ (HamVac N) := by
  intro x
  have hEq := HamVac_eq_HamDyn_add_Vac N
  rw [hEq]
  exact ((differentiable_HamDyn N x).add (hasFDerivAt_VacSmear N x).differentiableAt)

/-! ## LocalHamSmooth for the vacuum profile -/

def vacuumShiftLocalCellD (j : ZMod 2) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  hamDynLocalCellD j x + ((2 : ℝ) * x.1 j) • coordQ j

lemma vacuumShiftLocalCellD_eq_profilePartials (j : ZMod 2) (x : PhaseSpace 2) :
    vacuumShiftLocalCellD j x =
      (vacuumShiftLocalHa (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
        (vacuumShiftLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
        (vacuumShiftLocalHp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j := by
  -- Start from the HamDyn identity and add the vacuum Frechet term.
  have h := hamDynLocalCellD_eq_profilePartials j x
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : PhaseSpace 2 →L[ℝ] ℝ => L v) h
  simp only [vacuumShiftLocalCellD, vacuumShiftLocalHa, vacuumShiftLocalHb,
    vacuumShiftLocalHp, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, smul_eq_mul] at hv ⊢
  simp only [hamDynLocalHa, hamDynLocalHb, hamDynLocalHp] at hv ⊢
  linarith [hv]

set_option maxHeartbeats 800000 in
lemma hasFDerivAt_vacuumShiftLocalCell_raw (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 =>
        vacuumShiftLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j))
      (vacuumShiftLocalCellD j x) x := by
  have hDyn := hasFDerivAt_hamDynLocalCell_raw j x
  have hVac :=
    ((hasFDerivAt_coord_fst j x).mul (hasFDerivAt_coord_fst j x))
  have hform :
      (fun y : PhaseSpace 2 =>
          vacuumShiftLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j)) =
        (fun y => hamDynLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j)) +
          fun y => y.1 j * y.1 j := by
    funext y
    rfl
  rw [hform]
  have hAdd := hDyn.add hVac
  -- Match derivative: hamDynLocalCellD + (q·coordQ + q·coordQ) = vacuumShiftLocalCellD.
  convert hAdd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [vacuumShiftLocalCellD, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, coordQ_apply, smul_eq_mul]
  ring

lemma hasFDerivAt_vacuumShiftLocalCell (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 =>
        vacuumShiftLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j))
      ((vacuumShiftLocalHa (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
        (vacuumShiftLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
        (vacuumShiftLocalHp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j)
      x := by
  rw [← vacuumShiftLocalCellD_eq_profilePartials]
  exact hasFDerivAt_vacuumShiftLocalCell_raw j x

def vacuumShiftLocalSmooth : LocalHamSmooth vacuumShiftLocalProfile where
  ha := vacuumShiftLocalHa
  hb := vacuumShiftLocalHb
  hp := vacuumShiftLocalHp
  hasFDerivCell := hasFDerivAt_vacuumShiftLocalCell

/-! ## Bracket calculus -/

theorem bracket_MomDyn_VacSmear (w N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomDyn w) (VacSmear N) x =
      (2 : ℝ) * (x.1 1 - x.1 0) *
        (w 1 * N 0 * x.1 0 - w 0 * N 1 * x.1 1) := by
  have hL :
      bracket (MomDyn w) (VacSmear N) x =
        (pderivQ (MomDyn w) (0 : ZMod 2) x * pderivP (VacSmear N) (0 : ZMod 2) x -
            pderivP (MomDyn w) (0 : ZMod 2) x * pderivQ (VacSmear N) (0 : ZMod 2) x) +
          (pderivQ (MomDyn w) (1 : ZMod 2) x * pderivP (VacSmear N) (1 : ZMod 2) x -
            pderivP (MomDyn w) (1 : ZMod 2) x * pderivQ (VacSmear N) (1 : ZMod 2) x) := by
    unfold bracket
    rw [sum_zmod2]
  rw [hL, pderivQ_MomDyn_zero w x, pderivQ_MomDyn_one w x, pderivP_MomDyn_zero w x,
    pderivP_MomDyn_one w x, pderivQ_VacSmear N (0 : ZMod 2) x, pderivQ_VacSmear N (1 : ZMod 2) x,
    pderivP_VacSmear N (0 : ZMod 2) x, pderivP_VacSmear N (1 : ZMod 2) x]
  ring

set_option maxHeartbeats 800000 in
theorem bracket_MomDyn_HamVac (w N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomDyn w) (HamVac N) x
      = ∑ j : ZMod 2,
          w j *
            (N (j + 1) * vacuumShiftHamAdvTo x j -
              N j * vacuumShiftHamAdvFrom x j) := by
  have hFun : HamVac N = fun y => HamDyn N y + VacSmear N y :=
    HamVac_eq_HamDyn_add_Vac N
  have hDiffDyn : DifferentiableAt ℝ (HamDyn N) x := differentiable_HamDyn N x
  have hDiffVac : DifferentiableAt ℝ (VacSmear N) x :=
    (hasFDerivAt_VacSmear N x).differentiableAt
  have hBracket :
      bracket (MomDyn w) (HamVac N) x =
        bracket (MomDyn w) (HamDyn N) x + bracket (MomDyn w) (VacSmear N) x := by
    rw [hFun]
    exact HypersurfaceDeformation.bracket_add_right (n := 2) (MomDyn w) hDiffDyn hDiffVac
  have hDyn := bracket_MomDyn_HamDyn w N x
  have hVac := bracket_MomDyn_VacSmear w N x
  have hR :
      (∑ j : ZMod 2,
          w j *
            (N (j + 1) * vacuumShiftHamAdvTo x j -
              N j * vacuumShiftHamAdvFrom x j)) =
        w 0 * (N 1 * vacuumShiftHamAdvTo x 0 - N 0 * vacuumShiftHamAdvFrom x 0) +
          w 1 * (N 0 * vacuumShiftHamAdvTo x 1 - N 1 * vacuumShiftHamAdvFrom x 1) := by
    rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  have hR' :
      w 0 * (N 1 * vacuumShiftHamAdvTo x 0 - N 0 * vacuumShiftHamAdvFrom x 0) +
          w 1 * (N 0 * vacuumShiftHamAdvTo x 1 - N 1 * vacuumShiftHamAdvFrom x 1) =
        (w 0 * (N 1 * hamDynAdvTo x 0 - N 0 * hamDynAdvFrom x 0) +
            w 1 * (N 0 * hamDynAdvTo x 1 - N 1 * hamDynAdvFrom x 1)) +
          (2 : ℝ) * (x.1 1 - x.1 0) *
            (w 1 * N 0 * x.1 0 - w 0 * N 1 * x.1 1) := by
    simp only [vacuumShiftHamAdvTo, vacuumShiftHamAdvFrom, zmod2_zero_add_one,
      zmod2_one_add_one]
    ring
  have hDynSum :
      bracket (MomDyn w) (HamDyn N) x =
        w 0 * (N 1 * hamDynAdvTo x 0 - N 0 * hamDynAdvFrom x 0) +
          w 1 * (N 0 * hamDynAdvTo x 1 - N 1 * hamDynAdvFrom x 1) := by
    rw [hDyn, sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  calc
    bracket (MomDyn w) (HamVac N) x
        = bracket (MomDyn w) (HamDyn N) x + bracket (MomDyn w) (VacSmear N) x :=
          hBracket
    _ = (w 0 * (N 1 * hamDynAdvTo x 0 - N 0 * hamDynAdvFrom x 0) +
            w 1 * (N 0 * hamDynAdvTo x 1 - N 1 * hamDynAdvFrom x 1)) +
          (2 : ℝ) * (x.1 1 - x.1 0) *
            (w 1 * N 0 * x.1 0 - w 0 * N 1 * x.1 1) := by
          rw [hDynSum, hVac]
    _ = w 0 * (N 1 * vacuumShiftHamAdvTo x 0 - N 0 * vacuumShiftHamAdvFrom x 0) +
          w 1 * (N 0 * vacuumShiftHamAdvTo x 1 - N 1 * vacuumShiftHamAdvFrom x 1) :=
          hR'.symm
    _ = ∑ j : ZMod 2,
          w j *
            (N (j + 1) * vacuumShiftHamAdvTo x j -
              N j * vacuumShiftHamAdvFrom x j) := hR.symm

theorem bracket_VacSmear_VacSmear (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (VacSmear N) (VacSmear M) x = 0 := by
  simp only [bracket, pderivP_VacSmear]
  exact Finset.sum_eq_zero fun _ _ => by ring

theorem bracket_HamDyn_VacSmear (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (HamDyn N) (VacSmear M) x =
      -∑ k : ZMod 2, (2 : ℝ) * N k * x.2 k * M k * x.1 k := by
  unfold bracket
  have hterm : ∀ k : ZMod 2,
      pderivQ (HamDyn N) k x * pderivP (VacSmear M) k x -
          pderivP (HamDyn N) k x * pderivQ (VacSmear M) k x =
        -((2 : ℝ) * N k * x.2 k * M k * x.1 k) := by
    intro k
    rw [pderivP_VacSmear, pderivP_HamDyn, pderivQ_VacSmear]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_neg_distrib]

theorem bracket_VacSmear_HamDyn (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (VacSmear N) (HamDyn M) x =
      ∑ k : ZMod 2, (2 : ℝ) * M k * x.2 k * N k * x.1 k := by
  have h := bracket_HamDyn_VacSmear M N x
  have hAnti := HypersurfaceDeformation.bracket_antisymm (n := 2) (VacSmear N) (HamDyn M) x
  -- -(-(∑ 2 M π N q)) = ∑ 2 M π N q, after commuting scalars.
  calc
    bracket (VacSmear N) (HamDyn M) x
        = -bracket (HamDyn M) (VacSmear N) x := hAnti
    _ = -(-∑ k : ZMod 2, (2 : ℝ) * M k * x.2 k * N k * x.1 k) := by rw [h]
    _ = ∑ k : ZMod 2, (2 : ℝ) * M k * x.2 k * N k * x.1 k := neg_neg _

theorem bracket_HamVac_HamVac (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (HamVac N) (HamVac M) x = bracket (HamDyn N) (HamDyn M) x := by
  have hN : HamVac N = fun y => HamDyn N y + VacSmear N y :=
    HamVac_eq_HamDyn_add_Vac N
  have hM : HamVac M = fun y => HamDyn M y + VacSmear M y :=
    HamVac_eq_HamDyn_add_Vac M
  have hDiffDynN : DifferentiableAt ℝ (HamDyn N) x := differentiable_HamDyn N x
  have hDiffDynM : DifferentiableAt ℝ (HamDyn M) x := differentiable_HamDyn M x
  have hDiffVacN : DifferentiableAt ℝ (VacSmear N) x :=
    (hasFDerivAt_VacSmear N x).differentiableAt
  have hDiffVacM : DifferentiableAt ℝ (VacSmear M) x :=
    (hasFDerivAt_VacSmear M x).differentiableAt
  have hCancel :
      bracket (HamDyn N) (VacSmear M) x + bracket (VacSmear N) (HamDyn M) x = 0 := by
    rw [bracket_HamDyn_VacSmear, bracket_VacSmear_HamDyn]
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => by ring
  -- Expand both sides by bilinearity.
  calc
    bracket (HamVac N) (HamVac M) x
        = bracket (fun y => HamDyn N y + VacSmear N y)
            (fun y => HamDyn M y + VacSmear M y) x := by
          simp [hN, hM]
    _ = bracket (fun y => HamDyn N y + VacSmear N y) (HamDyn M) x +
          bracket (fun y => HamDyn N y + VacSmear N y) (VacSmear M) x :=
        HypersurfaceDeformation.bracket_add_right
          (fun y => HamDyn N y + VacSmear N y) hDiffDynM hDiffVacM
    _ = (bracket (HamDyn N) (HamDyn M) x + bracket (VacSmear N) (HamDyn M) x) +
          (bracket (HamDyn N) (VacSmear M) x + bracket (VacSmear N) (VacSmear M) x) := by
        rw [HypersurfaceDeformation.bracket_add_left (HamDyn M) hDiffDynN hDiffVacN,
          HypersurfaceDeformation.bracket_add_left (VacSmear M) hDiffDynN hDiffVacN]
    _ = bracket (HamDyn N) (HamDyn M) x +
          (bracket (HamDyn N) (VacSmear M) x + bracket (VacSmear N) (HamDyn M) x) := by
        rw [bracket_VacSmear_VacSmear, add_zero]
        abel
    _ = bracket (HamDyn N) (HamDyn M) x + 0 := by rw [hCancel]
    _ = bracket (HamDyn N) (HamDyn M) x := by ring

/-! ## Weak / strong / CanonicalMom inhabitants -/

def vacuumShiftWeakTarget : HKTPointSplitTargetDyn 2 where
  hamDensity := vacuumShiftHamDensity
  momDensity := momDynDensity
  structureFunction := structureDyn
  hamAdvFrom := vacuumShiftHamAdvFrom
  hamAdvTo := vacuumShiftHamAdvTo
  momBracketDensity := momDynBracketDensity
  ham_differentiable := by
    intro N
    have hEq : (fun x => ∑ j : ZMod 2, N j * vacuumShiftHamDensity x j) = HamVac N := by
      funext x
      rfl
    simpa [hEq] using differentiable_HamVac N
  mom_differentiable := differentiable_MomDyn
  structure_nonconstant := structureDyn_not_constant
  ham_local := by
    intro x y j hx0 hx1 hp
    dsimp only [vacuumShiftHamDensity, hamDynDensity]
    rw [hx0, hx1, hp]
  ham_covariant := by
    intro x a j
    unfold vacuumShiftHamDensity hamDynDensity
    have e1 : (j + a + 1 : ZMod 2) = j + 1 + a := by ring
    simp only [e1]
  structure_local := by
    intro x y j hx
    dsimp only [structureDyn]
    rw [hx]
  mom_mom := by
    intro v w x
    simpa [MomDyn] using bracket_MomDyn_MomDyn v w x
  mom_ham_split := by
    intro w N x
    have hEq :
        (fun y => ∑ j : ZMod 2, N j * vacuumShiftHamDensity y j) = HamVac N := by
      funext y
      rfl
    simpa [MomDyn, hEq] using bracket_MomDyn_HamVac w N x
  ham_ham := by
    intro N M x
    have hL := bracket_HamVac_HamVac N M x
    have hDyn := bracket_HamDyn_HamDyn N M x
    have hL' :
        bracket (fun y => ∑ j : ZMod 2, N j * vacuumShiftHamDensity y j)
            (fun y => ∑ j : ZMod 2, M j * vacuumShiftHamDensity y j) x =
          bracket (HamDyn N) (HamDyn M) x := by
      simpa [HamVac] using hL
    have hR :
        (∑ j : ZMod 2,
            (N j * M (j + 1) - M j * N (j + 1)) *
              (structureDyn x j * momDynDensity x j)) =
          bracket (HamDyn N) (HamDyn M) x := by
      -- Match HamDyn identity rewritten in structureDyn / momDynDensity.
      have h := hDyn
      simp only [structureDyn, momDynDensity, concreteDynamicInverseMetric, pow_two] at h ⊢
      exact h.symm
    exact hL'.trans hR.symm
  nondegenerate := by
    refine ⟨hamDynNondegPhase, (0 : ZMod 2), ?_⟩
    simp only [vacuumShiftHamDensity, hamDynDensity, hamDynNondegPhase]
    norm_num

def vacuumShiftStrongTarget : HKTPointSplitTargetDynStrong 2 where
  toHKTPointSplitTargetDyn := vacuumShiftWeakTarget
  mom_load_bearing := by
    refine ⟨delta0, delta1, momLoadBearingWitnessPhase, ?_⟩
    simpa [MomDyn] using hamDyn_mom_load_bearing_witness
  advFrom_tied := by
    intro x j
    simpa using hamAdvFrom_eq_computed vacuumShiftWeakTarget x j
  advTo_tied := by
    intro x j
    simpa using hamAdvTo_eq_computed vacuumShiftWeakTarget x j
  kinetic_regular := by
    refine ⟨hamDynNondegPhase, (0 : ZMod 2), ?_⟩
    -- Unit-lapse vacuum Ham = HamDyn 1 + VacSmear 1; π-partial of Vac vanishes.
    have hEq :
        (fun y => ∑ i : ZMod 2, vacuumShiftHamDensity y i) =
          fun y => HamDyn (fun _ => (1 : ℝ)) y + VacSmear (fun _ => (1 : ℝ)) y := by
      funext y
      have h1 : (∑ i : ZMod 2, vacuumShiftHamDensity y i) =
          HamVac (fun _ => (1 : ℝ)) y := by
        simp only [HamVac, one_mul]
      have h2 : HamVac (fun _ => (1 : ℝ)) y =
          HamDyn (fun _ => (1 : ℝ)) y + VacSmear (fun _ => (1 : ℝ)) y := by
        simpa using congrArg (fun F : PhaseSpace 2 → ℝ => F y)
          (HamVac_eq_HamDyn_add_Vac (fun _ => (1 : ℝ)))
      exact h1.trans h2
    have hDiffDyn : DifferentiableAt ℝ (HamDyn (fun _ => (1 : ℝ))) hamDynNondegPhase :=
      differentiable_HamDyn (fun _ => (1 : ℝ)) hamDynNondegPhase
    have hDiffVac : DifferentiableAt ℝ (VacSmear (fun _ => (1 : ℝ))) hamDynNondegPhase :=
      (hasFDerivAt_VacSmear (fun _ => (1 : ℝ)) hamDynNondegPhase).differentiableAt
    have hSum :
        pderivP (fun y => ∑ i : ZMod 2, vacuumShiftHamDensity y i) (0 : ZMod 2)
            hamDynNondegPhase =
          pderivP (HamDyn (fun _ => (1 : ℝ))) (0 : ZMod 2) hamDynNondegPhase +
            pderivP (VacSmear (fun _ => (1 : ℝ))) (0 : ZMod 2) hamDynNondegPhase := by
      rw [hEq]
      exact pderivP_fun_add (n := 2) hDiffDyn hDiffVac (0 : ZMod 2)
    have hPVac :
        pderivP (VacSmear (fun _ => (1 : ℝ))) (0 : ZMod 2) hamDynNondegPhase = 0 :=
      pderivP_VacSmear (fun _ => (1 : ℝ)) (0 : ZMod 2) hamDynNondegPhase
    have hPDyn :
        pderivP (HamDyn (fun _ => (1 : ℝ))) (0 : ZMod 2) hamDynNondegPhase ≠ 0 := by
      rw [pderivP_HamDyn]
      simp only [hamDynNondegPhase]
      norm_num
    -- Goal uses the weak-target field, definitionally the vacuum density.
    change pderivP (fun y => ∑ i : ZMod 2, vacuumShiftHamDensity y i) (0 : ZMod 2)
        hamDynNondegPhase ≠ 0
    rw [hSum, hPVac, add_zero]
    exact hPDyn

/-- THEOREM. Vacuum-shift density inhabits the CanonicalMom repaired class. -/
def vacuumShiftCanonicalMomTarget : HKTPointSplitTargetDynCanonicalMom where
  toHKTPointSplitTargetDynStrong := vacuumShiftStrongTarget
  local_ham_profile :=
    ⟨vacuumShiftLocalProfile, vacuumShiftLocalSmooth, vacuumShiftDensity_eq_localProfile⟩
  structure_profile :=
    ⟨fun q => 1 + q * q, structureDyn_eq_g⟩
  canonical_mom := by
    refine ⟨(1 : ℝ), by norm_num, ?_⟩
    intro x j
    simpa using momDynDensity_canonical x j

/-! ## Kill of unconditioned CanonicalMom rigidity -/

/-- Coincident configuration used in the vacuum kill: `qⱼ ≡ q`, `πⱼ ≡ 0`. -/
def coincidentPhase (q : ℝ) : PhaseSpace 2 :=
  (fun _ => q, fun _ => (0 : ℝ))

/-- THEOREM. Unconditioned CanonicalMom rigidity is false. -/
theorem not_HKTRigidityStatementPointSplitDynN2Canonical :
    ¬ HKTRigidityStatementPointSplitDynN2Canonical := by
  intro h
  obtain ⟨cKin, cGrad, cVac, cMom, _hcKin, _hcGrad, _hRel, hHam, _hMom⟩ :=
    h vacuumShiftCanonicalMomTarget
  have hAt (q : ℝ) :
      q * q = cVac := by
    have h0 := hHam (coincidentPhase q) (0 : ZMod 2)
    simp only [vacuumShiftCanonicalMomTarget, vacuumShiftStrongTarget, vacuumShiftWeakTarget,
      vacuumShiftHamDensity, hamDynDensity, structureDyn, coincidentPhase,
      zmod2_zero_add_one, sub_self, mul_zero, add_zero] at h0
    -- h0 : q² = cKin·0 + cGrad·(1+q²)·0 + cVac
    linarith
  have h0 := hAt 0
  have h1 := hAt 1
  norm_num at h0 h1
  linarith

/-! ## Repaired terminal (DEFINED only) -/

/-- DEFINED only. CanonicalMom rigidity modulo vacuum profile.

Same quantification as `HKTRigidityStatementPointSplitDynN2Canonical`, with
constant `cVac` weakened to a vacuum profile `V : ℝ → ℝ`. Do **not** cite as
a theorem: whether `structure_nonconstant` + the alternating FE forces the
kinetic/gradient sectors remains OPEN mathematics. -/
def HKTRigidityModVacuumStatementN2 : Prop :=
  ∀ T : HKTPointSplitTargetDynCanonicalMom,
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j))

/-- Honesty wall (named note). ContDiff-2 + FE alone do not force the
kinetic/gradient sectors (`sqrtAffineProfile`); that witness is blocked from
CanonicalMom only by `structure_nonconstant` (`g ≡ 1`). Superseded by C4:
`structure_nonconstant` also fails to close mod-vacuum (variable-kinetic kill
in `HKTKineticNormalizedRigidity`). -/
def Note_modVacuumSectorsRemainOpen : Prop := True

theorem note_modVacuumSectorsRemainOpen : Note_modVacuumSectorsRemainOpen := trivial

/-- C4 flip marker (bool status lives with the kill in
`HKTKineticNormalizedRigidity`; this note records the supersession). -/
def Note_modVacuumKilledInC4 : Prop := True

theorem note_modVacuumKilledInC4 : Note_modVacuumKilledInC4 := trivial

/-- ANCHOR (a). Vacuum-shift target satisfies the mod-vacuum conclusion shape. -/
theorem vacuumShift_satisfies_modVacuum :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          vacuumShiftCanonicalMomTarget.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (vacuumShiftCanonicalMomTarget.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          vacuumShiftCanonicalMomTarget.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), (1 : ℝ), fun a => a * a, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · norm_num
  · intro x j
    simp only [vacuumShiftCanonicalMomTarget, vacuumShiftStrongTarget, vacuumShiftWeakTarget,
      vacuumShiftHamDensity, hamDynDensity, structureDyn]
    ring
  · intro x j
    simp only [vacuumShiftCanonicalMomTarget, vacuumShiftStrongTarget, vacuumShiftWeakTarget,
      momDynDensity]
    ring

/-- ANCHOR (b). Honest HamDyn CanonicalMom target satisfies the mod-vacuum shape
(constant vacuum `V ≡ 0`). -/
theorem hamDyn_satisfies_modVacuum :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynPointSplitTargetCanonicalMom.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynPointSplitTargetCanonicalMom.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynPointSplitTargetCanonicalMom.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) := by
  obtain ⟨cKin, cGrad, cVac, cMom, hcKin, hcGrad, hRel, hHam, hMom⟩ :=
    hamDyn_smooth_scoped_rigidity
  refine ⟨cKin, cGrad, cMom, fun _ => cVac, hcKin, hcGrad, hRel, ?_, hMom⟩
  intro x j
  simpa using hHam x j

/-! ## Status (C3; gap5 unflipped) -/

structure HKTVacuumSectorKillStatus where
  /-- Unconditioned CanonicalMom rigidity killed by vacuum shift. -/
  canonicalMomRigidityKilled : Bool
  /-- Mod-vacuum repaired terminal: open at C3 close; killed in C4
  (`HKTKineticNormalizedRigidity.not_HKTRigidityModVacuumStatementN2`). -/
  modVacuumRigidityOpen : Bool
  /-- Local C3 status bit (historical): this module did not flip the ledger.
  Ledger flip is owned by `Gap5ConstraintCloseStatus` (C5). -/
  gap5ConstraintRecovery : Bool

def hktVacuumSectorKillStatus : HKTVacuumSectorKillStatus where
  canonicalMomRigidityKilled := true
  modVacuumRigidityOpen := false
  gap5ConstraintRecovery := false

/-- Binding: C3 kill of unconditioned rigidity; mod-vacuum open bit flipped
false by C4 (kill theorem lives in `HKTKineticNormalizedRigidity` to avoid a
circular import). Local gap5 bit stays false; ledger gap5 flipped at C5. -/
theorem hktVacuumSectorKillStatus_flags :
    hktVacuumSectorKillStatus.canonicalMomRigidityKilled = true ∧
      hktVacuumSectorKillStatus.modVacuumRigidityOpen = false ∧
        hktVacuumSectorKillStatus.gap5ConstraintRecovery = false ∧
          fullTheoryBenchmarks.gap5_constraint_recovery = true ∧
            ¬ HKTRigidityStatementPointSplitDynN2Canonical ∧
              Note_modVacuumKilledInC4 :=
  ⟨rfl, rfl, rfl, rfl, not_HKTRigidityStatementPointSplitDynN2Canonical,
    note_modVacuumKilledInC4⟩

/-! ### Axiom receipts -/

#print axioms not_HKTRigidityStatementPointSplitDynN2Canonical
#print axioms vacuumShift_satisfies_modVacuum
#print axioms hamDyn_satisfies_modVacuum
#print axioms hktVacuumSectorKillStatus_flags

end
end HKTVacuumSectorKill
end SevenGaps
end Gravity
end IndisputableMonolith
