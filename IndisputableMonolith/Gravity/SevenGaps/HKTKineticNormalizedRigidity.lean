import IndisputableMonolith.Gravity.SevenGaps.HKTVacuumSectorKill
import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidityPDE
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
/-!
# Wave C4/C5 gap5: mod-vacuum kill + kinetic-normalized rigidity terminal

Binding: `D-qg-hkt-modvacuum-verdict-20260723` (Codex cross-family, 2026-07-23);
C5 upgrade: `D-gap5-acceptance-adjudication-20260723`.

Part 1: `¬ HKTRigidityModVacuumStatementN2` via variable-kinetic CanonicalMom
inhabitant. Part 2: `KineticNormalizedCanonicalMom` intensivity field; FTC
recovery is theorem-derived (`ftc_recovery_of_normalized`), not an assumed
class field. Flip of `gap5_constraint_recovery` is owned by
`Gap5ConstraintCloseStatus` after both ledger halves bind green.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTKineticNormalizedRigidity

open HypersurfaceDeformation DynamicStructureBracket DynamicStructureFunctionBlocker
open HKTPointSplitTarget HKTPointSplitStrong HKTLocalFunctionalEquation
open HKTCanonicalMomTarget HKTCanonicalMomRigidity
open HKTVacuumSectorKill FullTheoryLedger

noncomputable section

open Finset

private lemma zmod2_zero_add_one : (0 : ZMod 2) + 1 = 1 := by decide
private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
private lemma zmod2_zero_add_two : (0 : ZMod 2) + 2 = 0 := by decide
private lemma zmod2_one_add_two : (1 : ZMod 2) + 2 = 1 := by decide

/-! ## §1. Variable-kinetic profiles -/

def vacuumKineticA (a : ℝ) : ℝ := (1 + a * a)⁻¹

def vacuumKineticW (a b : ℝ) : ℝ :=
  a ^ 6 / 24 + 7 * a ^ 4 / 24 - a ^ 3 * b ^ 3 / 6 - a ^ 3 * b / 2 +
    a ^ 2 * b ^ 4 / 8 + a ^ 2 * b ^ 2 / 4 + a ^ 2 / 4 -
    a * b ^ 3 / 6 - a * b / 2 + b ^ 4 / 8 + b ^ 2 / 4

def vacuumKineticK (a b : ℝ) : ℝ :=
  let d := b - a
  (1 + a * a) * (d * d) / 2 + (2 * a) * (d ^ 3) / 3 + (d ^ 4) / 4

theorem vacuumKineticW_eq_design (a b : ℝ) :
    vacuumKineticW a b =
      (1 / 2 : ℝ) * (1 + a * a) * vacuumKineticK a b := by
  unfold vacuumKineticW vacuumKineticK; ring

def vacuumKineticLocalProfile : LocalHamProfile :=
  fun a b p => vacuumKineticA a * (p * p) + vacuumKineticW a b

def vacuumKineticHamDensity (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  vacuumKineticLocalProfile (x.1 j) (x.1 (j + 1)) (x.2 j)

theorem one_add_sq_ne_zero (a : ℝ) : (1 : ℝ) + a * a ≠ 0 := by
  nlinarith [mul_self_nonneg a]

theorem vacuumKineticA_pos (a : ℝ) : 0 < vacuumKineticA a :=
  inv_pos.mpr (by nlinarith [mul_self_nonneg a])

theorem vacuumKineticA_ne_zero (a : ℝ) : vacuumKineticA a ≠ 0 :=
  (vacuumKineticA_pos a).ne'

theorem vacuumKineticW_diag (a : ℝ) : vacuumKineticW a a = 0 := by
  unfold vacuumKineticW; ring

theorem vacuumKinetic_diag (a p : ℝ) :
    vacuumKineticLocalProfile a a p = vacuumKineticA a * (p * p) := by
  simp only [vacuumKineticLocalProfile, vacuumKineticW_diag a, add_zero]

def vacuumKineticHbClosed (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + a * a) * (b - a) * (1 + b * b)

def vacuumKineticHpClosed (a p : ℝ) : ℝ :=
  (2 : ℝ) * vacuumKineticA a * p

/-! ### ContDiff-2 (obligation only needs 2; avoid ContDiff ⊤ and heavy `.comp` whnf) -/

/-- Inverse on ℝ first; product-space `.inv` at ⊤ times out. -/
private theorem contDiff_vacuumKineticA :
    ContDiff ℝ 2 vacuumKineticA := by
  have h1a2 : ContDiff ℝ 2 (fun a : ℝ => (1 : ℝ) + a * a) :=
    contDiff_const.add (contDiff_id.mul contDiff_id)
  change ContDiff ℝ 2 (fun a : ℝ => ((1 : ℝ) + a * a)⁻¹)
  exact h1a2.inv one_add_sq_ne_zero

private theorem contDiff_vacuumKinetic_kinTerm :
    ContDiff ℝ 2 (fun t : ℝ × ℝ × ℝ => vacuumKineticA t.1 * (t.2.2 * t.2.2)) := by
  have ha : ContDiff ℝ 2 (fun t : ℝ × ℝ × ℝ => t.1) := contDiff_fst
  have hp : ContDiff ℝ 2 (fun t : ℝ × ℝ × ℝ => t.2.2) :=
    contDiff_snd.comp contDiff_snd
  exact (contDiff_vacuumKineticA.comp ha).mul (hp.mul hp)

/-- Direct unfold+fun_prop; `.comp` of the 2-site W ContDiff times out in whnf. -/
private theorem contDiff_vacuumKinetic_wTerm :
    ContDiff ℝ 2 (fun t : ℝ × ℝ × ℝ => vacuumKineticW t.1 t.2.1) := by
  unfold vacuumKineticW
  fun_prop

set_option maxHeartbeats 800000 in
theorem vacuumKinetic_profile_contDiff :
    ContDiff ℝ 2 (profileMap vacuumKineticLocalProfile) := by
  have hEq : profileMap vacuumKineticLocalProfile =
      fun t => vacuumKineticA t.1 * (t.2.2 * t.2.2) + vacuumKineticW t.1 t.2.1 := by
    funext t; rfl
  rw [hEq]
  exact contDiff_vacuumKinetic_kinTerm.add contDiff_vacuumKinetic_wTerm

theorem vacuumKineticLocalProfile_contDiff2 :
    LocalHamSmoothContDiff2Obligation vacuumKineticLocalProfile :=
  vacuumKinetic_profile_contDiff

/-! ### Closed-form derivatives -/

theorem hasDerivAt_vacuumKinetic_p (a b p : ℝ) :
    HasDerivAt (fun t => vacuumKineticLocalProfile a b t)
      (vacuumKineticHpClosed a p) p := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℝ) * p) p := by
    simpa using (hasDerivAt_id p).pow 2
  have hkin := hpow.const_mul (vacuumKineticA a)
  have hW : HasDerivAt (fun _ : ℝ => vacuumKineticW a b) 0 p :=
    hasDerivAt_const p (vacuumKineticW a b)
  have heq : (fun t => vacuumKineticLocalProfile a b t) =
      fun t => vacuumKineticA a * t ^ 2 + vacuumKineticW a b := by
    funext t
    change vacuumKineticA a * (t * t) + vacuumKineticW a b =
      vacuumKineticA a * t ^ 2 + vacuumKineticW a b
    rw [pow_two]
  have hrw : vacuumKineticA a * ((2 : ℝ) * p) + 0 = vacuumKineticHpClosed a p := by
    simp [vacuumKineticHpClosed]; ring
  rw [heq]
  exact hrw ▸ hkin.add hW

private theorem hasDerivAt_vacuumKineticK_b (a b : ℝ) :
    HasDerivAt (fun s => vacuumKineticK a s)
      (((1 : ℝ) + a * a) * (b - a) + (2 * a) * (b - a) ^ 2 + (b - a) ^ 3) b := by
  have hd : HasDerivAt (fun s : ℝ => s - a) (1 : ℝ) b :=
    (hasDerivAt_id b).sub_const a
  -- Keep Mathlib's expanded derivative expressions, then rewrite coefficients.
  have t1raw :=
    ((hasDerivAt_const b ((1 : ℝ) + a * a)).mul (hd.pow 2)).div_const (2 : ℝ)
  have t1 :
      HasDerivAt (fun s => ((1 : ℝ) + a * a) * (s - a) ^ 2 / 2)
        (((1 : ℝ) + a * a) * (b - a)) b := by
    have hrw :
        ((0 : ℝ) * (b - a) ^ 2 + ((1 : ℝ) + a * a) * (↑2 * (b - a) ^ (2 - 1) * 1)) / 2 =
          ((1 : ℝ) + a * a) * (b - a) := by ring
    exact hrw ▸ t1raw
  have t2raw :=
    ((hasDerivAt_const b ((2 : ℝ) * a)).mul (hd.pow 3)).div_const (3 : ℝ)
  have t2 :
      HasDerivAt (fun s => (2 * a) * (s - a) ^ 3 / 3)
        ((2 * a) * (b - a) ^ 2) b := by
    have hrw :
        ((0 : ℝ) * (b - a) ^ 3 + (2 * a) * (↑3 * (b - a) ^ (3 - 1) * 1)) / 3 =
          (2 * a) * (b - a) ^ 2 := by ring
    exact hrw ▸ t2raw
  have t3raw := (hd.pow 4).div_const (4 : ℝ)
  have t3 :
      HasDerivAt (fun s => (s - a) ^ 4 / 4) ((b - a) ^ 3) b := by
    have hrw : (↑4 * (b - a) ^ (4 - 1) * 1) / 4 = (b - a) ^ 3 := by ring
    exact hrw ▸ t3raw
  have hfun :
      (fun s => vacuumKineticK a s) =
        fun s =>
          ((1 : ℝ) + a * a) * (s - a) ^ 2 / 2 +
            (2 * a) * (s - a) ^ 3 / 3 + (s - a) ^ 4 / 4 := by
    funext s; simp only [vacuumKineticK]; ring
  rw [hfun]
  exact (t1.add t2).add t3

theorem hasDerivAt_vacuumKineticW_b (a b : ℝ) :
    HasDerivAt (fun s => vacuumKineticW a s) (vacuumKineticHbClosed a b) b := by
  have hEq : (fun s => vacuumKineticW a s) =
      fun s => (1 / 2 : ℝ) * (1 + a * a) * vacuumKineticK a s := by
    funext s; exact vacuumKineticW_eq_design a s
  rw [hEq]
  have hC : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ) * (1 + a * a)) 0 b :=
    hasDerivAt_const b _
  have hK := hasDerivAt_vacuumKineticK_b a b
  have hrwW :
      0 * vacuumKineticK a b +
          ((1 / 2 : ℝ) * (1 + a * a)) *
            (((1 : ℝ) + a * a) * (b - a) + (2 * a) * (b - a) ^ 2 + (b - a) ^ 3) =
        vacuumKineticHbClosed a b := by
    simp only [vacuumKineticHbClosed]; ring
  exact hrwW ▸ hC.mul hK

theorem hasDerivAt_vacuumKinetic_b (a b p : ℝ) :
    HasDerivAt (fun s => vacuumKineticLocalProfile a s p)
      (vacuumKineticHbClosed a b) b := by
  have hA : HasDerivAt (fun _ : ℝ => vacuumKineticA a * (p * p)) 0 b :=
    hasDerivAt_const b (vacuumKineticA a * (p * p))
  have heq : (fun s => vacuumKineticLocalProfile a s p) =
      fun s => vacuumKineticA a * (p * p) + vacuumKineticW a s := by
    funext s; rfl
  have hrw : (0 : ℝ) + vacuumKineticHbClosed a b = vacuumKineticHbClosed a b := by
    ring
  rw [heq]
  exact hrw ▸ hA.add (hasDerivAt_vacuumKineticW_b a b)

/-! ### Slot partials via fderiv (definitional Frechet match) -/

def vacuumKineticLocalHa : LocalHamProfile :=
  fun a b p =>
    fderiv ℝ (profileMap vacuumKineticLocalProfile) (a, b, p) (1, 0, 0)

def vacuumKineticLocalHb : LocalHamProfile :=
  fun a b p =>
    fderiv ℝ (profileMap vacuumKineticLocalProfile) (a, b, p) (0, 1, 0)

def vacuumKineticLocalHp : LocalHamProfile :=
  fun a b p =>
    fderiv ℝ (profileMap vacuumKineticLocalProfile) (a, b, p) (0, 0, 1)

theorem vacuumKineticLocalHp_eq_closed (a b p : ℝ) :
    vacuumKineticLocalHp a b p = vacuumKineticHpClosed a p := by
  have hF :=
    ((vacuumKinetic_profile_contDiff.of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (a, b, p)).hasFDerivAt
  have hφ : HasDerivAt (fun t : ℝ => ((a, b, t) : ℝ × ℝ × ℝ)) (0, 0, 1) p :=
    (hasDerivAt_const p a).prodMk ((hasDerivAt_const p b).prodMk (hasDerivAt_id p))
  have hline := hF.comp_hasDerivAt p hφ
  have hclosed := hasDerivAt_vacuumKinetic_p a b p
  change HasDerivAt (fun t => vacuumKineticLocalProfile a b t) _ p at hline
  exact HasDerivAt.unique hline hclosed

theorem vacuumKineticLocalHb_eq_closed (a b p : ℝ) :
    vacuumKineticLocalHb a b p = vacuumKineticHbClosed a b := by
  have hF :=
    ((vacuumKinetic_profile_contDiff.of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (a, b, p)).hasFDerivAt
  have hφ : HasDerivAt (fun s : ℝ => ((a, s, p) : ℝ × ℝ × ℝ)) (0, 1, 0) b :=
    (hasDerivAt_const b a).prodMk ((hasDerivAt_id b).prodMk (hasDerivAt_const b p))
  have hline := hF.comp_hasDerivAt b hφ
  have hclosed := hasDerivAt_vacuumKinetic_b a b p
  change HasDerivAt (fun s => vacuumKineticLocalProfile a s p) _ b at hline
  exact HasDerivAt.unique hline hclosed

theorem vacuumKinetic_FE (a b p r : ℝ) :
    vacuumKineticLocalHb a b p * vacuumKineticLocalHp b a r -
        vacuumKineticLocalHb b a r * vacuumKineticLocalHp a b p =
      (1 : ℝ) * (b - a) *
        ((fun q => 1 + q * q) a * r + (fun q => 1 + q * q) b * p) := by
  rw [vacuumKineticLocalHb_eq_closed, vacuumKineticLocalHp_eq_closed,
    vacuumKineticLocalHb_eq_closed, vacuumKineticLocalHp_eq_closed]
  simp only [vacuumKineticHbClosed, vacuumKineticHpClosed, vacuumKineticA]
  have ha0 := one_add_sq_ne_zero a
  have hb0 := one_add_sq_ne_zero b
  field_simp [ha0, hb0]
  ring

theorem vacuumKinetic_localCoeff_eq_structure_mom
    (x : PhaseSpace 2) (j : ZMod 2) :
    vacuumKineticLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j) *
        vacuumKineticLocalHp (x.1 (j + 1)) (x.1 (j + 2)) (x.2 (j + 1)) =
      structureDyn x j * momDynDensity x j := by
  rw [vacuumKineticLocalHb_eq_closed, vacuumKineticLocalHp_eq_closed]
  simp only [vacuumKineticHbClosed, vacuumKineticHpClosed, vacuumKineticA,
    structureDyn, momDynDensity]
  have h := one_add_sq_ne_zero (x.1 (j + 1))
  field_simp [h]

/-! ### LocalHamSmooth -/

def vacuumKineticCellCoords (j : ZMod 2) (y : PhaseSpace 2) : ℝ × ℝ × ℝ :=
  (y.1 j, y.1 (j + 1), y.2 j)

def vacuumKineticCellCoordsD (j : ZMod 2) : PhaseSpace 2 →L[ℝ] ℝ × ℝ × ℝ :=
  (coordQ j).prod ((coordQ (j + 1)).prod (coordP j))

lemma hasFDerivAt_vacuumKineticCellCoords (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (vacuumKineticCellCoords j) (vacuumKineticCellCoordsD j) x :=
  (hasFDerivAt_coord_fst j x).prodMk
    ((hasFDerivAt_coord_fst (j + 1) x).prodMk (hasFDerivAt_coord_snd j x))

lemma hasFDerivAt_vacuumKineticLocalCell (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 =>
        vacuumKineticLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j))
      ((vacuumKineticLocalHa (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
        (vacuumKineticLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
        (vacuumKineticLocalHp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j)
      x := by
  have hProf :=
    ((vacuumKinetic_profile_contDiff.of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (vacuumKineticCellCoords j x)).hasFDerivAt
  have hcomp := hProf.comp x (hasFDerivAt_vacuumKineticCellCoords j x)
  have hfun :
      (fun y : PhaseSpace 2 =>
          vacuumKineticLocalProfile (y.1 j) (y.1 (j + 1)) (y.2 j)) =
        profileMap vacuumKineticLocalProfile ∘ vacuumKineticCellCoords j := rfl
  rw [hfun]
  have hL :
      fderiv ℝ (profileMap vacuumKineticLocalProfile) (vacuumKineticCellCoords j x) ∘L
          vacuumKineticCellCoordsD j =
        (vacuumKineticLocalHa (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
          (vacuumKineticLocalHb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
          (vacuumKineticLocalHp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j := by
    apply ContinuousLinearMap.ext
    intro v
    set hf :=
      fderiv ℝ (profileMap vacuumKineticLocalProfile)
        (vacuumKineticCellCoords j x)
    -- Evaluate both sides on v.
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.prod_apply,
      vacuumKineticCellCoordsD, vacuumKineticLocalHa, vacuumKineticLocalHb,
      vacuumKineticLocalHp, vacuumKineticCellCoords, coordQ_apply, coordP_apply,
      smul_eq_mul]
    -- hf (vq_j, vq_{j+1}, vp_j) = linear combination of basis images
    have hlin :
        hf (v.1 j, v.1 (j + 1), v.2 j) =
          hf (1, 0, 0) * v.1 j + hf (0, 1, 0) * v.1 (j + 1) +
            hf (0, 0, 1) * v.2 j := by
      have hv :
          ((v.1 j, v.1 (j + 1), v.2 j) : ℝ × ℝ × ℝ) =
            (v.1 j : ℝ) • ((1, 0, 0) : ℝ × ℝ × ℝ) +
              (v.1 (j + 1) : ℝ) • ((0, 1, 0) : ℝ × ℝ × ℝ) +
                (v.2 j : ℝ) • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
        simp [Prod.smul_def]
      rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
      simp [smul_eq_mul]
      ring
    exact hlin
  exact hL ▸ hcomp

def vacuumKineticLocalSmooth : LocalHamSmooth vacuumKineticLocalProfile where
  ha := vacuumKineticLocalHa
  hb := vacuumKineticLocalHb
  hp := vacuumKineticLocalHp
  hasFDerivCell := hasFDerivAt_vacuumKineticLocalCell

/-! ## §2. Advection + class inhabitant -/

def vacuumKineticHamAdvFrom (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  -bracket (fun y => ∑ i : ZMod 2, siteDelta j i * momDynDensity y i)
    (fun y => ∑ i : ZMod 2, siteDelta j i * vacuumKineticHamDensity y i) x

def vacuumKineticHamAdvTo (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  bracket (fun y => ∑ i : ZMod 2, siteDelta j i * momDynDensity y i)
    (fun y => ∑ i : ZMod 2, siteDelta (j + 1) i * vacuumKineticHamDensity y i) x

theorem vacuumKineticHam_eq_LocalHamFromProfile (N : ZMod 2 → ℝ) :
    (fun y => ∑ j : ZMod 2, N j * vacuumKineticHamDensity y j) =
      LocalHamFromProfile vacuumKineticLocalProfile N := by
  funext y; rfl

theorem differentiable_vacuumKineticHam (N : ZMod 2 → ℝ) :
    Differentiable ℝ (fun y => ∑ j : ZMod 2, N j * vacuumKineticHamDensity y j) := by
  simpa [vacuumKineticHam_eq_LocalHamFromProfile] using
    differentiable_LocalHamFromProfile vacuumKineticLocalProfile
      vacuumKineticLocalSmooth N

/-- Bilinear expansion of the Poisson bracket for two-site smeared densitiess. -/
theorem bracket_bilinear_basis_zmod2
    (F G : ZMod 2 → PhaseSpace 2 → ℝ)
    (hF : ∀ i, Differentiable ℝ (F i)) (hG : ∀ k, Differentiable ℝ (G k))
    (c d : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (fun y => ∑ i : ZMod 2, c i * F i y)
        (fun y => ∑ k : ZMod 2, d k * G k y) x =
      ∑ i : ZMod 2, ∑ k : ZMod 2, c i * d k * bracket (F i) (G k) x := by
  have hF0 := hF 0 x; have hF1 := hF 1 x
  have hG0 := hG 0 x; have hG1 := hG 1 x
  have hCL :
      (fun y => ∑ i : ZMod 2, c i * F i y) =
        fun y => c 0 * F 0 y + c 1 * F 1 y := by
    funext y; simp [sum_zmod2]
  have hDR :
      (fun y => ∑ k : ZMod 2, d k * G k y) =
        fun y => d 0 * G 0 y + d 1 * G 1 y := by
    funext y; simp [sum_zmod2]
  rw [hCL, hDR]
  have hR :=
    bracket_add_right (n := 2) (fun y => c 0 * F 0 y + c 1 * F 1 y)
      (hG0.const_mul (d 0)) (hG1.const_mul (d 1))
  have hL0 :=
    bracket_add_left (n := 2) (G 0) (hF0.const_mul (c 0)) (hF1.const_mul (c 1))
  have hL1 :=
    bracket_add_left (n := 2) (G 1) (hF0.const_mul (c 0)) (hF1.const_mul (c 1))
  have hc0G0 := bracket_const_mul_left (n := 2) (G 0) hF0 (c 0)
  have hc1G0 := bracket_const_mul_left (n := 2) (G 0) hF1 (c 1)
  have hc0G1 := bracket_const_mul_left (n := 2) (G 1) hF0 (c 0)
  have hc1G1 := bracket_const_mul_left (n := 2) (G 1) hF1 (c 1)
  have hd0F0 := bracket_const_mul_right (n := 2) (F 0) hG0 (d 0)
  have hd0F1 := bracket_const_mul_right (n := 2) (F 1) hG0 (d 0)
  have hd1F0 := bracket_const_mul_right (n := 2) (F 0) hG1 (d 1)
  have hd1F1 := bracket_const_mul_right (n := 2) (F 1) hG1 (d 1)
  -- Expand both sides on ZMod 2 and finish by bilinearity.
  simp only [sum_zmod2]
  have hMain :
      bracket (fun y => c 0 * F 0 y + c 1 * F 1 y)
          (fun y => d 0 * G 0 y + d 1 * G 1 y) x =
        c 0 * d 0 * bracket (F 0) (G 0) x + c 0 * d 1 * bracket (F 0) (G 1) x +
          (c 1 * d 0 * bracket (F 1) (G 0) x + c 1 * d 1 * bracket (F 1) (G 1) x) := by
    have hStep1 := hR
    have hStep2 :
        bracket (fun y => c 0 * F 0 y + c 1 * F 1 y) (fun y => d 0 * G 0 y) x +
            bracket (fun y => c 0 * F 0 y + c 1 * F 1 y) (fun y => d 1 * G 1 y) x =
          d 0 * bracket (fun y => c 0 * F 0 y + c 1 * F 1 y) (G 0) x +
            d 1 * bracket (fun y => c 0 * F 0 y + c 1 * F 1 y) (G 1) x := by
      rw [bracket_const_mul_right (n := 2)
          (fun y => c 0 * F 0 y + c 1 * F 1 y) hG0 (d 0),
        bracket_const_mul_right (n := 2)
          (fun y => c 0 * F 0 y + c 1 * F 1 y) hG1 (d 1)]
    have hStep3 :
        d 0 * bracket (fun y => c 0 * F 0 y + c 1 * F 1 y) (G 0) x +
            d 1 * bracket (fun y => c 0 * F 0 y + c 1 * F 1 y) (G 1) x =
          d 0 * (c 0 * bracket (F 0) (G 0) x + c 1 * bracket (F 1) (G 0) x) +
            d 1 * (c 0 * bracket (F 0) (G 1) x + c 1 * bracket (F 1) (G 1) x) := by
      rw [hL0, hL1, hc0G0, hc1G0, hc0G1, hc1G1]
    linarith [hStep1, hStep2, hStep3]
  exact hMain

theorem mom_ham_split_vacuumKinetic (w N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomDyn w)
        (fun y => ∑ j : ZMod 2, N j * vacuumKineticHamDensity y j) x =
      ∑ j : ZMod 2,
        w j *
          (N (j + 1) * vacuumKineticHamAdvTo x j -
            N j * vacuumKineticHamAdvFrom x j) := by
  let F : ZMod 2 → PhaseSpace 2 → ℝ := fun i y =>
    ∑ k : ZMod 2, siteDelta i k * momDynDensity y k
  let G : ZMod 2 → PhaseSpace 2 → ℝ := fun i y =>
    ∑ k : ZMod 2, siteDelta i k * vacuumKineticHamDensity y k
  have hF : ∀ i, Differentiable ℝ (F i) := by
    intro i; simpa [F, MomDyn] using differentiable_MomDyn (siteDelta i)
  have hG : ∀ i, Differentiable ℝ (G i) := by
    intro i
    simpa [G] using differentiable_vacuumKineticHam (siteDelta i)
  have hMom : MomDyn w = fun y => ∑ i : ZMod 2, w i * F i y := by
    funext y
    simp only [MomDyn, F, sum_zmod2, siteDelta]
    have h00 : siteDelta (0 : ZMod 2) 0 = (1 : ℝ) := by simp [siteDelta]
    have h11 : siteDelta (1 : ZMod 2) 1 = (1 : ℝ) := by simp [siteDelta]
    have h01 : siteDelta (0 : ZMod 2) 1 = (0 : ℝ) := by simp [siteDelta]
    have h10 : siteDelta (1 : ZMod 2) 0 = (0 : ℝ) := by simp [siteDelta]
    simp [h00, h11, h01, h10]
  have hHam :
      (fun y => ∑ j : ZMod 2, N j * vacuumKineticHamDensity y j) =
        fun y => ∑ k : ZMod 2, N k * G k y := by
    funext y
    simp only [G, sum_zmod2, siteDelta]
    have h00 : siteDelta (0 : ZMod 2) 0 = (1 : ℝ) := by simp [siteDelta]
    have h11 : siteDelta (1 : ZMod 2) 1 = (1 : ℝ) := by simp [siteDelta]
    have h01 : siteDelta (0 : ZMod 2) 1 = (0 : ℝ) := by simp [siteDelta]
    have h10 : siteDelta (1 : ZMod 2) 0 = (0 : ℝ) := by simp [siteDelta]
    simp [h00, h11, h01, h10]
  rw [hMom, hHam, bracket_bilinear_basis_zmod2 F G hF hG w N x]
  -- RHS Kronecker form.
  have hR :
      (∑ j : ZMod 2,
          w j *
            (N (j + 1) * vacuumKineticHamAdvTo x j -
              N j * vacuumKineticHamAdvFrom x j)) =
        ∑ i : ZMod 2, ∑ k : ZMod 2, w i * N k * bracket (F i) (G k) x := by
    simp only [vacuumKineticHamAdvFrom, vacuumKineticHamAdvTo, F, G, sum_zmod2,
      zmod2_zero_add_one, zmod2_one_add_one]
    ring
  exact hR.symm

theorem ham_ham_vacuumKinetic (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (fun y => ∑ j : ZMod 2, N j * vacuumKineticHamDensity y j)
        (fun y => ∑ j : ZMod 2, M j * vacuumKineticHamDensity y j) x =
      ∑ j : ZMod 2,
        (N j * M (j + 1) - M j * N (j + 1)) *
          (structureDyn x j * momDynDensity x j) := by
  have hL :=
    local_profile_ham_ham_form vacuumKineticLocalProfile vacuumKineticLocalSmooth
      N M x
  -- Transport density names to LocalHamFromProfile, then match coefficients.
  simpa [vacuumKineticHam_eq_LocalHamFromProfile, localHamHamCoefficient,
    vacuumKineticLocalSmooth, vacuumKinetic_localCoeff_eq_structure_mom] using hL

def vacuumKineticNondegPhase : PhaseSpace 2 :=
  (fun _ => (0 : ℝ), fun j => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

theorem vacuumKinetic_nondeg :
    vacuumKineticHamDensity vacuumKineticNondegPhase (0 : ZMod 2) ≠ 0 := by
  simp only [vacuumKineticHamDensity, vacuumKineticLocalProfile, vacuumKineticNondegPhase,
    vacuumKineticA, vacuumKineticW, zmod2_zero_add_one]
  norm_num

def vacuumKineticWeakTarget : HKTPointSplitTargetDyn 2 where
  hamDensity := vacuumKineticHamDensity
  momDensity := momDynDensity
  structureFunction := structureDyn
  hamAdvFrom := vacuumKineticHamAdvFrom
  hamAdvTo := vacuumKineticHamAdvTo
  momBracketDensity := momDynBracketDensity
  ham_differentiable := differentiable_vacuumKineticHam
  mom_differentiable := differentiable_MomDyn
  structure_nonconstant := structureDyn_not_constant
  ham_local := by
    intro x y j hx0 hx1 hp
    dsimp [vacuumKineticHamDensity]
    rw [hx0, hx1, hp]
  ham_covariant := by
    intro x a j
    dsimp [vacuumKineticHamDensity]
    have e1 : (j + a + 1 : ZMod 2) = j + 1 + a := by ring
    simp only [e1]
  structure_local := by
    intro x y j hx
    dsimp [structureDyn]; rw [hx]
  mom_mom := by
    intro v w x
    simpa [MomDyn] using bracket_MomDyn_MomDyn v w x
  mom_ham_split := by
    intro w N x
    simpa [MomDyn] using mom_ham_split_vacuumKinetic w N x
  ham_ham := ham_ham_vacuumKinetic
  nondegenerate := ⟨vacuumKineticNondegPhase, (0 : ZMod 2), vacuumKinetic_nondeg⟩

theorem vacuumKinetic_kinetic_regular_witness :
    pderivP (fun y => ∑ i : ZMod 2, vacuumKineticHamDensity y i) (0 : ZMod 2)
        vacuumKineticNondegPhase ≠ 0 := by
  have hEq :
      (fun y => ∑ i : ZMod 2, vacuumKineticHamDensity y i) =
        LocalHamFromProfile vacuumKineticLocalProfile (fun _ => (1 : ℝ)) := by
    funext y
    simp [LocalHamFromProfile, vacuumKineticHamDensity]
  rw [hEq]
  have hP :=
    pderivP_LocalHamFromProfile vacuumKineticLocalProfile vacuumKineticLocalSmooth
      (fun _ => (1 : ℝ)) (0 : ZMod 2) vacuumKineticNondegPhase
  rw [hP, one_mul]
  change vacuumKineticLocalHp (vacuumKineticNondegPhase.1 (0 : ZMod 2))
      (vacuumKineticNondegPhase.1 ((0 : ZMod 2) + 1))
      (vacuumKineticNondegPhase.2 (0 : ZMod 2)) ≠ 0
  have hq0 : vacuumKineticNondegPhase.1 (0 : ZMod 2) = 0 := by
    simp [vacuumKineticNondegPhase]
  have hq1 : vacuumKineticNondegPhase.1 ((0 : ZMod 2) + 1) = 0 := by
    simp [vacuumKineticNondegPhase, zmod2_zero_add_one]
  have hp0 : vacuumKineticNondegPhase.2 (0 : ZMod 2) = 1 := by
    simp [vacuumKineticNondegPhase]
  rw [hq0, hq1, hp0, vacuumKineticLocalHp_eq_closed]
  -- Goal: 2 * A(0) * 1 ≠ 0
  simp only [vacuumKineticHpClosed, vacuumKineticA]
  norm_num

def vacuumKineticStrongTarget : HKTPointSplitTargetDynStrong 2 where
  toHKTPointSplitTargetDyn := vacuumKineticWeakTarget
  mom_load_bearing := by
    refine ⟨delta0, delta1, momLoadBearingWitnessPhase, ?_⟩
    simpa [MomDyn] using hamDyn_mom_load_bearing_witness
  advFrom_tied := by
    intro x j
    simpa using hamAdvFrom_eq_computed vacuumKineticWeakTarget x j
  advTo_tied := by
    intro x j
    simpa using hamAdvTo_eq_computed vacuumKineticWeakTarget x j
  kinetic_regular :=
    ⟨vacuumKineticNondegPhase, (0 : ZMod 2), vacuumKinetic_kinetic_regular_witness⟩

theorem vacuumKineticDensity_eq_localProfile (x : PhaseSpace 2) (j : ZMod 2) :
    vacuumKineticHamDensity x j =
      vacuumKineticLocalProfile (x.1 j) (x.1 (j + 1)) (x.2 j) := rfl

/-- THEOREM. Variable-kinetic density inhabits CanonicalMom. -/
def vacuumKineticCanonicalMomTarget : HKTPointSplitTargetDynCanonicalMom where
  toHKTPointSplitTargetDynStrong := vacuumKineticStrongTarget
  local_ham_profile :=
    ⟨vacuumKineticLocalProfile, vacuumKineticLocalSmooth, vacuumKineticDensity_eq_localProfile⟩
  structure_profile := ⟨fun q => 1 + q * q, structureDyn_eq_g⟩
  canonical_mom := by
    refine ⟨(1 : ℝ), by norm_num, ?_⟩
    intro x j
    simpa using momDynDensity_canonical x j

/-! ## §3. Kill of mod-vacuum rigidity -/

def coincidentPhaseKin (q p : ℝ) : PhaseSpace 2 :=
  (fun _ => q, fun _ => p)

/-- THEOREM. Mod-vacuum CanonicalMom rigidity is false. -/
theorem not_HKTRigidityModVacuumStatementN2 :
    ¬ HKTRigidityModVacuumStatementN2 := by
  intro h
  obtain ⟨cKin, cGrad, cMom, V, hcKin, _hcGrad, _hRel, hHam, _hMom⟩ :=
    h vacuumKineticCanonicalMomTarget
  have hAt (q p : ℝ) :
      vacuumKineticA q * (p * p) = cKin * (p * p) + V q := by
    have h0 := hHam (coincidentPhaseKin q p) (0 : ZMod 2)
    simp only [vacuumKineticCanonicalMomTarget, vacuumKineticStrongTarget,
      vacuumKineticWeakTarget, vacuumKineticHamDensity, vacuumKineticLocalProfile,
      structureDyn, coincidentPhaseKin, zmod2_zero_add_one, sub_self, mul_zero,
      vacuumKineticW_diag, add_zero] at h0
    -- h0 : A q * p² = cKin p² + cGrad * _ * 0 + V q
    linarith
  have hV (q : ℝ) : V q = 0 := by
    have h0 := hAt q 0
    simp only [mul_zero, zero_add] at h0
    exact h0.symm
  have hA (q : ℝ) : vacuumKineticA q = cKin := by
    have h1 := hAt q 1
    simp only [mul_one, hV q, add_zero] at h1
    exact h1
  have h0 := hA 0
  have h1 := hA 1
  simp only [vacuumKineticA] at h0 h1
  norm_num at h0 h1
  exact absurd (h0.trans h1.symm) (by norm_num : (1 : ℝ) ≠ 1 / 2)

/-! ## Codified decoys -/

/-- Decoy: `structure_nonconstant` does not force ADM shape (counterexample witness). -/
theorem vacuumKinetic_structure_nonconstant :
    ¬ PhaseSpaceConstant vacuumKineticCanonicalMomTarget.structureFunction :=
  structureDyn_not_constant

/-- Decoy: the FE is `0 = 0` on the diagonal (does not force constant kinetic). -/
theorem fe_diagonal_trivial (a p r : ℝ) :
    vacuumKineticLocalHb a a p * vacuumKineticLocalHp a a r -
        vacuumKineticLocalHb a a r * vacuumKineticLocalHp a a p = 0 := by
  have h := vacuumKinetic_FE a a p r
  simpa using h

/-- The variable-kinetic counterexample fails the mod-vacuum ham-density shape. -/
theorem vacuumKinetic_fails_modVacuum_hamShape :
    ¬ ∃ cKin cGrad : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧
        ∀ (x : PhaseSpace 2) (j : ZMod 2),
          vacuumKineticCanonicalMomTarget.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (vacuumKineticCanonicalMomTarget.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j) := by
  rintro ⟨cKin, cGrad, V, hcKin, _hcGrad, hHam⟩
  have hAt (q p : ℝ) :
      vacuumKineticA q * (p * p) = cKin * (p * p) + V q := by
    have h0 := hHam (coincidentPhaseKin q p) (0 : ZMod 2)
    simp only [vacuumKineticCanonicalMomTarget, vacuumKineticStrongTarget,
      vacuumKineticWeakTarget, vacuumKineticHamDensity, vacuumKineticLocalProfile,
      structureDyn, coincidentPhaseKin, zmod2_zero_add_one, sub_self, mul_zero,
      vacuumKineticW_diag, add_zero] at h0
    linarith
  have hV (q : ℝ) : V q = 0 := by
    have hq := hAt q 0
    simp only [mul_zero, zero_add] at hq
    exact hq.symm
  have h0 := hAt 0 1
  have h1 := hAt 1 1
  simp only [vacuumKineticA, mul_one, hV, add_zero] at h0 h1
  norm_num at h0 h1
  exact absurd (h0.trans h1.symm) (by norm_num : (1 : ℝ) ≠ 1 / 2)

/-! ## §4. Kinetic-normalized positive terminal (C5: FTC derived) -/

/-- DISCLOSED. Kinetic-sector ultralocal intensivity normalization.

Intensivity `hp = 2 cKin p` plus ContDiff-2. The former assumed
`ftc_recovery` field is discharged as `ftc_recovery_of_normalized`
(`D-gap5-acceptance-adjudication-20260723`). -/
structure KineticNormalizedCanonicalMom where
  target : HKTPointSplitTargetDynCanonicalMom
  kinetic_normalized :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (cKin : ℝ),
      ContDiff ℝ 2 (profileMap h) ∧
        cKin ≠ 0 ∧
          (∀ (x : PhaseSpace 2) (j : ZMod 2),
            target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
          (∀ (a b p : ℝ), S.hp a b p = (2 * cKin) * p)

/-- Terminal Prop: every kinetic-normalized CanonicalMom target is ADM + vacuum profile. -/
def HKTRigidityKineticNormalizedN2 : Prop :=
  ∀ T : KineticNormalizedCanonicalMom,
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j))

private lemma localCellD_eval_p0 (h : LocalHamProfile) (S : LocalHamSmooth h)
    (a b p : ℝ) :
    localCellD h S (0 : ZMod 2) (fePhase a b p 0) (0, Pi.single (0 : ZMod 2) 1) =
      S.hp a b p := by
  simp only [localCellD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, smul_eq_mul, fePhase, zmod2_zero_add_one]
  simp [Pi.single_eq_same]

private lemma localCellD_eval_b0 (h : LocalHamProfile) (S : LocalHamSmooth h)
    (a b p : ℝ) :
    localCellD h S (0 : ZMod 2) (fePhase a b p 0)
        (Pi.single (1 : ZMod 2) 1, 0) =
      S.hb a b p := by
  simp only [localCellD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, smul_eq_mul, fePhase, zmod2_zero_add_one]
  simp [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : ZMod 2) ≠ 1)]

/-- Frechet uniqueness: slot `hp` is independent of the LocalHamSmooth witness. -/
theorem LocalHamSmooth_hp_unique (h : LocalHamProfile)
    (S₁ S₂ : LocalHamSmooth h) (a b p : ℝ) :
    S₁.hp a b p = S₂.hp a b p := by
  let x : PhaseSpace 2 := fePhase a b p 0
  have hL :=
    HasFDerivAt.unique (hasFDerivAt_localCell h S₁ (0 : ZMod 2) x)
      (hasFDerivAt_localCell h S₂ (0 : ZMod 2) x)
  have heval :=
    congrArg (fun L : PhaseSpace 2 →L[ℝ] ℝ => L (0, Pi.single (0 : ZMod 2) 1)) hL
  simpa [localCellD_eval_p0 h S₁ a b p, localCellD_eval_p0 h S₂ a b p, x] using heval

/-- Frechet uniqueness: slot `hb` is independent of the LocalHamSmooth witness. -/
theorem LocalHamSmooth_hb_unique (h : LocalHamProfile)
    (S₁ S₂ : LocalHamSmooth h) (a b p : ℝ) :
    S₁.hb a b p = S₂.hb a b p := by
  let x : PhaseSpace 2 := fePhase a b p 0
  have hL :=
    HasFDerivAt.unique (hasFDerivAt_localCell h S₁ (0 : ZMod 2) x)
      (hasFDerivAt_localCell h S₂ (0 : ZMod 2) x)
  have heval :=
    congrArg (fun L : PhaseSpace 2 →L[ℝ] ℝ => L (Pi.single (1 : ZMod 2) 1, 0)) hL
  simpa [localCellD_eval_b0 h S₁ a b p, localCellD_eval_b0 h S₂ a b p, x] using heval

/-! ### ContDiff-2 slot derivatives ↔ LocalHamSmooth coefficients -/

private theorem hasDerivAt_profileMap_p
    (h : LocalHamProfile) (hcd : ContDiff ℝ 2 (profileMap h)) (a b p : ℝ) :
    HasDerivAt (fun t => h a b t)
      (fderiv ℝ (profileMap h) (a, b, p) (0, 0, 1)) p := by
  have hF :=
    ((hcd.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (a, b, p)).hasFDerivAt
  have hφ : HasDerivAt (fun t : ℝ => ((a, b, t) : ℝ × ℝ × ℝ)) (0, 0, 1) p :=
    (hasDerivAt_const p a).prodMk ((hasDerivAt_const p b).prodMk (hasDerivAt_id p))
  have hline := hF.comp_hasDerivAt p hφ
  simpa [profileMap, Function.comp_def] using hline

private theorem hasDerivAt_profileMap_b
    (h : LocalHamProfile) (hcd : ContDiff ℝ 2 (profileMap h)) (a b p : ℝ) :
    HasDerivAt (fun s => h a s p)
      (fderiv ℝ (profileMap h) (a, b, p) (0, 1, 0)) b := by
  have hF :=
    ((hcd.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (a, b, p)).hasFDerivAt
  have hφ : HasDerivAt (fun s : ℝ => ((a, s, p) : ℝ × ℝ × ℝ)) (0, 1, 0) b :=
    (hasDerivAt_const b a).prodMk ((hasDerivAt_id b).prodMk (hasDerivAt_const b p))
  have hline := hF.comp_hasDerivAt b hφ
  simpa [profileMap, Function.comp_def] using hline

private def cellCoords0 (y : PhaseSpace 2) : ℝ × ℝ × ℝ :=
  (y.1 (0 : ZMod 2), y.1 (1 : ZMod 2), y.2 (0 : ZMod 2))

private def cellCoords0D : PhaseSpace 2 →L[ℝ] ℝ × ℝ × ℝ :=
  (coordQ (0 : ZMod 2)).prod ((coordQ (1 : ZMod 2)).prod (coordP (0 : ZMod 2)))

private lemma hasFDerivAt_cellCoords0 (x : PhaseSpace 2) :
    HasFDerivAt cellCoords0 cellCoords0D x :=
  (hasFDerivAt_coord_fst (0 : ZMod 2) x).prodMk
    ((hasFDerivAt_coord_fst (1 : ZMod 2) x).prodMk
      (hasFDerivAt_coord_snd (0 : ZMod 2) x))

private theorem cellCoords0_fePhase (a b p : ℝ) :
    cellCoords0 (fePhase a b p 0) = (a, b, p) := by
  simp [cellCoords0, fePhase]

private theorem LocalHamSmooth_hp_eq_fderiv
    (h : LocalHamProfile) (S : LocalHamSmooth h)
    (hcd : ContDiff ℝ 2 (profileMap h)) (a b p : ℝ) :
    S.hp a b p = fderiv ℝ (profileMap h) (a, b, p) (0, 0, 1) := by
  let x : PhaseSpace 2 := fePhase a b p 0
  have hx : cellCoords0 x = (a, b, p) := cellCoords0_fePhase a b p
  have hS := hasFDerivAt_localCell h S (0 : ZMod 2) x
  have hProf :=
    ((hcd.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (cellCoords0 x)).hasFDerivAt
  have hcomp := hProf.comp x (hasFDerivAt_cellCoords0 x)
  have hfun :
      (fun y : PhaseSpace 2 => h (y.1 (0 : ZMod 2)) (y.1 (1 : ZMod 2)) (y.2 (0 : ZMod 2))) =
        profileMap h ∘ cellCoords0 := rfl
  have hCD : HasFDerivAt
      (fun y : PhaseSpace 2 => h (y.1 (0 : ZMod 2)) (y.1 (1 : ZMod 2)) (y.2 (0 : ZMod 2)))
      (fderiv ℝ (profileMap h) (cellCoords0 x) ∘L cellCoords0D) x := by
    simpa [hfun] using hcomp
  have hUniq := HasFDerivAt.unique hS hCD
  have heval :=
    congrArg (fun L : PhaseSpace 2 →L[ℝ] ℝ => L (0, Pi.single (0 : ZMod 2) 1)) hUniq
  have hL : localCellD h S (0 : ZMod 2) x (0, Pi.single (0 : ZMod 2) 1) = S.hp a b p :=
    localCellD_eval_p0 h S a b p
  have hR :
      (fderiv ℝ (profileMap h) (cellCoords0 x) ∘L cellCoords0D)
          (0, Pi.single (0 : ZMod 2) 1) =
        fderiv ℝ (profileMap h) (a, b, p) (0, 0, 1) := by
    simp only [ContinuousLinearMap.comp_apply, cellCoords0D, ContinuousLinearMap.prod_apply,
      coordQ_apply, coordP_apply, Pi.single_eq_same, Pi.zero_apply, hx]
  have hLR :
      S.hp a b p =
        (fderiv ℝ (profileMap h) (cellCoords0 x) ∘L cellCoords0D)
          (0, Pi.single (0 : ZMod 2) 1) := by
    simpa [hL] using heval
  exact hLR.trans hR

private theorem LocalHamSmooth_hb_eq_fderiv
    (h : LocalHamProfile) (S : LocalHamSmooth h)
    (hcd : ContDiff ℝ 2 (profileMap h)) (a b p : ℝ) :
    S.hb a b p = fderiv ℝ (profileMap h) (a, b, p) (0, 1, 0) := by
  let x : PhaseSpace 2 := fePhase a b p 0
  have hx : cellCoords0 x = (a, b, p) := cellCoords0_fePhase a b p
  have hS := hasFDerivAt_localCell h S (0 : ZMod 2) x
  have hProf :=
    ((hcd.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      (cellCoords0 x)).hasFDerivAt
  have hcomp := hProf.comp x (hasFDerivAt_cellCoords0 x)
  have hfun :
      (fun y : PhaseSpace 2 => h (y.1 (0 : ZMod 2)) (y.1 (1 : ZMod 2)) (y.2 (0 : ZMod 2))) =
        profileMap h ∘ cellCoords0 := rfl
  have hCD : HasFDerivAt
      (fun y : PhaseSpace 2 => h (y.1 (0 : ZMod 2)) (y.1 (1 : ZMod 2)) (y.2 (0 : ZMod 2)))
      (fderiv ℝ (profileMap h) (cellCoords0 x) ∘L cellCoords0D) x := by
    simpa [hfun] using hcomp
  have hUniq := HasFDerivAt.unique hS hCD
  have heval :=
    congrArg (fun L : PhaseSpace 2 →L[ℝ] ℝ => L (Pi.single (1 : ZMod 2) 1, 0)) hUniq
  have hL : localCellD h S (0 : ZMod 2) x (Pi.single (1 : ZMod 2) 1, 0) = S.hb a b p :=
    localCellD_eval_b0 h S a b p
  have hR :
      (fderiv ℝ (profileMap h) (cellCoords0 x) ∘L cellCoords0D)
          (Pi.single (1 : ZMod 2) 1, 0) =
        fderiv ℝ (profileMap h) (a, b, p) (0, 1, 0) := by
    simp only [ContinuousLinearMap.comp_apply, cellCoords0D, ContinuousLinearMap.prod_apply,
      coordQ_apply, coordP_apply, Pi.single_eq_same, Pi.zero_apply,
      Pi.single_eq_of_ne (by decide : (0 : ZMod 2) ≠ 1), hx]
  have hLR :
      S.hb a b p =
        (fderiv ℝ (profileMap h) (cellCoords0 x) ∘L cellCoords0D)
          (Pi.single (1 : ZMod 2) 1, 0) := by
    simpa [hL] using heval
  exact hLR.trans hR

theorem hasDerivAt_hp_of_normalized
    (h : LocalHamProfile) (S : LocalHamSmooth h)
    (hcd : ContDiff ℝ 2 (profileMap h)) (a b p : ℝ) :
    HasDerivAt (fun t => h a b t) (S.hp a b p) p := by
  have hline := hasDerivAt_profileMap_p h hcd a b p
  rwa [← LocalHamSmooth_hp_eq_fderiv h S hcd a b p] at hline

theorem hasDerivAt_hb_of_normalized
    (h : LocalHamProfile) (S : LocalHamSmooth h)
    (hcd : ContDiff ℝ 2 (profileMap h)) (a b p : ℝ) :
    HasDerivAt (fun s => h a s p) (S.hb a b p) b := by
  have hline := hasDerivAt_profileMap_b h hcd a b p
  rwa [← LocalHamSmooth_hb_eq_fderiv h S hcd a b p] at hline

/-! ### (i) Kinetic split from intensivity -/

/-- Intensivity + ContDiff-2 ⇒ `h(a,b,p) = cKin p² + h(a,b,0)`. -/
theorem kinetic_split_of_intensivity
    (h : LocalHamProfile) (S : LocalHamSmooth h) (cKin : ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h))
    (hHp : ∀ (a b p : ℝ), S.hp a b p = (2 * cKin) * p)
    (a b p : ℝ) :
    h a b p = cKin * (p * p) + h a b 0 := by
  let F : ℝ → ℝ := fun t => h a b t - cKin * (t * t)
  have hFderiv (t : ℝ) : HasDerivAt F 0 t := by
    have h1 := hasDerivAt_hp_of_normalized h S hcd a b t
    have hpow : HasDerivAt (fun u : ℝ => u ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_id t).pow 2
    have h2pow : HasDerivAt (fun u : ℝ => cKin * u ^ 2) ((2 * cKin) * t) t := by
      have h2' := hpow.const_mul cKin
      convert h2' using 1; ring
    have h2 : HasDerivAt (fun u : ℝ => cKin * (u * u)) ((2 * cKin) * t) t := by
      have heq : (fun u : ℝ => cKin * (u * u)) = fun u => cKin * u ^ 2 := by
        funext u; rw [pow_two]
      simpa [heq] using h2pow
    have hsub : HasDerivAt F (S.hp a b t - (2 * cKin) * t) t := h1.sub h2
    simpa [hHp a b t, sub_self] using hsub
  have hdiff : Differentiable ℝ F := fun t => (hFderiv t).differentiableAt
  have hconst :=
    is_const_of_deriv_eq_zero hdiff (fun t => (hFderiv t).deriv) p 0
  have hF0 : F 0 = h a b 0 := by simp [F]
  have hFp : F p = h a b p - cKin * (p * p) := rfl
  linarith [hconst, hF0, hFp]

/-! ### (ii) Gradient recovery from FE + intensivity -/

/-- FE at `(p,r)=(0,1)` + intensivity ⇒ diagonal `hb` shape. -/
theorem hb0_of_intensivity_FE
    (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom cKin : ℝ)
    (hcKin : cKin ≠ 0)
    (hHp : ∀ (a b p : ℝ), S.hp a b p = (2 * cKin) * p)
    (hFE : ∀ (a b p r : ℝ),
      S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
        cMom * (b - a) * (g a * r + g b * p))
    (a b : ℝ) :
    S.hb a b 0 = (cMom / (2 * cKin)) * (g a * (b - a)) := by
  have h0 := hFE a b 0 1
  have hHpba : S.hp b a 1 = 2 * cKin := by simpa using hHp b a 1
  have hHpab : S.hp a b 0 = 0 := by simpa using hHp a b 0
  have h0' : S.hb a b 0 * (2 * cKin) = cMom * (b - a) * g a := by
    simpa [hHpba, hHpab, mul_zero, sub_zero, mul_one, add_zero] using h0
  have h2 : (2 : ℝ) * cKin ≠ 0 := mul_ne_zero (by norm_num) hcKin
  calc
    S.hb a b 0 = (S.hb a b 0 * (2 * cKin)) / (2 * cKin) := by field_simp [h2]
    _ = (cMom * (b - a) * g a) / (2 * cKin) := by rw [h0']
    _ = (cMom / (2 * cKin)) * (g a * (b - a)) := by ring

/-- Gradient-sector FTC: integrate the FE-forced `hb` from the diagonal. -/
theorem gradient_recovery_of_intensivity
    (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom cKin : ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h)) (hcKin : cKin ≠ 0)
    (hHp : ∀ (a b p : ℝ), S.hp a b p = (2 * cKin) * p)
    (hFE : ∀ (a b p r : ℝ),
      S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
        cMom * (b - a) * (g a * r + g b * p))
    (a b : ℝ) :
    h a b 0 =
      h a a 0 + (cMom / (4 * cKin)) * (g a * ((b - a) * (b - a))) := by
  let F : ℝ → ℝ := fun s => h a s 0
  let Gpow : ℝ → ℝ := fun s =>
    h a a 0 + (cMom / (4 * cKin)) * (g a * (s - a) ^ 2)
  have hHb0 (s : ℝ) :
      S.hb a s 0 = (cMom / (2 * cKin)) * (g a * (s - a)) :=
    hb0_of_intensivity_FE h S g cMom cKin hcKin hHp hFE a s
  have hFderiv (s : ℝ) : HasDerivAt F (S.hb a s 0) s :=
    hasDerivAt_hb_of_normalized h S hcd a s 0
  have hGderiv (s : ℝ) :
      HasDerivAt Gpow ((cMom / (2 * cKin)) * (g a * (s - a))) s := by
    have hd : HasDerivAt (fun s : ℝ => s - a) (1 : ℝ) s :=
      (hasDerivAt_id s).sub_const a
    have hsq : HasDerivAt (fun s : ℝ => (s - a) ^ 2) (2 * (s - a)) s := by
      convert hd.pow 2 using 1 <;> ring
    let c : ℝ := h a a 0
    let k : ℝ := cMom / (4 * cKin)
    have hga : HasDerivAt (fun s : ℝ => g a * (s - a) ^ 2)
        (g a * (2 * (s - a))) s := by
      convert (hasDerivAt_const s (g a)).mul hsq using 1 <;> ring
    have hterm : HasDerivAt (fun s : ℝ => k * (g a * (s - a) ^ 2))
        (k * (g a * (2 * (s - a)))) s := by
      convert hga.const_mul k using 1 <;> ring
    have hsum : HasDerivAt (fun s : ℝ => c + k * (g a * (s - a) ^ 2))
        (0 + k * (g a * (2 * (s - a)))) s :=
      (hasDerivAt_const s c).add hterm
    have hfun : Gpow = fun s => c + k * (g a * (s - a) ^ 2) := rfl
    rw [hfun]
    have hrw : 0 + k * (g a * (2 * (s - a))) =
        (cMom / (2 * cKin)) * (g a * (s - a)) := by
      change 0 + (cMom / (4 * cKin)) * (g a * (2 * (s - a))) =
          (cMom / (2 * cKin)) * (g a * (s - a))
      ring
    exact hrw ▸ hsum
  have hDiff (s : ℝ) : HasDerivAt (fun u => F u - Gpow u) 0 s := by
    have hsub : HasDerivAt (fun u => F u - Gpow u)
        (S.hb a s 0 - (cMom / (2 * cKin)) * (g a * (s - a))) s :=
      (hFderiv s).sub (hGderiv s)
    simpa [hHb0 s, sub_self] using hsub
  have hdiff : Differentiable ℝ (fun u => F u - Gpow u) :=
    fun s => (hDiff s).differentiableAt
  have hconst :=
    is_const_of_deriv_eq_zero hdiff (fun s => (hDiff s).deriv) b a
  have hFa : F a - Gpow a = 0 := by
    simp only [F, Gpow, sub_self, pow_two, mul_zero, add_zero]
  have hFb : F b - Gpow b = F a - Gpow a := hconst
  have hEq : F b = Gpow b := by linarith [hFb, hFa]
  -- F b = h a b 0 and Gpow b = h a a 0 + (cMom/(4 cKin)) g a (b-a)^2
  change h a b 0 = Gpow b at hEq
  simpa [Gpow, pow_two] using hEq

/-- FE for an explicit local-profile witness (same body as
`profiled_ham_ham_alternating_FE`, fixed `h`/`S`/`g`/`cMom`). -/
theorem alternating_FE_of_profile
    (T : HKTPointSplitTargetDynCanonicalMom)
    (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ)
    (hHam : ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j))
    (hG : ∀ (x : PhaseSpace 2) (j : ZMod 2), T.structureFunction x j = g (x.1 j))
    (hMom : ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.momDensity x j = cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j))
    (a b p r : ℝ) :
    S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
      cMom * (b - a) * (g a * r + g b * p) := by
  let x : PhaseSpace 2 := fePhase a b p r
  have hx0 : x.1 (0 : ZMod 2) = a := by simp [x, fePhase]
  have hx1 : x.1 (1 : ZMod 2) = b := by simp [x, fePhase]
  have hp0 : x.2 (0 : ZMod 2) = p := by simp [x, fePhase]
  have hp1 : x.2 (1 : ZMod 2) = r := by simp [x, fePhase]
  have hEq0 := hamDensity_smear_eq_LocalHamFromProfile T h hHam delta0
  have hEq1 := hamDensity_smear_eq_LocalHamFromProfile T h hHam delta1
  have hProf := local_profile_ham_ham_form h S delta0 delta1 x
  have hTarget := T.ham_ham delta0 delta1 x
  have hProf' :
      bracket (LocalHamFromProfile h delta0) (LocalHamFromProfile h delta1) x =
        localHamHamCoefficient h S x (0 : ZMod 2) -
          localHamHamCoefficient h S x (1 : ZMod 2) :=
    hProf.trans (localHamHamCoefficient_delta01 h S x)
  have hTarget' :
      bracket (fun y => ∑ j : ZMod 2, delta0 j * T.hamDensity y j)
          (fun y => ∑ j : ZMod 2, delta1 j * T.hamDensity y j) x =
        T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) -
          T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) :=
    hTarget.trans (structure_mom_delta01 T.structureFunction T.momDensity x)
  have hBracket :
      bracket (LocalHamFromProfile h delta0) (LocalHamFromProfile h delta1) x =
        T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) -
          T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) := by
    simpa [hEq0, hEq1] using hTarget'
  have hAlt :
      localHamHamCoefficient h S x (0 : ZMod 2) -
          localHamHamCoefficient h S x (1 : ZMod 2) =
        T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) -
          T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) :=
    hProf'.symm.trans hBracket
  have hC0 :
      localHamHamCoefficient h S x (0 : ZMod 2) =
        S.hb a b p * S.hp b a r := by
    simp only [localHamHamCoefficient, zmod2_zero_add_one, zmod2_zero_add_two]
    rw [hx0, hx1, hp0, hp1]
  have hC1 :
      localHamHamCoefficient h S x (1 : ZMod 2) =
        S.hb b a r * S.hp a b p := by
    simp only [localHamHamCoefficient, zmod2_one_add_one, zmod2_one_add_two]
    rw [hx0, hx1, hp0, hp1]
  have hR0 :
      T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) =
        g a * (cMom * r * (b - a)) := by
    rw [hG x (0 : ZMod 2), hMom x (0 : ZMod 2), zmod2_zero_add_one, hx0, hx1, hp1]
  have hR1 :
      T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) =
        g b * (cMom * p * (a - b)) := by
    rw [hG x (1 : ZMod 2), hMom x (1 : ZMod 2), zmod2_one_add_one, hx0, hx1, hp0]
  have hEq := hAlt
  rw [hC0, hC1, hR0, hR1] at hEq
  have hR :
      g a * (cMom * r * (b - a)) - g b * (cMom * p * (a - b)) =
        cMom * (b - a) * (g a * r + g b * p) := by ring
  exact hEq.trans hR

/-- THEOREM. FTC package derived from intensivity + ContDiff-2 + CanonicalMom FE.
No assumed conclusion-shaped class field. -/
theorem ftc_recovery_of_normalized (T : KineticNormalizedCanonicalMom) :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (cKin : ℝ) (g : ℝ → ℝ)
      (cMom : ℝ),
      cKin ≠ 0 ∧ cMom ≠ 0 ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.structureFunction x j = g (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.momDensity x j = cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) ∧
        (∀ (a b p : ℝ), S.hp a b p = (2 * cKin) * p) ∧
        (∀ (a b p r : ℝ),
          S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
            cMom * (b - a) * (g a * r + g b * p)) ∧
        (∀ (a b p : ℝ), h a b p = cKin * (p * p) + h a b 0) ∧
        (∀ (a b : ℝ),
          h a b 0 =
            h a a 0 + (cMom / (4 * cKin)) * (g a * ((b - a) * (b - a)))) := by
  obtain ⟨h, S, cKin, hcd, hcKin, hHam, hHp⟩ := T.kinetic_normalized
  obtain ⟨g, hG⟩ := T.target.structure_profile
  obtain ⟨cMom, hcMom, hMom⟩ := T.target.canonical_mom
  refine ⟨h, S, cKin, g, cMom, hcKin, hcMom, hHam, hG, hMom, hHp, ?_, ?_, ?_⟩
  · exact alternating_FE_of_profile T.target h S g cMom hHam hG hMom
  · intro a b p
    exact kinetic_split_of_intensivity h S cKin hcd hHp a b p
  · intro a b
    exact gradient_recovery_of_intensivity h S g cMom cKin hcd hcKin hHp
      (alternating_FE_of_profile T.target h S g cMom hHam hG hMom) a b

/-- THEOREM. Kinetic-normalized CanonicalMom rigidity at `n = 2`. -/
theorem HKTRigidityKineticNormalizedN2_holds : HKTRigidityKineticNormalizedN2 := by
  intro T
  obtain ⟨h, S, cKin, g, cMom, hcKin, hcMom, hHam, hG, hMom, hHp, _hFE, hSplit, hInt⟩ :=
    ftc_recovery_of_normalized T
  refine ⟨cKin, cMom / (4 * cKin), cMom, fun a => h a a 0, hcKin,
    div_ne_zero hcMom (mul_ne_zero (by norm_num) hcKin), ?_, ?_, hMom⟩
  · field_simp [hcKin]
  · intro x j
    have h1 := hHam x j
    have h2 := hG x j
    have h3 := hSplit (x.1 j) (x.1 (j + 1)) (x.2 j)
    have h4 := hInt (x.1 j) (x.1 (j + 1))
    calc
      T.target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j) := h1
      _ = cKin * (x.2 j * x.2 j) + h (x.1 j) (x.1 (j + 1)) 0 := h3
      _ = cKin * (x.2 j * x.2 j) +
            (h (x.1 j) (x.1 j) 0 +
              (cMom / (4 * cKin)) *
                (g (x.1 j) *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))) := by
          rw [h4]
      _ = cKin * (x.2 j * x.2 j) +
            (cMom / (4 * cKin)) *
              (T.target.structureFunction x j *
                ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
            h (x.1 j) (x.1 j) 0 := by
          rw [h2]; ring

/-! ### Anchors -/

def hamDynKineticNormalized : KineticNormalizedCanonicalMom where
  target := hamDynPointSplitTargetCanonicalMom
  kinetic_normalized := by
    refine ⟨hamDynLocalProfile, hamDynLocalSmooth, (1 / 2 : ℝ),
      hamDynLocalProfile_contDiff2, by norm_num, hamDynDensity_eq_localProfile, ?_⟩
    intro a b p
    change hamDynLocalHp a b p = (2 * (1 / 2 : ℝ)) * p
    simp only [hamDynLocalHp]; ring

theorem hamDyn_satisfies_kineticNormalized :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynKineticNormalized.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynKineticNormalized.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynKineticNormalized.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityKineticNormalizedN2_holds hamDynKineticNormalized

/-- Load-bearing: variable-kinetic counterexample is excluded (hp not globally
of the form `2 cKin p`). -/
theorem vacuumKinetic_not_kineticNormalized :
    ¬ ∃ T : KineticNormalizedCanonicalMom,
      T.target = vacuumKineticCanonicalMomTarget := by
  rintro ⟨T, hEq⟩
  obtain ⟨h, S, cKin, _hcd, hcKin, hHam, hHp⟩ := T.kinetic_normalized
  have hProf : h = vacuumKineticLocalProfile := by
    funext a b p
    have hT :
        T.target.hamDensity (fePhase a b p 0) (0 : ZMod 2) =
          vacuumKineticCanonicalMomTarget.hamDensity (fePhase a b p 0) (0 : ZMod 2) :=
      congrArg (fun U : HKTPointSplitTargetDynCanonicalMom =>
        U.hamDensity (fePhase a b p 0) (0 : ZMod 2)) hEq
    have hL := hHam (fePhase a b p 0) (0 : ZMod 2)
    have hR :
        vacuumKineticCanonicalMomTarget.hamDensity (fePhase a b p 0) (0 : ZMod 2) =
          vacuumKineticLocalProfile a b p := by
      simp [vacuumKineticCanonicalMomTarget, vacuumKineticStrongTarget,
        vacuumKineticWeakTarget, vacuumKineticHamDensity, fePhase, zmod2_zero_add_one]
    exact (hL.symm.trans hT).trans hR
  cases hProf
  have hUniq (a b p : ℝ) :
      S.hp a b p = vacuumKineticLocalSmooth.hp a b p :=
    LocalHamSmooth_hp_unique vacuumKineticLocalProfile S vacuumKineticLocalSmooth a b p
  have hA (a : ℝ) : vacuumKineticA a = cKin := by
    have hL : S.hp a 0 1 = (2 * cKin) * (1 : ℝ) := hHp a 0 1
    have hR : S.hp a 0 1 = vacuumKineticHpClosed a 1 :=
      (hUniq a 0 1).trans (by
        change vacuumKineticLocalHp a 0 1 = vacuumKineticHpClosed a 1
        exact vacuumKineticLocalHp_eq_closed a 0 1)
    simp only [mul_one, vacuumKineticHpClosed] at hL hR
    linarith
  have h0 := hA 0
  have h1 := hA 1
  simp only [vacuumKineticA] at h0 h1
  norm_num at h0 h1
  exact absurd (h0.trans h1.symm) (by norm_num : (1 : ℝ) ≠ 1 / 2)

/-! ## §5. Status (C5; gap5 flipped via Gap5ConstraintCloseStatus) -/

structure HKTKineticNormalizedRigidityStatus where
  modVacuumRigidityKilled : Bool
  kineticNormalizedRigidityClosed : Bool
  ftcRecoveryDerived : Bool
  gap5ConstraintRecovery : Bool

def hktKineticNormalizedRigidityStatus : HKTKineticNormalizedRigidityStatus where
  modVacuumRigidityKilled := true
  kineticNormalizedRigidityClosed := true
  ftcRecoveryDerived := true
  gap5ConstraintRecovery := true

theorem hktKineticNormalizedRigidityStatus_flags :
    hktKineticNormalizedRigidityStatus.modVacuumRigidityKilled = true ∧
      hktKineticNormalizedRigidityStatus.kineticNormalizedRigidityClosed = true ∧
        hktKineticNormalizedRigidityStatus.ftcRecoveryDerived = true ∧
          hktKineticNormalizedRigidityStatus.gap5ConstraintRecovery = true ∧
            fullTheoryBenchmarks.gap5_constraint_recovery = true ∧
              ¬ HKTRigidityModVacuumStatementN2 ∧
                HKTRigidityKineticNormalizedN2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, not_HKTRigidityModVacuumStatementN2,
    HKTRigidityKineticNormalizedN2_holds⟩

#print axioms not_HKTRigidityModVacuumStatementN2
#print axioms ftc_recovery_of_normalized
#print axioms HKTRigidityKineticNormalizedN2_holds
#print axioms hamDyn_satisfies_kineticNormalized
#print axioms vacuumKinetic_not_kineticNormalized
#print axioms kinetic_split_of_intensivity
#print axioms gradient_recovery_of_intensivity

end
end HKTKineticNormalizedRigidity
end SevenGaps
end Gravity
end IndisputableMonolith
