import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Wave C2 gap5: CanonicalMom rigidity session C2 (PDE under ContDiff-2)

Binding: `D-qg-hkt-rigidity-route-20260722`, re-scope
`N-qg-hkt-localham-contdiff2-20260722`.

## Finding (disclosed)

`ContDiff ℝ 2` of the local profile (as `ℝ × ℝ × ℝ → ℝ`) is the standard HKT
smoothness assumption. It does **not**, by itself, force the linear-`hp` /
p-free-`hb` ansatz used by the PDE route: the smooth witness
`sqrtAffineProfile` satisfies the alternating FE with `cMom = 1`, `g ≡ 1`, yet
its momentum partial is independent of `p` and its `b`-partial is linear in
`p`.

The unconditioned Prop `solve_profile_FE_quadratic` therefore remains open.
This session lands:
1. ContDiff-2 packaging (`LocalHamSmoothContDiff2Obligation`);
2. the FE counterexample (credit-bearing scope correction);
3. conditional ADM solve under the linear ansatz + constant kinetic/vacuum
   gauges (disclosed HKT kinetic ultralocality / vacuum normalization);
4. smooth-scoped rigidity `HKTRigidityPointSplitDynN2Canonical_smooth`;
5. honest HamDyn ContDiff-2 + ansatz discharge.

Do NOT flip `gap5_constraint_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTCanonicalMomRigidity

open HypersurfaceDeformation DynamicStructureBracket
open HKTPointSplitTarget HKTPointSplitStrong HKTLocalFunctionalEquation
open HKTCanonicalMomTarget FullTheoryLedger

noncomputable section

/-! ## Profile map and ContDiff packaging -/

/-- Package a local profile as a map on `ℝ × ℝ × ℝ`. -/
def profileMap (h : LocalHamProfile) : ℝ × ℝ × ℝ → ℝ :=
  fun t => h t.1 t.2.1 t.2.2

theorem LocalHamSmoothContDiff2Obligation_iff (h : LocalHamProfile) :
    LocalHamSmoothContDiff2Obligation h ↔ ContDiff ℝ 2 (profileMap h) :=
  Iff.rfl

/-! ## FE counterexample: ContDiff-2 does not force the linear ansatz -/

/-- Smooth FE witness profile: `h = √(1+(b-a)²) · p`. -/
def sqrtAffineProfile : LocalHamProfile :=
  fun a b p => Real.sqrt (1 + (b - a) * (b - a)) * p

/-- Explicit `b`-partial of `sqrtAffineProfile`. -/
def sqrtAffineHb : LocalHamProfile :=
  fun a b p =>
    ((b - a) / Real.sqrt (1 + (b - a) * (b - a))) * p

/-- Explicit `p`-partial of `sqrtAffineProfile`. -/
def sqrtAffineHp : LocalHamProfile :=
  fun a b _p => Real.sqrt (1 + (b - a) * (b - a))

theorem sqrtAffine_one_add_sq_pos (a b : ℝ) :
    0 < 1 + (b - a) * (b - a) := by
  nlinarith [mul_self_nonneg (b - a)]

theorem sqrtAffine_one_add_sq_ne_zero (a b : ℝ) :
    1 + (b - a) * (b - a) ≠ 0 :=
  (sqrtAffine_one_add_sq_pos a b).ne'

theorem sqrtAffineProfile_contDiff2 :
    LocalHamSmoothContDiff2Obligation sqrtAffineProfile := by
  change ContDiff ℝ 2 (profileMap sqrtAffineProfile)
  have hSq : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ =>
      (1 : ℝ) + (t.2.1 - t.1) * (t.2.1 - t.1)) := by
    apply ContDiff.add contDiff_const
    exact ((contDiff_fst.comp contDiff_snd).sub contDiff_fst).mul
      ((contDiff_fst.comp contDiff_snd).sub contDiff_fst)
  have hSqrt : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ =>
      Real.sqrt (1 + (t.2.1 - t.1) * (t.2.1 - t.1))) :=
    hSq.sqrt fun t => sqrtAffine_one_add_sq_ne_zero t.1 t.2.1
  have hP : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ => t.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hEq : profileMap sqrtAffineProfile =
      fun t : ℝ × ℝ × ℝ =>
        Real.sqrt (1 + (t.2.1 - t.1) * (t.2.1 - t.1)) * t.2.2 := by
    funext t
    rfl
  rw [hEq]
  exact (hSqrt.mul hP).of_le (by simp)

theorem sqrtAffine_satisfies_FE :
    ∀ (a b p r : ℝ),
      sqrtAffineHb a b p * sqrtAffineHp b a r -
          sqrtAffineHb b a r * sqrtAffineHp a b p =
        (1 : ℝ) * (b - a) *
          ((fun _ : ℝ => (1 : ℝ)) a * r + (fun _ : ℝ => (1 : ℝ)) b * p) := by
  intro a b p r
  have hs :
      Real.sqrt (1 + (a - b) * (a - b)) =
        Real.sqrt (1 + (b - a) * (b - a)) := by
    ring_nf
  simp only [sqrtAffineHb, sqrtAffineHp, hs, mul_one]
  set s := Real.sqrt (1 + (b - a) * (b - a))
  have hspos := sqrtAffine_one_add_sq_pos a b
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hspos).ne'
  field_simp [s, hs0]
  ring

/-- The explicit `hp` is not of the form `kinCoeff(a,b) * p`. -/
theorem sqrtAffineHp_not_linear_in_p :
    ¬ ∃ kinCoeff : ℝ → ℝ → ℝ,
        ∀ (a b p : ℝ), sqrtAffineHp a b p = kinCoeff a b * p := by
  rintro ⟨kinCoeff, hkin⟩
  have h0 := hkin 0 0 0
  simp only [sqrtAffineHp, sub_self, mul_zero] at h0
  have h1 : Real.sqrt (1 + 0) = 1 := by norm_num
  rw [h1] at h0
  exact (by norm_num : (1 : ℝ) ≠ 0) h0

/-- The explicit `hb` depends on its momentum slot. -/
theorem sqrtAffineHb_not_p_independent :
    ¬ ∀ (a b p p' : ℝ), sqrtAffineHb a b p = sqrtAffineHb a b p' := by
  intro hInd
  have h := hInd 0 1 0 1
  simp only [sqrtAffineHb, sub_zero, mul_zero, mul_one] at h
  have hne : (1 : ℝ) / Real.sqrt (1 + 1) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 + 1)).ne'
  exact hne h.symm

/-- FINDING. ContDiff-2 + the alternating FE do not force a linear-`hp` ansatz
on the FE coefficient functions. -/
theorem not_forced_linear_hp_of_contDiff2_FE :
    ∃ (h hb hp : LocalHamProfile) (g : ℝ → ℝ) (cMom : ℝ),
      LocalHamSmoothContDiff2Obligation h ∧
        cMom ≠ 0 ∧
        (∀ a b p r : ℝ,
          hb a b p * hp b a r - hb b a r * hp a b p =
            cMom * (b - a) * (g a * r + g b * p)) ∧
        ¬ ∃ kinCoeff : ℝ → ℝ → ℝ,
            ∀ (a b p : ℝ), hp a b p = kinCoeff a b * p :=
  ⟨sqrtAffineProfile, sqrtAffineHb, sqrtAffineHp, fun _ => 1, 1,
    sqrtAffineProfile_contDiff2, by norm_num, sqrtAffine_satisfies_FE,
    sqrtAffineHp_not_linear_in_p⟩

/-- FINDING. ContDiff-2 + the alternating FE do not force p-independence of
`hb`. -/
theorem not_forced_hb_p_independent_of_contDiff2_FE :
    ∃ (h hb hp : LocalHamProfile) (g : ℝ → ℝ) (cMom : ℝ),
      LocalHamSmoothContDiff2Obligation h ∧
        cMom ≠ 0 ∧
        (∀ a b p r : ℝ,
          hb a b p * hp b a r - hb b a r * hp a b p =
            cMom * (b - a) * (g a * r + g b * p)) ∧
        ¬ ∀ (a b p p' : ℝ), hb a b p = hb a b p' :=
  ⟨sqrtAffineProfile, sqrtAffineHb, sqrtAffineHp, fun _ => 1, 1,
    sqrtAffineProfile_contDiff2, by norm_num, sqrtAffine_satisfies_FE,
    sqrtAffineHb_not_p_independent⟩

/-! ## Conditional ADM solve (disclosed gauges) -/

/-- Disclosed HKT kinetic ultralocality: `S.hp a b p = 2 cKin · p` with
`cKin ≠ 0` (so `h` integrates to `cKin p² + ·`). -/
def ConstantKineticSlope (h : LocalHamProfile) (S : LocalHamSmooth h)
    (cKin : ℝ) : Prop :=
  cKin ≠ 0 ∧ ∀ (a b p : ℝ), S.hp a b p = (2 * cKin) * p

/-- Disclosed vacuum normalization: `h(a,a,0)` is constant. -/
def ConstantVacuumGauge (h : LocalHamProfile) (cVac : ℝ) : Prop :=
  ∀ a : ℝ, h a a 0 = cVac

/-- Coupling specialization: under constant kinetic slope, `hb(a,b,0)` has the
gradient shape `(cMom/(2 cKin)) g(a)(b-a)`. -/
theorem hb_shape_of_constant_kinetic_slope
    (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ)
    (hFE : ∀ (a b p r : ℝ),
      S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
        cMom * (b - a) * (g a * r + g b * p))
    (hHb : HbPIndependent h S)
    (cKin : ℝ) (hKin : ConstantKineticSlope h S cKin) :
    ∀ (a b : ℝ),
      S.hb a b 0 = (cMom / (2 * cKin)) * (g a * (b - a)) := by
  intro a b
  have hHp : ∀ (a b p : ℝ), S.hp a b p = (fun _ _ => 2 * cKin) a b * p := by
    intro a b p
    simpa using hKin.2 a b p
  have hCoup := hb_coupling_of_linear_ansatz S.hb S.hp g cMom
    (fun _ _ => 2 * cKin) hFE hHp (fun a b p => hHb a b p 0) a b
  have hcKin := hKin.1
  have h2 : (2 : ℝ) * cKin ≠ 0 := mul_ne_zero (by norm_num) hcKin
  have : S.hb a b 0 * (2 * cKin) = cMom * (b - a) * g a := by
    simpa using hCoup
  calc
    S.hb a b 0 = (S.hb a b 0 * (2 * cKin)) / (2 * cKin) := by field_simp [h2]
    _ = (cMom * (b - a) * g a) / (2 * cKin) := by rw [this]
    _ = (cMom / (2 * cKin)) * (g a * (b - a)) := by ring

/-- Clean conditional: constant kinetic slope + FTC recovery from partials ⇒
ADM quadratic form with `cMom = 4 cKin cGrad`. -/
theorem ADM_quadratic_of_gauges
    (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ)
    (hcMom : cMom ≠ 0)
    (cKin cVac : ℝ)
    (hKin : ConstantKineticSlope h S cKin)
    (hFromPartials :
      ∀ (a b p : ℝ),
        h a b p = cKin * (p * p) + h a b 0 ∧
          h a b 0 =
            (cMom / (4 * cKin)) * (g a * ((b - a) * (b - a))) + cVac) :
    ∃ cGrad : ℝ,
      cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        ∀ (a b p : ℝ),
          h a b p =
            cKin * (p * p) +
              cGrad * (g a * ((b - a) * (b - a))) + cVac := by
  refine ⟨cMom / (4 * cKin), ?_, ?_, ?_⟩
  · exact div_ne_zero hcMom (mul_ne_zero (by norm_num) hKin.1)
  · field_simp [hKin.1]
  · intro a b p
    obtain ⟨h1, h2⟩ := hFromPartials a b p
    calc
      h a b p = cKin * (p * p) + h a b 0 := h1
      _ = cKin * (p * p) +
            ((cMom / (4 * cKin)) * (g a * ((b - a) * (b - a))) + cVac) := by
          rw [h2]
      _ = cKin * (p * p) +
            (cMom / (4 * cKin)) * (g a * ((b - a) * (b - a))) + cVac := by
          abel

/-! ## Honest HamDyn ContDiff-2 + ansatz -/

theorem hamDynLocalProfile_contDiff2 :
    LocalHamSmoothContDiff2Obligation hamDynLocalProfile := by
  change ContDiff ℝ 2 (profileMap hamDynLocalProfile)
  have ha : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ => t.1) := contDiff_fst
  have hb : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ => t.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hp : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ => t.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hp2 := hp.mul hp
  have ha2 := ha.mul ha
  have h1 : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have h1a2 := h1.add ha2
  have hba := hb.sub ha
  have hba2 := hba.mul hba
  have hStruct := h1a2.mul hba2
  have hSum := hp2.add hStruct
  have hHalf : ContDiff ℝ ⊤ (fun t : ℝ × ℝ × ℝ =>
      (1 / 2 : ℝ) *
        (t.2.2 * t.2.2 +
          (1 + t.1 * t.1) * ((t.2.1 - t.1) * (t.2.1 - t.1)))) := by
    simpa using (contDiff_const (c := (1 / 2 : ℝ))).mul hSum
  have hEq : profileMap hamDynLocalProfile =
      fun t : ℝ × ℝ × ℝ =>
        (1 / 2 : ℝ) *
          (t.2.2 * t.2.2 +
            (1 + t.1 * t.1) * ((t.2.1 - t.1) * (t.2.1 - t.1))) := by
    funext t
    rfl
  rw [hEq]
  exact hHalf.of_le (by simp)

theorem hamDyn_HpLinearInP : HpLinearInP hamDynLocalProfile hamDynLocalSmooth := by
  refine ⟨fun _ _ => (1 : ℝ), ?_⟩
  intro a b p
  simp [hamDynLocalSmooth, hamDynLocalHp]

theorem hamDyn_HbPIndependent : HbPIndependent hamDynLocalProfile hamDynLocalSmooth := by
  intro a b p p'
  simp [hamDynLocalSmooth, hamDynLocalHb]

theorem hamDyn_constantKineticSlope :
    ConstantKineticSlope hamDynLocalProfile hamDynLocalSmooth (1 / 2 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  intro a b p
  change hamDynLocalHp a b p = (2 * (1 / 2 : ℝ)) * p
  simp only [hamDynLocalHp]
  ring

theorem hamDyn_constantVacuumGauge :
    ConstantVacuumGauge hamDynLocalProfile (0 : ℝ) := by
  intro a
  simp [hamDynLocalProfile]

/-- Smooth-scoped rigidity data package (ContDiff-2 + linear ansatz + gauges). -/
structure SmoothScopedCanonicalMomData
    (T : HKTPointSplitTargetDynCanonicalMom) where
  h : LocalHamProfile
  S : LocalHamSmooth h
  g : ℝ → ℝ
  cMom : ℝ
  cKin : ℝ
  cVac : ℝ
  hcMom : cMom ≠ 0
  hcd : LocalHamSmoothContDiff2Obligation h
  ham_profile :
    ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)
  structure_profile :
    ∀ (x : PhaseSpace 2) (j : ZMod 2), T.structureFunction x j = g (x.1 j)
  mom_profile :
    ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.momDensity x j = cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)
  hFE :
    ∀ (a b p r : ℝ),
      S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
        cMom * (b - a) * (g a * r + g b * p)
  hHp : HpLinearInP h S
  hHb : HbPIndependent h S
  hKin : ConstantKineticSlope h S cKin
  hVac : ConstantVacuumGauge h cVac
  /-- FTC/integration recovery from the partials under ContDiff (disclosed). -/
  hFromPartials :
    ∀ (a b p : ℝ),
      h a b p = cKin * (p * p) + h a b 0 ∧
        h a b 0 =
          (cMom / (4 * cKin)) * (g a * ((b - a) * (b - a))) + cVac

/-- THEOREM. Smooth-scoped CanonicalMom rigidity: ContDiff-2 + linear ansatz +
constant kinetic/vacuum gauges ⇒ ADM rigidity conclusion.

The unconditioned `HKTRigidityStatementPointSplitDynN2Canonical` remains open:
ContDiff-2 alone does not force the linear ansatz
(`not_forced_linear_hp_of_contDiff2_FE`), and profiles that are once- but not
twice-differentiable lie outside the ContDiff-2 scope. -/
theorem HKTRigidityPointSplitDynN2Canonical_smooth
    (T : HKTPointSplitTargetDynCanonicalMom)
    (D : SmoothScopedCanonicalMomData T) :
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
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) := by
  obtain ⟨cGrad, hGrad, hRel, hQuad⟩ :=
    ADM_quadratic_of_gauges D.h D.S D.g D.cMom D.hcMom D.cKin D.cVac D.hKin
      D.hFromPartials
  refine ⟨D.cKin, cGrad, D.cVac, D.cMom, D.hKin.1, hGrad, hRel, ?_, D.mom_profile⟩
  intro x j
  have h1 := D.ham_profile x j
  have h2 := D.structure_profile x j
  have h3 := hQuad (x.1 j) (x.1 (j + 1)) (x.2 j)
  calc
    T.hamDensity x j
        = D.h (x.1 j) (x.1 (j + 1)) (x.2 j) := h1
    _ = D.cKin * (x.2 j * x.2 j) +
          cGrad *
            (D.g (x.1 j) *
              ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
          D.cVac := h3
    _ = D.cKin * (x.2 j * x.2 j) +
          cGrad *
            (T.structureFunction x j *
              ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
          D.cVac := by rw [h2]

/-- Honest HamDyn supplies smooth-scoped rigidity data. -/
def hamDynSmoothScopedData :
    SmoothScopedCanonicalMomData hamDynPointSplitTargetCanonicalMom where
  h := hamDynLocalProfile
  S := hamDynLocalSmooth
  g := fun q => 1 + q * q
  cMom := 1
  cKin := 1 / 2
  cVac := 0
  hcMom := by norm_num
  hcd := hamDynLocalProfile_contDiff2
  ham_profile := hamDynDensity_eq_localProfile
  structure_profile := structureDyn_eq_g
  mom_profile := by
    intro x j
    simpa using momDynDensity_canonical x j
  hFE := by
    intro a b p r
    simp only [hamDynLocalSmooth, hamDynLocalHb, hamDynLocalHp]
    ring
  hHp := hamDyn_HpLinearInP
  hHb := hamDyn_HbPIndependent
  hKin := hamDyn_constantKineticSlope
  hVac := hamDyn_constantVacuumGauge
  hFromPartials := by
    intro a b p
    constructor
    · simp only [hamDynLocalProfile]; ring
    · simp only [hamDynLocalProfile]
      have hcoeff : (1 : ℝ) / (4 * (1 / 2)) = 1 / 2 := by norm_num
      rw [hcoeff]
      ring

theorem hamDyn_smooth_scoped_rigidity :
    ∃ cKin cGrad cVac cMom : ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynPointSplitTargetCanonicalMom.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynPointSplitTargetCanonicalMom.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              cVac) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynPointSplitTargetCanonicalMom.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityPointSplitDynN2Canonical_smooth hamDynPointSplitTargetCanonicalMom
    hamDynSmoothScopedData

/-- Conditional PDE solve: smooth-scoped data ⇒ `SolveProfileFEQuadratic`. -/
theorem SolveProfileFEQuadratic_of_smoothScopedData
    (T : HKTPointSplitTargetDynCanonicalMom)
    (D : SmoothScopedCanonicalMomData T) :
    SolveProfileFEQuadratic T := by
  obtain ⟨cGrad, hGrad, hRel, hQuad⟩ :=
    ADM_quadratic_of_gauges D.h D.S D.g D.cMom D.hcMom D.cKin D.cVac D.hKin
      D.hFromPartials
  refine ⟨D.h, D.S, D.g, D.cKin, cGrad, D.cVac, D.cMom, D.hKin.1, hGrad, D.hcMom,
    hRel, D.ham_profile, D.structure_profile, hQuad, D.mom_profile⟩

/-! ## Status (C2) -/

structure HKTCanonicalMomRigidityC2Status where
  feExtractionClosed : Bool
  feAnsatzCounterexampleClosed : Bool
  smoothScopedRigidityClosed : Bool
  /-- Unconditioned universal `solve_profile_FE_quadratic` still open. -/
  pdeLemmaClosed : Bool
  /-- C2-era flag: unconditioned rigidity was still open at C2 close.
  Superseded by C3 vacuum-sector kill in `HKTVacuumSectorKill`
  (`canonicalMomRigidityKilled`); kept for C2 receipt continuity. -/
  canonicalMomRigidityOpen : Bool
  gap5ConstraintRecovery : Bool

def hktCanonicalMomRigidityC2Status : HKTCanonicalMomRigidityC2Status where
  feExtractionClosed := true
  feAnsatzCounterexampleClosed := true
  smoothScopedRigidityClosed := true
  pdeLemmaClosed := false
  canonicalMomRigidityOpen := true
  gap5ConstraintRecovery := false

theorem hktCanonicalMomRigidityC2Status_flags :
    hktCanonicalMomRigidityC2Status.feExtractionClosed = true ∧
      hktCanonicalMomRigidityC2Status.feAnsatzCounterexampleClosed = true ∧
        hktCanonicalMomRigidityC2Status.smoothScopedRigidityClosed = true ∧
          hktCanonicalMomRigidityC2Status.pdeLemmaClosed = false ∧
            hktCanonicalMomRigidityC2Status.canonicalMomRigidityOpen = true ∧
              hktCanonicalMomRigidityC2Status.gap5ConstraintRecovery = false ∧
                fullTheoryBenchmarks.gap5_constraint_recovery = true := by
  decide

/-!
C3 status lives in `HKTVacuumSectorKill` (avoids circular import):
`canonicalMomRigidityKilled = true`, `modVacuumRigidityOpen = true`,
bound to `not_HKTRigidityStatementPointSplitDynN2Canonical`.
-/

/-! ### Axiom receipts -/

#print axioms sqrtAffineProfile_contDiff2
#print axioms not_forced_linear_hp_of_contDiff2_FE
#print axioms not_forced_hb_p_independent_of_contDiff2_FE
#print axioms hb_shape_of_constant_kinetic_slope
#print axioms ADM_quadratic_of_gauges
#print axioms HKTRigidityPointSplitDynN2Canonical_smooth
#print axioms hamDynLocalProfile_contDiff2
#print axioms hamDyn_smooth_scoped_rigidity
#print axioms SolveProfileFEQuadratic_of_smoothScopedData
#print axioms hktCanonicalMomRigidityC2Status_flags

end
end HKTCanonicalMomRigidity
end SevenGaps
end Gravity
end IndisputableMonolith
