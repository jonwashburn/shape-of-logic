import IndisputableMonolith.Gravity.SevenGaps.HKTPointSplitTarget

/-!
# Wave C2 repair: strengthened point-split HKT target (decoy excluded)

Codex adversarial pass `D-qg-hkt-pointsplit-adjudication-20260722` found that
`HKTPointSplitTargetDyn` is decoy-inhabitable (quartic zero-momentum) and that
rigidity over the weak class is therefore not a load-bearing grind target.

This module lands:
1. `HKTPointSplitTargetDynStrong` with load-bearing momentum, advection tied to
   the Mom–Ham bracket calculus, and kinetic regularity;
2. explicit `quarticZeroMomTarget` inhabiting the WEAK schema (formal witness of
   the critic finding) and excluded from the strong class by
   `mom_load_bearing`;
3. honest `hamDynPointSplitTargetStrong` inhabiting the strong class;
4. `HKTRigidityStatementPointSplitDynN2Strong` (now PROVEN FALSE via the
   balanced-quartic falsifier in `HKTCanonicalMomTarget`; binding rigidity
   moves to CanonicalMom).

No ledger flag is flipped. Discrimination gate: honest inhabitant passes,
quartic zero-momentum decoy fails. Strong-class rigidity is dead; see
`HKTCanonicalMomTarget`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTPointSplitStrong

open HypersurfaceDeformation DynamicStructureBracket DynamicStructureFunctionBlocker
open HKTPointSplitTarget

noncomputable section

open Finset

/-! ## Computed advection from the Mom–Ham bracket calculus -/

/-- Kronecker lapse / shift weight on `ZMod n`. -/
def siteDelta {n : ℕ} [NeZero n] (k : ZMod n) : ZMod n → ℝ :=
  fun j => if j = k then (1 : ℝ) else 0

lemma siteDelta_self {n : ℕ} [NeZero n] (k : ZMod n) : siteDelta k k = (1 : ℝ) := by
  simp [siteDelta]

lemma siteDelta_ne {n : ℕ} [NeZero n] {k j : ZMod n} (h : j ≠ k) :
    siteDelta k j = (0 : ℝ) := by
  simp [siteDelta, h]

/-- Source advection recovered by evaluating `{Mom δ_j, Ham δ_j}`. -/
def computedHamAdvFrom {n : ℕ} [NeZero n] (T : HKTPointSplitTargetDyn n)
    (x : PhaseSpace n) (j : ZMod n) : ℝ :=
  -bracket (fun y => ∑ i : ZMod n, siteDelta j i * T.momDensity y i)
    (fun y => ∑ i : ZMod n, siteDelta j i * T.hamDensity y i) x

/-- Target advection recovered by evaluating `{Mom δ_j, Ham δ_{j+1}}`. -/
def computedHamAdvTo {n : ℕ} [NeZero n] (T : HKTPointSplitTargetDyn n)
    (x : PhaseSpace n) (j : ZMod n) : ℝ :=
  bracket (fun y => ∑ i : ZMod n, siteDelta j i * T.momDensity y i)
    (fun y => ∑ i : ZMod n, siteDelta (j + 1) i * T.hamDensity y i) x

private lemma zmod2_succ_ne (j : ZMod 2) : (j + 1 : ZMod 2) ≠ j := by
  fin_cases j <;> decide

private lemma zmod2_zero_add_one' : (0 : ZMod 2) + 1 = 1 := by decide
private lemma zmod2_one_add_one' : (1 : ZMod 2) + 1 = 0 := by decide

/-- Under `mom_ham_split` at `n = 2`, source slots equal the bracket-calculus values. -/
theorem hamAdvFrom_eq_computed (T : HKTPointSplitTargetDyn 2)
    (x : PhaseSpace 2) (j : ZMod 2) :
    T.hamAdvFrom x j = computedHamAdvFrom T x j := by
  have h := T.mom_ham_split (siteDelta j) (siteDelta j) x
  unfold computedHamAdvFrom
  have hsum :
      (∑ i : ZMod 2,
          siteDelta j i *
            (siteDelta j (i + 1) * T.hamAdvTo x i -
              siteDelta j i * T.hamAdvFrom x i))
        = -T.hamAdvFrom x j := by
    rw [Finset.sum_eq_single j]
    · have hj : siteDelta j j = (1 : ℝ) := siteDelta_self j
      have hjp : siteDelta j (j + 1) = (0 : ℝ) := by
        simp [siteDelta, zmod2_succ_ne j]
      simp [hj, hjp]
    · intro i _ hi
      simp [siteDelta, hi]
    · simp
  have hbr :
      bracket (fun y => ∑ i : ZMod 2, siteDelta j i * T.momDensity y i)
          (fun y => ∑ i : ZMod 2, siteDelta j i * T.hamDensity y i) x
        = -T.hamAdvFrom x j :=
    h.trans hsum
  linarith

/-- Under `mom_ham_split` at `n = 2`, target slots equal the bracket-calculus values. -/
theorem hamAdvTo_eq_computed (T : HKTPointSplitTargetDyn 2)
    (x : PhaseSpace 2) (j : ZMod 2) :
    T.hamAdvTo x j = computedHamAdvTo T x j := by
  have h := T.mom_ham_split (siteDelta j) (siteDelta (j + 1)) x
  unfold computedHamAdvTo
  have hsum :
      (∑ i : ZMod 2,
          siteDelta j i *
            (siteDelta (j + 1) (i + 1) * T.hamAdvTo x i -
              siteDelta (j + 1) i * T.hamAdvFrom x i))
        = T.hamAdvTo x j := by
    rw [Finset.sum_eq_single j]
    · have hj : siteDelta j j = (1 : ℝ) := siteDelta_self j
      have hTo : siteDelta (j + 1) (j + 1) = (1 : ℝ) := siteDelta_self (j + 1)
      have hFrom : siteDelta (j + 1) j = (0 : ℝ) := by
        have : j ≠ (j + 1 : ZMod 2) := (zmod2_succ_ne j).symm
        simp [siteDelta, this]
      simp [hj, hTo, hFrom]
    · intro i _ hi
      simp [siteDelta, hi]
    · simp
  have hbr :
      bracket (fun y => ∑ i : ZMod 2, siteDelta j i * T.momDensity y i)
          (fun y => ∑ i : ZMod 2, siteDelta (j + 1) i * T.hamDensity y i) x
        = T.hamAdvTo x j :=
    h.trans hsum
  linarith

/-! ## Strengthened target -/

/-- STRENGTHENED TARGET. Extends the weak schema with three critic strengthenings:
(1) load-bearing momentum (nontrivial `{Mom, Mom}` bracket);
(2) advection slots equal the Mom–Ham bracket-calculus extractions
    (`computedHamAdvFrom` / `computedHamAdvTo`), not free decorative choices;
(3) kinetic regularity (some smeared-Ham momentum partial is nonzero),
    excluding purely potential densities.

The weak schema `HKTPointSplitTargetDyn` remains as documentation of the
decoy-inhabitable class. -/
structure HKTPointSplitTargetDynStrong (n : ℕ) [NeZero n]
    extends HKTPointSplitTargetDyn n where
  /-- (1) `momDensity` generates a nontrivial bracket. -/
  mom_load_bearing :
    ∃ (v w : ZMod n → ℝ) (x : PhaseSpace n),
      bracket (fun y => ∑ j : ZMod n, v j * momDensity y j)
          (fun y => ∑ j : ZMod n, w j * momDensity y j) x ≠ 0
  /-- (2) Source advection is the bracket-calculus value of `hamDensity`/`momDensity`. -/
  advFrom_tied : ∀ (x : PhaseSpace n) (j : ZMod n),
    hamAdvFrom x j = computedHamAdvFrom toHKTPointSplitTargetDyn x j
  /-- (2) Target advection is the bracket-calculus value of `hamDensity`/`momDensity`. -/
  advTo_tied : ∀ (x : PhaseSpace n) (j : ZMod n),
    hamAdvTo x j = computedHamAdvTo toHKTPointSplitTargetDyn x j
  /-- (3) Kinetic regularity: some π-partial of the unsmeared unit-lapse Ham is nonzero. -/
  kinetic_regular :
    ∃ (x : PhaseSpace n) (j : ZMod n),
      pderivP (fun y => ∑ i : ZMod n, hamDensity y i) j x ≠ 0

/-! ## Quartic zero-momentum decoy (inhabits WEAK; fails STRONG) -/

/-- MODEL. Quartic kinetic density on two sites: `h_j = π_j^4`. -/
def quarticHamDensity2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  (x.2 j) ^ 4

/-- MODEL. Vanishing momentum density (the decoy). -/
def zeroMomDensity2 (_x : PhaseSpace 2) (_j : ZMod 2) : ℝ :=
  0

/-- Decorative nonconstant structure (same shape as `structureDyn`). -/
def decorativeStructure2 (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  1 + x.1 j * x.1 j

def quarticHam2 (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, N j * quarticHamDensity2 x j

def quarticHam2D (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  ∑ i : ZMod 2, N i • ((4 • (x.2 i) ^ 3) • coordP i)

lemma hasFDerivAt_quarticHam2 (N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (quarticHam2 N) (quarticHam2D N x) x := by
  unfold quarticHam2 quarticHam2D quarticHamDensity2
  exact HasFDerivAt.fun_sum fun i _ =>
    ((hasFDerivAt_coord_snd i x).pow 4).const_mul (N i)

theorem differentiable_quarticHam2 (N : ZMod 2 → ℝ) :
    Differentiable ℝ (quarticHam2 N) :=
  fun x => (hasFDerivAt_quarticHam2 N x).differentiableAt

lemma pderivQ_quarticHam2 (N : ZMod 2 → ℝ) (j : ZMod 2) (x : PhaseSpace 2) :
    pderivQ (quarticHam2 N) j x = 0 := by
  rw [pderivQ, (hasFDerivAt_quarticHam2 N x).fderiv, quarticHam2D,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [coordP]

theorem bracket_quarticHam2_quarticHam2 (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (quarticHam2 N) (quarticHam2 M) x = 0 := by
  simp only [bracket, pderivQ_quarticHam2]
  exact Finset.sum_eq_zero fun _ _ => by ring

lemma zeroMom2_eq_zero (w : ZMod 2 → ℝ) :
    (fun x : PhaseSpace 2 => ∑ j : ZMod 2, w j * zeroMomDensity2 x j)
      = fun _ => (0 : ℝ) := by
  funext y
  simp [zeroMomDensity2]

lemma differentiable_zeroMom2 (w : ZMod 2 → ℝ) :
    Differentiable ℝ
      (fun x : PhaseSpace 2 => ∑ j : ZMod 2, w j * zeroMomDensity2 x j) := by
  rw [zeroMom2_eq_zero]
  exact differentiable_const 0

lemma bracket_zeroMom2_any (w : ZMod 2 → ℝ) (G : PhaseSpace 2 → ℝ)
    (x : PhaseSpace 2) :
    bracket (fun y => ∑ j : ZMod 2, w j * zeroMomDensity2 y j) G x = 0 := by
  have hz := zeroMom2_eq_zero w
  simp only [bracket, pderivQ, pderivP]
  have hQ : ∀ i, fderiv ℝ (fun y => ∑ j : ZMod 2, w j * zeroMomDensity2 y j) x
      (Pi.single i 1, 0) = 0 := by
    intro i
    rw [hz]
    simp
  have hP : ∀ i, fderiv ℝ (fun y => ∑ j : ZMod 2, w j * zeroMomDensity2 y j) x
      (0, Pi.single i 1) = 0 := by
    intro i
    rw [hz]
    simp
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [hQ i, hP i]

lemma decorativeStructure2_not_constant : ¬ PhaseSpaceConstant decorativeStructure2 := by
  intro h
  have hEq := h zeroPhasePoint unitConfigurationPoint (0 : ZMod 2)
  simp only [decorativeStructure2, zeroPhasePoint, unitConfigurationPoint] at hEq
  norm_num at hEq

def quarticNondegPhase : PhaseSpace 2 :=
  (fun _ => (0 : ℝ), fun j => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

theorem quarticHamDensity2_nondeg :
    quarticHamDensity2 quarticNondegPhase (0 : ZMod 2) ≠ 0 := by
  simp only [quarticHamDensity2, quarticNondegPhase]
  norm_num

/-- THEOREM. Quartic zero-momentum decoy inhabits the WEAK point-split schema.
Formal witness that `HKTPointSplitTargetDyn` is decoy-inhabitable
(`D-qg-hkt-pointsplit-adjudication-20260722`). -/
def quarticZeroMomTarget : HKTPointSplitTargetDyn 2 where
  hamDensity := quarticHamDensity2
  momDensity := zeroMomDensity2
  structureFunction := decorativeStructure2
  hamAdvFrom := fun _ _ => 0
  hamAdvTo := fun _ _ => 0
  momBracketDensity := fun _ _ => 0
  ham_differentiable := by
    intro N
    simpa [quarticHam2, quarticHamDensity2] using differentiable_quarticHam2 N
  mom_differentiable := differentiable_zeroMom2
  structure_nonconstant := decorativeStructure2_not_constant
  ham_local := by
    intro x y j _ _ hp
    dsimp only [quarticHamDensity2]
    rw [hp]
  ham_covariant := by
    intro x a j
    rfl
  structure_local := by
    intro x y j hx
    dsimp only [decorativeStructure2]
    rw [hx]
  mom_mom := by
    intro v w x
    have hL := bracket_zeroMom2_any v
      (fun y => ∑ j : ZMod 2, w j * zeroMomDensity2 y j) x
    -- Both sides vanish: LHS by zero mom, RHS by zero momBracketDensity.
    simpa [zeroMomDensity2] using hL
  mom_ham_split := by
    intro w N x
    have hL := bracket_zeroMom2_any w
      (fun y => ∑ j : ZMod 2, N j * quarticHamDensity2 y j) x
    -- Both sides vanish: LHS by zero mom, RHS by zero Adv slots.
    simpa [zeroMomDensity2] using hL
  ham_ham := by
    intro N M x
    have hL := bracket_quarticHam2_quarticHam2 N M x
    -- LHS vanishes (pure-π generators); RHS has zero momDensity factor.
    simpa [quarticHam2, quarticHamDensity2, zeroMomDensity2] using hL
  nondegenerate := ⟨quarticNondegPhase, (0 : ZMod 2), quarticHamDensity2_nondeg⟩

theorem quarticZeroMomTarget_mom_vanishes (x : PhaseSpace 2) (j : ZMod 2) :
    quarticZeroMomTarget.momDensity x j = 0 :=
  rfl

/-- The zero-momentum decoy has identically vanishing Mom–Mom brackets.
This is the strengthening field that kills it. -/
theorem quarticZeroMom_fails_mom_load_bearing :
    ¬ ∃ (v w : ZMod 2 → ℝ) (x : PhaseSpace 2),
      bracket (fun y => ∑ j : ZMod 2, v j * quarticZeroMomTarget.momDensity y j)
          (fun y => ∑ j : ZMod 2, w j * quarticZeroMomTarget.momDensity y j) x ≠ 0 := by
  rintro ⟨v, w, x, hne⟩
  have h := bracket_zeroMom2_any v
    (fun y => ∑ j : ZMod 2, w j * zeroMomDensity2 y j) x
  exact hne h

/-- THEOREM. The quartic zero-momentum decoy does **not** inhabit the
strengthened class. Killed by `mom_load_bearing`. -/
theorem quarticZeroMomTarget_not_strong :
    ¬ ∃ S : HKTPointSplitTargetDynStrong 2,
      S.toHKTPointSplitTargetDyn = quarticZeroMomTarget := by
  rintro ⟨S, hEq⟩
  have hBear := S.mom_load_bearing
  have hMom : S.momDensity = quarticZeroMomTarget.momDensity := by
    rw [← hEq]
  rw [hMom] at hBear
  exact quarticZeroMom_fails_mom_load_bearing hBear

/-! ## Honest HamDyn inhabitant of the strengthened class -/

def momLoadBearingWitnessPhase : PhaseSpace 2 :=
  (fun j : ZMod 2 => if j = (0 : ZMod 2) then (0 : ℝ) else 1,
    fun j : ZMod 2 => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

private lemma momLoadBearingWitness_vals :
    momLoadBearingWitnessPhase.1 (0 : ZMod 2) = 0 ∧
      momLoadBearingWitnessPhase.1 (1 : ZMod 2) = 1 ∧
        momLoadBearingWitnessPhase.2 (0 : ZMod 2) = 1 ∧
          momLoadBearingWitnessPhase.2 (1 : ZMod 2) = 0 := by
  simp [momLoadBearingWitnessPhase]

theorem hamDyn_mom_load_bearing_witness :
    bracket (MomDyn delta0) (MomDyn delta1) momLoadBearingWitnessPhase ≠ 0 := by
  have hv := momLoadBearingWitness_vals
  have h := bracket_MomDyn_MomDyn delta0 delta1 momLoadBearingWitnessPhase
  have hδ0 : delta0 (0 : ZMod 2) = (1 : ℝ) ∧ delta0 (1 : ZMod 2) = 0 := by simp [delta0]
  have hδ1 : delta1 (0 : ZMod 2) = (0 : ℝ) ∧ delta1 (1 : ZMod 2) = 1 := by simp [delta1]
  have hd0 : momDynBracketDensity momLoadBearingWitnessPhase (0 : ZMod 2) = (1 : ℝ) / 2 := by
    simp only [momDynBracketDensity, zmod2_zero_add_one', hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
    norm_num
  have hd1 : momDynBracketDensity momLoadBearingWitnessPhase (1 : ZMod 2) = (-1 : ℝ) / 2 := by
    simp only [momDynBracketDensity, zmod2_one_add_one', hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
    norm_num
  -- Coeffs: j=0 → 1, j=1 → -1; sum = 1/2 + 1/2 = 1.
  rw [h, sum_zmod2, zmod2_zero_add_one', zmod2_one_add_one', hδ0.1, hδ0.2, hδ1.1, hδ1.2, hd0,
    hd1]
  norm_num

theorem hamDyn_kinetic_regular_witness :
    pderivP (fun y => ∑ i : ZMod 2, hamDynDensity y i) (0 : ZMod 2)
        hamDynNondegPhase ≠ 0 := by
  have hEq : (fun y => ∑ i : ZMod 2, hamDynDensity y i) = HamDyn (fun _ => (1 : ℝ)) := by
    funext y
    have h := congrArg (fun F : PhaseSpace 2 → ℝ => F y)
      (hamDynDensity_smear (fun _ => (1 : ℝ)))
    -- h : ∑ 1 * ham = HamDyn 1; simplify the unit weights.
    simpa using h
  rw [hEq, pderivP_HamDyn]
  simp only [hamDynNondegPhase]
  norm_num

/-- THEOREM. Honest HamDyn inhabitant of the strengthened point-split target. -/
def hamDynPointSplitTargetStrong : HKTPointSplitTargetDynStrong 2 where
  toHKTPointSplitTargetDyn := hamDynPointSplitTarget
  mom_load_bearing := by
    refine ⟨delta0, delta1, momLoadBearingWitnessPhase, ?_⟩
    simpa [MomDyn] using hamDyn_mom_load_bearing_witness
  advFrom_tied := by
    intro x j
    simpa using hamAdvFrom_eq_computed hamDynPointSplitTarget x j
  advTo_tied := by
    intro x j
    simpa using hamAdvTo_eq_computed hamDynPointSplitTarget x j
  kinetic_regular :=
    ⟨hamDynNondegPhase, (0 : ZMod 2), hamDyn_kinetic_regular_witness⟩

theorem hktPointSplitTargetDynStrong_two_nonvacuous :
    Nonempty (HKTPointSplitTargetDynStrong 2) :=
  ⟨hamDynPointSplitTargetStrong⟩

/-- Discrimination receipt: honest passes strong; decoy fails strong. -/
theorem strong_target_discriminates_decoy :
    (Nonempty (HKTPointSplitTargetDynStrong 2)) ∧
      (¬ ∃ S : HKTPointSplitTargetDynStrong 2,
        S.toHKTPointSplitTargetDyn = quarticZeroMomTarget) :=
  ⟨hktPointSplitTargetDynStrong_two_nonvacuous, quarticZeroMomTarget_not_strong⟩

/-! ## Binding rigidity Prop over the strengthened class (PROVEN FALSE) -/

/-- PROVEN FALSE. Formerly the GR-strength rigidity target over
`HKTPointSplitTargetDynStrong` at `n = 2`. Killed by the balanced-quartic
inhabitant (`quarticBalancedStrongTarget`) in
`HKTCanonicalMomTarget.not_HKTRigidityStatementPointSplitDynN2Strong`
(`D-qg-hkt-rigidity-route-20260722`). Binding rigidity moves to
`HKTRigidityStatementPointSplitDynN2Canonical` over the CanonicalMom class. -/
def HKTRigidityStatementPointSplitDynN2Strong : Prop :=
  ∀ T : HKTPointSplitTargetDynStrong 2,
    ∃ cKin cGrad cVac : ℝ, ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.hamDensity x j
        = cKin * (x.2 j * x.2 j)
          + cGrad *
              (T.structureFunction x j *
                ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))
          + cVac

/-! ### Axiom receipts -/

#print axioms hamAdvFrom_eq_computed
#print axioms hamAdvTo_eq_computed
#print axioms quarticZeroMomTarget_not_strong
#print axioms hamDyn_mom_load_bearing_witness
#print axioms hamDyn_kinetic_regular_witness
#print axioms hktPointSplitTargetDynStrong_two_nonvacuous
#print axioms strong_target_discriminates_decoy

end
end HKTPointSplitStrong
end SevenGaps
end Gravity
end IndisputableMonolith
