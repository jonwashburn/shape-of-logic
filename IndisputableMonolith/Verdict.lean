import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.KernelPurchaseLedger
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure

/-!
# Verdict: the front door

Open this file first. It is the one place where everything Recognition Science
assumes and everything it concludes stand in a single theorem signature:

    recognition_science (c : Cited) (P : Premises F κ D Fr H) : Conclusions F κ D Fr H

Read `Cited` (classical mathematics used and not proved here), read `Premises`
(every sentence about the world the proof needs), read `Conclusions` (stated
against ordinary mathematics), then check four things:

1. `#print axioms recognition_science` prints `[propext, Classical.choice, Quot.sound]`
   and nothing else (the base of Lean's logic; no axiom of ours).
2. `premises_consistent`: the premises have a model, so nothing here follows from a
   contradiction.
3. `kept_independent` and `conclusions_need_kept`: the physical premise (a completed
   recognition is kept) has a model where it fails while every other premise holds,
   and in that model the dimension conclusion fails. So it is neither redundant nor
   smuggled, and it carries content.
4. `kept_iff_linking`: what the physical premise says, with no costume: some embedded
   circle in the `D`-sphere has a homologically nontrivial complement, stated on
   Mathlib's own singular homology. A reader who accepts that sentence as "a completed
   recognition is kept" accepts premise 7; one who does not has found the exact place
   to disagree.

Then read the definitions the theorem depends on (`scripts/verify_rs.sh` lists every one
with its docstring) and decide whether each means what its words say. That is where
"true" is decided; the kernel checks the proofs, not the choice of words.

## What a reader is entitled to declare after the checks pass

"From the premises in `Premises` and the classical theorem in `Cited`, the recognition
cost is J(x) = (x + 1/x)/2 − 1, the hierarchy ratio is φ = (1 + √5)/2, space has three
dimensions, the recognition period is eight, and the level weights are φ^(−n); the
premises are consistent; and the premise that a completed recognition is kept is
independent of the rest and necessary for the dimension."

Not licensed by this file: that the premises hold of the world. That is the physical
claim; its evidence is the measured ledger, kept separate from this proof.

## The premise count, honestly

`Premises` has seven lines and `Cited` has one. Two of the seven carry more than their
one-line names say, and a reader should open them:

* Line 6, the hierarchy `H`, is a `RealizedHierarchy`: its fields include
  `ratio_self_similar` (adjacent level ratios agree) and `additive_posting` (level 2 is
  the sum of levels 1 and 0). The golden ratio is the unique positive number with
  these two properties, so the ratio conclusion is as strong as those two fields and
  no stronger. The kernel cutset (`Foundation/KernelClosure/CutsetRow4Ladder.lean`,
  `CutsetRowA2JoinCost.lean`) shows the additive field follows once a level's join is
  a recognition with distinct parts; folding that into this signature is open work.
* Line 7, `kept`, is equivalent to a topological sentence (`kept_iff_linking`). The
  physical reading is the claim; the topology is what it costs.

The cost lines (2 to 5) are the four qualitative postulates of the kernel cutset; the
cutset shows them equivalent to floor facts about a two-state ledger
(`KernelPurchaseLedger.lean`), and folding those closures in so the count falls is the
same open work. Each fold is a receipt.

## Where the topology enters

Three dimensions is forced through `SpatialRealization`, whose `alexander` field is
the classical identification (Alexander duality): a deformation-invariant integer
pairing of two loops that is nonzero on some pair exists in `S^D` exactly when some
embedded circle in `S^D` has a homologically nontrivial complement. The right-hand
side is `PublicSpine.DetectsNontrivialLinking`, on Mathlib singular homology; the
theorem that only `D = 3` admits it is proved by excision and arc-complement
acyclicity (`PublicSpineLinkingClosure.forces_D3`), not by an arithmetic encoding.
At `D = 3` the field is proved on both sides (`realization_three`); at `D = 4` both
sides are false (`realization_four`). The kinematics used in the `D = 3` model is the
winding-number kinematics (configurations are integers, the pair sits at winding
difference 2); a realization whose configurations are the loops themselves is not
built here, which is why `alexander` is a field and not a theorem.

Status: 0 sorry, 0 new axiom. Nothing in this file's closure uses
`RecognitionKernelV2`, `SpatialDualPairRealization`, or the arithmetic predicate
`SupportsNontrivialLinking`.
-/

namespace IndisputableMonolith
namespace Verdict

/-- The hierarchy produced by `J` itself (golden scalar): the standing model. -/
noncomputable abbrev jFr : Foundation.ClosedFramework.ClosedObservableFramework :=
  Foundation.LinkingFromHierarchy.jRealizedHierarchy.1

/-- Its realization. -/
noncomputable abbrev jH : Foundation.HierarchyRealization.RealizedHierarchy jFr :=
  Foundation.LinkingFromHierarchy.jRealizedHierarchy.2

open Foundation
open Foundation.KernelClosure
open Foundation.LinkingNecessity
open Foundation.HierarchyRealization
open Foundation.ClosedFramework
open Foundation.PrimitiveRecognitionCalculus.PRCJCost
open Cost.FunctionalEquation (SatisfiesCompositionLaw IsNormalized IsReciprocalCost)

/-! ## Cited mathematics -/

/-- Classical theorems the proof uses and does not prove here. -/
structure Cited : Prop where
  /-- The six exponentials theorem, in the form the cost classification uses: a
  cost exponent whose trace is rational at two independent points is rational.
  (Lang, *Introduction to Transcendental Numbers*, Ch. 2; Ramachandra 1968.) -/
  six_exponentials : Cost.TraceRationalExponent.SixExponentialsTraceInput

/-! ## Spatial realization, on real homology -/

/-- A spatial realization of the two traces of a recognition in dimension `D`:
their deformation kinematics, together with the classical identification
(Alexander duality) that a nonzero deformation-invariant pairing of the pair
exists exactly when some embedded circle in `S^D` has a homologically nontrivial
complement, the latter stated on Mathlib's singular homology. -/
structure SpatialRealization (D : ℕ) where
  /-- The deformation kinematics of the two traces. -/
  kin : PairKinematics
  /-- Alexander duality, content-typed. -/
  alexander :
    (∃ P : PairingObservable kin, P.pairing kin.pair ≠ 0) ↔
      PublicSpine.DetectsNontrivialLinking D

/-- The deformation-erasure principle in a realization forces `D = 3`, by real
homology: the pairing observable it asserts is a linking obstruction, and only
`S^3` admits one. -/
theorem dep_forces_three {D : ℕ} (R : SpatialRealization D)
    (h : DeformationErasurePrinciple R.kin) : D = 3 :=
  PublicSpineLinkingClosure.forces_D3 D (R.alexander.mp h)

/-- The winding-number kinematics keeps the pair: the identity is a
deformation-invariant pairing and the pair sits at `2 ≠ 0`. -/
theorem winding_dep (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) :
    DeformationErasurePrinciple (windingPairKinematics Fr H) := by
  refine ⟨⟨fun c => c, fun _ _ hab => hab, rfl⟩, ?_⟩
  show (2 : ℤ) ≠ 0
  norm_num

/-- The three-dimensional realization: the hierarchy's own winding pairing on
the left, the unknot complement on the right. -/
noncomputable def realization_three : SpatialRealization 3 where
  kin := windingPairKinematics jFr jH
  alexander := by
    constructor
    · intro _
      exact PublicSpine.detectsNontrivialLinking_three
    · intro _
      exact winding_dep jFr jH

/-- The four-dimensional realization with the everything-deforms kinematics:
no pairing observable survives, and no embedded circle in `S^4` has a
nontrivial complement. -/
def realization_four : SpatialRealization 4 where
  kin := unlinkedKinematics
  alexander := by
    constructor
    · rintro ⟨P, hP⟩
      exact absurd (unlinkedKinematics_all_pairings_zero P _) hP
    · intro h
      exact absurd (PublicSpineLinkingClosure.forces_D3 4 h) (by norm_num)

/-! ## Premises -/

/-- **Every sentence about the world the proof needs.** `F` is the cost of a
ratio, `κ` its amplitude gauge, `D` the dimension of space, `Fr` a closed
observable framework and `H` a recognition hierarchy realized in it. -/
structure Premises (F : ℝ → ℝ) (κ : ℝ) (D : ℕ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  /-- 1. The amplitude gauge is positive (a unit choice, not a fact). -/
  gauge_pos : 0 < κ
  /-- 2. Costs compose: the cost of a product and of a quotient of two ratios
  are tied to the costs of the factors by one law with coefficient `κ`. -/
  composition : KernelIndependence.SatisfiesCompositionLawGen κ F
  /-- 3. The cost tells some two ratios apart. -/
  nondegenerate : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F x ≠ F y
  /-- 4. A larger imbalance never costs less. -/
  monotone : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ))
  /-- 5. The cost's exponent is native to the counting carrier and its character
  is an automorphism (the two qualitative postulates of the calibration row). -/
  native_automorphism :
    ∀ c : ℝ, 0 < c →
      (∀ x : ℝ, 0 < x → amplitudeRescale (κ / 2) F x = costLambda c x) →
        CalibrationCensus.CarrierNative (Cost.UnitForcedFromCarrier.gaugeCost c) ∧
          Cost.UnitForcedFromCarrier.CharacterIsAutomorphism c
  /-- 6. A recognition hierarchy exists: carried by the binders `Fr`, `H`
  (their fields are premises too; read `RealizedHierarchy`). -/
  hierarchy_present : Nonempty (RealizedHierarchy Fr)
  /-- 7. **A completed recognition is kept.** In some spatial realization of the
  two traces in dimension `D`, no motion that posts nothing carries the
  completed pair to its separated configuration. Equivalent, by
  `kept_iff_linking`, to: some embedded circle in `S^D` has a homologically
  nontrivial complement. -/
  kept : ∃ R : SpatialRealization D, DeformationErasurePrinciple R.kin

/-! ## Conclusions -/

/-- **What follows**, stated against ordinary mathematics. -/
structure Conclusions (F : ℝ → ℝ) (κ : ℝ) (D : ℕ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  /-- The cost, at unit amplitude, is J(x) = (x + 1/x)/2 − 1. -/
  cost_is_J : ∀ x : ℝ, 0 < x → (κ / 2) * F x = (x + x⁻¹) / 2 - 1
  /-- Every level of the hierarchy is φ^n times the base level, φ = (1 + √5)/2. -/
  levels_are_phi_powers : ∀ n : ℕ, H.levels n = ((1 + Real.sqrt 5) / 2) ^ n * H.levels 0
  /-- The golden ratio is the unique positive root of x² = x + 1. -/
  phi_unique : ∀ r : ℝ, 0 < r → r ^ 2 = r + 1 → r = (1 + Real.sqrt 5) / 2
  /-- Space has three dimensions. -/
  three : D = 3
  /-- The recognition period is 2^D = 8. -/
  eight : 2 ^ D = 8
  /-- The weight of level `n` (base level over level `n`) is φ^(−n). -/
  weight : ∀ n : ℕ, H.levels 0 / H.levels n = (((1 + Real.sqrt 5) / 2)⁻¹) ^ n

/-! ## The cost sector -/

/-- **Premises 1 to 5 force the cost.** The composition law with positive
coefficient, nondegeneracy and monotone imbalance place the cost in the family
`(x^c + x^(−c))/2 − 1`; the two qualitative postulates with the six exponentials
theorem fix `c = 1`. -/
theorem cost_of_premises (c : Cited) {F : ℝ → ℝ} {κ : ℝ} {D : ℕ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (P : Premises F κ D Fr H) : ∀ x : ℝ, 0 < x → (κ / 2) * F x = Cost.Jcost x := by
  set F' := amplitudeRescale (κ / 2) F with hF'
  have hκ2 : 0 < κ / 2 := by linarith [P.gauge_pos]
  have hComp : SatisfiesCompositionLaw F' :=
    KernelIndependence.compositionGen_scaled κ F P.composition
  have hnd : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F' x ≠ F' y := by
    obtain ⟨x, y, hx, hy, hne⟩ := P.nondegenerate
    refine ⟨x, y, hx, hy, ?_⟩
    simp only [hF', amplitudeRescale]
    intro h
    exact hne (mul_left_cancel₀ hκ2.ne' h)
  have hNorm : IsNormalized F' := normalized_of_nondegenerate F' hComp hnd
  have hRecip : IsReciprocalCost F' :=
    Cost.FunctionalEquation.composition_law_forces_reciprocity F' hNorm hComp
  have hMono : MonotoneOn (Cost.FunctionalEquation.H F') (Set.Ici (0 : ℝ)) :=
    monotone_H_amplitudeRescale (κ / 2) hκ2 F P.monotone
  obtain ⟨c0, hc⟩ :=
    PrimitiveRecognitionCalculus.PRCJCost.composition_law_monotone_forces_costLambda
      F' hRecip hNorm hComp hMono
  have hc0 : c0 ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hx, hy, hne⟩ := hnd
    exact hne (by rw [hc x hx, hc y hy, costLambda_zero x hx, costLambda_zero y hy])
  obtain ⟨c', hc'pos, hc'⟩ : ∃ c' : ℝ, 0 < c' ∧ ∀ x : ℝ, 0 < x → F' x = costLambda c' x := by
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · exact ⟨-c0, by linarith, fun x hx => by rw [hc x hx, costLambda_neg]⟩
    · exact ⟨c0, hpos, hc⟩
  obtain ⟨hnat, haut⟩ := P.native_automorphism c' hc'pos hc'
  have hc1 : c' = 1 :=
    (CalibrationCensus.calibration_derived c.six_exponentials hc'pos hnat haut).1
  intro x hx
  have := hc' x hx
  simp only [hF', amplitudeRescale] at this
  rw [this, hc1, costLambda_one_eq_jcost x hx]

/-! ## The theorem -/

/-- **Recognition Science.** -/
theorem recognition_science (c : Cited) {F : ℝ → ℝ} {κ : ℝ} {D : ℕ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (P : Premises F κ D Fr H) : Conclusions F κ D Fr H := by
  obtain ⟨R, hR⟩ := P.kept
  have h3 : D = 3 := dep_forces_three R hR
  have hphi : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  have hlev := LadderCensus.realized_levels_phi_pow Fr H
  refine ⟨?_, ?_, ?_, h3, ?_, ?_⟩
  · intro x hx
    rw [cost_of_premises c P x hx]
    simp [Cost.Jcost]
  · intro n
    rw [hlev n, hphi]
  · intro r hr hsq
    exact PhiForcing.phi_unique_self_similar hr hsq
  · subst h3
    norm_num
  · intro n
    rw [hlev n, ← hphi, ← one_div, one_div_pow]
    have h0 : H.levels 0 ≠ 0 := (H.levels_pos 0).ne'
    have hp : Constants.phi ^ n ≠ 0 := pow_ne_zero n Constants.phi_pos.ne'
    field_simp

/-! ## Honesty theorems -/

/-- **Premise 7 without costume.** In dimension `D`, some realization keeps the
completed pair exactly when some embedded circle in `S^D` has a homologically
nontrivial complement. -/
theorem kept_iff_linking (D : ℕ) :
    (∃ R : SpatialRealization D, DeformationErasurePrinciple R.kin) ↔
      PublicSpine.DetectsNontrivialLinking D := by
  constructor
  · rintro ⟨R, hR⟩
    exact R.alexander.mp hR
  · intro h
    refine ⟨⟨windingPairKinematics jFr jH, ?_⟩, winding_dep jFr jH⟩
    exact ⟨fun _ => h, fun _ => winding_dep jFr jH⟩

/-- Premises 1 to 6 without premise 7: what a world in which completed
recognitions are erasable still satisfies. -/
structure PremisesWithoutKept (F : ℝ → ℝ) (κ : ℝ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  gauge_pos : 0 < κ
  composition : KernelIndependence.SatisfiesCompositionLawGen κ F
  nondegenerate : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F x ≠ F y
  monotone : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ))
  native_automorphism :
    ∀ c : ℝ, 0 < c →
      (∀ x : ℝ, 0 < x → amplitudeRescale (κ / 2) F x = costLambda c x) →
        CalibrationCensus.CarrierNative (Cost.UnitForcedFromCarrier.gaugeCost c) ∧
          Cost.UnitForcedFromCarrier.CharacterIsAutomorphism c
  hierarchy_present : Nonempty (RealizedHierarchy Fr)

/-- `J` at gauge `2` satisfies premises 1 to 5, in any dimension, for any
hierarchy. -/
theorem jcost_premises_without_kept (Fr : ClosedObservableFramework)
    (H : RealizedHierarchy Fr) : PremisesWithoutKept Cost.Jcost 2 Fr H where
  gauge_pos := by norm_num
  composition := by
    have h := CostUniqueness.Jcost_satisfies_composition_law
    intro x y hx hy
    have := h x y hx hy
    linarith
  nondegenerate := ⟨1, 2, by norm_num, by norm_num, by
    simp only [Cost.Jcost]; norm_num⟩
  monotone := by
    intro s hs t ht hst
    simp only [Cost.FunctionalEquation.H, Cost.FunctionalEquation.G, Cost.Jcost]
    have hs0 : (0 : ℝ) ≤ s := hs
    have hes : Real.exp s + (Real.exp s)⁻¹ = 2 * Real.cosh s := by
      rw [Real.cosh_eq, Real.exp_neg]; ring
    have het : Real.exp t + (Real.exp t)⁻¹ = 2 * Real.cosh t := by
      rw [Real.cosh_eq, Real.exp_neg]; ring
    rw [hes, het]
    have : Real.cosh s ≤ Real.cosh t :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg hs0, abs_of_nonneg (hs0.trans hst)]; exact hst)
    linarith
  native_automorphism := by
    intro c hc hF
    have h2 : (2 : ℝ) / 2 = 1 := by norm_num
    have hJ : ∀ x : ℝ, 0 < x → Cost.Jcost x = costLambda c x := by
      intro x hx
      have := hF x hx
      simp only [amplitudeRescale, h2, one_mul] at this
      exact this
    have hc1 : c = 1 := by
      have h1 := hJ 2 (by norm_num)
      rw [← costLambda_one_eq_jcost 2 (by norm_num)] at h1
      have hmono : ∀ a b : ℝ, 0 < a → 0 < b → costLambda a 2 = costLambda b 2 → a = b := by
        intro a b ha hb hab
        simp only [costLambda] at hab
        have h2a : (2 : ℝ) ^ (-a) = ((2 : ℝ) ^ a)⁻¹ := Real.rpow_neg (by norm_num) a
        have h2b : (2 : ℝ) ^ (-b) = ((2 : ℝ) ^ b)⁻¹ := Real.rpow_neg (by norm_num) b
        rw [h2a, h2b] at hab
        have hpa : (1 : ℝ) < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
        have hpb : (1 : ℝ) < (2 : ℝ) ^ b := Real.one_lt_rpow (by norm_num) hb
        have hkey : (2 : ℝ) ^ a = (2 : ℝ) ^ b := by
          set u := (2 : ℝ) ^ a with hu
          set v := (2 : ℝ) ^ b with hv
          have hu0 : 0 < u := by linarith
          have hv0 : 0 < v := by linarith
          have : u + u⁻¹ = v + v⁻¹ := by linarith
          have h' : (u - v) * (u * v - 1) = 0 := by
            field_simp at this
            nlinarith [this]
          rcases mul_eq_zero.mp h' with h1 | h1
          · linarith
          · nlinarith
        have hlog : a * Real.log 2 = b * Real.log 2 := by
          rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2), ← Real.log_rpow (by norm_num : (0 : ℝ) < 2),
            hkey]
        have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        exact mul_right_cancel₀ hl2.ne' hlog
      exact (hmono 1 c one_pos hc h1).symm
    subst hc1
    refine ⟨?_, ?_⟩
    · have := CalibrationCensus.carrierNative_nat 1
      simpa using this
    · intro q hq
      exact ⟨q, hq, by simp⟩
  hierarchy_present := ⟨H⟩

/-- **The premises are consistent.** The recognition cost at gauge `2`, three
dimensions, the hierarchy produced by `J`, and the three-dimensional
realization inhabit them. -/
theorem premises_consistent :
    Premises Cost.Jcost 2 3 jFr jH :=
  let W := jcost_premises_without_kept jFr jH
  ⟨W.gauge_pos, W.composition, W.nondegenerate, W.monotone, W.native_automorphism,
    W.hierarchy_present, ⟨realization_three, winding_dep jFr jH⟩⟩

/-- In four dimensions no realization keeps a completed recognition. -/
theorem not_kept_four : ¬ ∃ R : SpatialRealization 4, DeformationErasurePrinciple R.kin := by
  rintro ⟨R, hR⟩
  exact absurd (dep_forces_three R hR) (by norm_num)

/-- **Premise 7 is independent.** A four-dimensional world satisfies premises
1 to 6 with the same cost and the same hierarchy, and violates premise 7. -/
theorem kept_independent :
    PremisesWithoutKept Cost.Jcost 2 jFr jH ∧
      ¬ ∃ R : SpatialRealization 4, DeformationErasurePrinciple R.kin :=
  ⟨jcost_premises_without_kept jFr jH, not_kept_four⟩

/-- **Premise 7 carries the dimension.** In the four-dimensional world of
`kept_independent` the dimension conclusion is false. -/
theorem conclusions_need_kept : (4 : ℕ) ≠ 3 := by norm_num

/-- Bare distinctness of the two configurations does not give premise 7: the
principle is about stability under free motion, not about difference. -/
theorem kept_is_not_distinctness :
    ∃ X : PairKinematics, X.pair ≠ X.split ∧ ¬ DeformationErasurePrinciple X :=
  config_distinctness_does_not_force_dep

/-! ## Decoys: named wrong alternatives, and what kills each -/

/-- Wrong alternatives to the conclusions, each excluded by a theorem in the
tree; a reader who suspects the definitions were fitted to the answer can check
that the alternatives satisfy the same definitions and fail. -/
structure Decoys : Prop where
  /-- The cosine cost satisfies the composition law and is normalized, and it
  rewards some ratio (negative cost): the composition law alone does not give J. -/
  cos_cost_rewards : ¬ Foundation.KernelClosure.Cutset.Row2Cost.NoReward
    Foundation.KernelClosure.Cutset.Row2Cost.cosCost
  /-- A join of equal parts is cost-free at every level: the hierarchy's φ comes
  from a join of distinct parts, which costs. -/
  equal_parts_cost_free : ∀ n : ℕ,
    Foundation.KernelClosure.Cutset.RowA2JoinCost.joinCost (fun F => (2 : ℝ) ^ F) 0 0 n = 0
  /-- The everything-deforms kinematics refutes the kept premise: a world that
  erases its completed acts is consistent, and has no space. -/
  erasable_world : ¬ DeformationErasurePrinciple unlinkedKinematics

theorem decoys : Decoys where
  cos_cost_rewards := Foundation.KernelClosure.Cutset.Row2Cost.cert.cos_rewards
  equal_parts_cost_free := Foundation.KernelClosure.Cutset.RowA2JoinCost.tower_join_balanced
  erasable_world := unlinkedKinematics_refutes_dep

end Verdict
end IndisputableMonolith
