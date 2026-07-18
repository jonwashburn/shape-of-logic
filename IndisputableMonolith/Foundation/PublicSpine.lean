import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Strength
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaForced
import IndisputableMonolith.Foundation.UniversalForcing.ReciprocalGenerator
import IndisputableMonolith.Foundation.AlexanderDuality
import IndisputableMonolith.Foundation.DimensionForcing
import IndisputableMonolith.Foundation.CircleWindingChain
import IndisputableMonolith.Foundation.MathlibCohomologyBridge
import IndisputableMonolith.Foundation.UnknotComplementRetract
import IndisputableMonolith.Foundation.LinkingVanishingLowDim
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Verification.T6T8SpineAudit

/-!
# PublicSpine — dual forcing surface (δ stratification)

This module is the **public dual** of `UnifiedForcingChain`. It does **not** delete
or replace UFC. The Boolean / certificate spine stays for loop compatibility and
pedagogy. This surface is the honest δ-stratified map:

* δ-only tower: ℕ / ℤ / ℚ (`forced_tower_holds`); continuum cut is
  `classicalExtension` (panel K2: do not put ¬ℝ under `deltaOnly`)
* cost form vs unit calibration (purchases / gauges, not free THEOREMs)
* φ from the reciprocal involution (`ReciprocalGenerator`)
* H₁(S¹;ℤ) ≅ ℤ kept as THEOREM; the D=3 / 8-tick bridge target is **CLOSED**
  (campaign P-d3link, 2026-07-18): `AlexanderLinkingBridge` is fully inhabited
  in `Foundation.PublicSpineLinkingClosure` (0 sorry, axioms exactly
  `[propext, Classical.choice, Quot.sound]`, no appeal to
  `DimensionForcing.linking_requires_D3`, no arithmetic encoding). The pieces:
  `d3_detects` (unknot complement retract), `CubePeriodEight` (pigeonhole),
  vanishing at D=0,1, and `forces_D3` for D=2 and D≥4 via the excision spine
  and arc-complement acyclicity (Hatcher 2B.1, arc case). The content-typed
  binder below is unchanged (panel K1: kills encoding cheat); only its
  inhabitation status moved from OPEN to THEOREM.

Contract (dual-surface rules):
1. Papers / loops that mean "what is forced" should cite **this** module.
2. UFC names remain valid as `CERTIFICATE` / floor witnesses, not as the
   architecture claim.
3. No encoding predicates: T8/T7 require `AlexanderLinkingBridge`, never
   `SphereAdmitsCircleLinking` as currently defined.
4. FOP / unique-cost paper is untouched; this is Lean-map honesty only.

Plan: `δ/Delta_Spine_Retype_Map_20260708.html`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open PrimitiveRecognitionCalculus
open PrimitiveRecognitionCalculus.Forced
open UniversalForcing.ReciprocalGenerator
open Cost.FunctionalEquation
open Verification.T6T8SpineAudit
open AlexanderDuality
open DimensionForcing

/-- Strength-tagged claim: the public surface refuses untagged THEOREM badges. -/
structure Tagged (tag : StrengthTag) (P : Prop) : Prop where
  holds : P

/-- **δ-only tower:** ℕ / ℤ / ℚ are physically real (choice-free certificates).
Panel K2: do NOT conjoin the classical `¬ℝ` half under `deltaOnly`. -/
def ForcedTower : Prop :=
  PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ

theorem forced_tower_holds : Tagged StrengthTag.deltaOnly ForcedTower where
  holds := forcedTower

/-- Continuum cut: ℝ is not δ-forced. Classical uncountability lives here, so the
tag is `classicalExtension`, not `deltaOnly` (panel K2). -/
theorem continuum_is_purchase :
    Tagged StrengthTag.classicalExtension (¬ DeltaForced ℝ) where
  holds := not_deltaForced_real

/-- Full demarcation package (tower + continuum cut). Classical tag: the ℝ half
uses uncountability. Prefer `forced_tower_holds` + `continuum_is_purchase` when
citing δ-only vs purchase separately. -/
def Floor_Demarcation : Prop :=
  PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧ ¬ PhysicallyReal ℝ

theorem floor_demarcation_holds :
    Tagged StrengthTag.classicalExtension Floor_Demarcation where
  holds := demarcation

/-- **Cost form vs selection.** The continuous uniqueness theorem selects `J`
under reciprocity, normalization, RCL, calibration, continuity, and the Aczél
package. Honest tag is at least `traceClosure` (continuum carrier) plus the
calibration gauge; never `deltaOnly`. -/
structure CostSelectionPackage : Prop where
  /-- J is unique among reciprocal continuous calibrated RCL costs. -/
  j_unique :
    ∀ (F : ℝ → ℝ) [AczelSmoothnessPackage],
      IsReciprocalCost F → IsNormalized F → SatisfiesCompositionLaw F →
      IsCalibrated F → ContinuousOn F (Set.Ioi 0) →
      ∀ {x : ℝ}, 0 < x → F x = Cost.Jcost x

theorem cost_selection_holds : Tagged StrengthTag.traceClosure CostSelectionPackage where
  holds := {
    j_unique := fun F _ hRecip hNorm hComp hCalib hCont {_x} hx =>
      law_of_logic_forces_jcost F hRecip hNorm hComp hCalib hCont _ hx
  }

/-- **φ from the reciprocal involution** (consumes reciprocity of J, not a
standalone quadratic). Tier: THEOREM (algebra of `ι` / `1+ι`). Hierarchy /
`MinimalHierarchy` routes remain FORCED-CONDITIONAL elsewhere. -/
structure PhiFromIota : Prop where
  cost_and_scale : ReciprocalGeneratorCert

theorem phi_from_iota_holds :
    Tagged StrengthTag.traceClosure PhiFromIota where
  holds := { cost_and_scale := reciprocalGeneratorCert_holds }

/-- **H₁(S¹;ℤ) ≅ ℤ** is proved; it is **not** yet a premise of a non-encoding
D=3 theorem (`T6T8SpineAudit`). -/
theorem circle_H1_holds :
    Tagged StrengthTag.classicalExtension MathlibCohomologyBridge.circleH1ZIsoInt where
  holds := CircleWindingChain.circleH1ZIsoInt_holds

/-- Audit: linking predicate still unfolds to arithmetic encoding. -/
theorem linking_still_encoding (D : ℕ) :
    SphereAdmitsCircleLinking D ↔ (D : ℤ) - 2 = 1 :=
  t8_linking_predicate_unfolds_to_arithmetic D

/-- **Content-typed linking object.** First singular homology (ℤ coefficients,
genuine Mathlib `singularHomologyFunctor`) of the complement of a continuous
map from S¹ into S^D. This is the object Alexander duality computes. Statements
about it cannot be discharged by arithmetic encodings: they require actual
homology computations of complements. -/
noncomputable def linkingComplementH1 (D : ℕ)
    (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)) : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of {x : TopCat.sphere.{0} D // x ∉ Set.range f})

/-- **Non-encoding detector (panel K1, corrected 2026-07-08).** Some embedded
circle in S^D has homologically nontrivial complement: the real linking
obstruction, stated on the Mathlib object itself.

History: the first binder used an abstract `detects : ℕ → Prop` field plus a
`not_encoding` name-firewall. That was broken both ways: the empty detector
`fun _ => False` inhabited it trivially (verified: the probe built), and by
`funext`+`propext` any honest detector is *equal* to the encoding predicate,
so the firewall excluded exactly the real bridge. Content-typing is the only
non-gameable form. -/
def DetectsNontrivialLinking (D : ℕ) : Prop :=
  ∃ f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D),
    Topology.IsEmbedding f ∧
      ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f)

/-- **The detection half is proved** (R2 of campaign P-d3link, 2026-07-17):
the flat unknot `z ↦ (z,0,0)` embeds S¹ in S³, and its complement retracts
onto the core circle `(0,0,w)`, so `H₁(S¹;ℤ) ≅ ℤ` (proved,
`circleH1ZIsoInt_holds`) is a retract of the complement's first homology,
which therefore is not zero. Real Mathlib singular homology throughout; no
arithmetic encoding anywhere in the proof
(`Foundation/UnknotComplementRetract.lean`). -/
theorem detectsNontrivialLinking_three : DetectsNontrivialLinking 3 :=
  ⟨UnknotComplementRetract.unknot, UnknotComplementRetract.unknot_isEmbedding,
    UnknotComplementRetract.unknotComplementH1_ne_zero
      CircleWindingChain.circleH1ZIsoInt_holds⟩

/-- **The purchase binder, content-typed.** All three fields are PROVED
(campaign P-d3link, 2026-07-18): `d3_detects` by the unknot complement
retract, and `forces_D3` unconditionally by the circle-complement dichotomy
(excision spine + arc-complement acyclicity), for arbitrary (possibly wild)
topological embeddings. None of it can be produced from
`SphereAdmitsCircleLinking`'s arithmetic. The full inhabitation lives in
`Foundation.PublicSpineLinkingClosure`. -/
structure AlexanderLinkingBridge : Prop where
  /-- H₁(S¹;ℤ) ≅ ℤ is available to the bridge (already proved). -/
  h1 : MathlibCohomologyBridge.circleH1ZIsoInt
  /-- Some embedded circle in S³ has nontrivial complement homology.
  PROVED: `detectsNontrivialLinking_three` (unknot complement retract). -/
  d3_detects : DetectsNontrivialLinking 3
  /-- Only D = 3 admits the obstruction. PROVED:
  `PublicSpineLinkingClosure.forces_D3` (unconditional). -/
  forces_D3 : ∀ D, DetectsNontrivialLinking D → D = 3

theorem D3_of_bridge (B : AlexanderLinkingBridge) :
    ∀ D, DetectsNontrivialLinking D → D = 3 :=
  B.forces_D3

/-- **Target: D=3 from non-encoding linking — now THEOREM** (campaign
P-d3link, 2026-07-18; proof: `PublicSpineLinkingClosure.target_D3`). Kept as
a `def` (gate requirement): the statement stays content-typed so no free-Prop
cheat could ever have discharged it; it was closed by real topology. -/
def target_D3_from_nonencoding_linking : Prop :=
  Nonempty AlexanderLinkingBridge

/-- **Vanishing at D = 0** (R3a of campaign P-d3link): every subspace of the
two-point S⁰ is totally disconnected, so complement H₁ vanishes for any map. -/
theorem not_detectsNontrivialLinking_zero : ¬ DetectsNontrivialLinking 0 :=
  LinkingVanishingLowDim.not_detects_zero

/-- **Vanishing at D = 1** (R3a of campaign P-d3link): an embedded circle in
S¹ is surjective (stereographic projection + connectedness), so the complement
is empty and its H₁ vanishes. -/
theorem not_detectsNontrivialLinking_one : ¬ DetectsNontrivialLinking 1 :=
  LinkingVanishingLowDim.not_detects_one

/-- Reduction lemma (historical shape of the campaign): given `forces_D3`,
the target follows because `h1` and `d3_detects` are proved. The premise is
now discharged unconditionally in `PublicSpineLinkingClosure`. -/
theorem bridge_of_forces_D3
    (h : ∀ D, DetectsNontrivialLinking D → D = 3) :
    target_D3_from_nonencoding_linking :=
  ⟨⟨CircleWindingChain.circleH1ZIsoInt_holds, detectsNontrivialLinking_three, h⟩⟩

/-- Real (non-`rfl`) eight-tick consequent: any periodic walk covering all
2³ = 8 corners of the 3-cube has period at least 8. Stated this way because
the literal `eight_tick = 2 ^ 3` is `rfl`-true (`eight_tick := 8`), which made
the previous eight-tick target vacuous. -/
def CubePeriodEight : Prop :=
  ∀ (walk : ℕ → (Fin 3 → Bool)) (p : ℕ), 0 < p →
    (∀ n, walk (n + p) = walk n) →
    Function.Surjective walk → 8 ≤ p

/-- **The eight-tick period bound holds** (R0 of campaign P-d3link,
2026-07-17). Periodicity confines the walk's range to its first `p` values,
so surjectivity onto the `2³ = 8` cube corners forces `8 ≤ p` by counting.
Honest pigeonhole content; nothing here touches the D=3 bridge. -/
theorem cubePeriodEight_holds : CubePeriodEight := by
  classical
  intro walk p hp hper hsurj
  have hshift : ∀ k n, walk (n + k * p) = walk n := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have hsplit : n + (k + 1) * p = (n + k * p) + p := by ring
      rw [hsplit, hper, ih]
  have hmod : ∀ n, walk n = walk (n % p) := by
    intro n
    have h := hshift (n / p) (n % p)
    rwa [Nat.mod_add_div'] at h
  let f : (Fin 3 → Bool) → Fin p := fun x =>
    ⟨(hsurj x).choose % p, Nat.mod_lt _ hp⟩
  have hf : ∀ x, walk ((f x : Fin p) : ℕ) = x := by
    intro x
    exact ((hmod (hsurj x).choose).symm.trans (hsurj x).choose_spec)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx := hf x
    rw [hxy, hf y] at hx
    exact hx.symm
  have hcard := Fintype.card_le_of_injective f hinj
  simpa using hcard

/-- **Target: eight-tick downstream of a non-encoding D=3 — now THEOREM.**
Both conjuncts are proved: the bridge (`PublicSpineLinkingClosure.target_D3`)
and the period half (`cubePeriodEight_holds`). See
`Skeleton.guidepost_public_eight_tick` for the assembled proof. -/
def target_eight_tick_from_D3 : Prop :=
  target_D3_from_nonencoding_linking ∧ CubePeriodEight

/-- The eight-tick target reduces to the D=3 bridge alone: the period half is
proved. -/
theorem target_eight_tick_of_bridge
    (h : target_D3_from_nonencoding_linking) : target_eight_tick_from_D3 :=
  ⟨h, cubePeriodEight_holds⟩

/-- Dual-surface certificate: inhabited pieces of the public spine. -/
structure PublicSpineCert : Prop where
  forced_tower : Tagged StrengthTag.deltaOnly ForcedTower
  continuum_purchase : Tagged StrengthTag.classicalExtension (¬ DeltaForced ℝ)
  cost_selection : Tagged StrengthTag.traceClosure CostSelectionPackage
  phi_from_iota : Tagged StrengthTag.traceClosure PhiFromIota
  circle_H1 : Tagged StrengthTag.classicalExtension MathlibCohomologyBridge.circleH1ZIsoInt
  linking_encoding_named : ∀ D, SphereAdmitsCircleLinking D ↔ (D : ℤ) - 2 = 1

theorem publicSpineCert_holds : PublicSpineCert where
  forced_tower := forced_tower_holds
  continuum_purchase := continuum_is_purchase
  cost_selection := cost_selection_holds
  phi_from_iota := phi_from_iota_holds
  circle_H1 := circle_H1_holds
  linking_encoding_named := linking_still_encoding

/-! ## Channel-B citation surface (2026-07-08; retiered 2026-07-18)

Downstream modules that previously bundled `UnifiedForcingChain.t0_holds`…`t8_holds`
as a closed architecture spine should cite these instead. Inhabited content is
`PublicSpineCert`. D=3 / eight-tick are now closed:
`PublicSpineLinkingClosure.target_D3` and
`Skeleton.guidepost_public_eight_tick`. -/

/-- Preferred name for the inhabited public substrate (Channel B retarget). -/
abbrev SubstrateCert : Prop := PublicSpineCert

theorem substrateCert_holds : SubstrateCert := publicSpineCert_holds

/-- Disclosure: the D=3 / eight-tick public targets are exactly the content-typed
binders above (both now proved; see `PublicSpineLinkingClosure`). Citing this is
the honest replacement for `Nonempty T7_EightTick_Forced` /
`Nonempty T8_Dimension_Forced`. -/
structure DimensionEightTickOpen : Prop where
  d3_is_bridge :
    target_D3_from_nonencoding_linking = Nonempty AlexanderLinkingBridge
  eight_is_bridge_and_period :
    target_eight_tick_from_D3 =
      (target_D3_from_nonencoding_linking ∧ CubePeriodEight)

theorem dimensionEightTickOpen_holds : DimensionEightTickOpen where
  d3_is_bridge := rfl
  eight_is_bridge_and_period := rfl

end PublicSpine
end Foundation
end IndisputableMonolith
