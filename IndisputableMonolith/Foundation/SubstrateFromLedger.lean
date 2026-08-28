import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Foundation.SubstrateAxioms
import IndisputableMonolith.Foundation.SingularSphere
import IndisputableMonolith.Foundation.MathlibCohomologyBridge
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Foundation.AmbientFromRecognition

/-!
# The substrate from the ledger: the ambient as a constructed object

The D=3 chain (`PublicSpineLinkingClosure.forces_D3`,
`PublicSpine.detectsNontrivialLinking_three`) runs on an ambient sphere that
until now entered as a hypothesis, packaged by the vacuous `SubstrateAxioms`
tokens (`AmbientFromRecognition.substrate_tokens_do_not_select_dimension` is
the recorded WALL: those tokens are inhabited in every dimension). This module
replaces the hypothesis with a construction.

## What is DEFINED (MODEL, named choices)

* `Grid D n`: the level-`n` dyadic refinement of the recognizer's state
  space, one record of resolution `2 ^ (-n)` per distinction. Level `0` IS
  the state space: `gridZeroEquivPattern : Grid D 0 ≃ Pattern D`.
* `cubeSet D` / `Ambient D`: the solid `D`-cube carrier into which the
  refinement records embed (`toPoint`).

The dyadic scheme is a choice; `ambient_forced_from_any_dense_refinement`
proves the choice is immaterial: every dense refinement family has the same
completion, up to unique uniform isomorphism.

## What is PROVED (THEOREM, kernel-checked)

* Row 1 (existence): `dense_ledgerSites`, `ledgerCompletion`,
  `ambient_unique_completion`. The countable ledger data (`ledgerSites`,
  `ledgerSites_countable`) determines the continuum ambient uniquely: the
  ambient is the completion of the refinement tower, not an assumption.
* Row 2 (alignment): `dimH_cubeSet : dimH (cubeSet D) = D`. The metric
  dimension of the constructed ambient equals the number of independent
  distinctions. Decoy: `dimension_is_not_state_count` (dimension `3`,
  states `8`).
* Row 3 (1-acyclicity): `ambient_oneAcyclic : IsZero (H₁ (Ambient D))` from
  convexity + `isZero_homology_of_contractible` (genuine Mathlib singular
  homology). Decoy FAILS as required: `circle_fails_oneAcyclic` (the circle's
  nonbounding 1-cycle, from the proved `H₁(S¹;ℤ) ≅ ℤ`). So the predicate
  `OneAcyclicAmbient` is not a token: it holds on the constructed ambient
  and fails on a genuine cycle carrier.
* Row 4 (composition): `detects_iff_D3` and `recognition_builds_its_stage`:
  the constructed ambient exists, has dimension `D`, is 1-acyclic, and the
  linking chain detects in exactly `D = 3`.

## The sphere joint (also closed)

`ambientSphereJoint_holds`: the one-point compactification of the ambient's
Euclidean model is `TopCat.sphere D` (stereographic,
`onePointEquivSphereOfFinrankEq`). `ambientInteriorCompactification`
sharpens it: the compactification of the constructed ambient's own interior
is the chain's sphere carrier. The sphere the linking chain runs on is the
ledger's completed continuum compactified, not an import.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SubstrateFromLedger

open Set CategoryTheory.Limits
open scoped ENNReal

attribute [local instance] AbstractCompletion.uniformStruct
  AbstractCompletion.complete AbstractCompletion.separation

/-! ## The carrier and the refinement tower -/

/-- The solid `D`-cube as a subset of `Fin D → ℝ` (sup metric). -/
def cubeSet (D : ℕ) : Set (Fin D → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

/-- The constructed ambient: the solid `D`-cube as a space. -/
abbrev Ambient (D : ℕ) := ↥(cubeSet D)

/-- Level-`n` refinement grid: one dyadic record per distinction. -/
abbrev Grid (D n : ℕ) := Fin D → Fin (2 ^ n + 1)

lemma toPoint_mem (D n : ℕ) (v : Grid D n) :
    (fun i => ((v i : ℕ) : ℝ) / (2 ^ n : ℝ)) ∈ cubeSet D := by
  intro i _
  have hk : ((v i : ℕ) : ℝ) ≤ (2 ^ n : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  exact ⟨by positivity, (div_le_one hpos).2 hk⟩

/-- A refinement record, placed in the ambient. -/
noncomputable def toPoint (D n : ℕ) (v : Grid D n) : Ambient D :=
  ⟨fun i => ((v i : ℕ) : ℝ) / (2 ^ n : ℝ), toPoint_mem D n v⟩

/-- One refinement step: each record doubles its resolution. -/
def refineStep (D n : ℕ) (v : Grid D n) : Grid D (n + 1) :=
  fun i =>
    ⟨2 * (v i : ℕ), by
      have hk : (v i : ℕ) ≤ 2 ^ n := Nat.lt_succ_iff.mp (v i).isLt
      have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      omega⟩

/-- Refinement does not move existing records: the tower is coherent. -/
theorem toPoint_refineStep (D n : ℕ) (v : Grid D n) :
    toPoint D (n + 1) (refineStep D n v) = toPoint D n v := by
  apply Subtype.ext
  funext i
  show ((2 * (v i : ℕ) : ℕ) : ℝ) / (2 ^ (n + 1) : ℝ) =
    ((v i : ℕ) : ℝ) / (2 ^ n : ℝ)
  have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  rw [pow_succ]
  field_simp

/-- All ledger sites: every record at every refinement level. -/
def ledgerSites (D : ℕ) : Set (Ambient D) :=
  ⋃ n, Set.range (toPoint D n)

theorem range_toPoint_mono (D n : ℕ) :
    Set.range (toPoint D n) ⊆ Set.range (toPoint D (n + 1)) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨refineStep D n v, toPoint_refineStep D n v⟩

/-- The ledger data is countable: recognition never posts more than countably
many records. The continuum below is therefore built, not assumed. -/
theorem ledgerSites_countable (D : ℕ) : (ledgerSites D).Countable :=
  Set.countable_iUnion fun _ => (Set.finite_range _).countable

/-! ## Level 0 is the recognizer's state space -/

/-- Level-0 records are exactly the Boolean patterns: the recognizer's
state space, one bit per distinction. -/
def gridZeroEquivPattern (D : ℕ) : Grid D 0 ≃ Patterns.Pattern D :=
  Equiv.piCongrRight fun _ => finTwoEquiv

theorem grid_zero_card (D : ℕ) : Fintype.card (Grid D 0) = 2 ^ D := by
  norm_num [Fintype.card_fun]

/-- Level-0 records land on cube vertices: every coordinate is 0 or 1. -/
theorem toPoint_zero_vertex (D : ℕ) (v : Grid D 0) (i : Fin D) :
    ((toPoint D 0 v : Fin D → ℝ) i = 0) ∨
      ((toPoint D 0 v : Fin D → ℝ) i = 1) := by
  have h2 : (v i : ℕ) < 2 := by
    have := (v i).isLt
    norm_num at this
    exact this
  have hv : (v i : ℕ) = 0 ∨ (v i : ℕ) = 1 := by omega
  rcases hv with h | h
  · left
    show ((v i : ℕ) : ℝ) / (2 ^ 0 : ℝ) = 0
    simp [h]
  · right
    show ((v i : ℕ) : ℝ) / (2 ^ 0 : ℝ) = 1
    simp [h]

/-! ## Row 1: density and the forced completion -/

/-- **Density.** Every point of the ambient is a limit of ledger records:
the refinement tower reaches everywhere. -/
theorem dense_ledgerSites (D : ℕ) : Dense (ledgerSites D) := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < r :=
    exists_pow_lt_of_lt_one hr (by norm_num)
  have hx : ∀ i, (x : Fin D → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    x.property i (Set.mem_univ i)
  have hbound : ∀ i, ⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊ < 2 ^ n + 1 := by
    intro i
    have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
    have hle : (x : Fin D → ℝ) i * 2 ^ n ≤ (2 ^ n : ℝ) := by
      calc (x : Fin D → ℝ) i * 2 ^ n
          ≤ 1 * 2 ^ n := mul_le_mul_of_nonneg_right (hx i).2 h2n
        _ = 2 ^ n := one_mul _
    have hx0 : (0 : ℝ) ≤ (x : Fin D → ℝ) i * 2 ^ n := by
      have := (hx i).1; positivity
    have hfle : (⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊ : ℝ) ≤ (2 ^ n : ℝ) :=
      le_trans (Nat.floor_le hx0) hle
    have : (⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊ : ℕ) ≤ 2 ^ n := by exact_mod_cast hfle
    omega
  set g : Grid D n := fun i => ⟨⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊, hbound i⟩ with hg
  refine ⟨toPoint D n g, Metric.mem_ball.mpr ?_,
    Set.mem_iUnion.mpr ⟨n, ⟨g, rfl⟩⟩⟩
  rw [Subtype.dist_eq]
  rcases Nat.eq_zero_or_pos D with hD | _
  · subst hD
    have hfn : (toPoint 0 n g : Fin 0 → ℝ) = (x : Fin 0 → ℝ) := by
      funext i; exact i.elim0
    rw [hfn, dist_self]
    exact hr
  rw [dist_pi_lt_iff hr]
  intro i
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hy0 : (0 : ℝ) ≤ (x : Fin D → ℝ) i * 2 ^ n := by
    have := (hx i).1; positivity
  have hfl : (⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊ : ℝ) ≤ (x : Fin D → ℝ) i * 2 ^ n :=
    Nat.floor_le hy0
  have hfu : (x : Fin D → ℝ) i * 2 ^ n < ⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊ + 1 :=
    Nat.lt_floor_add_one _
  have hgval : ((g i : ℕ) : ℝ) = (⌊(x : Fin D → ℝ) i * 2 ^ n⌋₊ : ℝ) := by
    simp [hg]
  have hlow : ((g i : ℕ) : ℝ) / (2 ^ n : ℝ) ≤ (x : Fin D → ℝ) i := by
    rw [div_le_iff₀ hpow, hgval]
    exact hfl
  have hup : (x : Fin D → ℝ) i < (((g i : ℕ) : ℝ) + 1) / (2 ^ n : ℝ) := by
    rw [lt_div_iff₀ hpow, hgval]
    exact hfu
  show dist (((g i : ℕ) : ℝ) / (2 ^ n : ℝ)) ((x : Fin D → ℝ) i) < r
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlow)]
  have hlt : (x : Fin D → ℝ) i - ((g i : ℕ) : ℝ) / (2 ^ n : ℝ) < 1 / 2 ^ n := by
    have hsplit : (((g i : ℕ) : ℝ) + 1) / (2 ^ n : ℝ) =
        ((g i : ℕ) : ℝ) / (2 ^ n : ℝ) + 1 / 2 ^ n := by
      field_simp
    linarith [hup, hsplit ▸ hup]
  calc (x : Fin D → ℝ) i - ((g i : ℕ) : ℝ) / (2 ^ n : ℝ)
      < 1 / 2 ^ n := hlt
    _ = (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]
    _ < r := hn

theorem isCompact_cubeSet (D : ℕ) : IsCompact (cubeSet D) :=
  isCompact_univ_pi fun _ => isCompact_Icc

instance (D : ℕ) : CompactSpace (Ambient D) :=
  isCompact_iff_compactSpace.mp (isCompact_cubeSet D)

/-- Any closed part of the ambient containing every ledger record is the
whole ambient: nothing smaller than the constructed continuum holds the
ledger's closure. -/
theorem closed_superset_of_sites_is_everything (D : ℕ) {C : Set (Ambient D)}
    (hC : IsClosed C) (hsub : ledgerSites D ⊆ C) : C = Set.univ := by
  have h1 : closure (ledgerSites D) ⊆ C := closure_minimal hsub hC
  have h2 : closure (ledgerSites D) = Set.univ := (dense_ledgerSites D).closure_eq
  exact Set.eq_univ_of_univ_subset (h2 ▸ h1)

/-- **The ambient is the completion of the ledger tower.** The countable
refinement data, together with the uniform structure it inherits, already
determines the solid cube: the cube is a completion package for the sites. -/
noncomputable def ledgerCompletion (D : ℕ) :
    AbstractCompletion ↥(ledgerSites D) where
  space := Ambient D
  coe := Subtype.val
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := isUniformEmbedding_subtype_val.isUniformInducing
  dense := (dense_ledgerSites D).denseRange_val

/-- **Uniqueness (the forcing statement).** Every completion of the ledger
sites is uniformly isomorphic to the constructed ambient: there is no choice
of continuum left once the ledger's refinement data is given. -/
theorem ambient_unique_completion (D : ℕ)
    (c : AbstractCompletion ↥(ledgerSites D)) :
    Nonempty (c.space ≃ᵤ Ambient D) :=
  ⟨c.compareEquiv (ledgerCompletion D)⟩

/-- The dyadic scheme is immaterial: ANY dense refinement family of the
ambient has the ambient as its completion. The construction does not depend
on how the ledger interleaves its records, only on refinement without bound. -/
noncomputable def denseRefinementCompletion (D : ℕ) (s : Set (Ambient D))
    (hs : Dense s) : AbstractCompletion ↥s where
  space := Ambient D
  coe := Subtype.val
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := isUniformEmbedding_subtype_val.isUniformInducing
  dense := hs.denseRange_val

theorem ambient_forced_from_any_dense_refinement (D : ℕ) (s : Set (Ambient D))
    (hs : Dense s) (c : AbstractCompletion ↥s) :
    Nonempty (c.space ≃ᵤ Ambient D) :=
  ⟨c.compareEquiv (denseRefinementCompletion D s hs)⟩

/-! ## Row 2: the alignment `dim M = D` -/

/-- **Alignment.** The Hausdorff dimension of the constructed ambient equals
`D`, the number of independent distinctions. Dimension is computed from the
construction, not postulated. -/
theorem dimH_cubeSet (D : ℕ) : dimH (cubeSet D) = (D : ℝ≥0∞) := by
  have hball : Metric.ball (fun _ => (1 / 2 : ℝ) : Fin D → ℝ) (1 / 2) ⊆
      cubeSet D := by
    intro y hy
    intro i _
    have hi : dist (y i) ((1 : ℝ) / 2) < 1 / 2 :=
      lt_of_le_of_lt (dist_le_pi_dist y (fun _ => (1 / 2 : ℝ)) i)
        (Metric.mem_ball.mp hy)
    rw [Real.dist_eq, abs_lt] at hi
    constructor <;> nlinarith [hi.1, hi.2]
  have hmem : cubeSet D ∈ nhds (fun _ => (1 / 2 : ℝ) : Fin D → ℝ) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds _ (by norm_num)) hball
  rw [Real.dimH_of_mem_nhds hmem]
  simp [Module.finrank_fintype_fun_eq_card]

/-- Decoy for the alignment: the dimension is the distinction count `3`,
not the state count `8`. A construction that confused the two would fail
here. -/
theorem dimension_is_not_state_count :
    dimH (cubeSet 3) = (3 : ℝ≥0∞) ∧
      Fintype.card (Grid 3 0) = 8 ∧ (3 : ℝ≥0∞) ≠ 8 := by
  refine ⟨dimH_cubeSet 3, by simpa using grid_zero_card 3, ?_⟩
  norm_num

/-! ## Row 3: 1-acyclicity, with a decoy that fails -/

theorem convex_cubeSet (D : ℕ) : Convex ℝ (cubeSet D) :=
  convex_pi fun _ _ => convex_Icc 0 1

theorem cubeSet_nonempty (D : ℕ) : (cubeSet D).Nonempty :=
  ⟨fun _ => 1 / 2, fun i _ => by constructor <;> norm_num⟩

instance ambient_contractible (D : ℕ) : ContractibleSpace (Ambient D) :=
  (convex_cubeSet D).contractibleSpace (cubeSet_nonempty D)

/-- Genuine 1-acyclicity: first singular homology (ℤ coefficients, Mathlib
functor) vanishes. This is the honest replacement for the vacuous
`SubstrateAxioms.OneAcyclicSubstrate` token. -/
def OneAcyclicAmbient (X : TopCat.{0}) : Prop :=
  CategoryTheory.Limits.IsZero (SingularSphere.Hgrp X 1)

/-- **Every posted cycle settles**: the constructed ambient is 1-acyclic. -/
theorem ambient_oneAcyclic (D : ℕ) :
    OneAcyclicAmbient (TopCat.of (Ambient D)) :=
  SingularSphere.isZero_homology_of_contractible (TopCat.of (Ambient D))
    one_ne_zero

/-- **The decoy fails, as it must.** The circle carries a nonbounding
1-cycle (`H₁(S¹;ℤ) ≅ ℤ`, proved), so the predicate rejects it: 1-acyclicity
is a real property of the constructed ambient, not a token inhabitable
everywhere. -/
theorem circle_fails_oneAcyclic : ¬ OneAcyclicAmbient (TopCat.sphere 1) :=
  MathlibCohomologyBridge.circleH1ZNonzero_of_iso_int
    CircleWindingChain.circleH1ZIsoInt_holds

/-- The discrimination pair, in one statement: holds on the constructed
ambient, fails on the cycle carrier. Contrast with the recorded WALL
`AmbientFromRecognition.substrate_tokens_do_not_select_dimension`. -/
theorem oneAcyclic_discriminates :
    OneAcyclicAmbient (TopCat.of (Ambient 3)) ∧
      ¬ OneAcyclicAmbient (TopCat.sphere 1) :=
  ⟨ambient_oneAcyclic 3, circle_fails_oneAcyclic⟩

/-! ## Row 4: composition with the linking chain -/

/-- Detection characterizes the dimension: the linking chain detects in
`D = 3` and only there. Existence: `detectsNontrivialLinking_three`.
Uniqueness: `forces_D3` (both unconditional). -/
theorem detects_iff_D3 (D : ℕ) :
    PublicSpine.DetectsNontrivialLinking D ↔ D = 3 :=
  ⟨PublicSpineLinkingClosure.forces_D3 D,
    fun h => h ▸ PublicSpine.detectsNontrivialLinking_three⟩

/-- **The stage is built by the play.** For every distinction count `D`:
the ledger's refinement tower is dense in a constructed ambient (so the
continuum is its completion, not an assumption), the ambient's dimension is
`D`, the ambient is 1-acyclic, and the linking chain detects in exactly
`D = 3`. No substrate hypothesis appears. -/
theorem recognition_builds_its_stage :
    (∀ D, Dense (ledgerSites D)) ∧
      (∀ D, dimH (cubeSet D) = (D : ℝ≥0∞)) ∧
      (∀ D, OneAcyclicAmbient (TopCat.of (Ambient D))) ∧
      (∀ D, PublicSpine.DetectsNontrivialLinking D ↔ D = 3) :=
  ⟨dense_ledgerSites, dimH_cubeSet, ambient_oneAcyclic, detects_iff_D3⟩

/-! ## The sphere joint: the compactified stage IS the chain's carrier -/

/-- The identification of the one-point compactification of the ambient's
Euclidean model with the sphere carrier of the linking chain. -/
def AmbientSphereJoint (D : ℕ) : Prop :=
  Nonempty ((OnePoint (Fin D → ℝ)) ≃ₜ TopCat.sphere.{0} D)

/-- The compactified Euclidean model is the chain's sphere
(`onePointEquivSphereOfFinrankEq`, stereographic). -/
noncomputable def ambientSphereEquiv (D : ℕ) :
    OnePoint (Fin D → ℝ) ≃ₜ TopCat.sphere.{0} D :=
  (onePointEquivSphereOfFinrankEq (ι := Fin (D + 1)) (V := Fin D → ℝ)
      (by simp [Module.finrank_fintype_fun_eq_card])).trans
    Homeomorph.ulift.symm

/-- **The joint holds**: no sphere is imported by hand. -/
theorem ambientSphereJoint_holds (D : ℕ) : AmbientSphereJoint D :=
  ⟨ambientSphereEquiv D⟩

/-! ## The interior model: the ambient's interior compactifies to the stage -/

private lemma real_ball_eq : Metric.ball (0 : ℝ) 1 = Set.Ioo (-1 : ℝ) 1 := by
  rw [Real.ball_eq_Ioo]; norm_num

private lemma half_ne_zero' : (1 / 2 : ℝ) ≠ 0 := by norm_num

private lemma affine_apply (x : ℝ) :
    affineHomeomorph (1 / 2 : ℝ) (1 / 2) half_ne_zero' x =
      (1 / 2) * x + 1 / 2 := rfl

private lemma affine_image_Ioo :
    (⇑(affineHomeomorph (1 / 2 : ℝ) (1 / 2) half_ne_zero')) ''
        Set.Ioo (-1 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_Ioo, affine_apply]
    constructor <;> linarith [hx.1, hx.2]
  · intro hy
    rw [Set.mem_Ioo] at hy
    exact ⟨2 * y - 1, Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩,
      by rw [affine_apply]; ring⟩

/-- The real line is homeomorphic to the open unit interval. -/
noncomputable def realHomeoIoo : ℝ ≃ₜ ↥(Set.Ioo (0 : ℝ) 1) :=
  (Homeomorph.unitBall (E := ℝ)).trans <|
    (Homeomorph.setCongr real_ball_eq).trans <|
      ((affineHomeomorph (1 / 2 : ℝ) (1 / 2) half_ne_zero').image
          (Set.Ioo (-1 : ℝ) 1)).trans
        (Homeomorph.setCongr affine_image_Ioo)

/-- Functions into the interval, as the set-pi subtype. -/
noncomputable def piIooHomeoSetPi (D : ℕ) :
    (Fin D → ↥(Set.Ioo (0 : ℝ) 1)) ≃ₜ
      ↥(Set.univ.pi fun _ : Fin D => Set.Ioo (0 : ℝ) 1) where
  toFun x := ⟨fun i => (x i : ℝ), fun i _ => (x i).2⟩
  invFun y := fun i => ⟨(y : Fin D → ℝ) i, y.2 i (Set.mem_univ i)⟩
  left_inv x := by funext i; exact Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val

/-- The interior of the constructed ambient is the open cube. -/
theorem interior_cubeSet (D : ℕ) :
    interior (cubeSet D) = Set.univ.pi fun _ : Fin D => Set.Ioo (0 : ℝ) 1 := by
  rw [cubeSet, interior_pi_set Set.finite_univ]
  simp [interior_Icc]

/-- The ambient's interior is the Euclidean model. -/
noncomputable def interiorModel (D : ℕ) :
    ↥(interior (cubeSet D)) ≃ₜ (Fin D → ℝ) :=
  (Homeomorph.setCongr (interior_cubeSet D)).trans <|
    (piIooHomeoSetPi D).symm.trans <|
      Homeomorph.piCongrRight fun _ => realHomeoIoo.symm

/-- **The stage, compactified, is the chain's carrier.** The one-point
compactification of the constructed ambient's interior is homeomorphic to
`TopCat.sphere D`: the sphere on which the linking chain runs is obtained
from the ledger's own completed continuum, not imported. -/
noncomputable def ambientInteriorCompactification (D : ℕ) :
    OnePoint ↥(interior (cubeSet D)) ≃ₜ TopCat.sphere.{0} D :=
  (interiorModel D).onePointCongr.trans (ambientSphereEquiv D)

end SubstrateFromLedger
end Foundation
end IndisputableMonolith
