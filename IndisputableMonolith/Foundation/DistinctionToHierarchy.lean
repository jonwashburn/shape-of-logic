import Mathlib
import IndisputableMonolith.Foundation.DistinctionToJCost

/-!
# Distinction to Hierarchy

This module deepens the T6 bridge.  It replaces the use of the large internal
`UnifiedForcingChain.t5_to_t6_forced_bridge_holds` bridge in the
distinction-threaded route with an explicit hierarchy construction:

* consume `T5_FromDistinction h`;
* construct the canonical positive multilevel hierarchy;
* prove it is uniformly scaled, growth-oriented, and seed-closed;
* prove the hierarchy base ratio is forced to φ.

This is still a normal-form construction.  The next still-deeper audit, if
needed, is to identify this normal form directly with every closed hierarchy
coming from a concrete ledger model.  But the route in this file no longer
hides T6 behind the monolithic T5→T6 bridge.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DistinctionToHierarchy

open DistinctionToJCost
open UnifiedForcingChain

/-! ## Canonical hierarchy generated after T5 -/

/-- The canonical hierarchy levels after J-cost uniqueness: a positive
geometric hierarchy with ratio φ. -/
noncomputable def canonicalPhiRungs : ℕ → ℝ :=
  fun k => PhiForcing.φ ^ k

/-- Every canonical φ level is positive. -/
theorem canonicalPhiRungs_pos : ∀ k, 0 < canonicalPhiRungs k := by
  intro k
  exact pow_pos PhiForcing.phi_pos k

/-- The canonical φ multilevel composition. -/
noncomputable def canonicalPhiHierarchy :
    HierarchyForcing.NontrivialMultilevelComposition where
  levels := canonicalPhiRungs
  levels_pos := canonicalPhiRungs_pos
  at_least_three := by
    constructor
    · exact canonicalPhiRungs_pos 0
    constructor
    · exact canonicalPhiRungs_pos 1
    · exact canonicalPhiRungs_pos 2

@[simp] theorem canonicalPhiHierarchy_level_zero :
    canonicalPhiHierarchy.levels 0 = 1 := by
  simp [canonicalPhiHierarchy, canonicalPhiRungs]

@[simp] theorem canonicalPhiHierarchy_level_one :
    canonicalPhiHierarchy.levels 1 = PhiForcing.φ := by
  simp [canonicalPhiHierarchy, canonicalPhiRungs]

@[simp] theorem canonicalPhiHierarchy_level_two :
    canonicalPhiHierarchy.levels 2 = PhiForcing.φ ^ 2 := by
  simp [canonicalPhiHierarchy, canonicalPhiRungs]

/-- The canonical φ hierarchy has base ratio φ. -/
theorem canonicalPhiHierarchy_base_ratio :
    canonicalBaseRatio canonicalPhiHierarchy = PhiForcing.φ := by
  unfold canonicalBaseRatio canonicalPhiHierarchy canonicalPhiRungs
  simp

/-- The canonical φ hierarchy has uniform adjacent ratio. -/
theorem canonicalPhiHierarchy_uniform :
    CanonicalUniformScaleLaw canonicalPhiHierarchy where
  uniform_step := by
    intro k
    rw [canonicalPhiHierarchy_base_ratio]
    change PhiForcing.φ ^ (k + 1) = PhiForcing.φ * PhiForcing.φ ^ k
    rw [pow_succ]
    ring

/-- The canonical φ hierarchy is growth-oriented. -/
theorem canonicalPhiHierarchy_growth :
    CanonicalGrowthOrientation canonicalPhiHierarchy where
  base_step_grows := by
    change canonicalPhiRungs 0 < canonicalPhiRungs 1
    simp [canonicalPhiRungs]
    exact PhiForcing.phi_gt_one

/-- The canonical φ hierarchy is seed-closed. -/
theorem canonicalPhiHierarchy_seed :
    CanonicalSeedSizeLaw canonicalPhiHierarchy where
  seed_size_law := by
    change canonicalPhiRungs canonical_seed_post_index =
      canonicalPhiRungs 0 + canonicalPhiRungs 1
    simp [canonicalPhiRungs, canonical_seed_post_index]
    simpa [add_comm] using PhiForcing.phi_equation

/-- Any uniform, growth-oriented, seed-closed hierarchy has base ratio φ. -/
theorem uniform_growth_seed_forces_phi
    (M : HierarchyForcing.NontrivialMultilevelComposition)
    (uniform : CanonicalUniformScaleLaw M)
    (growth : CanonicalGrowthOrientation M)
    (seed : CanonicalSeedSizeLaw M) :
    canonicalBaseRatio M = PhiForcing.φ :=
  canonicalBaseRatio_eq_phi_of_uniform_seed M uniform growth seed

/-! ## Distinction-threaded hierarchy certificate -/

/-- The explicit hierarchy surface forced after T5. -/
structure HierarchyFromDistinction
    {K : Type} (h : ∃ x y : K, x ≠ y) : Prop where
  /-- T5 is already forced from the same distinction. -/
  t5 : T5_FromDistinction h
  /-- The canonical hierarchy object. -/
  hierarchy : Nonempty HierarchyForcing.NontrivialMultilevelComposition
  /-- The canonical hierarchy is uniform. -/
  uniform : CanonicalUniformScaleLaw canonicalPhiHierarchy
  /-- The canonical hierarchy grows from level 0 to level 1. -/
  growth : CanonicalGrowthOrientation canonicalPhiHierarchy
  /-- The canonical hierarchy is seed-closed. -/
  seed : CanonicalSeedSizeLaw canonicalPhiHierarchy
  /-- The canonical hierarchy's base ratio is φ. -/
  base_ratio_phi : canonicalBaseRatio canonicalPhiHierarchy = PhiForcing.φ
  /-- The uniqueness theorem: every uniform, growing, seed-closed positive
      hierarchy has base ratio φ. -/
  uniqueness :
    ∀ M : HierarchyForcing.NontrivialMultilevelComposition,
      CanonicalUniformScaleLaw M →
      CanonicalGrowthOrientation M →
      CanonicalSeedSizeLaw M →
        canonicalBaseRatio M = PhiForcing.φ

/-- T5 forced from a distinction yields the explicit canonical hierarchy
surface. -/
theorem distinction_T5_to_hierarchy
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (h5 : T5_FromDistinction h) :
    HierarchyFromDistinction h where
  t5 := h5
  hierarchy := ⟨canonicalPhiHierarchy⟩
  uniform := canonicalPhiHierarchy_uniform
  growth := canonicalPhiHierarchy_growth
  seed := canonicalPhiHierarchy_seed
  base_ratio_phi := canonicalPhiHierarchy_base_ratio
  uniqueness := uniform_growth_seed_forces_phi

/-- A distinction witness forces the explicit hierarchy surface. -/
theorem distinction_forces_hierarchy
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    HierarchyFromDistinction h :=
  distinction_T5_to_hierarchy (DistinctionToJCost.distinction_forces_T5 h)

end DistinctionToHierarchy
end Foundation
end IndisputableMonolith
