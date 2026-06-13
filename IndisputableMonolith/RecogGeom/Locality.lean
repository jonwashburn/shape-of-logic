import Mathlib
import IndisputableMonolith.RecogGeom.Core

/-!
# Recognition Geometry: Locality Structure (RG1)

This module defines the neighborhood structure on configuration spaces.
Recognition is never global—it is always done from within some finite
neighborhood of configurations.

## Axiom RG1: Locality / Neighborhoods

Each configuration c ∈ C has a family N(c) of neighborhoods satisfying:
1. Intersection closure: intersections of neighborhoods contain neighborhoods
2. Refinement: points in a neighborhood have sub-neighborhoods

These are the minimal ingredients of a neighborhood structure, allowing us
to talk about "varying a configuration a little bit" without committing to
a particular topology or metric.

-/

namespace IndisputableMonolith
namespace RecogGeom

open Set

/-! ## Local Configuration Space (RG1) -/

/-- A local configuration space is a configuration space equipped with
    a neighborhood structure. This is RG1 of recognition geometry.

    The neighborhoods allow us to talk about "nearby" configurations
    without assuming a metric or full topology. -/
structure LocalConfigSpace (C : Type*) extends ConfigSpace C where
  /-- Neighborhood assignment: for each c, a family of "local" sets around c -/
  N : C → Set (Set C)

  /-- Every neighborhood of c contains c -/
  mem_of_mem_N : ∀ c U, U ∈ N c → c ∈ U

  /-- Neighborhoods are nonempty for each point -/
  N_nonempty : ∀ c, (N c).Nonempty

  /-- Intersection closure: if U, V ∈ N(c) both contain c, then there exists
      W ∈ N(c) with W ⊆ U ∩ V -/
  intersection_closed : ∀ c U V, U ∈ N c → V ∈ N c →
    ∃ W ∈ N c, W ⊆ U ∩ V

  /-- Refinement: if U ∈ N(c) and c' ∈ U, then there exists V ∈ N(c')
      with V ⊆ U -/
  refinement : ∀ c U c', U ∈ N c → c' ∈ U →
    ∃ V ∈ N c', V ⊆ U

/-! ## Basic Lemmas -/

variable {C : Type*} (L : LocalConfigSpace C)

/-- Every configuration has at least one neighborhood -/
theorem LocalConfigSpace.has_neighborhood (c : C) : (L.N c).Nonempty :=
  L.N_nonempty c

/-- Every point is in its own neighborhoods -/
theorem LocalConfigSpace.self_mem_neighborhood (c : C) (U : Set C) (hU : U ∈ L.N c) :
    c ∈ U :=
  L.mem_of_mem_N c U hU

/-- If U and V are neighborhoods of c, there's a common refinement -/
theorem LocalConfigSpace.common_refinement (c : C) (U V : Set C)
    (hU : U ∈ L.N c) (hV : V ∈ L.N c) :
    ∃ W ∈ L.N c, W ⊆ U ∧ W ⊆ V := by
  obtain ⟨W, hW, hWUV⟩ := L.intersection_closed c U V hU hV
  exact ⟨W, hW, subset_inter_iff.mp hWUV⟩

/-- Points in a neighborhood have sub-neighborhoods -/
theorem LocalConfigSpace.sub_neighborhood (c c' : C) (U : Set C)
    (hU : U ∈ L.N c) (hc' : c' ∈ U) :
    ∃ V ∈ L.N c', V ⊆ U :=
  L.refinement c U c' hU hc'

/-! ## Neighborhood Filter -/

/-- The neighborhoods of a point form a filter base -/
def LocalConfigSpace.neighborhoodFilterBase (c : C) : FilterBasis C where
  sets := L.N c
  nonempty := L.N_nonempty c
  inter_sets := by
    intro U V hU hV
    obtain ⟨W, hW, hWsub⟩ := L.intersection_closed c U V hU hV
    exact ⟨W, hW, hWsub⟩

/-- The neighborhood filter at a point -/
noncomputable def LocalConfigSpace.neighborhoodFilter (c : C) : Filter C :=
  (L.neighborhoodFilterBase c).filter

/-! ## Discrete Configuration Space -/

/-- A discrete configuration space where every subset is a neighborhood.
    This is the "maximally fine" locality structure. -/
def discreteLocalConfigSpace (C : Type*) [Nonempty C] : LocalConfigSpace C where
  nonempty := inferInstance
  N := fun c => {U : Set C | c ∈ U}
  mem_of_mem_N := fun c U hU => hU
  N_nonempty := fun c => ⟨Set.univ, mem_univ c⟩
  intersection_closed := fun c U V hU hV => ⟨U ∩ V, ⟨hU, hV⟩, Subset.rfl⟩
  refinement := fun c U c' hU hc' => ⟨U, hc', Subset.rfl⟩

/-! ## Trivial Configuration Space -/

/-- A trivial configuration space where only the whole space is a neighborhood.
    This is the "maximally coarse" locality structure. -/
def trivialLocalConfigSpace (C : Type*) [Nonempty C] : LocalConfigSpace C where
  nonempty := inferInstance
  N := fun _ => {Set.univ}
  mem_of_mem_N := fun c U hU => by
    simp only [Set.mem_singleton_iff] at hU
    rw [hU]
    exact mem_univ c
  N_nonempty := fun _ => ⟨Set.univ, rfl⟩
  intersection_closed := fun _ U V hU hV => by
    simp only [Set.mem_singleton_iff] at hU hV
    subst hU hV
    exact ⟨Set.univ, rfl, Set.inter_self _ ▸ Subset.rfl⟩
  refinement := fun _ U _ hU _ => by
    simp only [Set.mem_singleton_iff] at hU
    exact ⟨Set.univ, rfl, hU ▸ Subset.rfl⟩

/-! ## Module Status -/

def locality_status : String :=
  "✓ LocalConfigSpace defined (RG1)\n" ++
  "✓ Neighborhood axioms: mem_of_mem_N, intersection_closed, refinement\n" ++
  "✓ Basic lemmas: has_neighborhood, self_mem_neighborhood, common_refinement\n" ++
  "✓ Neighborhood filter construction\n" ++
  "✓ Discrete and trivial examples\n" ++
  "\n" ++
  "LOCALITY STRUCTURE (RG1) COMPLETE"

#eval locality_status

end RecogGeom
end IndisputableMonolith
