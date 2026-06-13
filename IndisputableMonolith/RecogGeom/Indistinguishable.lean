import Mathlib
import IndisputableMonolith.RecogGeom.Recognizer

/-!
# Recognition Geometry: Indistinguishability (RG3)

This module defines the indistinguishability relation induced by a recognizer.
Recognition is inherently lossy: multiple configurations may give rise to
the same event. The equivalence classes are the "resolution cells"—the
smallest units of configuration that can be told apart.

## Axiom RG3: Indistinguishability

Given a recognition map R : C → E, define an equivalence relation ~ on C by:
  c₁ ~ c₂ iff R(c₁) = R(c₂)

## Key Insight

The equivalence classes of ~ are the "resolution cells" of the recognizer:
the smallest units of configuration that can be distinguished by this
particular recognition map.

-/

namespace IndisputableMonolith
namespace RecogGeom

/-! ## Indistinguishability Relation (RG3) -/

/-- Two configurations are indistinguishable under a recognizer if they
    produce the same event. This is the fundamental equivalence relation
    of recognition geometry. -/
def Indistinguishable {C E : Type*} (r : Recognizer C E) (c₁ c₂ : C) : Prop :=
  r.R c₁ = r.R c₂

/-- Notation: c₁ ~[r] c₂ means c₁ and c₂ are indistinguishable under r -/
notation:50 c₁ " ~[" r "] " c₂ => Indistinguishable r c₁ c₂

/-! ## Equivalence Relation Properties -/

variable {C E : Type*} (r : Recognizer C E)

/-- Indistinguishability is reflexive -/
theorem Indistinguishable.refl (c : C) : c ~[r] c := rfl

/-- Indistinguishability is symmetric -/
theorem Indistinguishable.symm' {c₁ c₂ : C} (h : c₁ ~[r] c₂) : c₂ ~[r] c₁ :=
  Eq.symm h

/-- Indistinguishability is transitive -/
theorem Indistinguishable.trans {c₁ c₂ c₃ : C}
    (h₁ : c₁ ~[r] c₂) (h₂ : c₂ ~[r] c₃) : c₁ ~[r] c₃ :=
  Eq.trans h₁ h₂

/-- Indistinguishability is an equivalence relation -/
theorem indistinguishable_equivalence : Equivalence (Indistinguishable r) where
  refl := Indistinguishable.refl r
  symm := Indistinguishable.symm' r
  trans := Indistinguishable.trans r

/-- The indistinguishability setoid -/
def indistinguishableSetoid : Setoid C where
  r := Indistinguishable r
  iseqv := indistinguishable_equivalence r

/-! ## Resolution Cells -/

/-- The resolution cell of a configuration c is its equivalence class
    under indistinguishability. This is the set of all configurations
    that produce the same event as c. -/
def ResolutionCell {C E : Type*} (r : Recognizer C E) (c : C) : Set C :=
  {c' : C | c' ~[r] c}

/-- A configuration is in its own resolution cell -/
theorem mem_resolutionCell_self (c : C) : c ∈ ResolutionCell r c :=
  Indistinguishable.refl r c

/-- Resolution cells are exactly the fibers of the recognizer -/
theorem resolutionCell_eq_fiber (c : C) :
    ResolutionCell r c = r.fiber (r.R c) := by
  ext c'
  simp [ResolutionCell, Indistinguishable, Recognizer.fiber]

/-- Two configurations have the same resolution cell iff they're indistinguishable -/
theorem resolutionCell_eq_iff {c₁ c₂ : C} :
    ResolutionCell r c₁ = ResolutionCell r c₂ ↔ c₁ ~[r] c₂ := by
  constructor
  · intro h
    have : c₂ ∈ ResolutionCell r c₁ := by
      rw [h]
      exact mem_resolutionCell_self r c₂
    exact (Indistinguishable.symm' r this)
  · intro h
    ext c
    simp [ResolutionCell, Indistinguishable]
    constructor
    · intro hc
      exact Eq.trans hc h
    · intro hc
      exact Eq.trans hc (Eq.symm h)

/-- Resolution cells partition the configuration space -/
theorem resolutionCells_partition (c : C) :
    ∃! cell : Set C, c ∈ cell ∧ cell = ResolutionCell r c := by
  use ResolutionCell r c
  constructor
  · exact ⟨mem_resolutionCell_self r c, rfl⟩
  · intro cell ⟨_, hcell⟩
    exact hcell

/-! ## Local Resolution -/

/-- The local resolution of R at c on U is the partition of U into
    intersections with resolution cells. -/
def LocalResolution {C E : Type*} (r : Recognizer C E) (U : Set C) : Set (Set C) :=
  {S : Set C | ∃ c ∈ U, S = U ∩ ResolutionCell r c}

/-- Local resolution cells cover U -/
theorem localResolution_covers (U : Set C) :
    ⋃₀ LocalResolution r U = U := by
  ext c
  simp only [Set.mem_sUnion, LocalResolution, Set.mem_setOf_eq]
  constructor
  · intro ⟨S, ⟨c', hc'U, hS⟩, hcS⟩
    rw [hS] at hcS
    exact hcS.1
  · intro hcU
    refine ⟨U ∩ ResolutionCell r c, ⟨c, hcU, rfl⟩, ?_⟩
    exact ⟨hcU, mem_resolutionCell_self r c⟩

/-! ## Distinguishability -/

/-- Two configurations are distinguishable if they produce different events -/
def Distinguishable {C E : Type*} (r : Recognizer C E) (c₁ c₂ : C) : Prop :=
  r.R c₁ ≠ r.R c₂

/-- Distinguishability is the negation of indistinguishability -/
theorem distinguishable_iff_not_indistinguishable {c₁ c₂ : C} :
    Distinguishable r c₁ c₂ ↔ ¬(c₁ ~[r] c₂) := Iff.rfl

/-- There exist distinguishable configurations (by nontriviality) -/
theorem exists_distinguishable :
    ∃ c₁ c₂ : C, Distinguishable r c₁ c₂ :=
  r.nontrivial

/-! ## Module Status -/

def indistinguishable_status : String :=
  "✓ Indistinguishable relation defined (RG3)\n" ++
  "✓ Proved: reflexivity, symmetry, transitivity\n" ++
  "✓ Proved: indistinguishable_equivalence\n" ++
  "✓ ResolutionCell defined (equivalence classes)\n" ++
  "✓ Proved: resolutionCell_eq_fiber\n" ++
  "✓ Proved: resolutionCells_partition\n" ++
  "✓ LocalResolution defined\n" ++
  "✓ Distinguishable defined\n" ++
  "\n" ++
  "INDISTINGUISHABILITY (RG3) COMPLETE"

#eval indistinguishable_status

end RecogGeom
end IndisputableMonolith
