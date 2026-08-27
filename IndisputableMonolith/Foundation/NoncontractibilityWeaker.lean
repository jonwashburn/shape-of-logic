import Mathlib
import IndisputableMonolith.Foundation.ProbeDimensionSelection

/-!
# Non-contractibility is a different and weaker demand

First homology is the abelianization of the fundamental group, so it is
always abelian. A demand worded as "some probe cycle cannot be
contracted" therefore does not force a nonzero homology class: it can
be met by a nonabelian fundamental group whose abelianization vanishes.

Algebraically: if the commutator subgroup is the whole group, the
abelianization is a point. `A₅` has that property.

Geometrically: a dual-sphere probe already fires in more than one
dimension, so a homotopy-worded demand selects no unique `D`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace NoncontractibilityWeaker

/-- Abelianization is always commutative. Homology cannot see
nonabelian fundamental-group information. -/
theorem abelianization_comm {G : Type*} [Group G]
    (a b : Abelianization G) : a * b = b * a :=
  mul_comm a b

/-- If the commutator subgroup is the whole group, the abelianization
is a point. That is the algebraic form of `H₁ = 0` with `π₁ ≠ 1`. -/
theorem abelianization_trivial_of_commutator_top
    {G : Type*} [Group G] (h : commutator G = ⊤) :
    Subsingleton (Abelianization G) :=
  (QuotientGroup.subsingleton_iff (G := G)).2 h

theorem alternating_five_card :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup]
  decide

/-- Perfectness of `A₅`: the commutator is the whole group. -/
theorem alternating_five_commutator_top :
    commutator (alternatingGroup (Fin 5)) = ⊤ :=
  commutator_alternatingGroup_eq_top (by decide : 5 ≤ Fintype.card (Fin 5))

/-- The algebraic gap named in the paper: `A₅` is nontrivial, yet its
abelianization is a point. -/
theorem noncontractibility_does_not_force_H1 :
    Nontrivial (alternatingGroup (Fin 5)) ∧
      Subsingleton (Abelianization (alternatingGroup (Fin 5))) :=
  ⟨inferInstance,
    abelianization_trivial_of_commutator_top alternating_five_commutator_top⟩

/-- A homotopy-worded sphere-probe demand selects no unique dimension. -/
theorem homotopy_demand_selects_no_unique_dimension :
    ¬ ∃ D₀ : ℕ, ∀ D, 2 ≤ D →
      ProbeDimensionSelection.DetectsNontrivialSphereProbe (D - 2) D →
        D = D₀ :=
  ProbeDimensionSelection.dual_sphere_selects_no_unique_D

end NoncontractibilityWeaker
end Foundation
end IndisputableMonolith
