import Mathlib
import IndisputableMonolith.Foundation.GaugeFromCube

/-!
# Continuous connected groups cannot act nontrivially on Q₃

Milan's observation: a continuous homomorphism from a connected topological
group into the discrete permutation group of the 3-cube vertices is the
trivial homomorphism. Continuous rotational structure therefore lives off
Q₃; the cube symmetries that the tree already carries are the finite
hyperoctahedral action (`GaugeFromCube.SignedPerm 3`).

SO(3) is one connected group to which the theorem applies. The statement
is not special to SO(3): it holds for every connected topological group.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SO3CubeAutTriviality

open GaugeFromCube

/-- The 3-cube vertex set. -/
abbrev Q3 := CubeVertex 3

/-- Discrete topology on the combinatorial automorphism group of Q₃. -/
instance : TopologicalSpace (Equiv.Perm Q3) := ⊥
instance : DiscreteTopology (Equiv.Perm Q3) := ⟨rfl⟩

/-- A continuous map from a connected space into a discrete space is
constant. -/
theorem continuous_connected_to_discrete_const
    {α β : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    [TopologicalSpace β] [DiscreteTopology β]
    {f : α → β} (hf : Continuous f) (x y : α) : f x = f y := by
  have hfLC : IsLocallyConstant f :=
    (IsLocallyConstant.iff_continuous f).2 hf
  exact hfLC.apply_eq_of_preconnectedSpace x y

/-- A continuous group homomorphism from a preconnected group to a discrete
group is trivial. -/
theorem continuous_monoidHom_connected_to_discrete_trivial
    {G H : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (φ : G →* H) (hφ : Continuous φ) (g : G) : φ g = 1 := by
  have : φ g = φ 1 :=
    continuous_connected_to_discrete_const hφ g 1
  simpa [φ.map_one] using this

/-- **THEOREM.** Any continuous action of a preconnected group on the finite
discrete 3-cube is trivial. This is Milan's SO(3) vs Aut(Q₃) observation
as a theorem: Aut(Q₃) is discrete and finite, and a connected group cannot
map onto it continuously except at the identity. -/
theorem connected_action_on_Q3_trivial
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    (μ : G →* Equiv.Perm Q3) (hμ : Continuous μ) (g : G) :
    μ g = 1 :=
  continuous_monoidHom_connected_to_discrete_trivial μ hμ g

/-- The finite cube symmetry group already in the tree has order 48.
A connected continuous action cannot reproduce it. -/
theorem cube_aut_order_finite : Fintype.card (SignedPerm 3) = 48 :=
  cube_aut_order

/-- Specialization named for the rotation group: if SO(3) (or any
connected group) acts continuously on Q₃, the action is trivial. -/
theorem so3_style_action_on_Q3_trivial
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    (μ : G →* Equiv.Perm Q3) (hμ : Continuous μ) :
    μ = 1 :=
  MonoidHom.ext (connected_action_on_Q3_trivial μ hμ)

end SO3CubeAutTriviality
end Foundation
end IndisputableMonolith
