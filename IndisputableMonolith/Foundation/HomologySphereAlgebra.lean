import Mathlib
import IndisputableMonolith.Foundation.AlexanderDuality

/-!
# Homology-sphere algebra and implied orientability

The paper's homology-sphere lemma is Poincaré duality plus the universal
coefficient theorem: if `H₁(M;ℤ) = 0` and `H₂ ≅ H¹`, then `H₂ = 0`.
Orientability is the vanishing of `w₁ ∈ H¹(M;ℤ/2)`, and the same UCT
kills that group once `H₁ = 0` and `H₀` is free.

Mathlib does not yet supply Poincaré duality for a general closed
3-manifold. This module proves the algebraic implication the paper uses,
with the duality isomorphism as an explicit hypothesis, and proves the
UCT vanishing that makes orientability free.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace HomologySphereAlgebra

open AlexanderDuality

/-- A unique additive group is the zero group. -/
theorem unique_addCommGroup {G : Type*} [AddCommGroup G]
    (h : Subsingleton G) : ∀ x : G, x = 0 :=
  fun x => Subsingleton.elim x 0

/-- If the domain is a singleton, every additive homomorphism is zero. -/
theorem hom_subsingleton {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (h : Subsingleton A) : Subsingleton (A →+ B) :=
  ⟨fun f g => AddMonoidHom.ext fun x => by
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]⟩

/-- Algebraic core of the homology-sphere lemma: Poincaré duality
`H₂ ≅ H¹` and UCT `H¹ ≅ Hom(H₁,ℤ)` send `H₁ = 0` to `H₂ = 0`. -/
theorem homology_sphere_of_duality
    {H1 H2 H1coh : Type*}
    [AddCommGroup H1] [AddCommGroup H2] [AddCommGroup H1coh]
    (hPD : H2 ≃+ H1coh)
    (hUCT : H1coh ≃+ (H1 →+ ℤ))
    (hH1 : Subsingleton H1) :
    Subsingleton H2 := by
  haveI : Subsingleton (H1 →+ ℤ) := hom_subsingleton hH1
  haveI : Subsingleton H1coh := hUCT.injective.subsingleton
  exact hPD.injective.subsingleton

/-- The Hom term of UCT with `ℤ/2` coefficients also vanishes. -/
theorem H1_zero_implies_H1_mod2_zero
    {H1 : Type*} [AddCommGroup H1]
    (h : Subsingleton H1) :
    Subsingleton (H1 →+ ZMod 2) :=
  hom_subsingleton h

/-- Orientability, as vanishing of a class in `H¹(−;ℤ/2)`, follows from
`H₁ = 0` once that cohomology is identified with `Hom(H₁,ℤ/2)`. -/
theorem orientability_of_H1_zero
    {H1 H1mod2 : Type*} [AddCommGroup H1] [AddCommGroup H1mod2]
    (hUCT : H1mod2 ≃+ (H1 →+ ZMod 2))
    (hH1 : Subsingleton H1) :
    Subsingleton H1mod2 := by
  have : Subsingleton (H1 →+ ZMod 2) := H1_zero_implies_H1_mod2_zero hH1
  exact hUCT.injective.subsingleton

/-- If Alexander duality identifies complement `H₁` with reduced
cohomology of the circle in degree `D−2`, then that group is nontrivial
iff `D = 3`. -/
theorem codimension_of_alexander
    {G : Type*} [AddCommGroup G] (D : ℕ)
    (hAlex : Nontrivial G ↔ CircleReducedCohomologyNontrivial ((D : ℤ) - 2)) :
    Nontrivial G ↔ D = 3 := by
  rw [hAlex, circle_reduced_cohomology_iff]
  constructor
  · intro h
    have : (D : ℤ) - 2 = 1 := h
    have : (D : ℤ) = 3 := by linarith
    exact_mod_cast this
  · intro h
    subst h
    decide

end HomologySphereAlgebra
end Foundation
end IndisputableMonolith
