/-
  PrimitiveRecognitionCalculus/CubicalChainComplex.lean

  A stronger multi-distinction geometry packaging.

  `MultiDistinctionGeometry.lean` proves the local 2-face cancellation used by
  cubical homology. This module packages the same content as a finite chain
  complex interface: a boundary pair is a pair of maps whose composite vanishes.
  This is intentionally lightweight, but it gives the internal paper a stable
  "chain complex" theorem without overclaiming a full homology library.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.MultiDistinctionGeometry

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace CubicalChainComplex

/-- A two-step chain complex over types `C₂`, `C₁`, `C₀`: boundary after boundary
is zero. -/
structure BoundaryPair (C₂ C₁ C₀ : Type*) [Zero C₀] where
  d₂ : C₂ → C₁
  d₁ : C₁ → C₀
  square_zero : ∀ c : C₂, d₁ (d₂ c) = 0

/-- The explicit Delta square as a two-step chain complex. -/
def squareBoundaryPair : BoundaryPair ℤ MultiDistinctionGeometry.C1 MultiDistinctionGeometry.C0 where
  d₂ := MultiDistinctionGeometry.d2
  d₁ := MultiDistinctionGeometry.d1
  square_zero := by
    intro c
    exact MultiDistinctionGeometry.boundary_squared_zero c

/-- Any ambient 2-face in an `n`-channel cube has square-zero boundary. -/
theorem ambient_two_face_square_zero {n : ℕ}
    (base : MultiDistinctionGeometry.Config n) (i j : Fin n) (c : ℤ) :
    MultiDistinctionGeometry.faceBoundaryBoundary base i j c = fun _ => 0 :=
  MultiDistinctionGeometry.face_boundary_squared_zero_general base i j c

/-- **Cubical chain packaging headline.** Delta's multi-distinction geometry has
a concrete chain-complex interface on the square and square-zero boundary on
every ambient 2-face. The remaining stronger target is the full all-dimensions
homology API, not the local `∂²=0` law. -/
theorem cubical_chain_complex_headline :
    (∀ c : ℤ, squareBoundaryPair.d₁ (squareBoundaryPair.d₂ c) = 0)
      ∧ (∀ (n : ℕ) (base : MultiDistinctionGeometry.Config n) (i j : Fin n) (c : ℤ),
          MultiDistinctionGeometry.faceBoundaryBoundary base i j c = fun _ => 0) :=
  ⟨squareBoundaryPair.square_zero, fun _ base i j c => ambient_two_face_square_zero base i j c⟩

/-- A finite 2-face certificate inside an `n`-channel distinction cube. -/
structure TwoFaceCert (n : ℕ) where
  base : MultiDistinctionGeometry.Config n
  i : Fin n
  j : Fin n
  coeff : ℤ

/-- The boundary-of-boundary chain carried by a two-face certificate. -/
def TwoFaceCert.boundaryBoundary {n : ℕ} (F : TwoFaceCert n) :
    MultiDistinctionGeometry.Config n → ℤ :=
  MultiDistinctionGeometry.faceBoundaryBoundary F.base F.i F.j F.coeff

/-- Every finite 2-face certificate has zero boundary-of-boundary. -/
theorem twoFaceCert_boundary_squared_zero {n : ℕ} (F : TwoFaceCert n) :
    F.boundaryBoundary = fun _ => 0 :=
  ambient_two_face_square_zero F.base F.i F.j F.coeff

/-- A finite list of two-face certificates has zero total boundary-of-boundary.
This is the additive finite-certificate version of local cubical `∂²=0`. -/
theorem twoFaceCert_list_boundary_squared_zero {n : ℕ} (faces : List (TwoFaceCert n)) :
    (fun w : MultiDistinctionGeometry.Config n =>
      faces.foldl (fun acc F => acc + F.boundaryBoundary w) 0) = fun _ => 0 := by
  induction faces with
  | nil =>
      funext w
      simp
  | cons F rest ih =>
      funext w
      have hF := congrFun (twoFaceCert_boundary_squared_zero F) w
      have hrest := congrFun ih w
      simp [List.foldl_cons, hF, hrest]

/-- **Finite cubical certificate headline.** The local square-zero law is stable
under finite collections of certified 2-faces: every finite 2-face ledger has
zero total boundary-of-boundary. This is the all-finite-2-face strengthening
available from the current definitions without introducing a full homology API. -/
theorem finite_two_face_ledger_square_zero :
    ∀ (n : ℕ) (faces : List (TwoFaceCert n)),
      (fun w : MultiDistinctionGeometry.Config n =>
        faces.foldl (fun acc F => acc + F.boundaryBoundary w) 0) = fun _ => 0 :=
  fun n faces => twoFaceCert_list_boundary_squared_zero (n := n) faces

end CubicalChainComplex
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
