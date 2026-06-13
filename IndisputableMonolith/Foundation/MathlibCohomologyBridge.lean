import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Category.TopCat.Sphere
import IndisputableMonolith.Foundation.DimensionForcing

/-!
# Mathlib Cohomology Bridge Contract

Mathlib currently supplies the singular homology functor API, but the T8
replacement needs more: a Mathlib-backed computation of the reduced cohomology
of `S¹`, plus the Alexander-duality bridge from circle-complement homology to
that cohomology group.

This module records the exact backend object needed to replace the current
concrete `S¹` cohomology encoding.  It deliberately does not fake that backend
by reusing `AlexanderDuality.CircleReducedCohomologyNontrivial`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MathlibCohomologyBridge

universe u v w

open CategoryTheory

/-- Import-checked fact: the pinned Mathlib exposes the singular homology
functor API.  This is not yet the S¹ computation or Alexander-duality theorem;
it is the real Mathlib surface those future computations must use. -/
def MathlibSingularHomologyAPIAvailable : Prop :=
  ∀ (C : Type u) [CategoryTheory.Category.{v, u} C]
    [CategoryTheory.Limits.HasCoproducts.{w, v, u} C]
    [CategoryTheory.Preadditive C]
    [CategoryTheory.CategoryWithHomology C]
    (n : ℕ),
      Nonempty
        { F : CategoryTheory.Functor C (CategoryTheory.Functor TopCat.{w} C) //
          F = AlgebraicTopology.singularHomologyFunctor C n }

/-- The singular homology functor exists in the pinned Mathlib. -/
theorem mathlibSingularHomologyAPIAvailable :
    MathlibSingularHomologyAPIAvailable := by
  intro C _ _ _ _ n
  exact ⟨AlgebraicTopology.singularHomologyFunctor C n, rfl⟩

/-- The concrete Mathlib object that must eventually be computed:
first singular homology of the topological circle with integer coefficients. -/
noncomputable abbrev circleH1Z : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)

/-- The nonvanishing computation required from Mathlib before the current
concrete S¹ bridge can be replaced. -/
def circleH1ZNonzero : Prop :=
  ¬ CategoryTheory.Limits.IsZero circleH1Z

/-- Strong final Mathlib closure certificate: compute the circle's first
singular homology as the integer module. -/
def circleH1ZIsoInt : Prop :=
  Nonempty (circleH1Z ≅ ModuleCat.of ℤ ℤ)

/-- Final import interface for the missing pinned-Mathlib computation.  A future
upgrade should fill this from Mathlib's actual computation of `H_1(S¹; ℤ)`,
not from a project-local replacement. -/
structure CircleH1MathlibComputation : Prop where
  singular_homology_api_available : MathlibSingularHomologyAPIAvailable
  target_is_imported_circle_h1 :
    circleH1Z =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)
  h1_iso_int : circleH1ZIsoInt

/-- A proof of the strong target `H_1(S¹; ℤ) ≅ ℤ` fills the final Mathlib
computation interface, since the singular homology API and target identity are
already import-checked in this module. -/
theorem circleH1MathlibComputation_of_iso_int
    (hiso : circleH1ZIsoInt) : CircleH1MathlibComputation where
  singular_homology_api_available := mathlibSingularHomologyAPIAvailable
  target_is_imported_circle_h1 := rfl
  h1_iso_int := hiso

/-- The final Mathlib computation interface is equivalent to the strong target
`H_1(S¹; ℤ) ≅ ℤ`. -/
theorem circleH1MathlibComputation_iff_iso_int :
    Nonempty CircleH1MathlibComputation ↔ circleH1ZIsoInt := by
  constructor
  · rintro ⟨C⟩
    exact C.h1_iso_int
  · intro hiso
    exact ⟨circleH1MathlibComputation_of_iso_int hiso⟩

/-- The integer module is not a zero object in `ModuleCat ℤ`. -/
theorem intModuleCat_not_isZero :
    ¬ CategoryTheory.Limits.IsZero (ModuleCat.of ℤ ℤ) := by
  intro hzero
  rcases hzero.unique_to (ModuleCat.of ℤ ℤ) with ⟨u⟩
  letI : Unique ((ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ)) := u
  have hhom :
      (𝟙 (ModuleCat.of ℤ ℤ)) =
        (0 : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ)) :=
    Subsingleton.elim _ _
  have hlin := congrArg ModuleCat.Hom.hom hhom
  have hval := congrArg (fun f : ℤ →ₗ[ℤ] ℤ => f 1) hlin
  norm_num at hval

/-- Computing `H_1(S¹; ℤ)` as `ℤ` closes the required nonvanishing target. -/
theorem circleH1ZNonzero_of_iso_int
    (hiso : circleH1ZIsoInt) : circleH1ZNonzero := by
  intro hzero
  rcases hiso with ⟨e⟩
  have hz : CategoryTheory.Limits.IsZero (ModuleCat.of ℤ ℤ) :=
    CategoryTheory.Limits.IsZero.of_iso hzero e.symm
  exact intModuleCat_not_isZero hz

/-- The final computation interface supplies the strong `H_1(S¹; ℤ) ≅ ℤ`
certificate. -/
theorem circleH1ZIsoInt_of_mathlib_computation
    (C : CircleH1MathlibComputation) : circleH1ZIsoInt :=
  C.h1_iso_int

/-- The final computation interface closes the nonvanishing theorem. -/
theorem circleH1ZNonzero_of_mathlib_computation
    (C : CircleH1MathlibComputation) : circleH1ZNonzero :=
  circleH1ZNonzero_of_iso_int C.h1_iso_int

/-- Checked certificate for the exact final circle-H1 import target.  This does
not prove the missing homology computation; it proves that every remaining
circle-H1 handoff is pinned to the imported Mathlib object and to the single
strong target `H_1(S¹; ℤ) ≅ ℤ`. -/
structure CircleH1TargetCertificate : Prop where
  singular_homology_api_available : MathlibSingularHomologyAPIAvailable
  target_is_imported_circle_h1 :
    circleH1Z =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)
  computation_iff_iso_int :
    Nonempty CircleH1MathlibComputation ↔ circleH1ZIsoInt
  iso_int_implies_nonzero :
    circleH1ZIsoInt → circleH1ZNonzero
  computation_implies_nonzero :
    ∀ _C : CircleH1MathlibComputation, circleH1ZNonzero

/-- The final circle-H1 target certificate for the pinned Mathlib surface. -/
theorem circleH1TargetCertificate : CircleH1TargetCertificate where
  singular_homology_api_available := mathlibSingularHomologyAPIAvailable
  target_is_imported_circle_h1 := rfl
  computation_iff_iso_int := circleH1MathlibComputation_iff_iso_int
  iso_int_implies_nonzero := circleH1ZNonzero_of_iso_int
  computation_implies_nonzero := circleH1ZNonzero_of_mathlib_computation

/-- The circle homology target is the actual imported Mathlib singular homology
object, not a project-local placeholder. -/
theorem circleH1Z_is_mathlib_singular_homology :
    circleH1Z =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1) :=
  rfl

/-- The backend required to replace the current concrete S¹ cohomology encoding.

The key field is `linking_from_circle_h1`: a future backend must prove the
nonvanishing of the concrete Mathlib circle homology object and route linking
through that computation. -/
structure MathlibCircleLinkingBackend where
  supportsLinking : DimensionForcing.Dimension → Prop
  uses_singular_homology_api : MathlibSingularHomologyAPIAvailable
  circle_h1_nonzero : circleH1ZNonzero
  linking_from_circle_h1 :
    ∀ D : DimensionForcing.Dimension,
      supportsLinking D ↔ D = 3 ∧ circleH1ZNonzero

/-- A Mathlib circle-linking backend still gives the same D=3 characterization,
but now that characterization must pass through the concrete `H_1(𝕊¹; ℤ)`
nonvanishing target. -/
theorem MathlibCircleLinkingBackend.circle_linking_iff
    (B : MathlibCircleLinkingBackend) (D : DimensionForcing.Dimension) :
    B.supportsLinking D ↔ D = 3 := by
  constructor
  · intro h
    exact ((B.linking_from_circle_h1 D).mp h).1
  · intro hD
    exact (B.linking_from_circle_h1 D).mpr ⟨hD, B.circle_h1_nonzero⟩

/-- Any backend satisfying the Mathlib replacement contract agrees with the
current T8 linking surface. -/
theorem MathlibCircleLinkingBackend.agrees_with_current
    (B : MathlibCircleLinkingBackend) (D : DimensionForcing.Dimension) :
    B.supportsLinking D ↔ DimensionForcing.SupportsNontrivialLinking D := by
  constructor
  · intro h
    have hD : D = 3 := (B.circle_linking_iff D).mp h
    rw [hD]
    exact DimensionForcing.D3_has_linking
  · intro h
    exact (B.circle_linking_iff D).mpr (DimensionForcing.linking_requires_D3 D h)

/-- Any Mathlib linking backend has the same D=3 forcing theorem. -/
theorem MathlibCircleLinkingBackend.forces_D3
    (B : MathlibCircleLinkingBackend) (D : DimensionForcing.Dimension) :
    B.supportsLinking D → D = 3 :=
  (B.circle_linking_iff D).mp

/-- Any Mathlib linking backend supports D=3. -/
theorem MathlibCircleLinkingBackend.d3_supports_linking
    (B : MathlibCircleLinkingBackend) :
    B.supportsLinking 3 :=
  (B.circle_linking_iff 3).mpr rfl

/-- A proof of the concrete Mathlib circle-H1 nonvanishing target is enough to
build the backend object required by the T8 replacement. -/
def mathlibCircleLinkingBackend_from_circleH1ZNonzero
    (hH1 : circleH1ZNonzero) : MathlibCircleLinkingBackend where
  supportsLinking := fun D => D = 3
  uses_singular_homology_api := mathlibSingularHomologyAPIAvailable
  circle_h1_nonzero := hH1
  linking_from_circle_h1 := by
    intro D
    constructor
    · intro hD
      exact ⟨hD, hH1⟩
    · intro h
      exact h.1

/-- The remaining backend object is equivalent to the single concrete Mathlib
homology computation `circleH1ZNonzero`. -/
theorem mathlibCircleLinkingBackend_nonempty_iff_circleH1ZNonzero :
    Nonempty MathlibCircleLinkingBackend ↔ circleH1ZNonzero := by
  constructor
  · rintro ⟨B⟩
    exact B.circle_h1_nonzero
  · intro hH1
    exact ⟨mathlibCircleLinkingBackend_from_circleH1ZNonzero hH1⟩

/-- The backend object projects to the concrete circle-H1 nonvanishing theorem. -/
theorem circleH1ZNonzero_of_mathlibCircleLinkingBackend
    (hB : Nonempty MathlibCircleLinkingBackend) : circleH1ZNonzero :=
  mathlibCircleLinkingBackend_nonempty_iff_circleH1ZNonzero.mp hB

/-- The concrete circle-H1 nonvanishing theorem builds the backend object. -/
theorem mathlibCircleLinkingBackend_of_circleH1ZNonzero
    (hH1 : circleH1ZNonzero) : Nonempty MathlibCircleLinkingBackend :=
  mathlibCircleLinkingBackend_nonempty_iff_circleH1ZNonzero.mpr hH1

/-- The strong `H_1(S¹; ℤ) ≅ ℤ` target builds the backend object. -/
theorem mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (hiso : circleH1ZIsoInt) : Nonempty MathlibCircleLinkingBackend :=
  mathlibCircleLinkingBackend_of_circleH1ZNonzero
    (circleH1ZNonzero_of_iso_int hiso)

/-- The final Mathlib computation interface builds the backend object. -/
theorem mathlibCircleLinkingBackend_of_circleH1MathlibComputation
    (C : CircleH1MathlibComputation) : Nonempty MathlibCircleLinkingBackend :=
  mathlibCircleLinkingBackend_of_circleH1ZNonzero
    (circleH1ZNonzero_of_mathlib_computation C)

/-- Contract certificate for the present state: the Mathlib singular homology
API is imported and checked, while the backend replacing the concrete S¹
encoding remains a named `Nonempty MathlibCircleLinkingBackend` target. -/
structure MathlibCohomologyBridgeContract : Prop where
  singular_homology_api_available : MathlibSingularHomologyAPIAvailable
  circle_h1_target_certificate : CircleH1TargetCertificate
  circle_h1_object_checked :
    circleH1Z =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)
  current_linking_characterization :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.SupportsNontrivialLinking D ↔ D = 3
  backend_nonempty_implies_circle_h1_nonzero :
    Nonempty MathlibCircleLinkingBackend → circleH1ZNonzero
  backend_nonempty_iff_circle_h1_nonzero :
    Nonempty MathlibCircleLinkingBackend ↔ circleH1ZNonzero
  backend_of_circle_h1_nonzero :
    circleH1ZNonzero → Nonempty MathlibCircleLinkingBackend

/-- Checked contract for the remaining Mathlib cohomology replacement. -/
theorem mathlibCohomologyBridgeContract :
    MathlibCohomologyBridgeContract where
  singular_homology_api_available := mathlibSingularHomologyAPIAvailable
  circle_h1_target_certificate := circleH1TargetCertificate
  circle_h1_object_checked := circleH1Z_is_mathlib_singular_homology
  current_linking_characterization := by
    intro D
    constructor
    · exact DimensionForcing.linking_requires_D3 D
    · intro hD
      rw [hD]
      exact DimensionForcing.D3_has_linking
  backend_nonempty_implies_circle_h1_nonzero := by
    rintro ⟨B⟩
    exact B.circle_h1_nonzero
  backend_nonempty_iff_circle_h1_nonzero :=
    mathlibCircleLinkingBackend_nonempty_iff_circleH1ZNonzero
  backend_of_circle_h1_nonzero :=
    mathlibCircleLinkingBackend_of_circleH1ZNonzero

/-- Paper-facing handoff certificate for the exact external Mathlib target.
This packages the imported object, the strong `H_1(S¹; ℤ) ≅ ℤ` interface, the
weaker nonvanishing target, and the backend object used by T8. -/
structure MathlibBackendHandoffCertificate : Prop where
  bridge_contract : MathlibCohomologyBridgeContract
  target_certificate : CircleH1TargetCertificate
  target_is_imported_circle_h1 :
    circleH1Z =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)
  computation_iff_iso_int :
    Nonempty CircleH1MathlibComputation ↔ circleH1ZIsoInt
  iso_int_implies_nonzero :
    circleH1ZIsoInt → circleH1ZNonzero
  computation_implies_nonzero :
    CircleH1MathlibComputation → circleH1ZNonzero
  backend_iff_circle_h1_nonzero :
    Nonempty MathlibCircleLinkingBackend ↔ circleH1ZNonzero
  backend_from_circle_h1_nonzero :
    circleH1ZNonzero → Nonempty MathlibCircleLinkingBackend
  backend_from_iso_int :
    circleH1ZIsoInt → Nonempty MathlibCircleLinkingBackend
  backend_from_mathlib_computation :
    CircleH1MathlibComputation → Nonempty MathlibCircleLinkingBackend
  backend_agrees_with_current :
    ∀ (B : MathlibCircleLinkingBackend) (D : DimensionForcing.Dimension),
      B.supportsLinking D ↔ DimensionForcing.SupportsNontrivialLinking D
  backend_forces_D3 :
    ∀ (B : MathlibCircleLinkingBackend) (D : DimensionForcing.Dimension),
      B.supportsLinking D → D = 3
  backend_supports_D3 :
    ∀ B : MathlibCircleLinkingBackend, B.supportsLinking 3

/-- Checked handoff certificate for the exact external Mathlib target. -/
theorem mathlibBackendHandoffCertificate :
    MathlibBackendHandoffCertificate where
  bridge_contract := mathlibCohomologyBridgeContract
  target_certificate := circleH1TargetCertificate
  target_is_imported_circle_h1 := circleH1Z_is_mathlib_singular_homology
  computation_iff_iso_int := circleH1MathlibComputation_iff_iso_int
  iso_int_implies_nonzero := circleH1ZNonzero_of_iso_int
  computation_implies_nonzero := circleH1ZNonzero_of_mathlib_computation
  backend_iff_circle_h1_nonzero :=
    mathlibCircleLinkingBackend_nonempty_iff_circleH1ZNonzero
  backend_from_circle_h1_nonzero :=
    mathlibCircleLinkingBackend_of_circleH1ZNonzero
  backend_from_iso_int := by
    exact mathlibCircleLinkingBackend_of_circleH1ZIsoInt
  backend_from_mathlib_computation := by
    exact mathlibCircleLinkingBackend_of_circleH1MathlibComputation
  backend_agrees_with_current := by
    intro B D
    exact B.agrees_with_current D
  backend_forces_D3 := by
    intro B D
    exact B.forces_D3 D
  backend_supports_D3 := by
    intro B
    exact B.d3_supports_linking

end MathlibCohomologyBridge
end Foundation
end IndisputableMonolith
