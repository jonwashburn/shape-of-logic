import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import IndisputableMonolith.Foundation.CircleParam
import IndisputableMonolith.Foundation.CircleFundamentalSimplex
import IndisputableMonolith.Foundation.MathlibCohomologyBridge

/-!
# Circle H₁ Computation Workbench

This module is the local Mathlib-style workbench for the missing computation
`H₁(S¹; ℤ) ≅ ℤ`.  It does not replace `TopCat.sphere 1` and does not feed the
strict T8 bridge until a real equivalence to Mathlib's imported singular
homology object is proved.

The first proved atom is the algebraic core of the finite circle chain model:
a chain complex supported by `ℤ` in degree `1` has degree-`1` homology `ℤ`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleH1Computation

open CategoryTheory CategoryTheory.Limits ZeroObject Opposite

noncomputable section

/-- The integer chain complex supported in degree `1`.  This is the algebraic
core of the finite circle model before the topological transport to
`TopCat.sphere 1` is supplied. -/
abbrev singleDegreeOneIntComplex :
    HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ) :=
  (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
    (ModuleCat.of ℤ ℤ)

/-- Degree-`1` homology of the single-supported integer chain complex is the
integer module. -/
def singleDegreeOneIntComplexHomologyOneIsoInt :
    (((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
      (ModuleCat.of ℤ ℤ)).homology 1) ≅ ModuleCat.of ℤ ℤ :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 1
    (ModuleCat.of ℤ ℤ)

/-- Proposition-facing form of `singleDegreeOneIntComplexHomologyOneIsoInt`,
matching the `circleH1ZIsoInt` pattern used by the strict T8 bridge. -/
theorem singleDegreeOneIntComplexHomologyOneNonemptyIsoInt :
    Nonempty
      ((((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of ℤ ℤ)).homology 1) ≅ ModuleCat.of ℤ ℤ) :=
  ⟨singleDegreeOneIntComplexHomologyOneIsoInt⟩

/-- Any chain complex isomorphic to the degree-`1` single-supported integer
complex has degree-`1` homology `ℤ`.  This is the transport lemma needed once a
finite circle chain model is identified with the single degree-`1` reduced
model. -/
def homologyOneIsoIntOfIsoSingleDegreeOneIntComplex
    {K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)}
    (e : K ≅ singleDegreeOneIntComplex) :
    ((HomologicalComplex.homologyFunctor
      (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj K) ≅ ModuleCat.of ℤ ℤ :=
  ((HomologicalComplex.homologyFunctor
      (ModuleCat ℤ) (ComplexShape.down ℕ) 1).mapIso e) ≪≫
    singleDegreeOneIntComplexHomologyOneIsoInt

/-- Proposition-facing form of
`homologyOneIsoIntOfIsoSingleDegreeOneIntComplex`. -/
theorem homologyOneNonemptyIsoIntOfIsoSingleDegreeOneIntComplex
    {K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)}
    (e : K ≅ singleDegreeOneIntComplex) :
    Nonempty
      (((HomologicalComplex.homologyFunctor
        (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj K) ≅ ModuleCat.of ℤ ℤ) :=
  ⟨homologyOneIsoIntOfIsoSingleDegreeOneIntComplex e⟩

/-- Degree-local quasi-isomorphism transport: if a chain complex maps by a
quasi-isomorphism in degree `1` to the single-supported integer complex, then
its degree-`1` homology is `ℤ`. -/
def homologyOneIsoIntOfQuasiIsoAtSingleDegreeOneIntComplex
    {K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)}
    (f : K ⟶ singleDegreeOneIntComplex)
    [K.HasHomology 1] [QuasiIsoAt f 1] :
    K.homology 1 ≅ ModuleCat.of ℤ ℤ :=
  isoOfQuasiIsoAt f 1 ≪≫
    singleDegreeOneIntComplexHomologyOneIsoInt

/-- Proposition-facing form of the degree-local quasi-isomorphism transport. -/
theorem homologyOneNonemptyIsoIntOfQuasiIsoAtSingleDegreeOneIntComplex
    {K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)}
    (f : K ⟶ singleDegreeOneIntComplex)
    [K.HasHomology 1] [QuasiIsoAt f 1] :
    Nonempty (K.homology 1 ≅ ModuleCat.of ℤ ℤ) :=
  ⟨homologyOneIsoIntOfQuasiIsoAtSingleDegreeOneIntComplex f⟩

/-- Global quasi-isomorphism transport, for the common case where the finite
circle chain model is proved quasi-isomorphic to the single-supported reduced
model in every degree. -/
def homologyOneIsoIntOfQuasiIsoSingleDegreeOneIntComplex
    {K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)}
    (f : K ⟶ singleDegreeOneIntComplex)
    [∀ i, K.HasHomology i] [QuasiIso f] :
    K.homology 1 ≅ ModuleCat.of ℤ ℤ :=
  homologyOneIsoIntOfQuasiIsoAtSingleDegreeOneIntComplex f

/-- Proposition-facing form of the global quasi-isomorphism transport. -/
theorem homologyOneNonemptyIsoIntOfQuasiIsoSingleDegreeOneIntComplex
    {K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)}
    (f : K ⟶ singleDegreeOneIntComplex)
    [∀ i, K.HasHomology i] [QuasiIso f] :
    Nonempty (K.homology 1 ≅ ModuleCat.of ℤ ℤ) :=
  ⟨homologyOneIsoIntOfQuasiIsoSingleDegreeOneIntComplex f⟩

/-- The reduced cellular chain model of the circle: one integer generator in
degree `1` and zero elsewhere.  This is a finite chain model target, not a
replacement for `TopCat.sphere 1`. -/
abbrev reducedCellularCircleChainModel :
    HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ) :=
  singleDegreeOneIntComplex

/-- The reduced cellular circle model has chain group `ℤ` in degree `1`. -/
def reducedCellularCircleChainModelXOneIsoInt :
    reducedCellularCircleChainModel.X 1 ≅ ModuleCat.of ℤ ℤ :=
  HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
    (ModuleCat.of ℤ ℤ)

/-- The reduced cellular circle model has zero chain group in degree `0`. -/
theorem reducedCellularCircleChainModelXZeroIsZero :
    CategoryTheory.Limits.IsZero (reducedCellularCircleChainModel.X 0) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 1
    (ModuleCat.of ℤ ℤ) 0 (by norm_num)

/-- The reduced cellular circle model has zero chain groups above degree `1`. -/
theorem reducedCellularCircleChainModelXSuccSuccIsZero (n : ℕ) :
    CategoryTheory.Limits.IsZero (reducedCellularCircleChainModel.X (n + 2)) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 1
    (ModuleCat.of ℤ ℤ) (n + 2) (by omega)

/-- All differentials in the reduced cellular circle model are zero. -/
theorem reducedCellularCircleChainModel_d_eq_zero (i j : ℕ) :
    reducedCellularCircleChainModel.d i j = 0 :=
  HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 1
    (ModuleCat.of ℤ ℤ) i j

/-- The reduced cellular circle model has first homology `ℤ`. -/
def reducedCellularCircleChainModelH1IsoInt :
    reducedCellularCircleChainModel.homology 1 ≅ ModuleCat.of ℤ ℤ :=
  singleDegreeOneIntComplexHomologyOneIsoInt

/-- Proposition-facing form of
`reducedCellularCircleChainModelH1IsoInt`. -/
theorem reducedCellularCircleChainModelH1NonemptyIsoInt :
    Nonempty (reducedCellularCircleChainModel.homology 1 ≅ ModuleCat.of ℤ ℤ) :=
  ⟨reducedCellularCircleChainModelH1IsoInt⟩

/-- The ordinary two-cell cellular chain model of the circle: one integer
generator in degree `0`, one integer generator in degree `1`, no higher chain
groups, and zero boundary.  This remains an algebraic finite-chain model until
a later theorem connects it to Mathlib's `TopCat.sphere 1`. -/
def ordinaryCellularCircleChainModel :
    HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ) where
  X n := if n = 0 then ModuleCat.of ℤ ℤ
    else if n = 1 then ModuleCat.of ℤ ℤ
    else 0
  d _ _ := 0

/-- The ordinary cellular circle model has chain group `ℤ` in degree `0`. -/
def ordinaryCellularCircleChainModelXZeroIsoInt :
    ordinaryCellularCircleChainModel.X 0 ≅ ModuleCat.of ℤ ℤ :=
  eqToIso (by simp [ordinaryCellularCircleChainModel])

/-- The ordinary cellular circle model has chain group `ℤ` in degree `1`. -/
def ordinaryCellularCircleChainModelXOneIsoInt :
    ordinaryCellularCircleChainModel.X 1 ≅ ModuleCat.of ℤ ℤ :=
  eqToIso (by simp [ordinaryCellularCircleChainModel])

/-- The ordinary cellular circle model has zero chain groups above degree `1`. -/
theorem ordinaryCellularCircleChainModelXSuccSuccIsZero (n : ℕ) :
    CategoryTheory.Limits.IsZero (ordinaryCellularCircleChainModel.X (n + 2)) := by
  dsimp [ordinaryCellularCircleChainModel]
  exact isZero_zero (C := ModuleCat ℤ)

/-- All differentials in the ordinary cellular circle model are zero. -/
theorem ordinaryCellularCircleChainModel_d_eq_zero (i j : ℕ) :
    ordinaryCellularCircleChainModel.d i j = 0 :=
  rfl

/-- Since the outgoing degree-`1` boundary is zero, the degree-`1` cycles in the
ordinary cellular circle model are the whole degree-`1` chain group, hence
`ℤ`. -/
def ordinaryCellularCircleChainModelCyclesOneIsoInt :
    ordinaryCellularCircleChainModel.cycles 1 ≅ ModuleCat.of ℤ ℤ :=
  ordinaryCellularCircleChainModel.iCyclesIso 1 0 (by norm_num)
      (ordinaryCellularCircleChainModel_d_eq_zero 1 0) ≪≫
    ordinaryCellularCircleChainModelXOneIsoInt

/-- The ordinary two-cell cellular circle model has first homology `ℤ`. -/
def ordinaryCellularCircleChainModelH1IsoInt :
    ordinaryCellularCircleChainModel.homology 1 ≅ ModuleCat.of ℤ ℤ :=
  (ordinaryCellularCircleChainModel.isoHomologyπ 2 1 (by norm_num)
      (ordinaryCellularCircleChainModel_d_eq_zero 2 1)).symm ≪≫
    ordinaryCellularCircleChainModelCyclesOneIsoInt

/-- Proposition-facing form of `ordinaryCellularCircleChainModelH1IsoInt`. -/
theorem ordinaryCellularCircleChainModelH1NonemptyIsoInt :
    Nonempty (ordinaryCellularCircleChainModel.homology 1 ≅ ModuleCat.of ℤ ℤ) :=
  ⟨ordinaryCellularCircleChainModelH1IsoInt⟩

/-- The ordinary two-cell cellular circle model and the reduced one have the
same first homology.  This is an algebraic comparison of the two finite chain
models, independent of any topological claim about `TopCat.sphere 1`. -/
def ordinaryCellularCircleChainModelH1IsoReducedCellularH1 :
    ordinaryCellularCircleChainModel.homology 1 ≅
      reducedCellularCircleChainModel.homology 1 :=
  ordinaryCellularCircleChainModelH1IsoInt ≪≫
    reducedCellularCircleChainModelH1IsoInt.symm

/-- Proposition-facing form of
`ordinaryCellularCircleChainModelH1IsoReducedCellularH1`. -/
theorem ordinaryCellularCircleChainModelH1NonemptyIsoReducedCellularH1 :
    Nonempty
      (ordinaryCellularCircleChainModel.homology 1 ≅
        reducedCellularCircleChainModel.homology 1) :=
  ⟨ordinaryCellularCircleChainModelH1IsoReducedCellularH1⟩

/-- Chain map collapsing the degree-`0` cellular generator and retaining the
degree-`1` circle generator. -/
def ordinaryCellularToReducedChainMap :
    ordinaryCellularCircleChainModel ⟶ reducedCellularCircleChainModel :=
  HomologicalComplex.mkHomToSingle
    ordinaryCellularCircleChainModelXOneIsoInt.hom
    (by
      intro i _hi
      simp [ordinaryCellularCircleChainModel_d_eq_zero])

/-- In degree `1`, `ordinaryCellularToReducedChainMap` is the identity on the
chosen integer generator, modulo the definitional single-complex isomorphism. -/
theorem ordinaryCellularToReducedChainMap_f_one :
    ordinaryCellularToReducedChainMap.f 1 =
      ordinaryCellularCircleChainModelXOneIsoInt.hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 1 (ModuleCat.of ℤ ℤ)).inv := by
  simp [ordinaryCellularToReducedChainMap]

/-- Chain map including the reduced degree-`1` model into the ordinary two-cell
cellular circle model. -/
def reducedCellularToOrdinaryChainMap :
    reducedCellularCircleChainModel ⟶ ordinaryCellularCircleChainModel :=
  HomologicalComplex.mkHomFromSingle
    ordinaryCellularCircleChainModelXOneIsoInt.inv
    (by
      intro k _hk
      simp [ordinaryCellularCircleChainModel_d_eq_zero])

/-- In degree `1`, `reducedCellularToOrdinaryChainMap` is the inverse of the
chosen integer-generator identification, modulo the definitional
single-complex isomorphism. -/
theorem reducedCellularToOrdinaryChainMap_f_one :
    reducedCellularToOrdinaryChainMap.f 1 =
      (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 1 (ModuleCat.of ℤ ℤ)).hom ≫
        ordinaryCellularCircleChainModelXOneIsoInt.inv := by
  simp [reducedCellularToOrdinaryChainMap]

/-- The reduced model is a retract of the ordinary cellular model at the chain
level: include the degree-`1` generator and then collapse degree `0`, and the
reduced complex is unchanged. -/
theorem reducedCellularToOrdinary_comp_ordinaryCellularToReduced :
    reducedCellularToOrdinaryChainMap ≫ ordinaryCellularToReducedChainMap =
      𝟙 reducedCellularCircleChainModel := by
  apply HomologicalComplex.from_single_hom_ext
  simp [reducedCellularToOrdinaryChainMap_f_one,
    ordinaryCellularToReducedChainMap_f_one]

/-- The other composite need not be the identity on the ordinary two-cell
complex, because the ordinary model has an additional degree-`0` generator.
It is, however, the identity in degree `1`, the degree relevant to the circle
homology computation. -/
theorem ordinaryCellularToReduced_comp_reducedCellularToOrdinary_f_one :
    (ordinaryCellularToReducedChainMap ≫ reducedCellularToOrdinaryChainMap).f 1 =
      𝟙 (ordinaryCellularCircleChainModel.X 1) := by
  simp [ordinaryCellularToReducedChainMap_f_one,
    reducedCellularToOrdinaryChainMap_f_one]

/-- The collapse from the ordinary two-cell cellular circle model to the reduced
degree-`1` model is a quasi-isomorphism in degree `1`.

The proof uses Mathlib's zero-differential short-complex criterion: in degree
`1`, both relevant short complexes have zero differentials, and the middle
component of the collapse map is an isomorphism on the chosen integer
generator. -/
theorem ordinaryCellularToReducedChainMap_quasiIsoAt_one :
    QuasiIsoAt ordinaryCellularToReducedChainMap 1 := by
  rw [quasiIsoAt_iff]
  rw [ShortComplex.quasiIso_iff_isIso_liftCycles _ (by
    simp [ordinaryCellularCircleChainModel_d_eq_zero]) (by
    simp [ordinaryCellularCircleChainModel_d_eq_zero]) (by
    simp)]
  let S₂ :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).obj
      reducedCellularCircleChainModel
  let φ :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 1).map
      ordinaryCellularToReducedChainMap)
  let w : φ.τ₂ ≫ S₂.g = 0 := by
    dsimp [S₂, φ]
    simp
  change IsIso (S₂.liftCycles φ.τ₂ w)
  haveI : IsIso S₂.iCycles := S₂.isIso_iCycles (by
    dsimp [S₂])
  haveI : IsIso (S₂.liftCycles φ.τ₂ w ≫ S₂.iCycles) := by
    rw [ShortComplex.liftCycles_i]
    dsimp [S₂, φ]
    rw [ordinaryCellularToReducedChainMap_f_one]
    infer_instance
  exact IsIso.of_isIso_comp_right (S₂.liftCycles φ.τ₂ w) S₂.iCycles

/-- The finite cellular algebraic part of the circle-H1 computation is closed:
the reduced and ordinary cellular models have H₁ ≅ ℤ, the ordinary model
collapses to the reduced model in degree `1`, and the reduced model is a chain
retract of the ordinary one.  The remaining Phase 5 gap is only the geometric
transport from Mathlib's singular chains on `TopCat.sphere 1` to this cellular
model. -/
structure CellularCircleAlgebraicH1Certificate : Prop where
  reduced_h1_iso_int :
    Nonempty (reducedCellularCircleChainModel.homology 1 ≅ ModuleCat.of ℤ ℤ)
  ordinary_h1_iso_int :
    Nonempty (ordinaryCellularCircleChainModel.homology 1 ≅ ModuleCat.of ℤ ℤ)
  ordinary_h1_iso_reduced_h1 :
    Nonempty
      (ordinaryCellularCircleChainModel.homology 1 ≅
        reducedCellularCircleChainModel.homology 1)
  reduced_is_retract :
    reducedCellularToOrdinaryChainMap ≫ ordinaryCellularToReducedChainMap =
      𝟙 reducedCellularCircleChainModel
  collapse_quasiIsoAt_one :
    QuasiIsoAt ordinaryCellularToReducedChainMap 1

/-- Checked certificate for the finite cellular algebraic part of the
circle-H1 computation. -/
theorem cellularCircleAlgebraicH1Certificate :
    CellularCircleAlgebraicH1Certificate where
  reduced_h1_iso_int :=
    reducedCellularCircleChainModelH1NonemptyIsoInt
  ordinary_h1_iso_int :=
    ordinaryCellularCircleChainModelH1NonemptyIsoInt
  ordinary_h1_iso_reduced_h1 :=
    ordinaryCellularCircleChainModelH1NonemptyIsoReducedCellularH1
  reduced_is_retract :=
    reducedCellularToOrdinary_comp_ordinaryCellularToReduced
  collapse_quasiIsoAt_one :=
    ordinaryCellularToReducedChainMap_quasiIsoAt_one

/-- The imported Mathlib singular chain complex of `TopCat.sphere 1` with
integer coefficients.  This is the exact chain-level object whose degree-`1`
homology is the final strict T8 target. -/
abbrev sphereOneSingularIntChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)

/-- The degree-`1` singular chain selecting the once-around fundamental
singular 1-simplex of `TopCat.sphere 1`.  It is the coproduct summand inclusion
corresponding to `fundamentalSphereOneSingularOneSimplex`. -/
noncomputable def fundamentalSphereOneSingularOneChain :
    ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.X 1 :=
  Sigma.ι
    (fun _ : (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 1)) =>
      ModuleCat.of ℤ ℤ)
    CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex

/-- The fundamental singular 1-chain has zero boundary.  This is the
chain-level form of the equal-faces theorem for the once-around singular
1-simplex. -/
theorem fundamentalSphereOneSingularOneChain_boundary_zero :
    fundamentalSphereOneSingularOneChain ≫ sphereOneSingularIntChainComplex.d 1 0 = 0 := by
  dsimp [fundamentalSphereOneSingularOneChain, sphereOneSingularIntChainComplex,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex,
    sigmaConst]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  dsimp [AlgebraicTopology.AlternatingFaceMapComplex.objD]
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_zsmul, one_zsmul, Preadditive.comp_add, Preadditive.comp_neg]
  simp only [CategoryTheory.SimplicialObject.δ]
  dsimp [sigmaConst]
  simp only [Sigma.ι_comp_map', Category.id_comp]
  change Sigma.ι (fun x => ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
          CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex) +
      -Sigma.ι (fun x => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
            CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex) =
    0
  rw [CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex_faces_eq]
  simp

/-- Mathlib's homology infrastructure supplies the degree-`1` homology object
for the imported singular chain complex. -/
theorem sphereOneSingularIntChainComplexHasHomologyOne :
    sphereOneSingularIntChainComplex.HasHomology 1 :=
  inferInstance

/-- The final strict T8 singular-homology target is definitionally the degree-`1`
homology of the imported singular chain complex. -/
theorem singularHomologyFunctorSphereOneInt_eq_homologyOne :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) =
        sphereOneSingularIntChainComplex.homology 1 :=
  rfl

/-- Isomorphism form of `singularHomologyFunctorSphereOneInt_eq_homologyOne`. -/
def singularHomologyFunctorSphereOneIntIsoHomologyOne :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) ≅
        sphereOneSingularIntChainComplex.homology 1 :=
  Iso.refl _

/-- A degree-`1` quasi-isomorphism from Mathlib's singular chains on
`TopCat.sphere 1` to the ordinary cellular circle model computes the exact
`singularHomologyFunctor` target as `ℤ`.

This is not the missing geometric theorem itself; it isolates it as the single
remaining chain-level bridge `QuasiIsoAt f 1`. -/
def singularHomologyFunctorSphereOneIntIsoOfQuasiIsoAtOrdinaryCellular
    (f : sphereOneSingularIntChainComplex ⟶ ordinaryCellularCircleChainModel)
    [sphereOneSingularIntChainComplex.HasHomology 1] [QuasiIsoAt f 1] :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) ≅ ModuleCat.of ℤ ℤ :=
  isoOfQuasiIsoAt f 1 ≪≫ ordinaryCellularCircleChainModelH1IsoInt

/-- Proposition-facing form of
`singularHomologyFunctorSphereOneIntIsoOfQuasiIsoAtOrdinaryCellular`. -/
theorem singularHomologyFunctorSphereOneIntNonemptyIsoOfQuasiIsoAtOrdinaryCellular
    (f : sphereOneSingularIntChainComplex ⟶ ordinaryCellularCircleChainModel)
    [sphereOneSingularIntChainComplex.HasHomology 1] [QuasiIsoAt f 1] :
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) ≅ ModuleCat.of ℤ ℤ) :=
  ⟨singularHomologyFunctorSphereOneIntIsoOfQuasiIsoAtOrdinaryCellular f⟩

/-- The same conditional bridge stated in the exact proposition shape used by
`MathlibCohomologyBridge`.  The bridge file stays untouched until the
chain-level quasi-isomorphism is proved unconditionally. -/
theorem circleH1ZIsoIntOfQuasiIsoAtOrdinaryCellular
    (f : sphereOneSingularIntChainComplex ⟶ ordinaryCellularCircleChainModel)
    [sphereOneSingularIntChainComplex.HasHomology 1] [QuasiIsoAt f 1] :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  singularHomologyFunctorSphereOneIntNonemptyIsoOfQuasiIsoAtOrdinaryCellular f

/-- A degree-local chain homotopy equivalence between Mathlib's singular chains
on `TopCat.sphere 1` and the ordinary cellular circle model computes the exact
singular homology target as `ℤ`.  This is weaker in hypotheses than the global
quasi-isomorphism route: it only requires degree-`1` homology for the singular
chain complex. -/
def singularHomologyFunctorSphereOneIntIsoOfHomotopyEquivOrdinaryCellularAtOne
    (e : HomotopyEquiv sphereOneSingularIntChainComplex ordinaryCellularCircleChainModel)
    [sphereOneSingularIntChainComplex.HasHomology 1] :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) ≅ ModuleCat.of ℤ ℤ :=
  e.toHomologyIso 1 ≪≫ ordinaryCellularCircleChainModelH1IsoInt

/-- The degree-local homotopy-equivalence bridge stated in the exact proposition
shape used by `MathlibCohomologyBridge`. -/
theorem circleH1ZIsoIntOfHomotopyEquivOrdinaryCellularAtOne
    (e : HomotopyEquiv sphereOneSingularIntChainComplex ordinaryCellularCircleChainModel)
    [sphereOneSingularIntChainComplex.HasHomology 1] :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  ⟨singularHomologyFunctorSphereOneIntIsoOfHomotopyEquivOrdinaryCellularAtOne e⟩

/-- Proposition-facing closure target: it is enough to produce a chain homotopy
equivalence between Mathlib's singular chains on `TopCat.sphere 1` and the
ordinary cellular circle model. -/
theorem circleH1ZIsoIntOfNonemptyHomotopyEquivOrdinaryCellularAtOne
    (h : Nonempty
      (HomotopyEquiv sphereOneSingularIntChainComplex ordinaryCellularCircleChainModel))
    [sphereOneSingularIntChainComplex.HasHomology 1] :
    MathlibCohomologyBridge.circleH1ZIsoInt := by
  rcases h with ⟨e⟩
  exact circleH1ZIsoIntOfHomotopyEquivOrdinaryCellularAtOne e

/-- The remaining geometric chain-level bridge for the strict T8 circle-H1
closure: Mathlib's singular chain complex for `TopCat.sphere 1` is chain
homotopy equivalent to the ordinary two-cell cellular circle model. -/
def circleH1GeometricBridge : Prop :=
  Nonempty
    (HomotopyEquiv sphereOneSingularIntChainComplex ordinaryCellularCircleChainModel)

/-- The geometric bridge immediately computes the exact imported Mathlib
singular-H1 object as `ℤ`. -/
theorem singularHomologyFunctorSphereOneIntNonemptyIsoOfGeometricBridge
    (h : circleH1GeometricBridge) :
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) ≅ ModuleCat.of ℤ ℤ) := by
  rcases h with ⟨e⟩
  exact ⟨singularHomologyFunctorSphereOneIntIsoOfHomotopyEquivOrdinaryCellularAtOne e⟩

/-- The geometric bridge immediately closes the exact proposition used by
`MathlibCohomologyBridge`. -/
theorem circleH1ZIsoIntOfGeometricBridge
    (h : circleH1GeometricBridge) :
    MathlibCohomologyBridge.circleH1ZIsoInt := by
  rcases h with ⟨e⟩
  exact circleH1ZIsoIntOfHomotopyEquivOrdinaryCellularAtOne e

/-- The geometric bridge fills the Mathlib computation certificate used by the
strict T8 handoff. -/
theorem circleH1MathlibComputationOfGeometricBridge
    (h : circleH1GeometricBridge) :
    MathlibCohomologyBridge.CircleH1MathlibComputation :=
  MathlibCohomologyBridge.circleH1MathlibComputation_of_iso_int
    (circleH1ZIsoIntOfGeometricBridge h)

/-- The geometric bridge also builds the Mathlib circle-linking backend object. -/
theorem mathlibCircleLinkingBackendOfGeometricBridge
    (h : circleH1GeometricBridge) :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (circleH1ZIsoIntOfGeometricBridge h)

/-- A chain homotopy equivalence between Mathlib's singular chains on
`TopCat.sphere 1` and the ordinary cellular circle model is enough to compute
the exact singular homology target as `ℤ`. -/
def singularHomologyFunctorSphereOneIntIsoOfHomotopyEquivOrdinaryCellular
    (e : HomotopyEquiv sphereOneSingularIntChainComplex ordinaryCellularCircleChainModel)
    [∀ i, sphereOneSingularIntChainComplex.HasHomology i] :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere 1)) ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyFunctorSphereOneIntIsoOfQuasiIsoAtOrdinaryCellular e.hom

/-- The same homotopy-equivalence bridge stated in the exact proposition shape
used by `MathlibCohomologyBridge`. -/
theorem circleH1ZIsoIntOfHomotopyEquivOrdinaryCellular
    (e : HomotopyEquiv sphereOneSingularIntChainComplex ordinaryCellularCircleChainModel)
    [∀ i, sphereOneSingularIntChainComplex.HasHomology i] :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoIntOfQuasiIsoAtOrdinaryCellular e.hom

end

end CircleH1Computation
end Foundation
end IndisputableMonolith
