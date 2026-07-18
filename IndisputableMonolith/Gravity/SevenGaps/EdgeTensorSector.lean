import IndisputableMonolith.Gravity.TensorShearSector

/-!
# Seven-Gaps Lane 3: the edge (tensor) sector beyond the conformal ansatz

The vertex-conformal ansatz assigns one scalar per vertex and induces the
log-strain `(ξ u + ξ v) / 2` on the edge `{u, v}`
(`TensorShearSector.conformalEdgeLogStrain`).  This file measures, on the
actual `5 × 5 × 5` periodic Freudenthal 3-torus, how small that conformal
slice is inside the full edge-perturbation space, and exhibits the shear
complement concretely with an explicit localized witness.

## Honest status header

* THEOREM (everything below is fully proved: zero `sorry`, zero `admit`, no
  new axioms, no hypothesis taken as a silent assumption; no theorem in this
  file carries an undischarged hypothesis parameter):
  - Linearity: `conformalStrainLinearMap` packages the conformal ansatz as an
    `ℝ`-linear map `VertexPotential K →ₗ[ℝ] EdgePerturbation K` agreeing
    pointwise with `conformalEdgeLogStrain`
    (`conformalStrainLinearMap_apply`); membership in its range is exactly
    `IsConformalEdgePerturbation`
    (`isConformalEdgePerturbation_iff_mem_range`).
  - Rank bound on any finite 3D Regge triangulation:
    `conformalRange_finrank_le_nV` (conformal image has finrank at most
    `K.nV`), via `finrank_vertexPotential`, `finrank_edgePerturbation`, and
    Mathlib's `LinearMap.finrank_range_le`.
  - Concrete counts on the `N = 5` torus, computed from the definitions and
    not assumed: `periodicTorus5_nV_eq : PeriodicTorus5.K.nV = 125` and
    `periodicTorus5_nE_eq : PeriodicTorus5.K.nE = 875`.  Hence the dimension
    gap `periodicTorus5_conformalRange_finrank_lt_finrank_edgeSpace`
    (conformal rank ≤ 125 < 875 = edge-space dimension), the proper-subspace
    facts `periodicTorus5_conformalRange_ne_top` and
    `periodicTorus5_exists_not_mem_conformalRange`, and the existence of a
    non-conformal edge perturbation `periodicTorus5_exists_nonconformal`.
  - Explicit shear witness: `rectangleShearFace5` puts strain `+1` on the two
    x-edges and `-1` on the two y-edges of the unit coordinate square of the
    torus with corners `(0,0,0), (1,0,0), (1,1,0), (0,1,0)`.  It is not
    vertex-conformal, in typed and in encoded edge coordinates
    (`rectangleShearFace5_not_conformal_typed`,
    `rectangleShearFace5Encoded_not_conformal`).  A second witness, the
    uniform x-strain `xUniformStrain5`, is proved non-conformal by direct
    reuse of the repo's rectangle obstruction
    `nontrivial_rectangle_shear_not_vertexConformal` with `h = 1 ≠ 0 = v`
    (`xUniformStrain5_not_conformal_typed`,
    `xUniformStrain5Encoded_not_conformal`).
  - Orthogonal complement made concrete: `rectangleShearFace5` is orthogonal
    to the entire conformal slice with respect to
    `periodicEdgeInnerProduct5` (`rectangleShearFace5_inner_conformal_eq_zero`)
    and has self inner product `4`
    (`rectangleShearFace5_inner_self_eq_four`), so it is a nonzero vector of
    the orthogonal complement of the conformal subspace
    (`rectangleShearFace5_nonzero_in_orthogonal_complement`).  The uniform
    x-strain pairs to `2` against it
    (`rectangleShearFace5_inner_xUniformStrain5`), so `xUniformStrain5` has a
    nonzero orthogonal projection onto that complement
    (`xUniformStrain5_nonzero_orthogonal_component`).
* MODEL: the endpoint-average log-strain convention and the unit-weight edge
  inner product `periodicEdgeInnerProduct5` are the modeling choices
  inherited from `TensorShearSector`; nothing here depends on a choice of
  edge lengths or weights.
* OPEN: the full conformal ⊕ longitudinal-gauge ⊕ TT orthogonal decomposition
  of the 875-dimensional edge space (the projector data of
  `TensorShearSector.PeriodicTTProjectorData5`) and the TT polarization count
  remain open.  This file proves the conformal slice is a proper subspace and
  exhibits a nonzero vector of its orthogonal complement; it does not build
  the full splitting.

## `decide` usage

`decide` is used only for finite `Fin`-literal facts, never for a
real-number statement: the four face-edge endpoint computations
(`faceEdgeAB_endpoints`, `faceEdgeDC_endpoints`, `faceEdgeBC_endpoints`,
`faceEdgeAD_endpoints`), pairwise distinctness of the four face edges (inside
the `rectangleShearFace5_apply_*` value lemmas), the displacement facts
inside `xUniformStrain5_apply_*`, and the three `Finset` non-membership facts
(`faceEdgeAB_not_mem_rest`, `faceEdgeDC_not_mem_rest`,
`faceEdgeBC_not_mem_rest`) used to expand the four-term inner-product sum.
The pre-existing `PeriodicTorus5` itself uses `by decide` for `2 < 5` at its
definition site in `TensorShearSector`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace EdgeTensorSector

open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.PeriodicFreudenthalTorus
open TensorShearSector

set_option maxRecDepth 65536

noncomputable section

/-! ## 1. The conformal ansatz as a linear map -/

/-- The vertex-conformal log-strain map, packaged as an `ℝ`-linear map from
vertex potentials to edge perturbations. -/
def conformalStrainLinearMap (K : Triangulation3D) :
    VertexPotential K →ₗ[ℝ] EdgePerturbation K where
  toFun ξ := conformalEdgeLogStrain K ξ
  map_add' ξ η := by
    funext e
    simp only [conformalEdgeLogStrain, Pi.add_apply]
    ring
  map_smul' a ξ := by
    funext e
    simp only [conformalEdgeLogStrain, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] theorem conformalStrainLinearMap_apply
    (K : Triangulation3D) (ξ : VertexPotential K) :
    conformalStrainLinearMap K ξ = conformalEdgeLogStrain K ξ := rfl

/-- The conformal subspace predicate of `TensorShearSector` is exactly
membership in the range of the linear map. -/
theorem isConformalEdgePerturbation_iff_mem_range
    (K : Triangulation3D) (ε : EdgePerturbation K) :
    IsConformalEdgePerturbation K ε ↔
      ε ∈ LinearMap.range (conformalStrainLinearMap K) := by
  constructor
  · rintro ⟨ξ, hξ⟩
    exact LinearMap.mem_range.mpr ⟨ξ, hξ.symm⟩
  · intro hmem
    obtain ⟨ξ, hξ⟩ := LinearMap.mem_range.mp hmem
    exact ⟨ξ, hξ.symm⟩

/-! ## 2. Rank bound on an arbitrary finite triangulation -/

theorem finrank_vertexPotential (K : Triangulation3D) :
    Module.finrank ℝ (VertexPotential K) = K.nV := by
  show Module.finrank ℝ (Fin K.nV → ℝ) = K.nV
  simp [Module.finrank_fintype_fun_eq_card]

theorem finrank_edgePerturbation (K : Triangulation3D) :
    Module.finrank ℝ (EdgePerturbation K) = K.nE := by
  show Module.finrank ℝ (Fin K.nE → ℝ) = K.nE
  simp [Module.finrank_fintype_fun_eq_card]

/-- The conformal image inside the edge-perturbation space has dimension at
most the number of vertices. -/
theorem conformalRange_finrank_le_nV (K : Triangulation3D) :
    Module.finrank ℝ (LinearMap.range (conformalStrainLinearMap K)) ≤ K.nV := by
  have h := LinearMap.finrank_range_le (conformalStrainLinearMap K)
  exact h.trans (finrank_vertexPotential K).le

/-! ## 3. Concrete counts and the dimension gap on the `N = 5` torus -/

/-- The typed periodic edges are exactly base-vertex × displacement pairs. -/
def periodicEdge5EquivProd : PeriodicEdge5 ≃ PeriodicVertex5 × Fin 7 where
  toFun e := (e.base, e.disp)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Computed from the definitions: the `5 × 5 × 5` torus has 125 vertices. -/
theorem periodicTorus5_nV_eq : PeriodicTorus5.K.nV = 125 := by
  show Fintype.card PeriodicVertex5 = 125
  simp [PeriodicVertex5, Vertex]

/-- Computed from the definitions: the `5 × 5 × 5` torus has
`125 * 7 = 875` positive-displacement edges.  The proof routes through the
canonical edge equivalence `PeriodicTorus5.edgeEquiv`, avoiding any deep
unfolding of the encoded torus. -/
theorem periodicTorus5_nE_eq : PeriodicTorus5.K.nE = 875 := by
  have h : Fintype.card (Fin PeriodicTorus5.K.nE) = Fintype.card PeriodicEdge5 :=
    Fintype.card_congr PeriodicTorus5.edgeEquiv
  rw [Fintype.card_fin, Fintype.card_congr periodicEdge5EquivProd] at h
  simpa [PeriodicVertex5, Vertex] using h

theorem finrank_encodedEdgePerturbation5 :
    Module.finrank ℝ EncodedEdgePerturbation5 = 875 := by
  have h : Module.finrank ℝ EncodedEdgePerturbation5 = PeriodicTorus5.K.nE :=
    finrank_edgePerturbation PeriodicTorus5.K
  exact h.trans periodicTorus5_nE_eq

theorem periodicTorus5_conformalRange_finrank_le :
    Module.finrank ℝ
      (LinearMap.range (conformalStrainLinearMap PeriodicTorus5.K)) ≤ 125 := by
  have h := conformalRange_finrank_le_nV PeriodicTorus5.K
  exact h.trans periodicTorus5_nV_eq.le

/-- Dimension gap: the conformal slice (rank ≤ 125) is strictly smaller than
the 875-dimensional edge-perturbation space of the `N = 5` torus. -/
theorem periodicTorus5_conformalRange_finrank_lt_finrank_edgeSpace :
    Module.finrank ℝ
        (LinearMap.range (conformalStrainLinearMap PeriodicTorus5.K)) <
      Module.finrank ℝ EncodedEdgePerturbation5 := by
  have h1 := periodicTorus5_conformalRange_finrank_le
  have h2 := finrank_encodedEdgePerturbation5
  omega

/-- The conformal image is a proper subspace of the edge space. -/
theorem periodicTorus5_conformalRange_ne_top :
    LinearMap.range (conformalStrainLinearMap PeriodicTorus5.K) ≠ ⊤ := by
  intro htop
  have hlt := periodicTorus5_conformalRange_finrank_lt_finrank_edgeSpace
  rw [htop, finrank_top] at hlt
  exact lt_irrefl _ hlt

/-- Some edge perturbation of the `N = 5` torus lies outside the conformal
image. -/
theorem periodicTorus5_exists_not_mem_conformalRange :
    ∃ ε : EncodedEdgePerturbation5,
      ε ∉ LinearMap.range (conformalStrainLinearMap PeriodicTorus5.K) := by
  by_contra h
  apply periodicTorus5_conformalRange_ne_top
  rw [Submodule.eq_top_iff']
  intro ε
  by_contra hε
  exact h ⟨ε, hε⟩

/-- Existence form in the language of `IsConformalEdgePerturbation`. -/
theorem periodicTorus5_exists_nonconformal :
    ∃ ε : EncodedEdgePerturbation5,
      ¬ IsConformalEdgePerturbation PeriodicTorus5.K ε := by
  obtain ⟨ε, hε⟩ := periodicTorus5_exists_not_mem_conformalRange
  exact ⟨ε, fun hc =>
    hε ((isConformalEdgePerturbation_iff_mem_range PeriodicTorus5.K ε).mp hc)⟩

/-! ## Bridges between encoded and typed conformal descriptions -/

/-- Typed endpoint form of a conformal perturbation: some vertex potential
`φ` on typed torus vertices realizes it by endpoint averaging. -/
theorem periodicConformalLogSubspace5_endpoint_form
    (c : PeriodicEdgePerturbation5)
    (hc : PeriodicConformalLogSubspace5 c) :
    ∃ φ : PeriodicVertex5 → ℝ,
      ∀ e : PeriodicEdge5, c e = (φ e.endpoints.1 + φ e.endpoints.2) / 2 := by
  obtain ⟨ξ, rfl⟩ := hc
  refine ⟨fun v => ξ (periodicVertexEquiv5.symm v), fun e => ?_⟩
  unfold encodedToPeriodicEdgePerturbation5 conformalEdgeLogStrain
  rw [periodicTorus5_edgeVerts_symm_eq_endpoints]

/-- The typed conformal slice corresponds exactly to the encoded conformal
predicate across the canonical edge equivalence. -/
theorem periodicConformalLogSubspace5_iff_encodedConformal
    (c : PeriodicEdgePerturbation5) :
    PeriodicConformalLogSubspace5 c ↔
      IsConformalEdgePerturbation PeriodicTorus5.K
        (periodicToEncodedEdgePerturbation5 c) := by
  constructor
  · rintro ⟨ξ, rfl⟩
    refine ⟨ξ, ?_⟩
    funext i
    simp [periodicToEncodedEdgePerturbation5, encodedToPeriodicEdgePerturbation5]
  · rintro ⟨ξ, hξ⟩
    refine ⟨ξ, ?_⟩
    funext e
    have h := congrFun hξ (PeriodicTorus5.edgeEquiv.symm e)
    simpa [periodicToEncodedEdgePerturbation5,
      encodedToPeriodicEdgePerturbation5] using h

/-! ## 4. Explicit shear witness on one coordinate square of the torus -/

/-- Corner `(0,0,0)` of the witness square. -/
def faceVertexA : PeriodicVertex5 := (0, 0, 0)

/-- Corner `(1,0,0)` of the witness square. -/
def faceVertexB : PeriodicVertex5 := (1, 0, 0)

/-- Corner `(1,1,0)` of the witness square. -/
def faceVertexC : PeriodicVertex5 := (1, 1, 0)

/-- Corner `(0,1,0)` of the witness square. -/
def faceVertexD : PeriodicVertex5 := (0, 1, 0)

/-- Bottom x-edge `A → B` (displacement class 0 = `+x`). -/
def faceEdgeAB : PeriodicEdge5 := { base := faceVertexA, disp := 0 }

/-- Top x-edge `D → C`. -/
def faceEdgeDC : PeriodicEdge5 := { base := faceVertexD, disp := 0 }

/-- Right y-edge `B → C` (displacement class 1 = `+y`). -/
def faceEdgeBC : PeriodicEdge5 := { base := faceVertexB, disp := 1 }

/-- Left y-edge `A → D`. -/
def faceEdgeAD : PeriodicEdge5 := { base := faceVertexA, disp := 1 }

theorem faceEdgeAB_endpoints :
    faceEdgeAB.endpoints = (faceVertexA, faceVertexB) := by decide

theorem faceEdgeDC_endpoints :
    faceEdgeDC.endpoints = (faceVertexD, faceVertexC) := by decide

theorem faceEdgeBC_endpoints :
    faceEdgeBC.endpoints = (faceVertexB, faceVertexC) := by decide

theorem faceEdgeAD_endpoints :
    faceEdgeAD.endpoints = (faceVertexA, faceVertexD) := by decide

/-- The rectangle/shear pattern embedded on one face of one cube of the
torus: strain `+1` on the two opposite x-edges, `-1` on the two opposite
y-edges, `0` on all other 871 edges. -/
def rectangleShearFace5 : PeriodicEdgePerturbation5 := fun e =>
  if e = faceEdgeAB then 1
  else if e = faceEdgeDC then 1
  else if e = faceEdgeBC then -1
  else if e = faceEdgeAD then -1
  else 0

theorem rectangleShearFace5_apply_AB : rectangleShearFace5 faceEdgeAB = 1 := by
  simp [rectangleShearFace5]

theorem rectangleShearFace5_apply_DC : rectangleShearFace5 faceEdgeDC = 1 := by
  have h : faceEdgeDC ≠ faceEdgeAB := by decide
  simp [rectangleShearFace5, h]

theorem rectangleShearFace5_apply_BC : rectangleShearFace5 faceEdgeBC = -1 := by
  have h1 : faceEdgeBC ≠ faceEdgeAB := by decide
  have h2 : faceEdgeBC ≠ faceEdgeDC := by decide
  simp [rectangleShearFace5, h1, h2]

theorem rectangleShearFace5_apply_AD : rectangleShearFace5 faceEdgeAD = -1 := by
  have h1 : faceEdgeAD ≠ faceEdgeAB := by decide
  have h2 : faceEdgeAD ≠ faceEdgeDC := by decide
  have h3 : faceEdgeAD ≠ faceEdgeBC := by decide
  simp [rectangleShearFace5, h1, h2, h3]

theorem rectangleShearFace5_apply_of_ne (e : PeriodicEdge5)
    (h1 : e ≠ faceEdgeAB) (h2 : e ≠ faceEdgeDC)
    (h3 : e ≠ faceEdgeBC) (h4 : e ≠ faceEdgeAD) :
    rectangleShearFace5 e = 0 := by
  simp [rectangleShearFace5, h1, h2, h3, h4]

theorem faceEdgeAB_not_mem_rest :
    faceEdgeAB ∉ ({faceEdgeDC, faceEdgeBC, faceEdgeAD} : Finset PeriodicEdge5) := by
  decide

theorem faceEdgeDC_not_mem_rest :
    faceEdgeDC ∉ ({faceEdgeBC, faceEdgeAD} : Finset PeriodicEdge5) := by
  decide

theorem faceEdgeBC_not_mem_rest :
    faceEdgeBC ∉ ({faceEdgeAD} : Finset PeriodicEdge5) := by
  decide

/-- The 875-term inner product against the face shear collapses to its four
supported edges. -/
theorem periodicEdgeInnerProduct5_rectangleShearFace5_left
    (η : PeriodicEdgePerturbation5) :
    periodicEdgeInnerProduct5 rectangleShearFace5 η =
      η faceEdgeAB + η faceEdgeDC - η faceEdgeBC - η faceEdgeAD := by
  have hsubset :
      ({faceEdgeAB, faceEdgeDC, faceEdgeBC, faceEdgeAD} :
        Finset PeriodicEdge5) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hzero : ∀ e ∈ (Finset.univ : Finset PeriodicEdge5),
      e ∉ ({faceEdgeAB, faceEdgeDC, faceEdgeBC, faceEdgeAD} :
        Finset PeriodicEdge5) →
      rectangleShearFace5 e * η e = 0 := by
    intro e _ he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rw [rectangleShearFace5_apply_of_ne e he.1 he.2.1 he.2.2.1 he.2.2.2,
      zero_mul]
  have hsum := Finset.sum_subset hsubset hzero
  unfold periodicEdgeInnerProduct5
  rw [← hsum]
  rw [Finset.sum_insert faceEdgeAB_not_mem_rest,
    Finset.sum_insert faceEdgeDC_not_mem_rest,
    Finset.sum_insert faceEdgeBC_not_mem_rest,
    Finset.sum_singleton]
  rw [rectangleShearFace5_apply_AB, rectangleShearFace5_apply_DC,
    rectangleShearFace5_apply_BC, rectangleShearFace5_apply_AD]
  ring

/-! ## 5. The face shear is a nonzero vector of the conformal orthogonal
complement -/

/-- The face shear is orthogonal to the entire conformal slice: around the
square the endpoint averages telescope,
`(φA+φB) + (φD+φC) - (φB+φC) - (φA+φD) = 0`. -/
theorem rectangleShearFace5_inner_conformal_eq_zero
    (c : PeriodicEdgePerturbation5) (hc : PeriodicConformalLogSubspace5 c) :
    periodicEdgeInnerProduct5 rectangleShearFace5 c = 0 := by
  obtain ⟨φ, hφ⟩ := periodicConformalLogSubspace5_endpoint_form c hc
  have hAB : c faceEdgeAB = (φ faceVertexA + φ faceVertexB) / 2 := by
    rw [hφ faceEdgeAB, faceEdgeAB_endpoints]
  have hDC : c faceEdgeDC = (φ faceVertexD + φ faceVertexC) / 2 := by
    rw [hφ faceEdgeDC, faceEdgeDC_endpoints]
  have hBC : c faceEdgeBC = (φ faceVertexB + φ faceVertexC) / 2 := by
    rw [hφ faceEdgeBC, faceEdgeBC_endpoints]
  have hAD : c faceEdgeAD = (φ faceVertexA + φ faceVertexD) / 2 := by
    rw [hφ faceEdgeAD, faceEdgeAD_endpoints]
  rw [periodicEdgeInnerProduct5_rectangleShearFace5_left c,
    hAB, hDC, hBC, hAD]
  ring

theorem rectangleShearFace5_inner_self_eq_four :
    periodicEdgeInnerProduct5 rectangleShearFace5 rectangleShearFace5 = 4 := by
  rw [periodicEdgeInnerProduct5_rectangleShearFace5_left,
    rectangleShearFace5_apply_AB, rectangleShearFace5_apply_DC,
    rectangleShearFace5_apply_BC, rectangleShearFace5_apply_AD]
  norm_num

theorem rectangleShearFace5_ne_zero :
    rectangleShearFace5 ≠ (fun _ => 0) := by
  intro h
  have h1 := congrFun h faceEdgeAB
  rw [rectangleShearFace5_apply_AB] at h1
  exact one_ne_zero h1

/-- Deliverable 5 (orthogonal split, witness form): the face shear is a
nonzero edge perturbation orthogonal to the whole conformal subspace, so the
orthogonal complement of the conformal slice inside the 875-dimensional edge
space contains a concrete nonzero vector. -/
theorem rectangleShearFace5_nonzero_in_orthogonal_complement :
    (∀ c : PeriodicEdgePerturbation5, PeriodicConformalLogSubspace5 c →
      periodicEdgeInnerProduct5 rectangleShearFace5 c = 0) ∧
    rectangleShearFace5 ≠ (fun _ => 0) :=
  ⟨rectangleShearFace5_inner_conformal_eq_zero, rectangleShearFace5_ne_zero⟩

/-- The face shear is not vertex-conformal (typed coordinates): if it were,
orthogonality to itself would force its self inner product `4` to vanish. -/
theorem rectangleShearFace5_not_conformal_typed :
    ¬ PeriodicConformalLogSubspace5 rectangleShearFace5 := by
  intro hc
  have h0 := rectangleShearFace5_inner_conformal_eq_zero rectangleShearFace5 hc
  rw [rectangleShearFace5_inner_self_eq_four] at h0
  norm_num at h0

/-- The face shear pushed to encoded `Fin PeriodicTorus5.K.nE` indices. -/
def rectangleShearFace5Encoded : EncodedEdgePerturbation5 :=
  periodicToEncodedEdgePerturbation5 rectangleShearFace5

/-- Deliverable 4 (encoded form): an explicit edge perturbation of the
`N = 5` periodic Freudenthal torus with no vertex-conformal realization. -/
theorem rectangleShearFace5Encoded_not_conformal :
    ¬ IsConformalEdgePerturbation PeriodicTorus5.K rectangleShearFace5Encoded :=
  fun h =>
    rectangleShearFace5_not_conformal_typed
      ((periodicConformalLogSubspace5_iff_encodedConformal
        rectangleShearFace5).mpr h)

/-- Constructive form of `periodicTorus5_exists_nonconformal`: the witness is
explicit. -/
theorem periodicTorus5_exists_nonconformal_constructive :
    ∃ ε : EncodedEdgePerturbation5,
      ¬ IsConformalEdgePerturbation PeriodicTorus5.K ε :=
  ⟨rectangleShearFace5Encoded, rectangleShearFace5Encoded_not_conformal⟩

/-! ## Second witness: the uniform x-strain, via the rectangle obstruction -/

/-- Unit strain on every `+x` edge, zero on the other six displacement
classes: a globally anisotropic (pure-shear-type) perturbation. -/
def xUniformStrain5 : PeriodicEdgePerturbation5 := fun e =>
  if e.disp = 0 then 1 else 0

theorem xUniformStrain5_apply_AB : xUniformStrain5 faceEdgeAB = 1 := by
  have h : faceEdgeAB.disp = 0 := rfl
  simp [xUniformStrain5, h]

theorem xUniformStrain5_apply_DC : xUniformStrain5 faceEdgeDC = 1 := by
  have h : faceEdgeDC.disp = 0 := rfl
  simp [xUniformStrain5, h]

theorem xUniformStrain5_apply_BC : xUniformStrain5 faceEdgeBC = 0 := by
  have h : faceEdgeBC.disp ≠ 0 := by decide
  simp [xUniformStrain5, h]

theorem xUniformStrain5_apply_AD : xUniformStrain5 faceEdgeAD = 0 := by
  have h : faceEdgeAD.disp ≠ 0 := by decide
  simp [xUniformStrain5, h]

/-- The uniform x-strain is not vertex-conformal: instantiating the four
conformal endpoint averages on the witness square gives `h = 1`, `v = 0`, and
the rectangle obstruction of `TensorShearSector` forbids `h ≠ v`. -/
theorem xUniformStrain5_not_conformal_typed :
    ¬ PeriodicConformalLogSubspace5 xUniformStrain5 := by
  intro hc
  obtain ⟨φ, hφ⟩ := periodicConformalLogSubspace5_endpoint_form xUniformStrain5 hc
  have hAB : xUniformStrain5 faceEdgeAB = (φ faceVertexA + φ faceVertexB) / 2 := by
    rw [hφ faceEdgeAB, faceEdgeAB_endpoints]
  have hDC : xUniformStrain5 faceEdgeDC = (φ faceVertexD + φ faceVertexC) / 2 := by
    rw [hφ faceEdgeDC, faceEdgeDC_endpoints]
  have hBC : xUniformStrain5 faceEdgeBC = (φ faceVertexB + φ faceVertexC) / 2 := by
    rw [hφ faceEdgeBC, faceEdgeBC_endpoints]
  have hAD : xUniformStrain5 faceEdgeAD = (φ faceVertexA + φ faceVertexD) / 2 := by
    rw [hφ faceEdgeAD, faceEdgeAD_endpoints]
  rw [xUniformStrain5_apply_AB] at hAB
  rw [xUniformStrain5_apply_DC] at hDC
  rw [xUniformStrain5_apply_BC] at hBC
  rw [xUniformStrain5_apply_AD] at hAD
  refine nontrivial_rectangle_shear_not_vertexConformal 1 0 one_ne_zero
    ⟨φ faceVertexA, φ faceVertexB, φ faceVertexC, φ faceVertexD,
      ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- Encoded form of the uniform x-strain non-conformality. -/
theorem xUniformStrain5Encoded_not_conformal :
    ¬ IsConformalEdgePerturbation PeriodicTorus5.K
        (periodicToEncodedEdgePerturbation5 xUniformStrain5) :=
  fun h =>
    xUniformStrain5_not_conformal_typed
      ((periodicConformalLogSubspace5_iff_encodedConformal
        xUniformStrain5).mpr h)

/-- The uniform x-strain pairs to `2` against the conformal-orthogonal face
shear. -/
theorem rectangleShearFace5_inner_xUniformStrain5 :
    periodicEdgeInnerProduct5 rectangleShearFace5 xUniformStrain5 = 2 := by
  rw [periodicEdgeInnerProduct5_rectangleShearFace5_left,
    xUniformStrain5_apply_AB, xUniformStrain5_apply_DC,
    xUniformStrain5_apply_BC, xUniformStrain5_apply_AD]
  norm_num

/-- The uniform x-strain has a nonzero orthogonal projection onto the
complement of the conformal subspace: it pairs nontrivially with a vector
(`rectangleShearFace5`) that annihilates the whole conformal slice. -/
theorem xUniformStrain5_nonzero_orthogonal_component :
    ∃ t : PeriodicEdgePerturbation5,
      (∀ c : PeriodicEdgePerturbation5, PeriodicConformalLogSubspace5 c →
        periodicEdgeInnerProduct5 t c = 0) ∧
      periodicEdgeInnerProduct5 t xUniformStrain5 ≠ 0 := by
  refine ⟨rectangleShearFace5,
    rectangleShearFace5_inner_conformal_eq_zero, ?_⟩
  rw [rectangleShearFace5_inner_xUniformStrain5]
  norm_num

/-! ## Capstone -/

/-- Lane 3 capstone: on the `N = 5` periodic Freudenthal torus the conformal
slice has rank at most 125 inside the 875-dimensional edge space, and the gap
is realized by an explicit localized face shear with no vertex-conformal
realization. -/
theorem periodicTorus5_edge_tensor_sector_beyond_conformal :
    Module.finrank ℝ
        (LinearMap.range (conformalStrainLinearMap PeriodicTorus5.K)) ≤ 125 ∧
      Module.finrank ℝ EncodedEdgePerturbation5 = 875 ∧
      ¬ IsConformalEdgePerturbation PeriodicTorus5.K rectangleShearFace5Encoded :=
  ⟨periodicTorus5_conformalRange_finrank_le,
    finrank_encodedEdgePerturbation5,
    rectangleShearFace5Encoded_not_conformal⟩

end

end EdgeTensorSector
end SevenGaps
end Gravity
end IndisputableMonolith
