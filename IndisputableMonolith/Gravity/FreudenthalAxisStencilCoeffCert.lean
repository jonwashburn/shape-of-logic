import IndisputableMonolith.Gravity.PhysicalSixTetCubicDirichletInstance

/-!
# Corrected Freudenthal axis-stencil coefficient certificate

This module mirrors the exact rational audit in
`scripts/freudenthal_explicit_fiber_endpoint_analysis.py`.

It does not use floating-point arithmetic.  The certificate checks the
coefficient of every unordered monomial `xi(u) * xi(v)` in the corrected
`N = 5` mixed explicit-fiber axis-stencil residual.
-/

namespace IndisputableMonolith
namespace Gravity
namespace FreudenthalAxisStencilCoeffCert

open Geometry.PeriodicFreudenthalTorus
open Geometry.FreudenthalCubeTriangulation
open Geometry.ReggeRigorousFoundation
open PhysicalSixTetCubicDirichletInstance

abbrev Vertex5 := Vertex 5 5 5
abbrev PeriodicEdge5 := PeriodicEdge 5 5 5

def addFin5 (i j : Fin 5) : Fin 5 :=
  ⟨(i.1 + j.1) % 5, by omega⟩

def negFin5 (i : Fin 5) : Fin 5 :=
  ⟨(5 - i.1) % 5, by omega⟩

theorem addFin5_zero_left (i : Fin 5) :
    addFin5 0 i = i := by
  ext
  simp [addFin5]

theorem addFin5_neg_self (i : Fin 5) :
    addFin5 (negFin5 i) i = 0 := by
  ext
  simp [addFin5, negFin5]

theorem addFin5_neg_add_self (a i : Fin 5) :
    addFin5 (negFin5 a) (addFin5 a i) = i := by
  ext
  simp [addFin5, negFin5]
  omega

theorem addFin5_self_add_neg (a i : Fin 5) :
    addFin5 a (addFin5 (negFin5 a) i) = i := by
  ext
  simp [addFin5, negFin5]
  omega

def translateVertex5 (a v : Vertex5) : Vertex5 :=
  (addFin5 a.1 v.1, addFin5 a.2.1 v.2.1, addFin5 a.2.2 v.2.2)

def negVertex5 (v : Vertex5) : Vertex5 :=
  (negFin5 v.1, negFin5 v.2.1, negFin5 v.2.2)

def relativeVertex5 (base v : Vertex5) : Vertex5 :=
  translateVertex5 (negVertex5 base) v

def translateEdge5 (a : Vertex5) (edge : PeriodicEdge5) : PeriodicEdge5 :=
  { base := translateVertex5 a edge.base, disp := edge.disp }

theorem translateVertex5_neg_left (a v : Vertex5) :
    translateVertex5 (negVertex5 a) (translateVertex5 a v) = v := by
  rcases a with ⟨ax, ay, az⟩
  rcases v with ⟨x, y, z⟩
  ext <;> simp [translateVertex5, negVertex5, addFin5_neg_add_self]

theorem translateVertex5_neg_right (a v : Vertex5) :
    translateVertex5 a (translateVertex5 (negVertex5 a) v) = v := by
  rcases a with ⟨ax, ay, az⟩
  rcases v with ⟨x, y, z⟩
  ext <;> simp [translateVertex5, negVertex5, addFin5_self_add_neg]

def translateVertex5Equiv (a : Vertex5) : Vertex5 ≃ Vertex5 where
  toFun := translateVertex5 a
  invFun := translateVertex5 (negVertex5 a)
  left_inv := translateVertex5_neg_left a
  right_inv := translateVertex5_neg_right a

def translateEdge5Equiv (a : Vertex5) : PeriodicEdge5 ≃ PeriodicEdge5 where
  toFun := translateEdge5 a
  invFun := translateEdge5 (negVertex5 a)
  left_inv := by
    intro edge
    rcases edge with ⟨base, disp⟩
    simp [translateEdge5, translateVertex5_neg_left]
  right_inv := by
    intro edge
    rcases edge with ⟨base, disp⟩
    simp [translateEdge5, translateVertex5_neg_right]

def subOneMod5 (i : Fin 5) : Fin 5 :=
  ⟨(i.1 + 4) % 5, by omega⟩

def subBit5 (i : Fin 5) (b : Bool) : Fin 5 :=
  if b then subOneMod5 i else i

theorem subBit5_addFin5 (a i : Fin 5) (b : Bool) :
    subBit5 (addFin5 a i) b = addFin5 a (subBit5 i b) := by
  cases b <;> ext <;> simp [subBit5, subOneMod5, addFin5]
  omega

def matchingBaseCell5 (a : Fin 8) (target : Vertex5) : Vertex5 :=
  let b := vertexBits a
  (subBit5 target.1 b.1, subBit5 target.2.1 b.2.1, subBit5 target.2.2 b.2.2)

theorem matchingBaseCell5_spec (a : Fin 8) (target : Vertex5) :
    target = addVertexBits (matchingBaseCell5 a target) a := by
  rcases target with ⟨x, y, z⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases a <;> decide

def selectedCell5 (edge : PeriodicEdge5) (pair : FreudenthalLocalPair) : Vertex5 :=
  matchingBaseCell5 (cubeEdgeBase (localEdgeOf pair.1 pair.2)) edge.base

theorem selectedCell5_eq_freudenthalExplicitFiberPairSelectedCell
    (edge : PeriodicEdge5) (pair : FreudenthalLocalPair) :
    selectedCell5 edge pair =
      freudenthalExplicitFiberPairSelectedCell edge pair := by
  unfold selectedCell5 freudenthalExplicitFiberPairSelectedCell
  exact periodicMatchingBaseCell_unique
    (cubeEdgeBase (localEdgeOf pair.1 pair.2)) edge.base
    (matchingBaseCell5_spec (cubeEdgeBase (localEdgeOf pair.1 pair.2)) edge.base)

theorem matchingBaseCell5_translate (a target : Vertex5) (b : Fin 8) :
    matchingBaseCell5 b (translateVertex5 a target) =
      translateVertex5 a (matchingBaseCell5 b target) := by
  rcases a with ⟨ax, ay, az⟩
  rcases target with ⟨x, y, z⟩
  fin_cases b <;>
    ext <;>
    simp [matchingBaseCell5, translateVertex5, vertexBits, subBit5_addFin5]

theorem selectedCell5_translate (a : Vertex5) (edge : PeriodicEdge5)
    (pair : FreudenthalLocalPair) :
    selectedCell5 (translateEdge5 a edge) pair =
      translateVertex5 a (selectedCell5 edge pair) := by
  simp [selectedCell5, translateEdge5, matchingBaseCell5_translate]

theorem addVertexBits_translate5 (a cell : Vertex5) (b : Fin 8) :
    addVertexBits (translateVertex5 a cell) b =
      translateVertex5 a (addVertexBits cell b) := by
  rcases a with ⟨ax, ay, az⟩
  rcases cell with ⟨x, y, z⟩
  fin_cases b <;>
    ext <;>
    simp [addVertexBits, addBits, translateVertex5, addBit, addFin5, bit, vertexBits]
  all_goals omega

theorem translateEdge5_endpoints (a : Vertex5) (edge : PeriodicEdge5) :
    (translateEdge5 a edge).endpoints =
      (translateVertex5 a edge.endpoints.1, translateVertex5 a edge.endpoints.2) := by
  rcases a with ⟨ax, ay, az⟩
  rcases edge with ⟨base, disp⟩
  rcases base with ⟨x, y, z⟩
  fin_cases disp <;>
    ext <;>
    simp [translateEdge5, PeriodicEdge.endpoints, addBits, dispBits, translateVertex5,
      addBit, addFin5, bit]
  all_goals omega

def sqEdgeRat : Fin 6 → Rat
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 1

def snormRat : Fin 6 → Fin 6 → Rat
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => -1
  | 0, 5 => 2
  | 1, 0 => 0
  | 1, 1 => 2
  | 1, 2 => -2
  | 1, 3 => -4
  | 1, 4 => 4
  | 1, 5 => -2
  | 2, 0 => 0
  | 2, 1 => -3
  | 2, 2 => 2
  | 2, 3 => 6
  | 2, 4 => -3
  | 2, 5 => 0
  | 3, 0 => 0
  | 3, 1 => -2
  | 3, 2 => 2
  | 3, 3 => 2
  | 3, 4 => -2
  | 3, 5 => 0
  | 4, 0 => -2
  | 4, 1 => 4
  | 4, 2 => -2
  | 4, 3 => -4
  | 4, 4 => 2
  | 4, 5 => 0
  | 5, 0 => 2
  | 5, 1 => -1
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0

theorem sqEdgeRat_cast_eq_freudenthalTetSqEdges (k : Fin 6) :
    (sqEdgeRat k : ℝ) =
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k := by
  fin_cases k <;> norm_num [sqEdgeRat,
    Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges]

theorem snormRat_cast_eq_freudenthalSchlaefliTable (e k : Fin 6) :
    (snormRat e k : ℝ) =
      FreudenthalLengthChainEndpointCert.freudenthalSchlaefliPolySummandNormTable e k := by
  fin_cases e <;> fin_cases k <;> norm_num [snormRat,
    FreudenthalLengthChainEndpointCert.freudenthalSchlaefliPolySummandNormTable]

theorem freudenthalLocalPairDisp_eq_of_mem
    (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (hpair : pair ∈ freudenthalLocalPairDispFiber edge.disp) :
    freudenthalLocalPairDisp pair = edge.disp := by
  have h := hpair
  rw [freudenthalLocalPairDispFiber_eq_filter edge.disp] at h
  exact (Finset.mem_filter.mp h).2

theorem periodicDispSqEdge_eq_freudenthalTetSqEdges_of_mem
    (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (hpair : pair ∈ freudenthalLocalPairDispFiber edge.disp) :
    periodicDispSqEdge edge.disp =
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges pair.2 := by
  have hdisp := freudenthalLocalPairDisp_eq_of_mem edge pair hpair
  have hsq :=
    freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf
      (Nx := 5) (Ny := 5) (Nz := 5)
      (selectedCell5 edge pair) pair.1 pair.2
  rw [← hdisp]
  simpa [freudenthalLocalPairDisp, Geometry.FreudenthalCubeTriangulation.freudenthalTet]
    using hsq.symm

def sameUnordered (a b u v : Vertex5) : Bool :=
  decide ((a = u ∧ b = v) ∨ (a = v ∧ b = u))

theorem sameUnordered_translate (a x y u v : Vertex5) :
    sameUnordered (translateVertex5 a x) (translateVertex5 a y)
      (translateVertex5 a u) (translateVertex5 a v) =
    sameUnordered x y u v := by
  have hinj : Function.Injective (translateVertex5 a) :=
    (translateVertex5Equiv a).injective
  simp [sameUnordered, hinj.eq_iff]

def scaledPairLocalVertexCoeff
    (edge : PeriodicEdge5) (pair : FreudenthalLocalPair) (k : Fin 6)
    (endpoint : Vertex5) (u v : Vertex5) : Rat :=
  let cell := selectedCell5 edge pair
  let ev := edgeVertices k
  let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
  let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
  let c := snormRat pair.2 k * sqEdgeRat k / 4
  (if sameUnordered endpoint v0 u v then -c / 2 else 0) +
    (if sameUnordered endpoint v1 u v then -c / 2 else 0)

theorem scaledPairLocalVertexCoeff_translate
    (a : Vertex5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair) (k : Fin 6)
    (endpoint u v : Vertex5) :
    scaledPairLocalVertexCoeff (translateEdge5 a edge) pair k
        (translateVertex5 a endpoint) (translateVertex5 a u) (translateVertex5 a v) =
      scaledPairLocalVertexCoeff edge pair k endpoint u v := by
  simp [scaledPairLocalVertexCoeff, selectedCell5_translate, addVertexBits_translate5,
    sameUnordered_translate]

def mixedAxisEdgeLhsCoeff (edge : PeriodicEdge5) (u v : Vertex5) : Rat :=
  let ep := edge.endpoints
  ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
    ∑ k : Fin 6,
      (scaledPairLocalVertexCoeff edge pair k ep.1 u v +
        scaledPairLocalVertexCoeff edge pair k ep.2 u v)

theorem mixedAxisEdgeLhsCoeff_translate
    (a : Vertex5) (edge : PeriodicEdge5) (u v : Vertex5) :
    mixedAxisEdgeLhsCoeff (translateEdge5 a edge)
        (translateVertex5 a u) (translateVertex5 a v) =
      mixedAxisEdgeLhsCoeff edge u v := by
  dsimp only [mixedAxisEdgeLhsCoeff]
  rw [show (translateEdge5 a edge).disp = edge.disp by rfl]
  rw [translateEdge5_endpoints]
  apply Finset.sum_congr rfl
  intro pair hpair
  apply Finset.sum_congr rfl
  intro k hk
  simp only [scaledPairLocalVertexCoeff_translate]

def mixedAxisLhsCoeff (u v : Vertex5) : Rat :=
  ∑ edge : PeriodicEdge5, mixedAxisEdgeLhsCoeff edge u v

theorem mixedAxisLhsCoeff_eq_sum_edge (u v : Vertex5) :
    mixedAxisLhsCoeff u v = ∑ edge : PeriodicEdge5, mixedAxisEdgeLhsCoeff edge u v := rfl

def axisStencilResidualCoeff (u v : Vertex5) : Rat :=
  ∑ base : Vertex5, ∑ d : Fin 3,
    let edge : PeriodicEdge5 := { base := base, disp := periodicAxisDisp d }
    let ep := edge.endpoints
    (if ep.1 = u && ep.1 = v then -2 else 0) +
      (if ep.2 = u && ep.2 = v then -2 else 0) +
        (if sameUnordered ep.1 ep.2 u v then 4 else 0)

def mixedAxisResidualCoeff (u v : Vertex5) : Rat :=
  mixedAxisLhsCoeff u v + axisStencilResidualCoeff u v

def originVertex : Vertex5 :=
  (0, 0, 0)

theorem translateVertex5_origin_left (v : Vertex5) :
    translateVertex5 originVertex v = v := by
  rcases v with ⟨x, y, z⟩
  ext <;> simp [translateVertex5, originVertex, addFin5_zero_left]

theorem relativeVertex5_origin_eq_self (v : Vertex5) :
    relativeVertex5 originVertex v = v := by
  rw [relativeVertex5]
  rw [show negVertex5 originVertex = originVertex by
    ext <;> simp [negVertex5, negFin5, originVertex]]
  exact translateVertex5_origin_left v

theorem relativeVertex5_self_eq_origin (v : Vertex5) :
    relativeVertex5 v v = originVertex := by
  rcases v with ⟨x, y, z⟩
  ext <;> simp [relativeVertex5, translateVertex5, negVertex5, addFin5, negFin5, originVertex]

/-- Full coefficient-vanishing statement for the corrected `N = 5` axis-stencil
residual.  This is the finite certificate still needed before converting the
coefficient audit into `CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5`. -/
def FullResidualCoeffCert : Prop :=
  ∀ u v : Vertex5, mixedAxisResidualCoeff u v = 0

/-- Translation invariance of the mixed explicit-fiber LHS coefficient model.
This is now the only heavy finite reindexing bridge left in the corrected
axis-stencil coefficient certificate. -/
def MixedAxisLhsCoeffTranslationInvariant : Prop :=
  ∀ u v : Vertex5,
    mixedAxisLhsCoeff u v =
      mixedAxisLhsCoeff originVertex (relativeVertex5 u v)

/-- Edge-summand form of the mixed LHS translation bridge.  This is the
remaining local target after factoring `mixedAxisLhsCoeff` as a sum over
`PeriodicEdge5`. -/
def MixedAxisEdgeLhsCoeffTranslationInvariant : Prop :=
  ∀ (a : Vertex5) (edge : PeriodicEdge5) (u v : Vertex5),
    mixedAxisEdgeLhsCoeff (translateEdge5 a edge)
        (translateVertex5 a u) (translateVertex5 a v) =
      mixedAxisEdgeLhsCoeff edge u v

theorem mixedAxisLhsCoeff_translationInvariant_of_edge
    (hedge : MixedAxisEdgeLhsCoeffTranslationInvariant) :
    MixedAxisLhsCoeffTranslationInvariant := by
  intro u v
  let a := negVertex5 u
  have hsum :
      mixedAxisLhsCoeff (translateVertex5 a u) (translateVertex5 a v) =
        mixedAxisLhsCoeff u v := by
    unfold mixedAxisLhsCoeff
    symm
    exact Fintype.sum_equiv (translateEdge5Equiv a)
      (fun edge : PeriodicEdge5 => mixedAxisEdgeLhsCoeff edge u v)
      (fun edge : PeriodicEdge5 =>
        mixedAxisEdgeLhsCoeff edge (translateVertex5 a u) (translateVertex5 a v))
      (fun edge => by
        exact (hedge a edge u v).symm)
  have hu : translateVertex5 a u = originVertex := by
    dsimp [a]
    exact relativeVertex5_self_eq_origin u
  have hv : translateVertex5 a v = relativeVertex5 u v := by
    rfl
  rw [hu, hv] at hsum
  exact hsum.symm

def rowMixedAxisLhsCoeffTranslationInvariant (u : Vertex5) : Bool :=
  decide (∀ v : Vertex5,
    mixedAxisLhsCoeff u v =
      mixedAxisLhsCoeff originVertex (relativeVertex5 u v))

/-- Translation invariance of the corrected three-axis stencil coefficient
model.  This side is small enough to certify directly in Lean. -/
def AxisStencilResidualCoeffTranslationInvariant : Prop :=
  ∀ u v : Vertex5,
    axisStencilResidualCoeff u v =
      axisStencilResidualCoeff originVertex (relativeVertex5 u v)

/-- Translation-invariance bridge for the rational residual coefficient model.
Once proved, the origin-row certificate gives the full 125-by-125 table without
naively compiling every row. -/
def MixedAxisResidualCoeffTranslationInvariant : Prop :=
  ∀ u v : Vertex5,
    mixedAxisResidualCoeff u v =
      mixedAxisResidualCoeff originVertex (relativeVertex5 u v)

def axisStencilResidualCoeffTranslationInvariantCheck : Bool :=
  decide (∀ u v : Vertex5,
    axisStencilResidualCoeff u v =
      axisStencilResidualCoeff originVertex (relativeVertex5 u v))

theorem axisStencilResidualCoeffTranslationInvariantCheck_eq_true :
    axisStencilResidualCoeffTranslationInvariantCheck = true := by
  native_decide

theorem axisStencilResidualCoeff_translationInvariant :
    AxisStencilResidualCoeffTranslationInvariant := by
  change ∀ u v : Vertex5,
    axisStencilResidualCoeff u v =
      axisStencilResidualCoeff originVertex (relativeVertex5 u v)
  exact of_decide_eq_true
    (by
      simpa [axisStencilResidualCoeffTranslationInvariantCheck] using
        axisStencilResidualCoeffTranslationInvariantCheck_eq_true)

theorem mixedAxisResidualCoeff_translationInvariant_of_lhs
    (hlhs : MixedAxisLhsCoeffTranslationInvariant) :
    MixedAxisResidualCoeffTranslationInvariant := by
  intro u v
  unfold mixedAxisResidualCoeff
  rw [hlhs u v, axisStencilResidualCoeff_translationInvariant u v]

/-- Translation-normalized exact rational coefficient audit for the corrected
`N = 5` axis-stencil target.  The companion Python audit checks all unordered
vertex pairs; this Lean theorem checks the 125 origin-offset representatives in
the same rational coefficient model. -/
def originResidualCoeffsZero : Bool :=
  decide (∀ v : Vertex5, mixedAxisResidualCoeff originVertex v = 0)

theorem originResidualCoeffsZero_eq_true :
    originResidualCoeffsZero = true := by
  native_decide

theorem originResidualCoeffCert :
    ∀ v : Vertex5, mixedAxisResidualCoeff originVertex v = 0 := by
  exact of_decide_eq_true originResidualCoeffsZero_eq_true

theorem fullResidualCoeffCert_of_translationInvariant
    (htrans : MixedAxisResidualCoeffTranslationInvariant) :
    FullResidualCoeffCert := by
  intro u v
  rw [htrans u v]
  exact originResidualCoeffCert (relativeVertex5 u v)

theorem fullResidualCoeffCert_of_lhs_translationInvariant
    (hlhs : MixedAxisLhsCoeffTranslationInvariant) :
    FullResidualCoeffCert :=
  fullResidualCoeffCert_of_translationInvariant
    (mixedAxisResidualCoeff_translationInvariant_of_lhs hlhs)

theorem fullResidualCoeffCert_of_edge_lhs_translationInvariant
    (hedge : MixedAxisEdgeLhsCoeffTranslationInvariant) :
    FullResidualCoeffCert :=
  fullResidualCoeffCert_of_lhs_translationInvariant
    (mixedAxisLhsCoeff_translationInvariant_of_edge hedge)

theorem mixedAxisEdgeLhsCoeff_translationInvariant :
    MixedAxisEdgeLhsCoeffTranslationInvariant := by
  intro a edge u v
  exact mixedAxisEdgeLhsCoeff_translate a edge u v

theorem mixedAxisLhsCoeff_translationInvariant :
    MixedAxisLhsCoeffTranslationInvariant :=
  mixedAxisLhsCoeff_translationInvariant_of_edge mixedAxisEdgeLhsCoeff_translationInvariant

theorem fullResidualCoeffCert :
    FullResidualCoeffCert :=
  fullResidualCoeffCert_of_edge_lhs_translationInvariant
    mixedAxisEdgeLhsCoeff_translationInvariant

/-- Canonical `N = 5` encoded periodic Freudenthal torus used by the corrected
axis-stencil certificate. -/
noncomputable abbrev P5 :=
  canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)

abbrev VertexPotential5 :=
  Geometry.ReggeHessian3D.VertexPotential P5.K

noncomputable def potentialAtVertex5 (ξ : VertexPotential5) (v : Vertex5) : ℝ :=
  ξ ((vertexFinEquiv 5 5 5).symm v)

/-- The flat local edge-length derivative at the selected explicit-fiber cell,
rewritten in the same typed vertex coordinates used by the coefficient atoms. -/
theorem freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_selectedCell5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) :
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv
        (by decide) (by decide) (by decide) ξ (selectedCell5 edge pair) pair.1 k =
      let ev := edgeVertices k
      let v0 := addVertexBits (selectedCell5 edge pair) (tetVerts pair.1 ev.1)
      let v1 := addVertexBits (selectedCell5 edge pair) (tetVerts pair.1 ev.2)
      Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) *
        ((potentialAtVertex5 ξ v0 + potentialAtVertex5 ξ v1) / 2) := by
  rw [selectedCell5_eq_freudenthalExplicitFiberPairSelectedCell edge pair]
  unfold freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv potentialAtVertex5
  dsimp
  rw [freudenthalExplicitFiber_canonicalTetVerts_eq
    (by decide) (by decide) (by decide) edge pair (edgeVertices k).1]
  rw [freudenthalExplicitFiber_canonicalTetVerts_eq
    (by decide) (by decide) (by decide) edge pair (edgeVertices k).2]

/-- A total-order key for `N = 5` periodic vertices.  This is used only to
choose a canonical representative of an unordered monomial; the product order
on `Fin 5 × Fin 5 × Fin 5` is partial and would drop incomparable pairs. -/
def vertex5Code (v : Vertex5) : Nat :=
  v.1.val * 25 + v.2.1.val * 5 + v.2.2.val

theorem vertex5Code_injective : Function.Injective vertex5Code := by
  intro a b h
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, by', bz⟩
  ext <;> simp [vertex5Code] at h ⊢ <;> omega

/-- Canonical total-order representative for unordered vertex pairs at `N = 5`. -/
def vertex5CanonLE (u v : Vertex5) : Prop :=
  vertex5Code u ≤ vertex5Code v

instance (u v : Vertex5) : Decidable (vertex5CanonLE u v) :=
  inferInstanceAs (Decidable (vertex5Code u ≤ vertex5Code v))

/-- Unordered coefficient expansion for a diagonal monomial at `N = 5`.
This is the square-term half of the axis-stencil soundness calculation. -/
theorem unorderedDiagonalMonomialExpansionAtN5
    (ξ : VertexPotential5) (a : Vertex5) (c : ℝ) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (if a = u && a = v then c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v else 0)
      else 0) =
      c * potentialAtVertex5 ξ a * potentialAtVertex5 ξ a := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp [vertex5CanonLE]
    · intro v _ hv
      simp [hv.symm]
    · intro hnot
      exact (hnot (Finset.mem_univ a)).elim
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    simp [hu.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ a)).elim

/-- Unordered coefficient expansion for an off-diagonal monomial at `N = 5`.
This is the cross-term half of the axis-stencil soundness calculation. -/
theorem unorderedCrossMonomialExpansionAtN5
    (ξ : VertexPotential5) (a b : Vertex5) (c : ℝ) (hne : a ≠ b) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (if sameUnordered a b u v then
          c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
        else 0)
      else 0) =
      c * potentialAtVertex5 ξ a * potentialAtVertex5 ξ b := by
  classical
  by_cases hab : vertex5CanonLE a b
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp [sameUnordered, hab]
      · intro v _ hv
        by_cases huv : vertex5CanonLE a v
        · by_cases hsu : sameUnordered a b a v
          · have hp : (a = a ∧ b = v) ∨ (a = v ∧ b = a) := by
              simpa [sameUnordered] using hsu
            have hvb : v = b := by
              rcases hp with ⟨_, hbv⟩ | ⟨_, hba⟩
              · exact hbv.symm
              · exact (hne hba.symm).elim
            exact (hv hvb).elim
          · simp [huv, hsu]
        · simp [huv]
      · intro hnot
        exact (hnot (Finset.mem_univ b)).elim
    · intro u _ hu
      apply Finset.sum_eq_zero
      intro v _
      by_cases huv : vertex5CanonLE u v
      · by_cases hsu : sameUnordered a b u v
        · have hp : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
            simpa [sameUnordered] using hsu
          rcases hp with ⟨hau, _⟩ | ⟨_, hbu⟩
          · exact (hu hau.symm).elim
          · subst u
            subst v
            exact (hne (vertex5Code_injective (le_antisymm hab huv))).elim
        · simp [huv, hsu]
      · simp [huv]
    · intro hnot
      exact (hnot (Finset.mem_univ a)).elim
  · have hba : vertex5CanonLE b a := by
      unfold vertex5CanonLE at hab ⊢
      exact Nat.le_of_not_ge hab
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · simp [sameUnordered, hba]
        ring
      · intro v _ hv
        by_cases huv : vertex5CanonLE b v
        · by_cases hsu : sameUnordered a b b v
          · have hp : (a = b ∧ b = v) ∨ (a = v ∧ b = b) := by
              simpa [sameUnordered] using hsu
            have hva : v = a := by
              rcases hp with ⟨hab', _⟩ | ⟨hav, _⟩
              · exact (hne hab').elim
              · exact hav.symm
            exact (hv hva).elim
          · simp [huv, hsu]
        · simp [huv]
      · intro hnot
        exact (hnot (Finset.mem_univ a)).elim
    · intro u _ hu
      apply Finset.sum_eq_zero
      intro v _
      by_cases huv : vertex5CanonLE u v
      · by_cases hsu : sameUnordered a b u v
        · have hp : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
            simpa [sameUnordered] using hsu
          rcases hp with ⟨_, _⟩ | ⟨_, hbu⟩
          · subst u
            subst v
            exact (hne (vertex5Code_injective (le_antisymm huv hba))).elim
          · exact (hu hbu.symm).elim
        · simp [huv, hsu]
      · simp [huv]
    · intro hnot
      exact (hnot (Finset.mem_univ b)).elim

/-- Unified unordered monomial expansion, valid also on the diagonal.  This is
the atom needed by the explicit-fiber LHS, where periodic wraparound can make
many endpoint/local-vertex pairs incomparable in the product order. -/
theorem unorderedSameUnorderedMonomialExpansionAtN5
    (ξ : VertexPotential5) (a b : Vertex5) (c : ℝ) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (if sameUnordered a b u v then
          c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
        else 0)
      else 0) =
      c * potentialAtVertex5 ξ a * potentialAtVertex5 ξ b := by
  classical
  by_cases h : a = b
  · subst b
    have hsame : ∀ u v : Vertex5, sameUnordered a a u v = (a = u && a = v) := by
      intro u v
      by_cases hu : a = u <;> by_cases hv : a = v <;>
        simp [sameUnordered, hu, hv]
    calc
      (∑ u : Vertex5, ∑ v : Vertex5,
        if vertex5CanonLE u v then
          (if sameUnordered a a u v then
            c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
          else 0)
        else 0) =
          (∑ u : Vertex5, ∑ v : Vertex5,
            if vertex5CanonLE u v then
              (if a = u && a = v then
                c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
              else 0)
            else 0) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            refine Finset.sum_congr rfl ?_
            intro v _
            by_cases huv : vertex5CanonLE u v <;> simp [huv, hsame u v]
      _ = c * potentialAtVertex5 ξ a * potentialAtVertex5 ξ a :=
          unorderedDiagonalMonomialExpansionAtN5 ξ a c
  · exact unorderedCrossMonomialExpansionAtN5 ξ a b c h

/-- One endpoint contribution from one explicit-fiber local pair and local edge
slot expands to the two unordered monomials encoded by
`scaledPairLocalVertexCoeff`. -/
theorem scaledPairLocalVertexCoeffExpansionAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (endpoint : Vertex5) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        ((scaledPairLocalVertexCoeff edge pair k endpoint u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
      let cell := selectedCell5 edge pair
      let ev := edgeVertices k
      let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
      let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
      let c : ℝ := ((-(snormRat pair.2 k * sqEdgeRat k / 4) / 2 : Rat) : ℝ)
      c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v0 +
        c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v1 := by
  classical
  let cell := selectedCell5 edge pair
  let ev := edgeVertices k
  let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
  let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
  let cRat : Rat := -(snormRat pair.2 k * sqEdgeRat k / 4) / 2
  let c : ℝ := (cRat : ℝ)
  have h0 := unorderedSameUnorderedMonomialExpansionAtN5 ξ endpoint v0 c
  have h1 := unorderedSameUnorderedMonomialExpansionAtN5 ξ endpoint v1 c
  calc
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        ((scaledPairLocalVertexCoeff edge pair k endpoint u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            (if sameUnordered endpoint v0 u v then
              c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
            else 0)
          else 0) +
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            (if sameUnordered endpoint v1 u v then
              c * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
            else 0)
          else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases huv : vertex5CanonLE u v
          · by_cases h0' : sameUnordered endpoint v0 u v
            · by_cases h1' : sameUnordered endpoint v1 u v
              · have h0raw :
                    sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).1)) u v = true := by
                    simpa [cell, ev, v0] using h0'
                have h1raw :
                    sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).2)) u v = true := by
                    simpa [cell, ev, v1] using h1'
                simp [scaledPairLocalVertexCoeff, cell, ev, v0, v1, c, cRat,
                  huv, h0', h1', h0raw, h1raw]
                try ring_nf
              · have h0raw :
                    sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).1)) u v = true := by
                    simpa [cell, ev, v0] using h0'
                have h1raw :
                    ¬ sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).2)) u v = true := by
                    simpa [cell, ev, v1] using h1'
                simp [scaledPairLocalVertexCoeff, cell, ev, v0, v1, c, cRat,
                  huv, h0', h1', h0raw, h1raw]
                try ring_nf
            · by_cases h1' : sameUnordered endpoint v1 u v
              · have h0raw :
                    ¬ sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).1)) u v = true := by
                    simpa [cell, ev, v0] using h0'
                have h1raw :
                    sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).2)) u v = true := by
                    simpa [cell, ev, v1] using h1'
                simp [scaledPairLocalVertexCoeff, cell, ev, v0, v1, c, cRat,
                  huv, h0', h1', h0raw, h1raw]
                try ring_nf
              · have h0raw :
                    ¬ sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).1)) u v = true := by
                    simpa [cell, ev, v0] using h0'
                have h1raw :
                    ¬ sameUnordered endpoint
                      (addVertexBits (selectedCell5 edge pair)
                        (tetVerts pair.1 (edgeVertices k).2)) u v = true := by
                    simpa [cell, ev, v1] using h1'
                simp [scaledPairLocalVertexCoeff, cell, ev, v0, v1, c, cRat,
                  huv, h0', h1', h0raw, h1raw]
                try ring_nf
          · simp [huv]
    _ = c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v0 +
        c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v1 := by
          rw [h0, h1]
    _ = (let cell := selectedCell5 edge pair
      let ev := edgeVertices k
      let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
      let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
      let c : ℝ := ((-(snormRat pair.2 k * sqEdgeRat k / 4) / 2 : Rat) : ℝ)
      c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v0 +
        c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v1) := by
          simp [cell, ev, v0, v1, c, cRat]

/-- The two endpoint contributions for one local pair and local edge slot expand
by summing the endpoint-local atom theorem twice. -/
theorem scaledPairLocalVertexCoeffEndpointSumExpansionAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (endpoint₀ endpoint₁ : Vertex5) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (((scaledPairLocalVertexCoeff edge pair k endpoint₀ u v +
            scaledPairLocalVertexCoeff edge pair k endpoint₁ u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v)
      else 0) =
      (let cell := selectedCell5 edge pair
       let ev := edgeVertices k
       let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
       let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
       let c : ℝ := ((-(snormRat pair.2 k * sqEdgeRat k / 4) / 2 : Rat) : ℝ)
       c * potentialAtVertex5 ξ endpoint₀ * potentialAtVertex5 ξ v0 +
         c * potentialAtVertex5 ξ endpoint₀ * potentialAtVertex5 ξ v1) +
      (let cell := selectedCell5 edge pair
       let ev := edgeVertices k
       let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
       let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
       let c : ℝ := ((-(snormRat pair.2 k * sqEdgeRat k / 4) / 2 : Rat) : ℝ)
       c * potentialAtVertex5 ξ endpoint₁ * potentialAtVertex5 ξ v0 +
         c * potentialAtVertex5 ξ endpoint₁ * potentialAtVertex5 ξ v1) := by
  classical
  have h0 := scaledPairLocalVertexCoeffExpansionAtN5 ξ edge pair k endpoint₀
  have h1 := scaledPairLocalVertexCoeffExpansionAtN5 ξ edge pair k endpoint₁
  calc
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (((scaledPairLocalVertexCoeff edge pair k endpoint₀ u v +
            scaledPairLocalVertexCoeff edge pair k endpoint₁ u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v)
      else 0) =
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            ((scaledPairLocalVertexCoeff edge pair k endpoint₀ u v : Rat) : ℝ) *
              potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
          else 0) +
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            ((scaledPairLocalVertexCoeff edge pair k endpoint₁ u v : Rat) : ℝ) *
              potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
          else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases huv : vertex5CanonLE u v
          · simp [huv]
            ring
          · simp [huv]
    _ = _ := by
      rw [h0, h1]

/-- Closed-form value produced by one endpoint/local-pair/local-slot coefficient
atom after unordered monomial expansion. -/
noncomputable def scaledPairEndpointExpansionValueAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (endpoint : Vertex5) : ℝ :=
  let cell := selectedCell5 edge pair
  let ev := edgeVertices k
  let v0 := addVertexBits cell (tetVerts pair.1 ev.1)
  let v1 := addVertexBits cell (tetVerts pair.1 ev.2)
  let c : ℝ := ((-(snormRat pair.2 k * sqEdgeRat k / 4) / 2 : Rat) : ℝ)
  c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v0 +
    c * potentialAtVertex5 ξ endpoint * potentialAtVertex5 ξ v1

noncomputable def scaledPairEndpointSumExpansionValueAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (endpoint₀ endpoint₁ : Vertex5) : ℝ :=
  scaledPairEndpointExpansionValueAtN5 ξ edge pair k endpoint₀ +
    scaledPairEndpointExpansionValueAtN5 ξ edge pair k endpoint₁

/-- One real explicit-fiber Schläfli/local-length slot equals the corresponding
scaled coefficient atom after the edge/pair square-root cancellation. -/
theorem explicitFiberMixedLhsSlot_scaledPairExpansionAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (hpair : pair ∈ freudenthalLocalPairDispFiber edge.disp) :
    Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv
        P5.K P5.hK ξ (P5.edgeEquiv.symm edge) *
      (-(freudenthalLocalPairClosedFormSchlaefliCoeff pair k *
        freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv
          (by decide) (by decide) (by decide) ξ (selectedCell5 edge pair) pair.1 k)) =
      scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
        edge.endpoints.1 edge.endpoints.2 := by
  classical
  have hhinge :=
    hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge
      (Nx := 5) (Ny := 5) (Nz := 5)
      (hx := by decide) (hy := by decide) (hz := by decide) ξ edge
  have hlen :=
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_selectedCell5 ξ edge pair k
  have hsqDisp := periodicDispSqEdge_eq_freudenthalTetSqEdges_of_mem edge pair hpair
  have hsqK_nonneg :
      0 ≤ Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k := by
    fin_cases k <;> norm_num [Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges]
  have hsqrK :
      Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) *
          Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) =
        Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k := by
    rw [← pow_two, Real.sq_sqrt hsqK_nonneg]
  have hsqrK_pow :
      Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) ^ (2 : ℕ) =
        Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k :=
    Real.sq_sqrt hsqK_nonneg
  have hsqrtPair_ne :
      Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges pair.2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    rcases pair with ⟨_tet, slot⟩
    fin_cases slot <;> norm_num [Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges]
  rw [hhinge, hlen, freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table]
  rw [hsqDisp]
  rw [← snormRat_cast_eq_freudenthalSchlaefliTable pair.2 k]
  unfold scaledPairEndpointSumExpansionValueAtN5 scaledPairEndpointExpansionValueAtN5
    potentialAtVertex5
  field_simp [hsqrtPair_ne]
  try simp
  rw [hsqrK_pow, ← sqEdgeRat_cast_eq_freudenthalTetSqEdges k]
  ring_nf

/-- One explicit-fiber local pair contribution expands to the sum of its six
checked endpoint-slot coefficient atoms. -/
theorem explicitFiberMixedLhsPair_scaledPairExpansionAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (hpair : pair ∈ freudenthalLocalPairDispFiber edge.disp) :
    Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv
        P5.K P5.hK ξ (P5.edgeEquiv.symm edge) *
      (-(freudenthalExplicitFiberPairExpandedSummand
        (by decide) (by decide) (by decide) ξ edge pair)) =
      ∑ k : Fin 6,
        scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
          edge.endpoints.1 edge.endpoints.2 := by
  classical
  have hclosed :
      freudenthalExplicitFiberPairClosedFormExpandedSummand
          (by decide) (by decide) (by decide) ξ edge pair =
        freudenthalExplicitFiberPairExpandedSummand
          (by decide) (by decide) (by decide) ξ edge pair :=
    (freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat
        (by decide) (by decide) (by decide) ξ edge pair).trans
      (freudenthalExplicitFiberPairFlatExpandedSummand_eq_expanded
        (by decide) (by decide) (by decide) ξ edge pair)
  rw [← hclosed]
  unfold freudenthalExplicitFiberPairClosedFormExpandedSummand
    freudenthalLocalPairClosedFormExpandedSummand
  rw [← selectedCell5_eq_freudenthalExplicitFiberPairSelectedCell edge pair]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  change
    Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv
        P5.K P5.hK ξ (P5.edgeEquiv.symm edge) *
      (-(freudenthalLocalPairClosedFormSchlaefliCoeff pair k *
        freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv
          (by decide) (by decide) (by decide) ξ (selectedCell5 edge pair) pair.1 k)) =
      scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
        edge.endpoints.1 edge.endpoints.2
  exact explicitFiberMixedLhsSlot_scaledPairExpansionAtN5 ξ edge pair k hpair

/-- Edge-local real explicit-fiber LHS expansion against the checked endpoint-slot
coefficient atoms. -/
theorem explicitFiberMixedLhsEdge_scaledPairExpansionAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) :
    Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv
        P5.K P5.hK ξ (P5.edgeEquiv.symm edge) *
      (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand
          (by decide) (by decide) (by decide) ξ edge pair) =
      ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        ∑ k : Fin 6,
          scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
            edge.endpoints.1 edge.endpoints.2 := by
  classical
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro pair hpair
  exact explicitFiberMixedLhsPair_scaledPairExpansionAtN5 ξ edge pair hpair

theorem scaledPairLocalVertexCoeffExpansionAtN5_value
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (endpoint : Vertex5) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        ((scaledPairLocalVertexCoeff edge pair k endpoint u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
      scaledPairEndpointExpansionValueAtN5 ξ edge pair k endpoint := by
  simpa [scaledPairEndpointExpansionValueAtN5] using
    scaledPairLocalVertexCoeffExpansionAtN5 ξ edge pair k endpoint

theorem scaledPairLocalVertexCoeffEndpointSumExpansionAtN5_value
    (ξ : VertexPotential5) (edge : PeriodicEdge5) (pair : FreudenthalLocalPair)
    (k : Fin 6) (endpoint₀ endpoint₁ : Vertex5) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (((scaledPairLocalVertexCoeff edge pair k endpoint₀ u v +
            scaledPairLocalVertexCoeff edge pair k endpoint₁ u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v)
      else 0) =
      scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k endpoint₀ endpoint₁ := by
  simpa [scaledPairEndpointSumExpansionValueAtN5, scaledPairEndpointExpansionValueAtN5] using
    scaledPairLocalVertexCoeffEndpointSumExpansionAtN5 ξ edge pair k endpoint₀ endpoint₁

/-- Edge-local LHS coefficient expansion: the unordered polynomial encoded by
`mixedAxisEdgeLhsCoeff edge` is the sum of the checked endpoint/local-slot atoms
for that edge. -/
theorem mixedAxisEdgeLhsCoeffExpansionAtN5
    (ξ : VertexPotential5) (edge : PeriodicEdge5) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        ((mixedAxisEdgeLhsCoeff edge u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
      ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        ∑ k : Fin 6,
          scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
            edge.endpoints.1 edge.endpoints.2 := by
  classical
  let F := fun (pair : FreudenthalLocalPair) (k : Fin 6) (u v : Vertex5) =>
    if vertex5CanonLE u v then
      (((scaledPairLocalVertexCoeff edge pair k edge.endpoints.1 u v +
          scaledPairLocalVertexCoeff edge pair k edge.endpoints.2 u v : Rat) : ℝ) *
        potentialAtVertex5 ξ u * potentialAtVertex5 ξ v)
    else 0
  have hdist :
      (∑ u : Vertex5, ∑ v : Vertex5,
        if vertex5CanonLE u v then
          ((mixedAxisEdgeLhsCoeff edge u v : Rat) : ℝ) *
            potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
        else 0) =
        ∑ u : Vertex5, ∑ v : Vertex5,
          ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
            F pair k u v := by
    unfold mixedAxisEdgeLhsCoeff
    refine Finset.sum_congr rfl ?_
    intro u _
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases huv : vertex5CanonLE u v
    · simp [F, huv, Finset.sum_mul]
    · simp [F, huv]
  have hreorder :
      (∑ u : Vertex5, ∑ v : Vertex5,
          ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
            F pair k u v) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
          ∑ u : Vertex5, ∑ v : Vertex5, F pair k u v := by
    calc
      (∑ u : Vertex5, ∑ v : Vertex5,
          ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
            F pair k u v) =
        ∑ u : Vertex5, ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          ∑ v : Vertex5, ∑ k : Fin 6, F pair k u v := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [Finset.sum_comm
            (s := (Finset.univ : Finset Vertex5))
            (t := freudenthalLocalPairDispFiber edge.disp)
            (f := fun v pair => ∑ k : Fin 6, F pair k u v)]
      _ =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ u : Vertex5,
          ∑ v : Vertex5, ∑ k : Fin 6, F pair k u v := by
          rw [Finset.sum_comm
            (s := (Finset.univ : Finset Vertex5))
            (t := freudenthalLocalPairDispFiber edge.disp)
            (f := fun u pair => ∑ v : Vertex5, ∑ k : Fin 6, F pair k u v)]
      _ = ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
          ∑ u : Vertex5, ∑ v : Vertex5, F pair k u v := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          calc
            (∑ u : Vertex5, ∑ v : Vertex5, ∑ k : Fin 6, F pair k u v) =
              ∑ u : Vertex5, ∑ k : Fin 6, ∑ v : Vertex5, F pair k u v := by
                refine Finset.sum_congr rfl ?_
                intro u _
                rw [Finset.sum_comm
                  (s := (Finset.univ : Finset Vertex5))
                  (t := (Finset.univ : Finset (Fin 6)))
                  (f := fun v k => F pair k u v)]
            _ = ∑ k : Fin 6, ∑ u : Vertex5, ∑ v : Vertex5, F pair k u v := by
                rw [Finset.sum_comm
                  (s := (Finset.univ : Finset Vertex5))
                  (t := (Finset.univ : Finset (Fin 6)))
                  (f := fun u k => ∑ v : Vertex5, F pair k u v)]
  calc
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        ((mixedAxisEdgeLhsCoeff edge u v : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
        ∑ u : Vertex5, ∑ v : Vertex5,
          ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
            F pair k u v := hdist
    _ = ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
          ∑ u : Vertex5, ∑ v : Vertex5, F pair k u v := hreorder
    _ = ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp, ∑ k : Fin 6,
          scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
            edge.endpoints.1 edge.endpoints.2 := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          refine Finset.sum_congr rfl ?_
          intro k _
          simpa [F] using
            scaledPairLocalVertexCoeffEndpointSumExpansionAtN5_value
              ξ edge pair k edge.endpoints.1 edge.endpoints.2

/-- On a five-periodic coordinate, adding one tick always remains comparable
with the starting point in the product order: either it moves forward without
wraparound, or it wraps from `4` to `0`. -/
theorem addBitTrueComparable5 (i : Fin 5) :
    i ≤ addBit i true ∨ addBit i true ≤ i := by
  fin_cases i <;> decide

/-- Axis-edge endpoints in the `N = 5` periodic Freudenthal torus are comparable
in the product order.  This remains useful for local geometry audits, although
the coefficient expansion now uses `vertex5CanonLE` to cover every unordered
pair on the periodic torus. -/
theorem axisEdgeEndpointsComparable5 (base : Vertex5) (d : Fin 3) :
    let edge : PeriodicEdge5 := { base := base, disp := periodicAxisDisp d }
    edge.endpoints.1 ≤ edge.endpoints.2 ∨ edge.endpoints.2 ≤ edge.endpoints.1 := by
  rcases base with ⟨x, y, z⟩
  fin_cases d
  · dsimp [PeriodicEdge.endpoints, periodicAxisDisp, dispBits, addBits]
    simp only [addBit_false]
    rcases addBitTrueComparable5 x with hx | hx
    · left
      constructor
      · exact hx
      · constructor <;> rfl
    · right
      constructor
      · exact hx
      · constructor <;> rfl
  · dsimp [PeriodicEdge.endpoints, periodicAxisDisp, dispBits, addBits]
    simp only [addBit_false]
    rcases addBitTrueComparable5 y with hy | hy
    · left
      constructor
      · rfl
      · constructor
        · exact hy
        · rfl
    · right
      constructor
      · rfl
      · constructor
        · exact hy
        · rfl
  · dsimp [PeriodicEdge.endpoints, periodicAxisDisp, dispBits, addBits]
    simp only [addBit_false]
    rcases addBitTrueComparable5 z with hz | hz
    · left
      constructor
      · rfl
      · constructor
        · rfl
        · exact hz
    · right
      constructor
      · rfl
      · constructor
        · rfl
        · exact hz

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- The three local coefficient atoms for one non-loop axis edge
expand to the negative corrected Dirichlet contribution. -/
theorem pairAxisCoeffExpansionAtN5
    (ξ : VertexPotential5) (a b : Vertex5) (hne : a ≠ b) :
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (((if a = u && a = v then (-2 : Rat) else 0) +
          (if b = u && b = v then (-2 : Rat) else 0) +
          (if sameUnordered a b u v then (4 : Rat) else 0) : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
      -2 * (potentialAtVertex5 ξ a - potentialAtVertex5 ξ b) ^ (2 : ℕ) := by
  classical
  have hdiagA := unorderedDiagonalMonomialExpansionAtN5 ξ a (-2)
  have hdiagB := unorderedDiagonalMonomialExpansionAtN5 ξ b (-2)
  have hcross := unorderedCrossMonomialExpansionAtN5 ξ a b 4 hne
  calc
    (∑ u : Vertex5, ∑ v : Vertex5,
      if vertex5CanonLE u v then
        (((if a = u && a = v then (-2 : Rat) else 0) +
          (if b = u && b = v then (-2 : Rat) else 0) +
          (if sameUnordered a b u v then (4 : Rat) else 0) : Rat) : ℝ) *
          potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
      else 0) =
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            (if a = u && a = v then
              (-2 : ℝ) * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
            else 0)
          else 0) +
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            (if b = u && b = v then
              (-2 : ℝ) * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
            else 0)
          else 0) +
        (∑ u : Vertex5, ∑ v : Vertex5,
          if vertex5CanonLE u v then
            (if sameUnordered a b u v then
              (4 : ℝ) * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
            else 0)
          else 0) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases huv : vertex5CanonLE u v
          · by_cases ha : a = u && a = v
            · by_cases hb : b = u && b = v
              · by_cases hc : sameUnordered a b u v <;> simp [huv, ha, hb, hc] <;> ring
              · by_cases hc : sameUnordered a b u v <;> simp [huv, ha, hb, hc] <;> ring
            · by_cases hb : b = u && b = v
              · by_cases hc : sameUnordered a b u v <;> simp [huv, ha, hb, hc] <;> ring
              · by_cases hc : sameUnordered a b u v <;> simp [huv, ha, hb, hc] <;> ring
          · simp [huv]
    _ = (-2) * potentialAtVertex5 ξ a * potentialAtVertex5 ξ a +
        (-2) * potentialAtVertex5 ξ b * potentialAtVertex5 ξ b +
        4 * potentialAtVertex5 ξ a * potentialAtVertex5 ξ b := by
          rw [hdiagA, hdiagB, hcross]
    _ = -2 * (potentialAtVertex5 ξ a - potentialAtVertex5 ξ b) ^ (2 : ℕ) := by
          ring

/-- Real-valued residual of the corrected explicit-fiber axis-stencil identity at
`N = 5`, written as `LHS - RHS`. -/
noncomputable def explicitFiberAxisStencilResidualAtN5 (ξ : VertexPotential5) : ℝ :=
  (∑ edge : PeriodicEdge5,
      let e := P5.edgeEquiv.symm edge
      Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv P5.K P5.hK ξ e *
        (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand
            (by decide) (by decide) (by decide) ξ edge pair)) -
    canonicalPeriodicMixedAxisStencilAction 5 5 5 (by decide) (by decide) (by decide) ξ

noncomputable def explicitFiberMixedLhsAtN5 (ξ : VertexPotential5) : ℝ :=
  ∑ edge : PeriodicEdge5,
    let e := P5.edgeEquiv.symm edge
    Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv P5.K P5.hK ξ e *
      (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand
          (by decide) (by decide) (by decide) ξ edge pair)

noncomputable def axisStencilResidualAtN5 (ξ : VertexPotential5) : ℝ :=
  -canonicalPeriodicMixedAxisStencilAction 5 5 5 (by decide) (by decide) (by decide) ξ

theorem explicitFiberAxisStencilResidualAtN5_eq_lhs_add_axis
    (ξ : VertexPotential5) :
    explicitFiberAxisStencilResidualAtN5 ξ =
      explicitFiberMixedLhsAtN5 ξ + axisStencilResidualAtN5 ξ := by
  unfold explicitFiberAxisStencilResidualAtN5 explicitFiberMixedLhsAtN5 axisStencilResidualAtN5
  ring

/-- Canonical unordered monomial expansion of the corrected rational residual
coefficient model.  The Python audit indexes coefficients by unordered vertex
pairs; here `u ≤ v` gives the Lean-side canonical representative. -/
noncomputable def unorderedResidualCoeffExpansionAtN5 (ξ : VertexPotential5) : ℝ :=
  ∑ u : Vertex5, ∑ v : Vertex5,
    if vertex5CanonLE u v then
      (mixedAxisResidualCoeff u v : ℝ) * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
    else
      0

noncomputable def unorderedLhsCoeffExpansionAtN5 (ξ : VertexPotential5) : ℝ :=
  ∑ u : Vertex5, ∑ v : Vertex5,
    if vertex5CanonLE u v then
      (mixedAxisLhsCoeff u v : ℝ) * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
    else
      0

noncomputable def unorderedAxisCoeffExpansionAtN5 (ξ : VertexPotential5) : ℝ :=
  ∑ u : Vertex5, ∑ v : Vertex5,
    if vertex5CanonLE u v then
      (axisStencilResidualCoeff u v : ℝ) * potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
    else
      0

/-- Global coefficient-side LHS expansion, obtained by summing the edge-local
`mixedAxisEdgeLhsCoeffExpansionAtN5` theorem over all periodic edges. -/
theorem unorderedLhsCoeffExpansionAtN5_eq_edge_scaledPairSum
    (ξ : VertexPotential5) :
    unorderedLhsCoeffExpansionAtN5 ξ =
      ∑ edge : PeriodicEdge5,
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          ∑ k : Fin 6,
            scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
              edge.endpoints.1 edge.endpoints.2 := by
  classical
  let F := fun (edge : PeriodicEdge5) (u v : Vertex5) =>
    if vertex5CanonLE u v then
      ((mixedAxisEdgeLhsCoeff edge u v : Rat) : ℝ) *
        potentialAtVertex5 ξ u * potentialAtVertex5 ξ v
    else 0
  have hdist : unorderedLhsCoeffExpansionAtN5 ξ =
      ∑ u : Vertex5, ∑ v : Vertex5, ∑ edge : PeriodicEdge5, F edge u v := by
    unfold unorderedLhsCoeffExpansionAtN5 mixedAxisLhsCoeff
    refine Finset.sum_congr rfl ?_
    intro u _
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases huv : vertex5CanonLE u v
    · simp [F, huv, Finset.sum_mul]
    · simp [F, huv]
  have hreorder :
      (∑ u : Vertex5, ∑ v : Vertex5, ∑ edge : PeriodicEdge5, F edge u v) =
        ∑ edge : PeriodicEdge5, ∑ u : Vertex5, ∑ v : Vertex5, F edge u v := by
    calc
      (∑ u : Vertex5, ∑ v : Vertex5, ∑ edge : PeriodicEdge5, F edge u v) =
        ∑ u : Vertex5, ∑ edge : PeriodicEdge5, ∑ v : Vertex5, F edge u v := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [Finset.sum_comm
            (s := (Finset.univ : Finset Vertex5))
            (t := (Finset.univ : Finset PeriodicEdge5))
            (f := fun v edge => F edge u v)]
      _ = ∑ edge : PeriodicEdge5, ∑ u : Vertex5, ∑ v : Vertex5, F edge u v := by
          rw [Finset.sum_comm
            (s := (Finset.univ : Finset Vertex5))
            (t := (Finset.univ : Finset PeriodicEdge5))
            (f := fun u edge => ∑ v : Vertex5, F edge u v)]
  calc
    unorderedLhsCoeffExpansionAtN5 ξ =
        ∑ u : Vertex5, ∑ v : Vertex5, ∑ edge : PeriodicEdge5, F edge u v := hdist
    _ = ∑ edge : PeriodicEdge5, ∑ u : Vertex5, ∑ v : Vertex5, F edge u v := hreorder
    _ = ∑ edge : PeriodicEdge5,
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          ∑ k : Fin 6,
            scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
              edge.endpoints.1 edge.endpoints.2 := by
          refine Finset.sum_congr rfl ?_
          intro edge _
          simpa [F] using mixedAxisEdgeLhsCoeffExpansionAtN5 ξ edge

theorem unorderedResidualCoeffExpansionAtN5_eq_lhs_add_axis
    (ξ : VertexPotential5) :
    unorderedResidualCoeffExpansionAtN5 ξ =
      unorderedLhsCoeffExpansionAtN5 ξ + unorderedAxisCoeffExpansionAtN5 ξ := by
  unfold unorderedResidualCoeffExpansionAtN5 unorderedLhsCoeffExpansionAtN5
    unorderedAxisCoeffExpansionAtN5 mixedAxisResidualCoeff
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro v _
  by_cases huv : vertex5CanonLE u v
  · simp [huv]
    ring
  · simp [huv]

/-- Global real explicit-fiber LHS expansion over the same edge/pair/slot atoms
used by the coefficient-side theorem. -/
theorem explicitFiberMixedLhsAtN5_eq_edge_scaledPairSum
    (ξ : VertexPotential5) :
    explicitFiberMixedLhsAtN5 ξ =
      ∑ edge : PeriodicEdge5,
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          ∑ k : Fin 6,
            scaledPairEndpointSumExpansionValueAtN5 ξ edge pair k
              edge.endpoints.1 edge.endpoints.2 := by
  classical
  unfold explicitFiberMixedLhsAtN5
  refine Finset.sum_congr rfl ?_
  intro edge _
  simpa using explicitFiberMixedLhsEdge_scaledPairExpansionAtN5 ξ edge

def ExplicitFiberMixedLhsCoeffSoundnessAtN5 : Prop :=
  ∀ ξ : VertexPotential5,
    explicitFiberMixedLhsAtN5 ξ = unorderedLhsCoeffExpansionAtN5 ξ

/-- The real explicit-fiber mixed LHS and the rational unordered LHS coefficient
model are the same quadratic form at `N = 5`. -/
theorem explicitFiberMixedLhsCoeffSoundnessAtN5 :
    ExplicitFiberMixedLhsCoeffSoundnessAtN5 := by
  intro ξ
  rw [explicitFiberMixedLhsAtN5_eq_edge_scaledPairSum,
    unorderedLhsCoeffExpansionAtN5_eq_edge_scaledPairSum]

def AxisStencilCoeffSoundnessAtN5 : Prop :=
  ∀ ξ : VertexPotential5,
    axisStencilResidualAtN5 ξ = unorderedAxisCoeffExpansionAtN5 ξ

/-- The corrected three-axis stencil is sound with respect to the unordered
coefficient expansion.  This closes the RHS half of
`ExplicitFiberAxisStencilCoeffSoundnessAtN5`; the remaining packaging work is
the explicit-fiber LHS expansion. -/
theorem axisStencilCoeffSoundnessAtN5 :
    AxisStencilCoeffSoundnessAtN5 := by
  intro ξ
  let atom := fun (base : Vertex5) (d : Fin 3) (u v : Vertex5) =>
    let edge : PeriodicEdge5 := { base := base, disp := periodicAxisDisp d }
    let ep := edge.endpoints
    (if ep.1 = u && ep.1 = v then (-2 : Rat) else 0) +
      (if ep.2 = u && ep.2 = v then (-2 : Rat) else 0) +
        (if sameUnordered ep.1 ep.2 u v then (4 : Rat) else 0)
  let F := fun (u v base : Vertex5) (d : Fin 3) =>
    if vertex5CanonLE u v then ((atom base d u v : Rat) : ℝ) *
      potentialAtVertex5 ξ u * potentialAtVertex5 ξ v else 0
  have hdist : unorderedAxisCoeffExpansionAtN5 ξ =
      ∑ u : Vertex5, ∑ v : Vertex5, ∑ base : Vertex5, ∑ d : Fin 3,
        F u v base d := by
    unfold unorderedAxisCoeffExpansionAtN5 axisStencilResidualCoeff
    refine Finset.sum_congr rfl ?_
    intro u _
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases huv : vertex5CanonLE u v
    · simp only [huv, if_true, F]
      simp [atom, Finset.sum_mul]
    · simp [F, huv]
  have hreorder :
      (∑ u : Vertex5, ∑ v : Vertex5, ∑ base : Vertex5, ∑ d : Fin 3,
        F u v base d) =
      ∑ base : Vertex5, ∑ d : Fin 3, ∑ u : Vertex5, ∑ v : Vertex5,
        F u v base d := by
    calc
      (∑ u : Vertex5, ∑ v : Vertex5, ∑ base : Vertex5, ∑ d : Fin 3,
        F u v base d) =
          ∑ u : Vertex5, ∑ base : Vertex5, ∑ v : Vertex5, ∑ d : Fin 3,
            F u v base d := by
            refine Finset.sum_congr rfl ?_
            intro u _
            rw [@Finset.sum_comm Vertex5 ℝ Vertex5 _
              (s := Finset.univ) (t := Finset.univ)
              (f := fun v base => ∑ d : Fin 3, F u v base d)]
      _ = ∑ base : Vertex5, ∑ u : Vertex5, ∑ v : Vertex5, ∑ d : Fin 3,
            F u v base d := by
            rw [@Finset.sum_comm Vertex5 ℝ Vertex5 _
              (s := Finset.univ) (t := Finset.univ)
              (f := fun u base => ∑ v : Vertex5, ∑ d : Fin 3, F u v base d)]
      _ = ∑ base : Vertex5, ∑ d : Fin 3, ∑ u : Vertex5, ∑ v : Vertex5,
            F u v base d := by
            refine Finset.sum_congr rfl ?_
            intro base _
            calc
              (∑ u : Vertex5, ∑ v : Vertex5, ∑ d : Fin 3,
                F u v base d) =
                  ∑ u : Vertex5, ∑ d : Fin 3, ∑ v : Vertex5,
                    F u v base d := by
                    refine Finset.sum_congr rfl ?_
                    intro u _
                    rw [@Finset.sum_comm (Fin 3) ℝ Vertex5 _
                      (s := Finset.univ) (t := Finset.univ)
                      (f := fun v d => F u v base d)]
              _ = ∑ d : Fin 3, ∑ u : Vertex5, ∑ v : Vertex5,
                    F u v base d := by
                    rw [@Finset.sum_comm (Fin 3) ℝ Vertex5 _
                      (s := Finset.univ) (t := Finset.univ)
                      (f := fun u d => ∑ v : Vertex5, F u v base d)]
  have hpairSum :
      (∑ base : Vertex5, ∑ d : Fin 3, ∑ u : Vertex5, ∑ v : Vertex5,
        F u v base d) =
      ∑ base : Vertex5, ∑ d : Fin 3,
        -2 * (potentialAtVertex5 ξ
            ({ base := base, disp := periodicAxisDisp d } : PeriodicEdge5).endpoints.1 -
          potentialAtVertex5 ξ
            ({ base := base, disp := periodicAxisDisp d } : PeriodicEdge5).endpoints.2) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro base _
    refine Finset.sum_congr rfl ?_
    intro d _
    let edge : PeriodicEdge5 := { base := base, disp := periodicAxisDisp d }
    have hne : edge.endpoints.1 ≠ edge.endpoints.2 :=
      PeriodicEdge.endpoints_ne (by decide) (by decide) (by decide) edge
    simpa [F, atom, edge] using
      pairAxisCoeffExpansionAtN5 ξ edge.endpoints.1 edge.endpoints.2 hne
  have hcoeff : unorderedAxisCoeffExpansionAtN5 ξ =
      ∑ base : Vertex5, ∑ d : Fin 3,
        -2 * (potentialAtVertex5 ξ
            ({ base := base, disp := periodicAxisDisp d } : PeriodicEdge5).endpoints.1 -
          potentialAtVertex5 ξ
            ({ base := base, disp := periodicAxisDisp d } : PeriodicEdge5).endpoints.2) ^ (2 : ℕ) := by
    rw [hdist, hreorder, hpairSum]
  have haxis : axisStencilResidualAtN5 ξ =
      ∑ base : Vertex5, ∑ d : Fin 3,
        -2 * (potentialAtVertex5 ξ
            ({ base := base, disp := periodicAxisDisp d } : PeriodicEdge5).endpoints.1 -
          potentialAtVertex5 ξ
            ({ base := base, disp := periodicAxisDisp d } : PeriodicEdge5).endpoints.2) ^ (2 : ℕ) := by
    unfold axisStencilResidualAtN5 canonicalPeriodicMixedAxisStencilAction potentialAtVertex5
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro base _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro d _
    ring
  rw [haxis, hcoeff]

/-- Coefficient-soundness bridge for the corrected `N = 5` certificate: the real
explicit-fiber residual is the unordered monomial expansion of the rational
residual coefficients.  This is the remaining algebraic packaging surface after
Session 212 closed every coefficient. -/
def ExplicitFiberAxisStencilCoeffSoundnessAtN5 : Prop :=
  ∀ ξ : VertexPotential5,
    explicitFiberAxisStencilResidualAtN5 ξ = unorderedResidualCoeffExpansionAtN5 ξ

theorem ExplicitFiberAxisStencilCoeffSoundnessAtN5_of_parts
    (hlhs : ExplicitFiberMixedLhsCoeffSoundnessAtN5)
    (haxis : AxisStencilCoeffSoundnessAtN5) :
    ExplicitFiberAxisStencilCoeffSoundnessAtN5 := by
  intro ξ
  rw [explicitFiberAxisStencilResidualAtN5_eq_lhs_add_axis,
    unorderedResidualCoeffExpansionAtN5_eq_lhs_add_axis, hlhs ξ, haxis ξ]

/-- Combined coefficient-soundness theorem for the corrected explicit-fiber
axis-stencil residual at `N = 5`. -/
theorem explicitFiberAxisStencilCoeffSoundnessAtN5 :
    ExplicitFiberAxisStencilCoeffSoundnessAtN5 :=
  ExplicitFiberAxisStencilCoeffSoundnessAtN5_of_parts
    explicitFiberMixedLhsCoeffSoundnessAtN5
    axisStencilCoeffSoundnessAtN5

theorem fullResidualCoeffCert_unordered_expansion_zero
    (hcoeff : FullResidualCoeffCert) (ξ : VertexPotential5) :
    unorderedResidualCoeffExpansionAtN5 ξ = 0 := by
  unfold unorderedResidualCoeffExpansionAtN5
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  by_cases huv : vertex5CanonLE u v
  · simp [huv, hcoeff u v]
  · simp [huv]

/-- Packaging reduction from the coefficient certificate to the corrected
explicit-fiber axis-stencil target.  The only remaining input is the algebraic
soundness theorem identifying the real residual with the coefficient model. -/
theorem canonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5_of_coeffSoundness
    (hsound : ExplicitFiberAxisStencilCoeffSoundnessAtN5) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5 := by
  intro ξ
  have hres := hsound ξ
  have hzero : unorderedResidualCoeffExpansionAtN5 ξ = 0 :=
    fullResidualCoeffCert_unordered_expansion_zero fullResidualCoeffCert ξ
  have hdiff : explicitFiberAxisStencilResidualAtN5 ξ = 0 := by
    rw [hres, hzero]
  unfold explicitFiberAxisStencilResidualAtN5 at hdiff
  exact sub_eq_zero.mp hdiff

theorem canonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5_of_coeffSoundness
    (hsound : ExplicitFiberAxisStencilCoeffSoundnessAtN5) :
    CanonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5 :=
  canonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5_of_explicitFiberAxis
    (canonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5_of_coeffSoundness hsound)

/-- Closed corrected explicit-fiber axis-stencil target at `N = 5`, obtained
from the finite coefficient certificate and the real/coefficient soundness
bridge. -/
theorem canonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5 :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5 :=
  canonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5_of_coeffSoundness
    explicitFiberAxisStencilCoeffSoundnessAtN5

/-- Closed corrected mixed axis-stencil target at `N = 5`, via the explicit-fiber
wrapper. -/
theorem canonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5 :
    CanonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5 :=
  canonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5_of_coeffSoundness
    explicitFiberAxisStencilCoeffSoundnessAtN5

theorem rowMixedAxisLhsCoeffTranslationInvariant_100_eq_true :
    rowMixedAxisLhsCoeffTranslationInvariant (1, 0, 0) = true := by
  native_decide

def rowResidualCoeffsZero (u : Vertex5) : Bool :=
  decide (∀ v : Vertex5, mixedAxisResidualCoeff u v = 0)

theorem rowResidualCoeffsZero_100_eq_true :
    rowResidualCoeffsZero (1, 0, 0) = true := by
  native_decide

end FreudenthalAxisStencilCoeffCert
end Gravity
end IndisputableMonolith
