import IndisputableMonolith.Foundation.CircleWinding
import IndisputableMonolith.Foundation.CircleLifting
import IndisputableMonolith.Foundation.CircleFundamentalSimplex
import IndisputableMonolith.Foundation.CircleH1Computation
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The winding invariant on singular 1-simplices, and the kills-boundaries identity

This module lifts the path-level winding/displacement invariant of
`CircleWinding` to the level of *singular simplices* of `TopCat.sphere 1`, and
proves the single fact that makes it a homology invariant:

* `simplexDisplacement` assigns a real number (the displacement, i.e. `2π ×`
  winding) to every singular `1`-simplex `f : C(Δ¹, S¹)`, by reparameterising the
  standard `1`-simplex `Δ¹` to the unit interval and taking `pathDisplacement`.

* `simplexDisplacement_boundary`: for every singular `2`-simplex
  `F : C(Δ², S¹)`, the alternating face sum
  `disp(δ₀F) − disp(δ₁F) + disp(δ₂F)` is `0`.

The second theorem is the chain-level "winding kills boundaries" statement.  Its
proof is the `2`-simplex telescoping: the boundary walk `v₀ → v₁ → v₂` along two
edges is homotopic rel endpoints (inside the convex, hence simply connected,
standard `2`-simplex) to the direct edge `v₀ → v₂`; pushing that homotopy through
`F` and combining `pathDisplacement_trans` (additivity) with
`pathDisplacement_homotopic` (homotopy invariance) gives
`disp(δ₁F) = disp(δ₂F) + disp(δ₀F)`, which is the vanishing of the alternating
sum.

Together with `CircleWinding.pathWinding_fundamentalLoop` (the invariant sends the
once-around generator to `1`), this gives a winding homomorphism on `1`-cycles
that is a left inverse to the fundamental class: the "split-injective" half of
`H₁(S¹;ℤ) ≅ ℤ`.  The converse (every `1`-cycle is homologous to an integer
multiple of the fundamental cycle, i.e. surjectivity of the integer comparison
map) is the generation half and requires the simplicial prism / subdivision
operator, which Mathlib's singular homology does not yet provide.

No axioms, `sorry`, or project-local `S¹` replacements are used.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleWindingChain

open CategoryTheory Opposite
open CircleParam CircleWinding
open scoped BigOperators Real unitInterval Topology

noncomputable section

/-- A singular `1`-simplex of `TopCat.sphere 1`, presented as a continuous map
from the standard topological `1`-simplex `Δ¹ = stdSimplex ℝ (Fin 2)`. -/
abbrev OneSimplex : Type := C(stdSimplex ℝ (Fin 2), SphereOne)

/-- A singular `2`-simplex of `TopCat.sphere 1`, presented as a continuous map
from the standard topological `2`-simplex `Δ² = stdSimplex ℝ (Fin 3)`. -/
abbrev TwoSimplex : Type := C(stdSimplex ℝ (Fin 3), SphereOne)

/-- The reparameterisation of the unit interval onto the standard `1`-simplex,
`t ↦ (1 - t, t)`.  It is the inverse of Mathlib's
`stdSimplexHomeomorphUnitInterval`. -/
def intervalToSimplex : C(I, stdSimplex ℝ (Fin 2)) :=
  ⟨stdSimplexHomeomorphUnitInterval.symm, stdSimplexHomeomorphUnitInterval.symm.continuous⟩

@[simp] theorem intervalToSimplex_apply (t : I) :
    intervalToSimplex t = stdSimplexHomeomorphUnitInterval.symm t := rfl

theorem intervalToSimplex_zero :
    intervalToSimplex 0 = stdSimplex.vertex (0 : Fin 2) := by
  have h0 : stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (0 : Fin 2)) = 0 :=
    stdSimplexHomeomorphUnitInterval_zero
  simp only [intervalToSimplex_apply]
  rw [← h0, Homeomorph.symm_apply_apply]

theorem intervalToSimplex_one :
    intervalToSimplex 1 = stdSimplex.vertex (1 : Fin 2) := by
  have h1 : stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (1 : Fin 2)) = 1 :=
    stdSimplexHomeomorphUnitInterval_one
  simp only [intervalToSimplex_apply]
  rw [← h1, Homeomorph.symm_apply_apply]

/-- A singular `1`-simplex, read as a path in the unit-interval parameterisation. -/
def oneSimplexPath (f : OneSimplex) : C(I, SphereOne) := f.comp intervalToSimplex

/-- A unit-interval path, read as a concrete singular `1`-simplex via the standard
homeomorphism `Δ¹ ≃ I`. -/
noncomputable def oneSimplexOfPath (γ : C(I, SphereOne)) : OneSimplex :=
  γ.comp ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- Converting a path to a concrete `1`-simplex and then reading it back as a path
returns the original path. -/
theorem oneSimplexPath_ofPath (γ : C(I, SphereOne)) :
    oneSimplexPath (oneSimplexOfPath γ) = γ := by
  ext t
  unfold oneSimplexPath oneSimplexOfPath intervalToSimplex
  simp

/-- The unit-interval parameterisation and its inverse recover a concrete
singular `1`-simplex. -/
theorem oneSimplexOfPath_oneSimplexPath (f : OneSimplex) :
    oneSimplexOfPath (oneSimplexPath f) = f := by
  ext x
  unfold oneSimplexOfPath oneSimplexPath intervalToSimplex
  simp

/-- **The displacement of a singular `1`-simplex**: the lift-independent angular
travel `2π × (winding number)`, obtained from the path-level displacement. -/
def simplexDisplacement (f : OneSimplex) : ℝ := pathDisplacement (oneSimplexPath f)

/-- **The winding number of a singular `1`-simplex**, normalised by one full
turn. -/
def simplexWinding (f : OneSimplex) : ℝ := simplexDisplacement f / (2 * Real.pi)

/-- The topological face map `Δ¹ → Δ²` induced by the `i`-th coface
`δ i : ⦋1⦌ ⟶ ⦋2⦌`, realised as an affine map of standard simplices. -/
def faceMap (i : Fin 3) : C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 3)) :=
  ⟨stdSimplex.map (ConcreteCategory.hom (SimplexCategory.δ i)),
    stdSimplex.continuous_map _⟩

@[simp] theorem faceMap_apply (i : Fin 3) (x : stdSimplex ℝ (Fin 2)) :
    faceMap i x = stdSimplex.map (ConcreteCategory.hom (SimplexCategory.δ i)) x := rfl

open CategoryTheory in
/-- On the base face `δ₂ : Δ¹ → Δ²`, the second barycentric coordinate is
preserved.  This is the coordinate identity needed by the cone parameter
`x₁ / (1 - x₂)`. -/
theorem faceMap_two_coord_one (x : stdSimplex ℝ (Fin 2)) :
    ((faceMap (2 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 1 = x 1 := by
  rw [faceMap_apply]
  change FunOnFinite.linearMap ℝ ℝ
      ((ConcreteCategory.hom (SimplexCategory.δ (2 : Fin 3))) : Fin 2 → Fin 3) x 1 = x 1
  have hδ :
      ((ConcreteCategory.hom (SimplexCategory.δ (2 : Fin 3))) : Fin 2 → Fin 3) =
        (fun j : Fin 2 => (j.castSucc : Fin 3)) := by
    ext j
    fin_cases j <;> rfl
  rw [hδ, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_single (1 : Fin 2)
    (by
      intro b hb hbne
      fin_cases b <;> simp at hb hbne)
    (by
      intro hnot
      simp at hnot)

open CategoryTheory in
/-- On the base face `δ₂ : Δ¹ → Δ²`, the cone coordinate `x₂` is zero. -/
theorem faceMap_two_coord_two (x : stdSimplex ℝ (Fin 2)) :
    ((faceMap (2 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = 0 := by
  rw [faceMap_apply]
  change FunOnFinite.linearMap ℝ ℝ
      ((ConcreteCategory.hom (SimplexCategory.δ (2 : Fin 3))) : Fin 2 → Fin 3) x 2 = 0
  have hδ :
      ((ConcreteCategory.hom (SimplexCategory.δ (2 : Fin 3))) : Fin 2 → Fin 3) =
        (fun j : Fin 2 => (j.castSucc : Fin 3)) := by
    ext j
    fin_cases j <;> rfl
  rw [hδ, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_zero (by
    intro b hb
    fin_cases b <;> simp at hb)

open CategoryTheory in
/-- On the side face `δ₀ : Δ¹ → Δ²`, the coordinate `x₁` is the initial
`Δ¹` barycentric coordinate. -/
theorem faceMap_zero_coord_one (x : stdSimplex ℝ (Fin 2)) :
    ((faceMap (0 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 1 = x 0 := by
  rw [faceMap_apply]
  change FunOnFinite.linearMap ℝ ℝ
      ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 3))) : Fin 2 → Fin 3) x 1 = x 0
  have hδ :
      ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 3))) : Fin 2 → Fin 3) =
        (fun j : Fin 2 => j.succ) := by
    ext j
    fin_cases j <;> rfl
  rw [hδ, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_single (0 : Fin 2)
    (by
      intro b hb hbne
      fin_cases b <;> simp at hb hbne)
    (by
      intro hnot
      simp at hnot)

open CategoryTheory in
/-- On the side face `δ₀ : Δ¹ → Δ²`, the coordinate `x₂` is the terminal
`Δ¹` barycentric coordinate. -/
theorem faceMap_zero_coord_two (x : stdSimplex ℝ (Fin 2)) :
    ((faceMap (0 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = x 1 := by
  rw [faceMap_apply]
  change FunOnFinite.linearMap ℝ ℝ
      ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 3))) : Fin 2 → Fin 3) x 2 = x 1
  have hδ :
      ((ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 3))) : Fin 2 → Fin 3) =
        (fun j : Fin 2 => j.succ) := by
    ext j
    fin_cases j <;> rfl
  rw [hδ, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_single (1 : Fin 2)
    (by
      intro b hb hbne
      fin_cases b <;> simp at hb hbne)
    (by
      intro hnot
      simp at hnot)

open CategoryTheory in
/-- On the side face `δ₁ : Δ¹ → Δ²`, the coordinate `x₁` is zero. -/
theorem faceMap_one_coord_one (x : stdSimplex ℝ (Fin 2)) :
    ((faceMap (1 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 1 = 0 := by
  rw [faceMap_apply]
  change FunOnFinite.linearMap ℝ ℝ
      ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 3))) : Fin 2 → Fin 3) x 1 = 0
  have hδ :
      ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 3))) : Fin 2 → Fin 3) =
        (fun j : Fin 2 => if j = 0 then (0 : Fin 3) else 2) := by
    ext j
    fin_cases j <;> rfl
  rw [hδ, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_zero (by
    intro b hb
    fin_cases b <;> simp at hb)

open CategoryTheory in
/-- On the side face `δ₁ : Δ¹ → Δ²`, the coordinate `x₂` is the terminal
`Δ¹` barycentric coordinate. -/
theorem faceMap_one_coord_two (x : stdSimplex ℝ (Fin 2)) :
    ((faceMap (1 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = x 1 := by
  rw [faceMap_apply]
  change FunOnFinite.linearMap ℝ ℝ
      ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 3))) : Fin 2 → Fin 3) x 2 = x 1
  have hδ :
      ((ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 3))) : Fin 2 → Fin 3) =
        (fun j : Fin 2 => if j = 0 then (0 : Fin 3) else 2) := by
    ext j
    fin_cases j <;> rfl
  rw [hδ, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_single (1 : Fin 2)
    (by
      intro b hb hbne
      fin_cases b <;> simp at hb hbne)
    (by
      intro hnot
      simp at hnot)

/-- The `i`-th face of a singular `2`-simplex, as a singular `1`-simplex. -/
def face (F : TwoSimplex) (i : Fin 3) : OneSimplex := F.comp (faceMap i)

/-- The geometric edge of `Δ²` selected by the `i`-th face map, as a continuous
map from the unit interval. -/
def simplexEdge (i : Fin 3) : C(I, stdSimplex ℝ (Fin 3)) := (faceMap i).comp intervalToSimplex

@[simp] theorem simplexEdge_apply (i : Fin 3) (t : I) :
    simplexEdge i t = faceMap i (intervalToSimplex t) := rfl

/-- Vertex `k` of the standard `2`-simplex. -/
abbrev V (k : Fin 3) : stdSimplex ℝ (Fin 3) := stdSimplex.vertex k

theorem simplexEdge_zero (i : Fin 3) :
    simplexEdge i 0 = stdSimplex.vertex (ConcreteCategory.hom (SimplexCategory.δ i) 0) := by
  rw [simplexEdge_apply, intervalToSimplex_zero, faceMap_apply, stdSimplex.map_vertex]

theorem simplexEdge_one (i : Fin 3) :
    simplexEdge i 1 = stdSimplex.vertex (ConcreteCategory.hom (SimplexCategory.δ i) 1) := by
  rw [simplexEdge_apply, intervalToSimplex_one, faceMap_apply, stdSimplex.map_vertex]

/-- The edge `v₀ → v₁` of `Δ²`, realised by the face map `δ 2`. -/
def edge01 : Path (V 0) (V 1) where
  toContinuousMap := simplexEdge 2
  source' := by show simplexEdge 2 0 = V 0; rw [simplexEdge_zero]; congr 1
  target' := by show simplexEdge 2 1 = V 1; rw [simplexEdge_one]; congr 1

/-- The edge `v₁ → v₂` of `Δ²`, realised by the face map `δ 0`. -/
def edge12 : Path (V 1) (V 2) where
  toContinuousMap := simplexEdge 0
  source' := by show simplexEdge 0 0 = V 1; rw [simplexEdge_zero]; congr 1
  target' := by show simplexEdge 0 1 = V 2; rw [simplexEdge_one]; congr 1

/-- The edge `v₀ → v₂` of `Δ²`, realised by the face map `δ 1`. -/
def edge02 : Path (V 0) (V 2) where
  toContinuousMap := simplexEdge 1
  source' := by show simplexEdge 1 0 = V 0; rw [simplexEdge_zero]; congr 1
  target' := by show simplexEdge 1 1 = V 2; rw [simplexEdge_one]; congr 1

/-- Reading the face `δᵢF` in the unit-interval parameterisation is the same as
composing `F` with the geometric edge `simplexEdge i`. -/
theorem oneSimplexPath_face (F : TwoSimplex) (i : Fin 3) :
    oneSimplexPath (face F i) = F.comp (simplexEdge i) := by
  ext t; rfl

/-- The face displacement equals the displacement of the edge path pushed through
`F`.  This is the bridge between the singular-simplex face and the geometric
edge used in the telescoping. -/
theorem simplexDisplacement_face (F : TwoSimplex) (i : Fin 3)
    {a b : stdSimplex ℝ (Fin 3)} (e : Path a b) (he : e.toContinuousMap = simplexEdge i) :
    simplexDisplacement (face F i) = pathDisplacement ((e.map F.continuous) : C(I, SphereOne)) := by
  rw [simplexDisplacement, oneSimplexPath_face]
  congr 1
  ext t
  show F (simplexEdge i t) = F (e t)
  rw [← he]; rfl

/-- **The winding invariant kills boundaries.**  For every singular `2`-simplex
`F`, the alternating sum of the displacements of its three faces vanishes.  This
is the `2`-simplex telescoping: the broken boundary walk is homotopic rel
endpoints, inside the simply connected standard `2`-simplex, to the direct edge. -/
theorem simplexDisplacement_boundary (F : TwoSimplex) :
    simplexDisplacement (face F 0) - simplexDisplacement (face F 1)
      + simplexDisplacement (face F 2) = 0 := by
  haveI : SimplyConnectedSpace (stdSimplex ℝ (Fin 3)) :=
    CircleLifting.stdSimplex_simplyConnectedSpace 3
  -- The broken walk `v₀ → v₁ → v₂` and the direct edge `v₀ → v₂` are homotopic
  -- rel endpoints in the simply connected standard `2`-simplex.
  have hhom : (edge01.trans edge12).Homotopic edge02 :=
    SimplyConnectedSpace.paths_homotopic _ _
  -- Push the homotopy through `F`.
  have hmap := hhom.map F
  rw [Path.map_trans] at hmap
  -- Convert to a `HomotopicRel` between the corresponding maps `I → S¹`.
  have hrel : ((edge01.map F.continuous).trans (edge12.map F.continuous) : C(I, SphereOne)).HomotopicRel
      ((edge02.map F.continuous) : C(I, SphereOne)) {0, 1} := by
    obtain ⟨H⟩ := hmap
    exact ⟨H⟩
  -- Homotopy invariance + additivity of the displacement give the telescoping.
  have htel : pathDisplacement ((edge02.map F.continuous) : C(I, SphereOne))
      = pathDisplacement ((edge01.map F.continuous) : C(I, SphereOne))
        + pathDisplacement ((edge12.map F.continuous) : C(I, SphereOne)) := by
    rw [← pathDisplacement_homotopic hrel,
      pathDisplacement_trans (edge01.map F.continuous) (edge12.map F.continuous)]
  -- Identify each face displacement with the corresponding edge displacement.
  have h2 : simplexDisplacement (face F 2)
      = pathDisplacement ((edge01.map F.continuous) : C(I, SphereOne)) :=
    simplexDisplacement_face F 2 edge01 rfl
  have h0 : simplexDisplacement (face F 0)
      = pathDisplacement ((edge12.map F.continuous) : C(I, SphereOne)) :=
    simplexDisplacement_face F 0 edge12 rfl
  have h1 : simplexDisplacement (face F 1)
      = pathDisplacement ((edge02.map F.continuous) : C(I, SphereOne)) :=
    simplexDisplacement_face F 1 edge02 rfl
  rw [h0, h1, h2, htel]; ring

/-- The winding form of the kills-boundaries identity: the alternating face sum of
the winding numbers of a singular `2`-simplex vanishes. -/
theorem simplexWinding_boundary (F : TwoSimplex) :
    simplexWinding (face F 0) - simplexWinding (face F 1) + simplexWinding (face F 2) = 0 := by
  simp only [simplexWinding]
  have hb := simplexDisplacement_boundary F
  linear_combination hb / (2 * Real.pi)

/-- The second barycentric coordinate of `intervalToSimplex t` is `t` itself.
This is the affine reparameterisation `t ↦ (1 - t, t)`. -/
theorem intervalToSimplex_coord_one (t : I) :
    ((intervalToSimplex t : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 = (t : ℝ) := rfl

/-- Barycentric base parameter for coning a closed edge over the apex `v₂`.
Away from the apex it is `x₁ / (1 - x₂)`, i.e. the normalized coordinate along
the base edge `v₀ → v₁`; at the apex the value is set to `0`.  The eventual
zero-winding cone filler will feed this parameter into the lifted edge path and
multiply by `1 - x₂` to get continuity at the apex. -/
noncomputable def coneBaseParam (x : stdSimplex ℝ (Fin 3)) : I :=
  if h : x 2 = (1 : ℝ) then 0 else
    ⟨x 1 / (1 - x 2), by
      have hx1nonneg : 0 ≤ x 1 := (mem_Icc_of_mem_stdSimplex x.2 1).1
      have hx2le : x 2 ≤ (1 : ℝ) := (mem_Icc_of_mem_stdSimplex x.2 2).2
      have hx2lt : x 2 < (1 : ℝ) := lt_of_le_of_ne hx2le h
      have hdenpos : 0 < 1 - x 2 := sub_pos.mpr hx2lt
      constructor
      · exact div_nonneg hx1nonneg (le_of_lt hdenpos)
      · rw [div_le_one hdenpos]
        have hsum : x 0 + x 1 + x 2 = (1 : ℝ) := by
          have hsum := stdSimplex.sum_eq_one x
          rw [Fin.sum_univ_three] at hsum
          exact hsum
        have hx0nonneg : 0 ≤ x 0 := (mem_Icc_of_mem_stdSimplex x.2 0).1
        linarith
    ⟩

/-- If `x₂ ≠ 1`, the cone base parameter is the expected normalized barycentric
coordinate `x₁ / (1 - x₂)`. -/
theorem coneBaseParam_coe_of_coord_two_ne_one (x : stdSimplex ℝ (Fin 3))
    (h : x 2 ≠ (1 : ℝ)) :
    (coneBaseParam x : ℝ) = x 1 / (1 - x 2) := by
  simp [coneBaseParam, h]

/-- Away from the apex `x₂ = 1`, the real-valued cone base parameter is
continuous.  The remaining non-apex continuity of `coneCirclePoint` is therefore
only the standard subtype-continuity wrapper for feeding this parameter into
`pathLift`. -/
theorem continuousAt_coneBaseParam_coe_of_coord_two_ne_one
    (x : stdSimplex ℝ (Fin 3)) (h : x 2 ≠ (1 : ℝ)) :
    ContinuousAt (fun y : stdSimplex ℝ (Fin 3) => (coneBaseParam y : ℝ)) x := by
  let raw : stdSimplex ℝ (Fin 3) → ℝ := fun y => y 1 / (1 - y 2)
  have hc1 : ContinuousAt (fun y : stdSimplex ℝ (Fin 3) => y 1) x :=
    ((continuous_apply 1).comp continuous_subtype_val).continuousAt
  have hc2 : ContinuousAt (fun y : stdSimplex ℝ (Fin 3) => y 2) x :=
    ((continuous_apply 2).comp continuous_subtype_val).continuousAt
  have hraw : ContinuousAt raw x := by
    apply ContinuousAt.div
    · exact hc1
    · exact continuousAt_const.sub hc2
    · exact sub_ne_zero.mpr h.symm
  apply hraw.congr_of_eventuallyEq
  have hcoord_cont : Continuous (fun y : stdSimplex ℝ (Fin 3) => y 2) :=
    (continuous_apply 2).comp continuous_subtype_val
  filter_upwards [hcoord_cont.continuousAt.eventually (isOpen_ne.mem_nhds h)] with y hy
  unfold raw
  exact coneBaseParam_coe_of_coord_two_ne_one y hy

/-- Away from the apex, the cone base parameter is continuous as an
`I`-valued function, not merely after coercion to `ℝ`. -/
theorem continuousAt_coneBaseParam_of_coord_two_ne_one
    (x : stdSimplex ℝ (Fin 3)) (h : x 2 ≠ (1 : ℝ)) :
    ContinuousAt coneBaseParam x := by
  rw [ContinuousAt]
  rw [tendsto_subtype_rng]
  exact continuousAt_coneBaseParam_coe_of_coord_two_ne_one x h

/-- On the base face `δ₂`, the cone base parameter is exactly the original
`Δ¹` coordinate. -/
theorem coneBaseParam_faceMap_two_coe (x : stdSimplex ℝ (Fin 2)) :
    (coneBaseParam (faceMap (2 : Fin 3) x) : ℝ) = x 1 := by
  rw [coneBaseParam_coe_of_coord_two_ne_one]
  · rw [faceMap_two_coord_one, faceMap_two_coord_two]
    ring
  · rw [faceMap_two_coord_two]
    norm_num

/-- Along the actual geometric base edge `v₀ → v₁`, the cone base parameter is
the unit-interval parameter. -/
theorem coneBaseParam_simplexEdge_two_coe (t : I) :
    (coneBaseParam (simplexEdge (2 : Fin 3) t) : ℝ) = (t : ℝ) := by
  rw [simplexEdge_apply, coneBaseParam_faceMap_two_coe, intervalToSimplex_coord_one]

/-- On the side face `δ₀`, away from the apex, the cone base parameter is `1`.
In the lifted cone formula this side therefore evaluates at the terminal endpoint
of the original closed edge. -/
theorem coneBaseParam_faceMap_zero_coe_of_not_apex (x : stdSimplex ℝ (Fin 2))
    (h : x 1 ≠ (1 : ℝ)) :
    (coneBaseParam (faceMap (0 : Fin 3) x) : ℝ) = 1 := by
  rw [coneBaseParam_coe_of_coord_two_ne_one]
  · rw [faceMap_zero_coord_one, faceMap_zero_coord_two]
    have hsum : x 0 + x 1 = (1 : ℝ) := by
      have hsum := stdSimplex.sum_eq_one x
      rw [Fin.sum_univ_two] at hsum
      exact hsum
    have hx0 : x 0 = 1 - x 1 := by linarith
    rw [hx0]
    exact div_self (sub_ne_zero.mpr h.symm)
  · rw [faceMap_zero_coord_two]
    exact h

/-- On the side face `δ₁`, away from the apex, the cone base parameter is `0`.
This is the initial-endpoint side of the lifted cone formula. -/
theorem coneBaseParam_faceMap_one_coe_of_not_apex (x : stdSimplex ℝ (Fin 2))
    (h : x 1 ≠ (1 : ℝ)) :
    (coneBaseParam (faceMap (1 : Fin 3) x) : ℝ) = 0 := by
  rw [coneBaseParam_coe_of_coord_two_ne_one]
  · rw [faceMap_one_coord_one]
    simp
  · rw [faceMap_one_coord_two]
    exact h

/-- The real lifted angle used by the cone filler for a closed zero-winding edge.
It contracts the lifted edge radially toward the apex value.  The only remaining
hard analysis is continuity at the apex, where `coneBaseParam` itself is not
continuous but the prefactor `1 - x₂` vanishes. -/
noncomputable def coneLiftAngle (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 3)) : ℝ :=
  (1 - x 2) * pathLift γ (coneBaseParam x) + x 2 * pathLift γ 0

/-- Shifted form of the lifted cone angle.  This isolates the vanishing factor
`1 - x₂` at the apex. -/
theorem coneLiftAngle_sub_start
    (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 3)) :
    coneLiftAngle γ x - pathLift γ 0 =
      (1 - x 2) * (pathLift γ (coneBaseParam x) - pathLift γ 0) := by
  unfold coneLiftAngle
  ring

/-- Uniform apex estimate for the lifted cone angle.  If the shifted lift is
bounded by `C`, then the distance from the cone angle to the apex angle is at
most `(1 - x₂) * C`.  Since `1 - x₂ → 0` at the apex, this is the squeeze
estimate that remains to be fed into the final continuity proof. -/
theorem norm_coneLiftAngle_sub_start_le
    (γ : C(I, SphereOne)) (C : ℝ)
    (hC : ∀ t : I, ‖pathLift γ t - pathLift γ 0‖ ≤ C)
    (x : stdSimplex ℝ (Fin 3)) :
    ‖coneLiftAngle γ x - pathLift γ 0‖ ≤ (1 - x 2) * C := by
  rw [coneLiftAngle_sub_start]
  have hnonneg : 0 ≤ 1 - x 2 := by
    have hx2le : x 2 ≤ (1 : ℝ) := (mem_Icc_of_mem_stdSimplex x.2 2).2
    linarith
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_left (hC (coneBaseParam x)) hnonneg

/-- The lifted cone angle tends to the apex lift value at the cone apex.  This is
the analytic heart of the cone construction: compactness bounds the shifted lift,
and the barycentric factor `1 - x₂` squeezes the shifted term to zero. -/
theorem coneLiftAngle_tendsto_apex (γ : C(I, SphereOne)) :
    Filter.Tendsto (coneLiftAngle γ) (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 (pathLift γ 0)) := by
  obtain ⟨C, hC⟩ := pathLift_shifted_exists_norm_bound γ
  have hbound : ∀ x : stdSimplex ℝ (Fin 3),
      ‖coneLiftAngle γ x - pathLift γ 0‖ ≤ (1 - x 2) * C :=
    norm_coneLiftAngle_sub_start_le γ C hC
  have hscale : Filter.Tendsto (fun x : stdSimplex ℝ (Fin 3) => (1 - x 2) * C)
      (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 0) := by
    have hx2 : Filter.Tendsto (fun x : stdSimplex ℝ (Fin 3) => x 2)
        (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 (1 : ℝ)) := by
      have hc : Continuous (fun x : stdSimplex ℝ (Fin 3) => x 2) :=
        (continuous_apply 2).comp continuous_subtype_val
      exact hc.tendsto (stdSimplex.vertex (2 : Fin 3))
    have hsub : Filter.Tendsto (fun x : stdSimplex ℝ (Fin 3) => 1 - x 2)
        (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 (0 : ℝ)) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hx2
      simpa using h
    have hmul := hsub.mul (tendsto_const_nhds (x := C))
    simpa using hmul
  have hdiff : Filter.Tendsto (fun x : stdSimplex ℝ (Fin 3) => coneLiftAngle γ x - pathLift γ 0)
      (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 0) := by
    exact squeeze_zero_norm hbound hscale
  have hnorm : Filter.Tendsto (fun x : stdSimplex ℝ (Fin 3) => ‖coneLiftAngle γ x - pathLift γ 0‖)
      (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 0) := by
    simpa using hdiff.norm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Away from the apex, the lifted cone angle is continuous by ordinary
coordinate arithmetic and continuity of the lifted path. -/
theorem continuousAt_coneLiftAngle_of_coord_two_ne_one
    (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 3)) (h : x 2 ≠ (1 : ℝ)) :
    ContinuousAt (coneLiftAngle γ) x := by
  unfold coneLiftAngle
  have hparam : ContinuousAt coneBaseParam x :=
    continuousAt_coneBaseParam_of_coord_two_ne_one x h
  have hpath :
      ContinuousAt (fun y : stdSimplex ℝ (Fin 3) => pathLift γ (coneBaseParam y)) x :=
    (pathLift γ).continuous.continuousAt.comp hparam
  have hc2 : ContinuousAt (fun y : stdSimplex ℝ (Fin 3) => y 2) x :=
    ((continuous_apply 2).comp continuous_subtype_val).continuousAt
  exact ((continuousAt_const.sub hc2).mul hpath).add (hc2.mul continuousAt_const)

/-- On the base edge of the cone, the lifted cone angle is the original lifted
path. -/
theorem coneLiftAngle_simplexEdge_two (γ : C(I, SphereOne)) (t : I) :
    coneLiftAngle γ (simplexEdge (2 : Fin 3) t) = pathLift γ t := by
  unfold coneLiftAngle
  have h2 : ((simplexEdge (2 : Fin 3) t : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = 0 := by
    rw [simplexEdge_apply, faceMap_two_coord_two]
  have hp : coneBaseParam (simplexEdge (2 : Fin 3) t) = t := by
    ext
    exact coneBaseParam_simplexEdge_two_coe t
  rw [h2, hp]
  ring

/-- On the `δ₁` side of the cone, the lifted cone angle is constantly the initial
lift value. -/
theorem coneLiftAngle_simplexEdge_one (γ : C(I, SphereOne)) (t : I) :
    coneLiftAngle γ (simplexEdge (1 : Fin 3) t) = pathLift γ 0 := by
  unfold coneLiftAngle
  have h2 : ((simplexEdge (1 : Fin 3) t : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = (t : ℝ) := by
    rw [simplexEdge_apply, faceMap_one_coord_two, intervalToSimplex_coord_one]
  rw [h2]
  by_cases ht : (t : ℝ) = 1
  · have htI : t = (1 : I) := by
      ext
      exact ht
    subst t
    simp [coneBaseParam]
  · have hparam : (coneBaseParam (simplexEdge (1 : Fin 3) t) : ℝ) = 0 := by
      rw [simplexEdge_apply]
      apply coneBaseParam_faceMap_one_coe_of_not_apex
      intro h1
      have : (t : ℝ) = 1 := by
        rw [← intervalToSimplex_coord_one t]
        exact h1
      exact ht this
    have hp : coneBaseParam (simplexEdge (1 : Fin 3) t) = (0 : I) := by
      ext
      exact hparam
    rw [hp]
    ring

/-- On the `δ₀` side of a zero-winding closed cone, the lifted cone angle is also
constant.  The hypothesis is exactly the lifted endpoint equality forced by zero
winding. -/
theorem coneLiftAngle_simplexEdge_zero_of_lift_endpoint_eq
    (γ : C(I, SphereOne)) (hlift : pathLift γ 1 = pathLift γ 0) (t : I) :
    coneLiftAngle γ (simplexEdge (0 : Fin 3) t) = pathLift γ 0 := by
  unfold coneLiftAngle
  have h2 : ((simplexEdge (0 : Fin 3) t : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = (t : ℝ) := by
    rw [simplexEdge_apply, faceMap_zero_coord_two, intervalToSimplex_coord_one]
  rw [h2]
  by_cases ht : (t : ℝ) = 1
  · have htI : t = (1 : I) := by
      ext
      exact ht
    subst t
    simp [coneBaseParam]
  · have hparam : (coneBaseParam (simplexEdge (0 : Fin 3) t) : ℝ) = 1 := by
      rw [simplexEdge_apply]
      apply coneBaseParam_faceMap_zero_coe_of_not_apex
      intro h1
      have : (t : ℝ) = 1 := by
        rw [← intervalToSimplex_coord_one t]
        exact h1
      exact ht this
    have hp : coneBaseParam (simplexEdge (0 : Fin 3) t) = (1 : I) := by
      ext
      exact hparam
    rw [hp, hlift]
    ring

/-- The pointwise `S¹` cone obtained by projecting the lifted cone angle through
the circle cover.  This is not yet packaged as a `ContinuousMap`; the next
frontier is proving continuity at the apex. -/
def coneCirclePoint (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 3)) : SphereOne :=
  trigCirclePoint (coneLiftAngle γ x)

/-- The pointwise `S¹` cone tends to the basepoint at the apex. -/
theorem coneCirclePoint_tendsto_apex (γ : C(I, SphereOne)) :
    Filter.Tendsto (coneCirclePoint γ) (𝓝 (stdSimplex.vertex (2 : Fin 3))) (𝓝 (γ 0)) := by
  have htrig := continuous_trigCirclePoint.tendsto (pathLift γ 0)
  have ht := htrig.comp (coneLiftAngle_tendsto_apex γ)
  have h0 : trigCirclePoint (pathLift γ 0) = γ 0 := by
    exact congrFun (pathLift_lifts γ) 0
  rw [h0] at ht
  exact ht

/-- The pointwise `S¹` cone is continuous at the apex.  Away from the apex the
remaining continuity is ordinary quotient-coordinate continuity; the apex was
the only singular analytic point. -/
theorem continuousAt_coneCirclePoint_apex (γ : C(I, SphereOne)) :
    ContinuousAt (coneCirclePoint γ) (stdSimplex.vertex (2 : Fin 3)) := by
  change Filter.Tendsto (coneCirclePoint γ) (𝓝 (stdSimplex.vertex (2 : Fin 3)))
    (𝓝 (coneCirclePoint γ (stdSimplex.vertex (2 : Fin 3))))
  have hapex : coneCirclePoint γ (stdSimplex.vertex (2 : Fin 3)) = γ 0 := by
    unfold coneCirclePoint coneLiftAngle
    change trigCirclePoint
        ((1 - (1 : ℝ)) * pathLift γ (coneBaseParam (stdSimplex.vertex (2 : Fin 3))) +
          (1 : ℝ) * pathLift γ 0) = γ 0
    simp
    exact congrFun (pathLift_lifts γ) 0
  rw [hapex]
  exact coneCirclePoint_tendsto_apex γ

/-- Away from the apex, `coneCirclePoint` is continuous by composing the
non-apex continuity of `coneLiftAngle` with the circle covering map. -/
theorem continuousAt_coneCirclePoint_of_coord_two_ne_one
    (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 3)) (h : x 2 ≠ (1 : ℝ)) :
    ContinuousAt (coneCirclePoint γ) x := by
  unfold coneCirclePoint
  exact continuous_trigCirclePoint.continuousAt.comp
    (continuousAt_coneLiftAngle_of_coord_two_ne_one γ x h)

/-- In `Δ²`, the condition `x₂ = 1` forces the point to be the apex vertex
`v₂`. -/
theorem stdSimplex_eq_vertex_two_of_coord_two_eq_one
    (x : stdSimplex ℝ (Fin 3)) (h : x 2 = (1 : ℝ)) :
    x = stdSimplex.vertex (2 : Fin 3) := by
  ext i
  fin_cases i
  · have hsum : x 0 + x 1 + x 2 = (1 : ℝ) := by
      have hsum := stdSimplex.sum_eq_one x
      rw [Fin.sum_univ_three] at hsum
      exact hsum
    have hx0nonneg : 0 ≤ x 0 := (mem_Icc_of_mem_stdSimplex x.2 0).1
    have hx1nonneg : 0 ≤ x 1 := (mem_Icc_of_mem_stdSimplex x.2 1).1
    have hx0 : x 0 = 0 := by linarith
    simpa using hx0
  · have hsum : x 0 + x 1 + x 2 = (1 : ℝ) := by
      have hsum := stdSimplex.sum_eq_one x
      rw [Fin.sum_univ_three] at hsum
      exact hsum
    have hx0nonneg : 0 ≤ x 0 := (mem_Icc_of_mem_stdSimplex x.2 0).1
    have hx1nonneg : 0 ≤ x 1 := (mem_Icc_of_mem_stdSimplex x.2 1).1
    have hx1 : x 1 = 0 := by linarith
    simpa using hx1
  · simpa using h

/-- The pointwise cone is a continuous map `Δ² → S¹`.  This closes the analytic
packaging gap left after the pointwise cone identities: non-apex continuity is
ordinary coordinate continuity, and the apex is handled by the squeeze theorem
above. -/
theorem continuous_coneCirclePoint (γ : C(I, SphereOne)) :
    Continuous (coneCirclePoint γ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : x 2 = (1 : ℝ)
  · rw [stdSimplex_eq_vertex_two_of_coord_two_eq_one x h]
    exact continuousAt_coneCirclePoint_apex γ
  · exact continuousAt_coneCirclePoint_of_coord_two_ne_one γ x h

/-- The pointwise cone restricts to the original path on the base edge. -/
theorem coneCirclePoint_simplexEdge_two (γ : C(I, SphereOne)) (t : I) :
    coneCirclePoint γ (simplexEdge (2 : Fin 3) t) = γ t := by
  unfold coneCirclePoint
  rw [coneLiftAngle_simplexEdge_two]
  exact congrFun (pathLift_lifts γ) t

/-- The pointwise cone is constant on the `δ₁` side. -/
theorem coneCirclePoint_simplexEdge_one (γ : C(I, SphereOne)) (t : I) :
    coneCirclePoint γ (simplexEdge (1 : Fin 3) t) = γ 0 := by
  unfold coneCirclePoint
  rw [coneLiftAngle_simplexEdge_one]
  exact congrFun (pathLift_lifts γ) 0

/-- The pointwise cone is constant on the `δ₀` side once the lifted endpoints
agree, which is the zero-winding condition in lifted form. -/
theorem coneCirclePoint_simplexEdge_zero_of_lift_endpoint_eq
    (γ : C(I, SphereOne)) (hlift : pathLift γ 1 = pathLift γ 0) (t : I) :
    coneCirclePoint γ (simplexEdge (0 : Fin 3) t) = γ 0 := by
  unfold coneCirclePoint
  rw [coneLiftAngle_simplexEdge_zero_of_lift_endpoint_eq γ hlift]
  exact congrFun (pathLift_lifts γ) 0

/-- Arbitrary-base-face version of `coneLiftAngle_simplexEdge_two`: on the whole
base face `δ₂`, the lifted cone angle agrees with the lifted edge after the
standard `Δ¹ ≃ I` reparameterisation. -/
theorem coneLiftAngle_faceMap_two_of_oneSimplex (f : OneSimplex)
    (x : stdSimplex ℝ (Fin 2)) :
    coneLiftAngle (oneSimplexPath f) (faceMap (2 : Fin 3) x) =
      pathLift (oneSimplexPath f) (stdSimplexHomeomorphUnitInterval x) := by
  unfold coneLiftAngle
  have h2 : ((faceMap (2 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = 0 :=
    faceMap_two_coord_two x
  have hp : coneBaseParam (faceMap (2 : Fin 3) x) = stdSimplexHomeomorphUnitInterval x := by
    ext
    exact coneBaseParam_faceMap_two_coe x
  rw [h2, hp]
  ring

/-- Path-parametric base-face version: on `δ₂`, the lifted cone angle agrees with
the lifted path. -/
theorem coneLiftAngle_faceMap_two (γ : C(I, SphereOne))
    (x : stdSimplex ℝ (Fin 2)) :
    coneLiftAngle γ (faceMap (2 : Fin 3) x) =
      pathLift γ (stdSimplexHomeomorphUnitInterval x) := by
  unfold coneLiftAngle
  have h2 : ((faceMap (2 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = 0 :=
    faceMap_two_coord_two x
  have hp : coneBaseParam (faceMap (2 : Fin 3) x) = stdSimplexHomeomorphUnitInterval x := by
    ext
    exact coneBaseParam_faceMap_two_coe x
  rw [h2, hp]
  ring

/-- Pointwise base-face restriction for the cone: after projection to `S¹`, the
base face is exactly the original concrete singular edge. -/
theorem coneCirclePoint_faceMap_two_of_oneSimplex (f : OneSimplex)
    (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint (oneSimplexPath f) (faceMap (2 : Fin 3) x) = f x := by
  unfold coneCirclePoint
  rw [coneLiftAngle_faceMap_two_of_oneSimplex]
  have htrig :
      trigCirclePoint (pathLift (oneSimplexPath f) (stdSimplexHomeomorphUnitInterval x)) =
        (oneSimplexPath f) (stdSimplexHomeomorphUnitInterval x) := by
    simpa [Function.comp_apply] using
      congrFun (pathLift_lifts (oneSimplexPath f)) (stdSimplexHomeomorphUnitInterval x)
  rw [htrig]
  unfold oneSimplexPath
  simp [intervalToSimplex]

/-- Path-parametric base-face restriction for the cone. -/
theorem coneCirclePoint_faceMap_two (γ : C(I, SphereOne))
    (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint γ (faceMap (2 : Fin 3) x) = oneSimplexOfPath γ x := by
  unfold coneCirclePoint oneSimplexOfPath
  rw [coneLiftAngle_faceMap_two]
  exact congrFun (pathLift_lifts γ) (stdSimplexHomeomorphUnitInterval x)

/-- Arbitrary-side-face version for `δ₁`: the lifted cone angle is constant on
the whole side face. -/
theorem coneLiftAngle_faceMap_one (γ : C(I, SphereOne))
    (x : stdSimplex ℝ (Fin 2)) :
    coneLiftAngle γ (faceMap (1 : Fin 3) x) = pathLift γ 0 := by
  unfold coneLiftAngle
  have h2 : ((faceMap (1 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = x 1 :=
    faceMap_one_coord_two x
  rw [h2]
  by_cases hx : x 1 = (1 : ℝ)
  · rw [hx]
    simp
  · have hparam : (coneBaseParam (faceMap (1 : Fin 3) x) : ℝ) = 0 :=
      coneBaseParam_faceMap_one_coe_of_not_apex x hx
    have hp : coneBaseParam (faceMap (1 : Fin 3) x) = (0 : I) := by
      ext
      exact hparam
    rw [hp]
    ring

/-- Arbitrary-side-face version for `δ₀`: the lifted cone angle is constant on
the whole side face once the lifted endpoints agree. -/
theorem coneLiftAngle_faceMap_zero_of_lift_endpoint_eq
    (γ : C(I, SphereOne)) (hlift : pathLift γ 1 = pathLift γ 0)
    (x : stdSimplex ℝ (Fin 2)) :
    coneLiftAngle γ (faceMap (0 : Fin 3) x) = pathLift γ 0 := by
  unfold coneLiftAngle
  have h2 : ((faceMap (0 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = x 1 :=
    faceMap_zero_coord_two x
  rw [h2]
  by_cases hx : x 1 = (1 : ℝ)
  · rw [hx]
    simp
  · have hparam : (coneBaseParam (faceMap (0 : Fin 3) x) : ℝ) = 1 :=
      coneBaseParam_faceMap_zero_coe_of_not_apex x hx
    have hp : coneBaseParam (faceMap (0 : Fin 3) x) = (1 : I) := by
      ext
      exact hparam
    rw [hp, hlift]
    ring

/-- Arbitrary-side-face formula for `δ₀` without closing the edge.  This is the
terminal-return side of the cone: it linearly joins the terminal lift of the edge
back to its initial lift. -/
theorem coneLiftAngle_faceMap_zero
    (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 2)) :
    coneLiftAngle γ (faceMap (0 : Fin 3) x) =
      (1 - x 1) * pathLift γ 1 + x 1 * pathLift γ 0 := by
  unfold coneLiftAngle
  have h2 : ((faceMap (0 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 2 = x 1 :=
    faceMap_zero_coord_two x
  rw [h2]
  by_cases hx : x 1 = (1 : ℝ)
  · rw [hx]
    simp
  · have hparam : (coneBaseParam (faceMap (0 : Fin 3) x) : ℝ) = 1 :=
      coneBaseParam_faceMap_zero_coe_of_not_apex x hx
    have hp : coneBaseParam (faceMap (0 : Fin 3) x) = (1 : I) := by
      ext
      exact hparam
    rw [hp]

/-- The concrete terminal-return side of the cone over a path. -/
noncomputable def coneTerminalSide (γ : C(I, SphereOne)) : OneSimplex where
  toFun x := trigCirclePoint ((1 - x 1) * pathLift γ 1 + x 1 * pathLift γ 0)
  continuous_toFun := by
    have hc1 : Continuous (fun x : stdSimplex ℝ (Fin 2) => x 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    exact continuous_trigCirclePoint.comp
      (((continuous_const.sub hc1).mul continuous_const).add (hc1.mul continuous_const))

/-- The concrete constant singular edge at a point of the circle. -/
def constantOneSimplex (p : SphereOne) : OneSimplex :=
  ContinuousMap.const (stdSimplex ℝ (Fin 2)) p

/-- If the lifted endpoints of the base path agree, the terminal-return side of
the cone collapses to the constant apex edge. -/
theorem coneTerminalSide_eq_constantOneSimplex_of_lift_endpoint_eq
    (γ : C(I, SphereOne)) (hlift : pathLift γ 1 = pathLift γ 0) :
    coneTerminalSide γ = constantOneSimplex (γ 0) := by
  ext x
  change trigCirclePoint ((1 - x 1) * pathLift γ 1 + x 1 * pathLift γ 0) = γ 0
  rw [hlift]
  have h : (1 - x 1) * pathLift γ 0 + x 1 * pathLift γ 0 = pathLift γ 0 := by
    ring
  rw [h]
  exact congrFun (pathLift_lifts γ) 0

/-- Zero winding collapses the terminal-return side of the cone over a singular
edge to the constant apex edge. -/
theorem coneTerminalSide_eq_constantOneSimplex_of_simplexWinding_zero
    (f : OneSimplex) (hzero : simplexWinding f = 0) :
    coneTerminalSide (oneSimplexPath f) =
      constantOneSimplex ((oneSimplexPath f) 0) := by
  have hlift : pathLift (oneSimplexPath f) 1 = pathLift (oneSimplexPath f) 0 := by
    apply pathLift_endpoint_eq_of_winding_zero
    simpa [simplexWinding, simplexDisplacement, pathWinding] using hzero
  exact coneTerminalSide_eq_constantOneSimplex_of_lift_endpoint_eq (oneSimplexPath f) hlift

/-- Pointwise `S¹` side restriction for `δ₁`: the cone is constant on this side. -/
theorem coneCirclePoint_faceMap_one (γ : C(I, SphereOne))
    (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint γ (faceMap (1 : Fin 3) x) = γ 0 := by
  unfold coneCirclePoint
  rw [coneLiftAngle_faceMap_one]
  exact congrFun (pathLift_lifts γ) 0

/-- Pointwise `S¹` side restriction for `δ₀` under lifted endpoint equality. -/
theorem coneCirclePoint_faceMap_zero_of_lift_endpoint_eq
    (γ : C(I, SphereOne)) (hlift : pathLift γ 1 = pathLift γ 0)
    (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint γ (faceMap (0 : Fin 3) x) = γ 0 := by
  unfold coneCirclePoint
  rw [coneLiftAngle_faceMap_zero_of_lift_endpoint_eq γ hlift]
  exact congrFun (pathLift_lifts γ) 0

/-- Pointwise `S¹` side restriction for `δ₀` without the zero-winding endpoint
equality: the face is the terminal-return side of the cone. -/
theorem coneCirclePoint_faceMap_zero
    (γ : C(I, SphereOne)) (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint γ (faceMap (0 : Fin 3) x) = coneTerminalSide γ x := by
  unfold coneCirclePoint coneTerminalSide
  rw [coneLiftAngle_faceMap_zero]
  rfl

/-- The two side faces of the pointwise cone agree once the lifted endpoints of
the base path agree.  This is the pointwise form of the future face equation
`face F 0 = face F 1`. -/
theorem coneCirclePoint_side_faces_eq_of_lift_endpoint_eq
    (γ : C(I, SphereOne)) (hlift : pathLift γ 1 = pathLift γ 0)
    (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint γ (faceMap (0 : Fin 3) x) =
      coneCirclePoint γ (faceMap (1 : Fin 3) x) := by
  rw [coneCirclePoint_faceMap_zero_of_lift_endpoint_eq γ hlift,
    coneCirclePoint_faceMap_one γ]

/-- Zero-winding form of the pointwise side-face equality for the cone. -/
theorem coneCirclePoint_side_faces_eq_of_winding_zero
    (γ : C(I, SphereOne)) (hw : pathWinding γ = 0)
    (x : stdSimplex ℝ (Fin 2)) :
    coneCirclePoint γ (faceMap (0 : Fin 3) x) =
      coneCirclePoint γ (faceMap (1 : Fin 3) x) :=
  coneCirclePoint_side_faces_eq_of_lift_endpoint_eq γ
    (pathLift_endpoint_eq_of_winding_zero γ hw) x

/-- Package the pointwise cone as a concrete singular `2`-simplex once its
continuity has been proved.  This definition deliberately isolates the only
remaining analytic obligation: continuity of `coneCirclePoint` at the apex. -/
def coneCircleMapOfContinuous (γ : C(I, SphereOne))
    (hcont : Continuous (coneCirclePoint γ)) : TwoSimplex where
  toFun := coneCirclePoint γ
  continuous_toFun := hcont

/-- If the pointwise zero-winding cone is continuous, then its base face is the
original singular edge. -/
theorem coneCircleMapOfContinuous_face_two (f : OneSimplex)
    (hcont : Continuous (coneCirclePoint (oneSimplexPath f))) :
    face (coneCircleMapOfContinuous (oneSimplexPath f) hcont) (2 : Fin 3) = f := by
  ext x
  exact coneCirclePoint_faceMap_two_of_oneSimplex f x

/-- Path-parametric base face of the cone. -/
theorem coneCircleMapOfContinuous_face_two_path (γ : C(I, SphereOne))
    (hcont : Continuous (coneCirclePoint γ)) :
    face (coneCircleMapOfContinuous γ hcont) (2 : Fin 3) = oneSimplexOfPath γ := by
  ext x
  change coneCirclePoint γ (faceMap (2 : Fin 3) x) = oneSimplexOfPath γ x
  exact coneCirclePoint_faceMap_two γ x

/-- The `δ₀` face of the cone is the terminal-return side.  This is the open-edge
face formula needed before side terms are cancelled in a multi-edge prism. -/
theorem coneCircleMapOfContinuous_face_zero (γ : C(I, SphereOne))
    (hcont : Continuous (coneCirclePoint γ)) :
    face (coneCircleMapOfContinuous γ hcont) (0 : Fin 3) = coneTerminalSide γ := by
  ext x
  exact coneCirclePoint_faceMap_zero γ x

/-- The `δ₁` face of the cone is the constant edge at the cone apex. -/
theorem coneCircleMapOfContinuous_face_one (γ : C(I, SphereOne))
    (hcont : Continuous (coneCirclePoint γ)) :
    face (coneCircleMapOfContinuous γ hcont) (1 : Fin 3) = constantOneSimplex (γ 0) := by
  ext x
  unfold constantOneSimplex
  exact coneCirclePoint_faceMap_one γ x

/-- If the pointwise zero-winding cone is continuous, then its two side faces
agree. -/
theorem coneCircleMapOfContinuous_side_faces_eq_of_winding_zero (f : OneSimplex)
    (hzero : simplexWinding f = 0)
    (hcont : Continuous (coneCirclePoint (oneSimplexPath f))) :
    face (coneCircleMapOfContinuous (oneSimplexPath f) hcont) (0 : Fin 3) =
      face (coneCircleMapOfContinuous (oneSimplexPath f) hcont) (1 : Fin 3) := by
  ext x
  exact coneCirclePoint_side_faces_eq_of_winding_zero (oneSimplexPath f) hzero x

/-- The fundamental singular `1`-simplex of `CircleFundamentalSimplex`, read in the
unit-interval parameterisation, is exactly the fundamental once-around loop. -/
theorem oneSimplexPath_fundamental :
    oneSimplexPath CircleFundamentalSimplex.fundamentalCirclePathMap = fundamentalLoop := by
  ext t
  show trigCirclePoint (2 * Real.pi * ((intervalToSimplex t : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1)
      = trigCirclePoint (2 * Real.pi * (t : ℝ))
  rw [intervalToSimplex_coord_one]

/-- **The displacement of the fundamental singular `1`-simplex is one full turn.** -/
theorem simplexDisplacement_fundamental :
    simplexDisplacement CircleFundamentalSimplex.fundamentalCirclePathMap = 2 * Real.pi := by
  rw [simplexDisplacement, oneSimplexPath_fundamental, pathDisplacement_fundamentalLoop]

/-- **The winding invariant is a left inverse to the fundamental class.**  The
winding number of the once-around fundamental singular `1`-simplex is `1`. -/
theorem simplexWinding_fundamental :
    simplexWinding CircleFundamentalSimplex.fundamentalCirclePathMap = 1 := by
  rw [simplexWinding, simplexDisplacement_fundamental]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp

/-- A singular `1`-simplex whose two endpoints agree has integer winding. -/
theorem simplexWinding_loop_integral (f : OneSimplex)
    (hloop : f (stdSimplex.vertex (1 : Fin 2)) = f (stdSimplex.vertex (0 : Fin 2))) :
    ∃ k : ℤ, simplexWinding f = (k : ℝ) := by
  unfold simplexWinding simplexDisplacement oneSimplexPath
  apply pathWinding_loop_integral
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, intervalToSimplex_one,
    intervalToSimplex_zero]
  exact hloop

/-- **Closed-walk winding integrality (path form).**  Let `f : Fin k → C(I,S¹)`
be a cyclically connected family of paths: the terminal point of `f i` is the
initial point of `f (finRotate k i)` for every `i` (so the family closes up into
a single loop).  Then the total displacement around the walk is an integer
multiple of `2π`.

This is the multi-edge generalization of `pathDisplacement_loop_intMul`: the
displacement is the endpoint difference of the canonical lift, and at each
junction the two lifts sit in the same fiber, so they differ by an element of the
deck group `2πℤ`.  Summing the junction differences cyclically (reindexing by
`finRotate`) telescopes the per-edge displacements to a single integer multiple of
`2π`.  It is exactly the integrality input needed for the `winding_integral`
field of a multi-edge cyclic edge-list piece, and it needs no prism/subdivision
operator. -/
theorem displacementSum_cyclic_intMul {k : ℕ} (f : Fin k → C(I, SphereOne))
    (hconn : ∀ i : Fin k, (f i) 1 = (f (finRotate k i)) 0) :
    ∃ m : ℤ, ∑ i, pathDisplacement (f i) = (m : ℝ) * (2 * Real.pi) := by
  have hjunc : ∀ i : Fin k, ∃ m : ℤ,
      pathLift (f i) 1 - pathLift (f (finRotate k i)) 0 = (m : ℝ) * (2 * Real.pi) := by
    intro i
    have h1 : trigCirclePoint (pathLift (f i) 1) = (f i) 1 :=
      congrFun (pathLift_lifts (f i)) 1
    have h0 : trigCirclePoint (pathLift (f (finRotate k i)) 0) = (f (finRotate k i)) 0 :=
      congrFun (pathLift_lifts (f (finRotate k i))) 0
    have hfib :
        trigCirclePoint (pathLift (f i) 1)
          = trigCirclePoint (pathLift (f (finRotate k i)) 0) := by
      rw [h1, h0]; exact hconn i
    obtain ⟨m, hm⟩ := (CircleLifting.trigCirclePoint_eq_iff _ _).1 hfib
    exact ⟨m, by rw [hm]; ring⟩
  choose m hm using hjunc
  refine ⟨∑ i, m i, ?_⟩
  calc
    ∑ i, pathDisplacement (f i)
        = ∑ i, (pathLift (f i) 1 - pathLift (f i) 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact pathDisplacement_self (f i)
    _ = (∑ i, pathLift (f i) 1) - ∑ i, pathLift (f i) 0 := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i, pathLift (f i) 1) - ∑ i, pathLift (f (finRotate k i)) 0 := by
          congr 1
          exact (Equiv.sum_comp (finRotate k) (fun i => pathLift (f i) 0)).symm
    _ = ∑ i, (pathLift (f i) 1 - pathLift (f (finRotate k i)) 0) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i, ((m i : ℝ) * (2 * Real.pi)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact hm i
    _ = (∑ i, m i : ℤ) * (2 * Real.pi) := by
          rw [← Finset.sum_mul]; push_cast; ring

/-! ## Connection to the actual singular chain complex

The development above works with singular simplices presented as continuous maps
`C(Δⁿ, S¹)` via `TopCat.toSSetObjEquiv`.  The following lemmas connect this to the
actual simplicial face maps `(TopCat.toSSet.obj (TopCat.sphere 1)).δ i`, so that the
kills-boundaries identity is a statement about the genuine boundary in
`CircleH1Computation.sphereOneSingularIntChainComplex`. -/

/-- A singular `2`-simplex in the actual singular simplicial set of
`TopCat.sphere 1`. -/
abbrev SingularTwoSimplex : Type :=
  (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 2))

/-- A singular `1`-simplex in the actual singular simplicial set of
`TopCat.sphere 1`. -/
abbrev SingularOneSimplex : Type :=
  (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 1))

/-- A singular `0`-simplex in the actual singular simplicial set of
`TopCat.sphere 1`. -/
abbrev SingularZeroSimplex : Type :=
  (TopCat.toSSet.obj (TopCat.sphere 1)).obj (op (SimplexCategory.mk 0))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free module on the actual singular `0`-simplices of `TopCat.sphere 1`. -/
abbrev singularZeroChainFree : ModuleCat ℤ :=
  (ModuleCat.free ℤ).obj SingularZeroSimplex

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The raw singular chain group `C₀(S¹;ℤ)` maps to the explicit free module on
singular `0`-simplices by sending each coproduct summand to the corresponding
free generator. -/
noncomputable def singularZeroChainToFree :
    sphereOneSingularIntChainComplex.X 0 ⟶ singularZeroChainFree :=
  Sigma.desc (fun s : SingularZeroSimplex =>
    ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ singularZeroChainFree (ModuleCat.freeMk s)))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free module on the actual singular `1`-simplices of `TopCat.sphere 1`. -/
abbrev singularOneChainFree : ModuleCat ℤ :=
  (ModuleCat.free ℤ).obj SingularOneSimplex

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free module on the actual singular `2`-simplices of `TopCat.sphere 1`. -/
abbrev singularTwoChainFree : ModuleCat ℤ :=
  (ModuleCat.free ℤ).obj SingularTwoSimplex

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The raw singular chain group `C₁(S¹;ℤ)` maps to the explicit free module on
singular `1`-simplices by sending each coproduct summand to the corresponding
free generator. -/
noncomputable def singularOneChainToFree :
    sphereOneSingularIntChainComplex.X 1 ⟶ singularOneChainFree :=
  Sigma.desc (fun s : SingularOneSimplex =>
    ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ singularOneChainFree (ModuleCat.freeMk s)))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free module on singular `1`-simplices maps back to `C₁(S¹;ℤ)` by
sending each free generator to the matching coproduct summand generator. -/
noncomputable def singularOneChainFreeToChain :
    singularOneChainFree ⟶ sphereOneSingularIntChainComplex.X 1 :=
  ModuleCat.freeDesc (fun s : SingularOneSimplex =>
    ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) 1)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free module on singular `2`-simplices maps back to `C₂(S¹;ℤ)` by
sending each free generator to the matching coproduct summand generator. -/
noncomputable def singularTwoChainFreeToChain :
    singularTwoChainFree ⟶ sphereOneSingularIntChainComplex.X 2 :=
  ModuleCat.freeDesc (fun s : SingularTwoSimplex =>
    ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) 1)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Mathlib's raw `C₂(S¹;ℤ)` chain group maps to the explicit free module on
actual singular `2`-simplices by sending each coproduct summand generator to the
corresponding free singleton.  This is the `C₂` analog of
`singularOneChainToFree` and `singularZeroChainToFree`. -/
noncomputable def singularTwoChainToFree :
    sphereOneSingularIntChainComplex.X 2 ⟶ singularTwoChainFree :=
  Sigma.desc (fun s : SingularTwoSimplex =>
    ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ singularTwoChainFree (ModuleCat.freeMk s)))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free-module boundary on singular `1`-simplices: each directed
edge maps to terminal `0`-face minus initial `0`-face. -/
noncomputable def singularOneBoundaryFree :
    singularOneChainFree ⟶ singularZeroChainFree :=
  ModuleCat.freeDesc (fun s : SingularOneSimplex =>
    ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s) -
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free-module boundary on singular `2`-simplices: the alternating
sum of its three singular `1`-faces. -/
noncomputable def singularTwoBoundaryFree :
    singularTwoChainFree ⟶ singularOneChainFree :=
  ModuleCat.freeDesc (fun s : SingularTwoSimplex =>
    ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) s) -
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) s) +
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) s))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- On a singular generator summand, `singularOneChainToFree` is exactly the
corresponding free-module singleton map. -/
theorem singularOneChainToFree_ι (s : SingularOneSimplex) :
    Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫ singularOneChainToFree =
      ModuleCat.ofHom
        (LinearMap.toSpanSingleton ℤ singularOneChainFree (ModuleCat.freeMk s)) := by
  rw [singularOneChainToFree, Sigma.ι_desc]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- On a free generator, `singularOneChainFreeToChain` is the matching singular
chain coproduct generator. -/
theorem singularOneChainFreeToChain_freeMk (s : SingularOneSimplex) :
    ModuleCat.Hom.hom singularOneChainFreeToChain (ModuleCat.freeMk s) =
      ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) 1 := by
  rw [singularOneChainFreeToChain, ModuleCat.freeDesc_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free boundary sends a free singular `1`-simplex generator to
terminal `0`-face minus initial `0`-face. -/
theorem singularOneBoundaryFree_freeMk (s : SingularOneSimplex) :
    ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk s) =
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s) -
        ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s) := by
  rw [singularOneBoundaryFree, ModuleCat.freeDesc_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free boundary sends a free singular `2`-simplex generator to the
alternating sum of its three singular `1`-faces. -/
theorem singularTwoBoundaryFree_freeMk (s : SingularTwoSimplex) :
    ModuleCat.Hom.hom singularTwoBoundaryFree (ModuleCat.freeMk s) =
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) s) -
        ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) s) +
        ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) s) := by
  rw [singularTwoBoundaryFree, ModuleCat.freeDesc_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Cone boundary shell for a singular edge.  If a singular `2`-simplex has base
face `δ₂` equal to a singular `1`-simplex `s` and its two side faces agree, then
its explicit free boundary is exactly the free generator of `s`.  Geometrically,
this is the algebraic content of filling a loop by coning it to a point. -/
theorem singularTwoBoundaryFree_freeMk_of_cone_faces
    (sigma : SingularTwoSimplex) (s : SingularOneSimplex)
    (hbase : (TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) sigma = s)
    (hsides :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) sigma =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) sigma) :
    ModuleCat.Hom.hom singularTwoBoundaryFree (ModuleCat.freeMk sigma) =
      ModuleCat.freeMk s := by
  rw [singularTwoBoundaryFree_freeMk, hbase, hsides]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The constant actual singular `1`-simplex at a point of `S¹`. -/
noncomputable def constantSingularOneSimplex (p : SphereOne) : SingularOneSimplex :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin 2)) p)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The constant actual singular `2`-simplex at a point of `S¹`. -/
noncomputable def constantSingularTwoSimplex (p : SphereOne) : SingularTwoSimplex :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 2))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin 3)) p)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Every face of the constant singular `2`-simplex is the constant singular
`1`-simplex at the same point. -/
theorem constantSingularTwoSimplex_face (p : SphereOne) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ i (constantSingularTwoSimplex p) =
      constantSingularOneSimplex p := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).injective
  dsimp [constantSingularTwoSimplex, constantSingularOneSimplex,
    TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr, face, faceMap]
  ext x
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The constant singular `1`-simplex bounds the constant singular `2`-simplex in
the explicit free chain complex.  This is the degenerate base case of the
null-homotopy prism construction. -/
theorem constantSingularOneSimplex_free_boundary (p : SphereOne) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk (constantSingularTwoSimplex p)) =
        ModuleCat.freeMk (constantSingularOneSimplex p) := by
  rw [singularTwoBoundaryFree_freeMk]
  rw [constantSingularTwoSimplex_face p 0,
    constantSingularTwoSimplex_face p 1,
    constantSingularTwoSimplex_face p 2]
  abel

/-- Terminal vertex of a directed singular edge, matching the positive boundary
term. -/
def edgeTerminal (e : SingularOneSimplex) : SingularZeroSimplex :=
  (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) e

/-- Initial vertex of a directed singular edge, matching the negative boundary
term. -/
def edgeInitial (e : SingularOneSimplex) : SingularZeroSimplex :=
  (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) e

/-- Incidence coefficient of a directed singular edge at a singular vertex:
`+1` at the terminal vertex, `-1` at the initial vertex, and the algebraic sum
when both endpoints coincide. -/
def incidenceCoeff [DecidableEq SingularZeroSimplex]
    (e : SingularOneSimplex) (v : SingularZeroSimplex) : ℤ :=
  (if edgeTerminal e = v then 1 else 0) - (if edgeInitial e = v then 1 else 0)

/-- Orientation for an occurrence of a singular edge in a directed walk.  Backward
orientation represents the negative of the raw singular edge. -/
inductive EdgeOrientation where
  | forward
  | backward
  deriving DecidableEq

/-- A singular edge together with a traversal orientation. -/
structure OrientedSingularEdge where
  edge : SingularOneSimplex
  orientation : EdgeOrientation

/-- Initial vertex of an oriented singular edge occurrence. -/
def OrientedSingularEdge.initial (o : OrientedSingularEdge) : SingularZeroSimplex :=
  match o.orientation with
  | .forward => edgeInitial o.edge
  | .backward => edgeTerminal o.edge

/-- Terminal vertex of an oriented singular edge occurrence. -/
def OrientedSingularEdge.terminal (o : OrientedSingularEdge) : SingularZeroSimplex :=
  match o.orientation with
  | .forward => edgeTerminal o.edge
  | .backward => edgeInitial o.edge

/-- Free edge-chain contribution of one oriented singular edge occurrence. -/
noncomputable def OrientedSingularEdge.chain (o : OrientedSingularEdge) :
    singularOneChainFree :=
  match o.orientation with
  | .forward => ModuleCat.freeMk o.edge
  | .backward => - ModuleCat.freeMk o.edge

/-- Coefficient of an edge in the explicit free `C₁` module. -/
def edgeCoeff (c : singularOneChainFree) (e : SingularOneSimplex) : ℤ :=
  c.toFun e

/-- Coefficient of a vertex in the explicit free `C₀` module. -/
def vertexCoeff (z : singularZeroChainFree) (v : SingularZeroSimplex) : ℤ :=
  z.toFun v

/-- Boundary coefficient at a vertex for a free edge-chain. -/
def vertexBoundaryCoeff (c : singularOneChainFree) (v : SingularZeroSimplex) : ℤ :=
  vertexCoeff (ModuleCat.Hom.hom singularOneBoundaryFree c) v

/-- Support of a free edge-chain. -/
def edgeSupport (c : singularOneChainFree) : Finset SingularOneSimplex :=
  c.support

/-- Cardinality of the support of a free edge-chain. -/
def edgeSupportCard (c : singularOneChainFree) : ℕ :=
  c.support.card

/-- A free edge-chain has empty support exactly when it is zero. -/
theorem edgeSupport_eq_empty_iff (c : singularOneChainFree) :
    edgeSupport c = ∅ ↔ c = 0 := by
  unfold edgeSupport
  exact Finsupp.support_eq_empty

/-- A free edge-chain has support-cardinality zero exactly when it is zero. -/
theorem edgeSupportCard_eq_zero_iff (c : singularOneChainFree) :
    edgeSupportCard c = 0 ↔ c = 0 := by
  unfold edgeSupportCard
  rw [Finset.card_eq_zero]
  exact Finsupp.support_eq_empty

/-- Edge membership in support is nonzero coefficient. -/
theorem mem_edgeSupport_iff (c : singularOneChainFree) (e : SingularOneSimplex) :
    e ∈ edgeSupport c ↔ edgeCoeff c e ≠ 0 := by
  unfold edgeSupport edgeCoeff
  exact Finsupp.mem_support_iff

/-- The free generator has coefficient `1` on itself. -/
theorem edgeCoeff_freeMk_self (e : SingularOneSimplex) :
    edgeCoeff (ModuleCat.freeMk e) e = 1 := by
  unfold edgeCoeff ModuleCat.freeMk
  exact Finsupp.single_eq_same

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A free edge-chain with singleton support is its coefficient times that single
free generator. -/
theorem eq_zsmul_freeMk_of_edgeSupport_eq_single [DecidableEq SingularOneSimplex]
    (c : singularOneChainFree) (e : SingularOneSimplex)
    (hsupp : edgeSupport c = {e}) :
    c = edgeCoeff c e • ModuleCat.freeMk e := by
  apply Finsupp.ext
  intro x
  by_cases hx : x = e
  · subst x
    rw [ModuleCat.freeMk]
    change c.toFun e = c.toFun e * (Finsupp.single e (1 : ℤ) e)
    rw [Finsupp.single_eq_same]
    ring
  · have hx_not_mem : x ∉ edgeSupport c := by
      rw [hsupp]
      simp [hx]
    have hcx : edgeCoeff c x = 0 :=
      Classical.not_not.mp (mt (mem_edgeSupport_iff c x).mpr hx_not_mem)
    unfold edgeCoeff at hcx
    change c.toFun x = (edgeCoeff c e • ModuleCat.freeMk e).toFun x
    rw [hcx]
    rw [ModuleCat.freeMk]
    change 0 = edgeCoeff c e * (Finsupp.single e (1 : ℤ) x)
    have hsingle : (Finsupp.single e (1 : ℤ) : SingularOneSimplex →₀ ℤ) x = 0 :=
      Finsupp.single_eq_of_ne hx
    rw [hsingle]
    ring

/-- If a finite integer sum is zero and one summand is positive, then some
summand is negative.  This is the finite algebra step behind the balanced-flow
"next edge" argument. -/
theorem exists_negative_of_sum_zero_of_positive
    {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    {a : α} (ha : a ∈ s) (hpos : 0 < f a)
    (hsum : ∑ x ∈ s, f x = 0) :
    ∃ b ∈ s, f b < 0 := by
  by_contra hnone
  push_neg at hnone
  have hnonneg : ∀ x ∈ s, 0 ≤ f x := by
    intro x hx
    exact hnone x hx
  have hle : f a ≤ ∑ x ∈ s, f x := by
    exact Finset.single_le_sum (fun x hx => hnonneg x hx) ha
  have hsum_pos : 0 < ∑ x ∈ s, f x := lt_of_lt_of_le hpos hle
  omega

/-- Choose the traversal orientation suggested by an integer coefficient:
positive coefficients are followed forward, negative coefficients backward. -/
def orientationOfCoeff (n : ℤ) : EdgeOrientation :=
  if 0 < n then .forward else .backward

/-- A supported edge of a flow, oriented according to the sign of its coefficient. -/
def orientedEdgeOfCoeff (c : singularOneChainFree) (e : SingularOneSimplex) :
    OrientedSingularEdge where
  edge := e
  orientation := orientationOfCoeff (edgeCoeff c e)

/-- The signed coefficient of the edge in the chosen orientation. -/
def orientedCoeff (c : singularOneChainFree) (e : SingularOneSimplex) : ℤ :=
  match orientationOfCoeff (edgeCoeff c e) with
  | .forward => edgeCoeff c e
  | .backward => -edgeCoeff c e

/-- A supported edge has positive coefficient when read in its sign-selected
orientation. -/
theorem orientedCoeff_pos_of_mem_edgeSupport
    (c : singularOneChainFree) {e : SingularOneSimplex} (he : e ∈ edgeSupport c) :
    0 < orientedCoeff c e := by
  have hne : edgeCoeff c e ≠ 0 := (mem_edgeSupport_iff c e).mp he
  unfold orientedCoeff orientationOfCoeff
  by_cases hp : 0 < edgeCoeff c e
  · simp [hp]
  · simp [hp]
    have hneg : edgeCoeff c e < 0 := by omega
    omega

/-- Boundary coefficient of a single directed edge at a vertex.  It is `+1` at
the terminal endpoint, `-1` at the initial endpoint, and the algebraic sum if the
two endpoints coincide. -/
theorem vertexBoundaryCoeff_freeMk [DecidableEq SingularZeroSimplex]
    (e : SingularOneSimplex) (v : SingularZeroSimplex) :
    vertexBoundaryCoeff (ModuleCat.freeMk e) v =
      incidenceCoeff e v := by
  unfold vertexBoundaryCoeff vertexCoeff
  rw [singularOneBoundaryFree_freeMk]
  unfold incidenceCoeff edgeTerminal edgeInitial
  change ((ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) e) -
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) e) :
        SingularZeroSimplex →₀ ℤ) v) = _
  rw [Finsupp.sub_apply]
  by_cases ht : (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) e = v
  · by_cases hi : (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) e = v
    · simp [ModuleCat.freeMk, ht, hi]
    · simp [ModuleCat.freeMk, ht, hi]
  · by_cases hi : (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) e = v
    · simp [ModuleCat.freeMk, ht, hi]
    · simp [ModuleCat.freeMk, ht, hi]

/-- The incidence-sum expression for the boundary coefficient of a finite free
edge-chain.  Proving `vertexBoundaryCoeff_eq_incidenceSum` below is the local
finite-support algebra needed for the support-decreasing graph proof. -/
def boundaryIncidenceSum [DecidableEq SingularZeroSimplex]
    (c : singularOneChainFree) (v : SingularZeroSimplex) : ℤ :=
  c.sum (fun e n => n * incidenceCoeff e v)

/-- Contribution of one raw edge coefficient to the boundary coefficient at a
vertex. -/
def edgeContribution [DecidableEq SingularZeroSimplex]
    (c : singularOneChainFree) (e : SingularOneSimplex) (v : SingularZeroSimplex) : ℤ :=
  edgeCoeff c e * incidenceCoeff e v

/-- A supported non-loop edge, read in its sign-selected orientation, contributes
positively to the boundary coefficient at its terminal vertex.  This is the local
positivity fact used to force a compensating outgoing edge in a balanced flow. -/
theorem edgeContribution_pos_at_oriented_terminal
    [DecidableEq SingularZeroSimplex]
    (c : singularOneChainFree) {e : SingularOneSimplex}
    (he : e ∈ edgeSupport c)
    (hnotloop : (orientedEdgeOfCoeff c e).initial ≠ (orientedEdgeOfCoeff c e).terminal) :
    0 < edgeContribution c e (orientedEdgeOfCoeff c e).terminal := by
  have hne : edgeCoeff c e ≠ 0 := (mem_edgeSupport_iff c e).mp he
  by_cases hp : 0 < edgeCoeff c e
  · have hinit_ne : edgeInitial e ≠ edgeTerminal e := by
      simpa [orientedEdgeOfCoeff, OrientedSingularEdge.initial, OrientedSingularEdge.terminal,
        orientationOfCoeff, hp] using hnotloop
    simp [edgeContribution, incidenceCoeff, orientedEdgeOfCoeff,
      OrientedSingularEdge.terminal, orientationOfCoeff, hp, hinit_ne]
  · have hneg : edgeCoeff c e < 0 := by omega
    have hterm_ne : edgeTerminal e ≠ edgeInitial e := by
      simpa [orientedEdgeOfCoeff, OrientedSingularEdge.initial, OrientedSingularEdge.terminal,
        orientationOfCoeff, hp] using hnotloop
    simp [edgeContribution, incidenceCoeff, orientedEdgeOfCoeff,
      OrientedSingularEdge.terminal, orientationOfCoeff, hp, hterm_ne]
    omega

/-- Incidence sum of a singleton edge coefficient. -/
theorem boundaryIncidenceSum_single [DecidableEq SingularZeroSimplex]
    (e : SingularOneSimplex) (n : ℤ) (v : SingularZeroSimplex) :
    boundaryIncidenceSum (Finsupp.single e n : singularOneChainFree) v =
      n * incidenceCoeff e v := by
  unfold boundaryIncidenceSum
  rw [Finsupp.sum_single_index]
  · ring_nf

/-- Incidence sum is additive in the edge-flow. -/
theorem boundaryIncidenceSum_add [DecidableEq SingularZeroSimplex]
    (f g : singularOneChainFree) (v : SingularZeroSimplex) :
    boundaryIncidenceSum (f + g) v =
      boundaryIncidenceSum f v + boundaryIncidenceSum g v := by
  unfold boundaryIncidenceSum
  rw [Finsupp.sum_add_index']
  · intro e
    ring_nf
  · intro e a b
    ring

/-- Incidence sum of the zero edge-flow. -/
theorem boundaryIncidenceSum_zero [DecidableEq SingularZeroSimplex]
    (v : SingularZeroSimplex) :
    boundaryIncidenceSum (0 : singularOneChainFree) v = 0 := by
  unfold boundaryIncidenceSum
  simp

/-- The incidence sum is the explicit finite sum over the edge support. -/
theorem boundaryIncidenceSum_eq_support_sum
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (c : singularOneChainFree) (v : SingularZeroSimplex) :
    boundaryIncidenceSum c v =
      ∑ e ∈ edgeSupport c, edgeContribution c e v := by
  unfold boundaryIncidenceSum edgeContribution edgeSupport edgeCoeff
  rw [Finsupp.sum]
  rfl

/-- Target local balance formula: the boundary coefficient of any finite edge
flow is the finite sum of its edge coefficients times incidence signs. -/
def vertexBoundaryCoeff_eq_incidenceSum : Prop :=
  ∀ [DecidableEq SingularZeroSimplex] (c : singularOneChainFree) (v : SingularZeroSimplex),
    vertexBoundaryCoeff c v = boundaryIncidenceSum c v

/-- Boundary coefficient of any finite free edge-flow is the finite incidence sum
over its support. -/
theorem vertexBoundaryCoeff_eq_incidenceSum_holds :
    vertexBoundaryCoeff_eq_incidenceSum := by
  intro _ c v
  induction c using Finsupp.induction_linear with
  | zero =>
      rw [boundaryIncidenceSum_zero]
      unfold vertexBoundaryCoeff vertexCoeff
      change (0 : singularZeroChainFree).toFun v = 0
      rfl
  | add f g hf hg =>
      rw [boundaryIncidenceSum_add]
      have hadd : vertexBoundaryCoeff (f + g) v =
          vertexBoundaryCoeff f v + vertexBoundaryCoeff g v := by
        unfold vertexBoundaryCoeff vertexCoeff
        rw [map_add]
        rfl
      rw [hadd, hf, hg]
  | single e n =>
      rw [boundaryIncidenceSum_single]
      have hsingle : (Finsupp.single e n : singularOneChainFree) =
          n • ModuleCat.freeMk e := by
        rw [ModuleCat.freeMk]
        rw [Finsupp.smul_single]
        simp
      rw [hsingle]
      unfold vertexBoundaryCoeff vertexCoeff
      rw [map_zsmul]
      change (n • (ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk e) :
          singularZeroChainFree)).toFun v =
        n * incidenceCoeff e v
      change n * ((ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk e) :
          singularZeroChainFree).toFun v) =
        n * incidenceCoeff e v
      rw [show (ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk e) :
            singularZeroChainFree).toFun v =
          vertexBoundaryCoeff (ModuleCat.freeMk e) v by rfl]
      rw [vertexBoundaryCoeff_freeMk]

/-- If the incidence-sum formula is proved, every free-boundary-zero flow has zero
incidence sum at each vertex. -/
theorem boundaryIncidenceSum_eq_zero_of_boundary_zero
    (hformula : vertexBoundaryCoeff_eq_incidenceSum)
    [DecidableEq SingularZeroSimplex]
    {c : singularOneChainFree}
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    (v : SingularZeroSimplex) :
    boundaryIncidenceSum c v = 0 := by
  rw [← hformula c v]
  unfold vertexBoundaryCoeff vertexCoeff
  rw [hzero]
  rfl

/-- Every free-boundary-zero flow has zero incidence sum at each vertex. -/
theorem boundaryIncidenceSum_eq_zero_of_boundary_zero'
    [DecidableEq SingularZeroSimplex]
    {c : singularOneChainFree}
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    (v : SingularZeroSimplex) :
    boundaryIncidenceSum c v = 0 :=
  boundaryIncidenceSum_eq_zero_of_boundary_zero
    vertexBoundaryCoeff_eq_incidenceSum_holds hzero v

/-- In a balanced flow, a positive contribution at a vertex forces some negative
contribution at the same vertex.  Applied to a sign-selected supported edge, this
is the algebraic core of the next-edge existence step. -/
theorem exists_negative_edgeContribution_at_oriented_terminal
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    {c : singularOneChainFree}
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    {e : SingularOneSimplex}
    (he : e ∈ edgeSupport c)
    (hnotloop : (orientedEdgeOfCoeff c e).initial ≠ (orientedEdgeOfCoeff c e).terminal) :
    ∃ e' ∈ edgeSupport c,
      edgeContribution c e' (orientedEdgeOfCoeff c e).terminal < 0 := by
  let v := (orientedEdgeOfCoeff c e).terminal
  have hsum0 : boundaryIncidenceSum c v = 0 :=
    boundaryIncidenceSum_eq_zero_of_boundary_zero' hzero v
  have hsupport :
      boundaryIncidenceSum c v =
        ∑ x ∈ edgeSupport c, edgeContribution c x v :=
    boundaryIncidenceSum_eq_support_sum c v
  have hsum : ∑ x ∈ edgeSupport c, edgeContribution c x v = 0 := by
    rw [← hsupport, hsum0]
  have hpos : 0 < edgeContribution c e v :=
    edgeContribution_pos_at_oriented_terminal c he hnotloop
  exact exists_negative_of_sum_zero_of_positive
    (edgeSupport c) (fun x => edgeContribution c x v) he hpos hsum

/-- If an edge contributes negatively to the boundary coefficient at a vertex,
then the sign-selected orientation of that edge starts at that vertex. -/
theorem initial_eq_of_negative_edgeContribution
    [DecidableEq SingularZeroSimplex]
    (c : singularOneChainFree) (e : SingularOneSimplex) (v : SingularZeroSimplex)
    (hneg : edgeContribution c e v < 0) :
    (orientedEdgeOfCoeff c e).initial = v := by
  unfold edgeContribution incidenceCoeff at hneg
  unfold orientedEdgeOfCoeff OrientedSingularEdge.initial orientationOfCoeff
  by_cases hp : 0 < edgeCoeff c e
  · simp [hp]
    by_cases hi : edgeInitial e = v
    · exact hi
    · by_cases ht : edgeTerminal e = v
      · simp [ht, hi] at hneg
        omega
      · simp [ht, hi] at hneg
  · simp [hp]
    by_cases hz : edgeCoeff c e = 0
    · simp [hz] at hneg
    · have hnegcoeff : edgeCoeff c e < 0 := by omega
      by_cases ht : edgeTerminal e = v
      · exact ht
      · by_cases hi : edgeInitial e = v
        · simp [ht, hi] at hneg
          omega
        · simp [ht, hi] at hneg

/-- Local successor-edge theorem: in a balanced flow, a supported non-loop
oriented edge has a supported edge whose sign-selected orientation starts at its
terminal vertex. -/
theorem exists_next_orientedEdge_from_terminal
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    {c : singularOneChainFree}
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    {e : SingularOneSimplex}
    (he : e ∈ edgeSupport c)
    (hnotloop : (orientedEdgeOfCoeff c e).initial ≠ (orientedEdgeOfCoeff c e).terminal) :
    ∃ e' ∈ edgeSupport c,
      (orientedEdgeOfCoeff c e').initial = (orientedEdgeOfCoeff c e).terminal := by
  obtain ⟨e', he', hneg⟩ :=
    exists_negative_edgeContribution_at_oriented_terminal hzero he hnotloop
  exact ⟨e', he', initial_eq_of_negative_edgeContribution
    c e' (orientedEdgeOfCoeff c e).terminal hneg⟩

/-- Boundary of one oriented singular edge occurrence: terminal vertex minus
initial vertex. -/
theorem OrientedSingularEdge.boundary_free (o : OrientedSingularEdge) :
    ModuleCat.Hom.hom singularOneBoundaryFree o.chain =
      ModuleCat.freeMk o.terminal - ModuleCat.freeMk o.initial := by
  cases o with
  | mk e ori =>
    cases ori
    · unfold OrientedSingularEdge.chain OrientedSingularEdge.terminal
        OrientedSingularEdge.initial
      rw [singularOneBoundaryFree_freeMk]
      rfl
    · unfold OrientedSingularEdge.chain OrientedSingularEdge.terminal
        OrientedSingularEdge.initial
      rw [map_neg, singularOneBoundaryFree_freeMk]
      unfold edgeInitial edgeTerminal
      abel_nf

/-- Boundary coefficient of one oriented edge occurrence at a vertex. -/
theorem OrientedSingularEdge.vertexBoundaryCoeff_chain [DecidableEq SingularZeroSimplex]
    (o : OrientedSingularEdge) (v : SingularZeroSimplex) :
    vertexCoeff (ModuleCat.Hom.hom singularOneBoundaryFree o.chain) v =
      (if o.terminal = v then 1 else 0) - (if o.initial = v then 1 else 0) := by
  rw [o.boundary_free]
  unfold vertexCoeff
  change ((ModuleCat.freeMk o.terminal - ModuleCat.freeMk o.initial :
        SingularZeroSimplex →₀ ℤ) v) = _
  rw [Finsupp.sub_apply]
  by_cases ht : o.terminal = v
  · by_cases hi : o.initial = v <;> simp [ModuleCat.freeMk, ht, hi]
  · by_cases hi : o.initial = v <;> simp [ModuleCat.freeMk, ht, hi]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- `C₁(S¹;ℤ)` is the explicit free ℤ-module on actual singular `1`-simplices.
This exposes the finite-support normal form needed for the remaining raw-chain
cancellation theorem. -/
noncomputable def singularOneChainFreeIso :
    sphereOneSingularIntChainComplex.X 1 ≅ singularOneChainFree where
  hom := singularOneChainToFree
  inv := singularOneChainFreeToChain
  hom_inv_id := by
    apply Sigma.hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro n
    change ModuleCat.Hom.hom
        ((Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫ singularOneChainToFree) ≫
          singularOneChainFreeToChain) n =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) n
    rw [singularOneChainToFree, Sigma.ι_desc]
    change ModuleCat.Hom.hom
        (ModuleCat.ofHom
            (LinearMap.toSpanSingleton ℤ singularOneChainFree (ModuleCat.freeMk s)) ≫
          singularOneChainFreeToChain) n =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) n
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.toSpanSingleton_apply]
    rw [map_zsmul]
    rw [singularOneChainFreeToChain, ModuleCat.freeDesc_apply]
    change n •
        (ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) 1) =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) n
    rw [← map_zsmul]
    simp
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro s
    change ModuleCat.Hom.hom (singularOneChainFreeToChain ≫ singularOneChainToFree)
        (ModuleCat.freeMk s) =
      ModuleCat.Hom.hom (𝟙 singularOneChainFree) (ModuleCat.freeMk s)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp, Function.comp_apply]
    rw [singularOneChainFreeToChain, ModuleCat.freeDesc_apply]
    change ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom
          (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) 1) =
      ModuleCat.freeMk s
    change ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫ singularOneChainToFree) 1 =
      ModuleCat.freeMk s
    rw [singularOneChainToFree, Sigma.ι_desc]
    simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- `C₂(S¹;ℤ)` is the explicit free ℤ-module on actual singular `2`-simplices.
This is the degree-`2` analog of `singularOneChainFreeIso`; it removes the
purely representational gap between raw singular `2`-chains and free-coordinate
`2`-chains. -/
noncomputable def singularTwoChainFreeIso :
    sphereOneSingularIntChainComplex.X 2 ≅ singularTwoChainFree where
  hom := singularTwoChainToFree
  inv := singularTwoChainFreeToChain
  hom_inv_id := by
    apply Sigma.hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro n
    change ModuleCat.Hom.hom
        ((Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s ≫ singularTwoChainToFree) ≫
          singularTwoChainFreeToChain) n =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) n
    rw [singularTwoChainToFree, Sigma.ι_desc]
    change ModuleCat.Hom.hom
        (ModuleCat.ofHom
            (LinearMap.toSpanSingleton ℤ singularTwoChainFree (ModuleCat.freeMk s)) ≫
          singularTwoChainFreeToChain) n =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) n
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.toSpanSingleton_apply]
    rw [map_zsmul]
    rw [singularTwoChainFreeToChain, ModuleCat.freeDesc_apply]
    change n •
        (ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) 1) =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) n
    rw [← map_zsmul]
    simp
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro s
    change ModuleCat.Hom.hom (singularTwoChainFreeToChain ≫ singularTwoChainToFree)
        (ModuleCat.freeMk s) =
      ModuleCat.Hom.hom (𝟙 singularTwoChainFree) (ModuleCat.freeMk s)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp, Function.comp_apply]
    rw [singularTwoChainFreeToChain, ModuleCat.freeDesc_apply]
    change ModuleCat.Hom.hom singularTwoChainToFree
        (ModuleCat.Hom.hom
          (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) 1) =
      ModuleCat.freeMk s
    change ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s ≫ singularTwoChainToFree) 1 =
      ModuleCat.freeMk s
    rw [singularTwoChainToFree, Sigma.ι_desc]
    simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free module on singular `0`-simplices maps back to `C₀(S¹;ℤ)` by
sending each free generator to the matching coproduct summand generator.  This is
the `C₀` analog of `singularOneChainFreeToChain`. -/
noncomputable def singularZeroChainFreeToChain :
    singularZeroChainFree ⟶ sphereOneSingularIntChainComplex.X 0 :=
  ModuleCat.freeDesc (fun s : SingularZeroSimplex =>
    ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s) 1)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- `C₀(S¹;ℤ)` is the explicit free ℤ-module on actual singular `0`-simplices.
This is the `C₀` analog of `singularOneChainFreeIso`; in particular
`singularZeroChainToFree` is an isomorphism, hence injective, which is what lets a
boundary computed in the explicit free `C₀` module be transported back to the raw
chain group. -/
noncomputable def singularZeroChainFreeIso :
    sphereOneSingularIntChainComplex.X 0 ≅ singularZeroChainFree where
  hom := singularZeroChainToFree
  inv := singularZeroChainFreeToChain
  hom_inv_id := by
    apply Sigma.hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro n
    change ModuleCat.Hom.hom
        ((Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s ≫ singularZeroChainToFree) ≫
          singularZeroChainFreeToChain) n =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s) n
    rw [singularZeroChainToFree, Sigma.ι_desc]
    change ModuleCat.Hom.hom
        (ModuleCat.ofHom
            (LinearMap.toSpanSingleton ℤ singularZeroChainFree (ModuleCat.freeMk s)) ≫
          singularZeroChainFreeToChain) n =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s) n
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.toSpanSingleton_apply]
    rw [map_zsmul]
    rw [singularZeroChainFreeToChain, ModuleCat.freeDesc_apply]
    change n •
        (ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s) 1) =
      ModuleCat.Hom.hom (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s) n
    rw [← map_zsmul]
    simp
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro s
    change ModuleCat.Hom.hom (singularZeroChainFreeToChain ≫ singularZeroChainToFree)
        (ModuleCat.freeMk s) =
      ModuleCat.Hom.hom (𝟙 singularZeroChainFree) (ModuleCat.freeMk s)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp, Function.comp_apply]
    rw [singularZeroChainFreeToChain, ModuleCat.freeDesc_apply]
    change ModuleCat.Hom.hom singularZeroChainToFree
        (ModuleCat.Hom.hom
          (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s) 1) =
      ModuleCat.freeMk s
    change ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularZeroSimplex => ModuleCat.of ℤ ℤ) s ≫ singularZeroChainToFree) 1 =
      ModuleCat.freeMk s
    rw [singularZeroChainToFree, Sigma.ι_desc]
    simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- `singularZeroChainToFree` is injective: it is the forward map of an
isomorphism. -/
theorem singularZeroChainToFree_injective :
    Function.Injective (ModuleCat.Hom.hom singularZeroChainToFree) := by
  haveI : IsIso singularZeroChainToFree := by
    change IsIso singularZeroChainFreeIso.hom
    infer_instance
  exact (ModuleCat.mono_iff_injective singularZeroChainToFree).mp inferInstance

/-- **The combinatorial face map agrees with the geometric one.**  The `i`-th
simplicial face of a singular `2`-simplex `σ`, transported through
`TopCat.toSSetObjEquiv`, is the geometric face `face` of the corresponding
continuous map.  This is the bridge identifying the chain-complex boundary with
the affine edge maps used in the telescoping. -/
theorem toSSetObjEquiv_delta (s : SingularTwoSimplex) (i : Fin 3) :
    TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))
        ((TopCat.toSSet.obj (TopCat.sphere 1)).δ i s)
      = face (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 2)) s) i := by
  ext x
  dsimp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr, face, faceMap]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Turn a concrete continuous `1`-simplex `C(Δ¹,S¹)` into the corresponding
actual singular simplex in Mathlib's simplicial set. -/
noncomputable def singularOneSimplexOfMap (f : OneSimplex) : SingularOneSimplex :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).symm f

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Turn a concrete continuous `2`-simplex `C(Δ²,S¹)` into the corresponding
actual singular simplex in Mathlib's simplicial set. -/
noncomputable def singularTwoSimplexOfMap (F : TwoSimplex) : SingularTwoSimplex :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 2))).symm F

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Transport a concrete face equation through `TopCat.toSSetObjEquiv`: the
simplicial `δᵢ` face of the singular simplex associated to `F : C(Δ²,S¹)` is
the singular simplex associated to the concrete face map `face F i`. -/
theorem singularTwoSimplexOfMap_delta (F : TwoSimplex) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ i (singularTwoSimplexOfMap F) =
      singularOneSimplexOfMap (face F i) := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).injective
  rw [toSSetObjEquiv_delta]
  unfold singularOneSimplexOfMap singularTwoSimplexOfMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem stdSimplexHomeomorphUnitInterval_coe (x : stdSimplex ℝ (Fin 2)) :
    ((stdSimplexHomeomorphUnitInterval x : I) : ℝ) = x 1 := by
  have h := intervalToSimplex_coord_one (stdSimplexHomeomorphUnitInterval x)
  unfold intervalToSimplex at h
  simp at h
  exact h.symm

/-- The second barycentric coordinate of a `2`-simplex, read as a unit-interval
parameter. -/
noncomputable def twoSimplexCoordOneParam (x : stdSimplex ℝ (Fin 3)) : I :=
  ⟨x 1, mem_Icc_of_mem_stdSimplex x.2 1⟩

theorem continuous_twoSimplexCoordOneParam :
    Continuous twoSimplexCoordOneParam := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_subtype_rng]
  exact ((continuous_apply 1).comp continuous_subtype_val).continuousAt

theorem twoSimplexCoordOneParam_face_two (x : stdSimplex ℝ (Fin 2)) :
    twoSimplexCoordOneParam (faceMap (2 : Fin 3) x) =
      stdSimplexHomeomorphUnitInterval x := by
  ext
  change ((faceMap (2 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 1 =
    ((stdSimplexHomeomorphUnitInterval x : I) : ℝ)
  rw [faceMap_two_coord_one, stdSimplexHomeomorphUnitInterval_coe]

theorem twoSimplexCoordOneParam_face_one (x : stdSimplex ℝ (Fin 2)) :
    twoSimplexCoordOneParam (faceMap (1 : Fin 3) x) = 0 := by
  ext
  change ((faceMap (1 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 1 = (0 : ℝ)
  exact faceMap_one_coord_one x

theorem twoSimplexCoordOneParam_face_zero (x : stdSimplex ℝ (Fin 2)) :
    twoSimplexCoordOneParam (faceMap (0 : Fin 3) x) =
      unitInterval.symm (stdSimplexHomeomorphUnitInterval x) := by
  ext
  change ((faceMap (0 : Fin 3) x : stdSimplex ℝ (Fin 3)) : Fin 3 → ℝ) 1 =
    1 - ((stdSimplexHomeomorphUnitInterval x : I) : ℝ)
  rw [stdSimplexHomeomorphUnitInterval_coe, faceMap_zero_coord_one]
  have hsum : x 0 + x 1 = (1 : ℝ) := by
    have hs := stdSimplex.sum_eq_one x
    rw [Fin.sum_univ_two] at hs
    exact hs
  linarith

/-- The triangular backtrack prism over a path `γ`.  It maps `x ∈ Δ²` to
`γ(x₁)`, so its three faces are the reversed path, the constant initial edge,
and the original path. -/
noncomputable def pathBacktrackMap (γ : C(I, SphereOne)) : TwoSimplex where
  toFun x := γ (twoSimplexCoordOneParam x)
  continuous_toFun := γ.continuous.comp continuous_twoSimplexCoordOneParam

theorem pathBacktrackMap_face_zero (γ : C(I, SphereOne)) :
    face (pathBacktrackMap γ) (0 : Fin 3) =
      oneSimplexOfPath (CircleWinding.reversePath γ) := by
  ext x
  exact congrArg γ (twoSimplexCoordOneParam_face_zero x)

theorem pathBacktrackMap_face_one (γ : C(I, SphereOne)) :
    face (pathBacktrackMap γ) (1 : Fin 3) = constantOneSimplex (γ 0) := by
  ext x
  exact congrArg γ (twoSimplexCoordOneParam_face_one x)

theorem pathBacktrackMap_face_two (γ : C(I, SphereOne)) :
    face (pathBacktrackMap γ) (2 : Fin 3) = oneSimplexOfPath γ := by
  ext x
  exact congrArg γ (twoSimplexCoordOneParam_face_two x)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The singular `2`-simplex associated to the triangular backtrack prism over
a path. -/
noncomputable def pathBacktrackSingularTwoSimplex
    (γ : C(I, SphereOne)) : SingularTwoSimplex :=
  singularTwoSimplexOfMap (pathBacktrackMap γ)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
theorem singularOneSimplexOfMap_constantOneSimplex (p : SphereOne) :
    singularOneSimplexOfMap (constantOneSimplex p) = constantSingularOneSimplex p := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).injective
  unfold singularOneSimplexOfMap constantOneSimplex constantSingularOneSimplex
  rw [Equiv.apply_symm_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Boundary of the triangular backtrack prism: reverse path minus the constant
initial edge plus the original path. -/
theorem singularTwoBoundaryFree_freeMk_pathBacktrack
    (γ : C(I, SphereOne)) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk (pathBacktrackSingularTwoSimplex γ)) =
      ModuleCat.freeMk
        (singularOneSimplexOfMap (oneSimplexOfPath (CircleWinding.reversePath γ))) -
        ModuleCat.freeMk (constantSingularOneSimplex (γ 0)) +
          ModuleCat.freeMk (singularOneSimplexOfMap (oneSimplexOfPath γ)) := by
  unfold pathBacktrackSingularTwoSimplex
  rw [singularTwoBoundaryFree_freeMk]
  rw [singularTwoSimplexOfMap_delta, singularTwoSimplexOfMap_delta,
    singularTwoSimplexOfMap_delta]
  rw [pathBacktrackMap_face_zero, pathBacktrackMap_face_one,
    pathBacktrackMap_face_two]
  rw [singularOneSimplexOfMap_constantOneSimplex]

/-! ### Geodesic (lift-linear) simplices in the universal cover

The terminal-return side of every cone, the fundamental loop, and every chain
appearing in the terminal-side correction are *geodesics*: projections of
straight lines in the universal cover `ℝ → S¹`, of the form
`x ↦ trigCirclePoint((1 - x₁)·a + x₁·b)`.  Two structural facts reduce the
terminal-side correction to arithmetic of lift endpoints:

* geodesics compose additively in homology, witnessed by an explicit lift-affine
  `2`-simplex `linearTwoSimplexMap` whose three faces are geodesics;
* a `2π·ℤ` shift of both lift endpoints leaves the geodesic unchanged, because
  `2π` is the deck period of the covering.
-/

/-- A geodesic singular `1`-simplex: the projection of the straight line from the
lift value `a` to the lift value `b` in the universal cover `ℝ → S¹`. -/
noncomputable def geodesicOneSimplex (a b : ℝ) : OneSimplex where
  toFun x := trigCirclePoint ((1 - x 1) * a + x 1 * b)
  continuous_toFun := by
    have hc1 : Continuous (fun x : stdSimplex ℝ (Fin 2) => x 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    exact continuous_trigCirclePoint.comp
      (((continuous_const.sub hc1).mul continuous_const).add (hc1.mul continuous_const))

@[simp] theorem geodesicOneSimplex_apply (a b : ℝ) (x : stdSimplex ℝ (Fin 2)) :
    geodesicOneSimplex a b x = trigCirclePoint ((1 - x 1) * a + x 1 * b) := rfl

/-- The terminal-return side of the cone is exactly the geodesic from the
terminal lift value to the initial lift value. -/
theorem coneTerminalSide_eq_geodesic (γ : C(I, SphereOne)) :
    coneTerminalSide γ = geodesicOneSimplex (pathLift γ 1) (pathLift γ 0) := rfl

/-- A geodesic with equal endpoints is the constant edge at the projected point. -/
theorem geodesicOneSimplex_self (a : ℝ) :
    geodesicOneSimplex a a = constantOneSimplex (trigCirclePoint a) := by
  ext x
  simp only [geodesicOneSimplex_apply]
  rw [show (1 - x 1) * a + x 1 * a = a by ring]
  rfl

/-- Shift invariance of geodesics: translating both lift endpoints by an integer
number of full turns `2π` leaves the geodesic unchanged. -/
theorem geodesicOneSimplex_shift (a b : ℝ) (m : ℤ) :
    geodesicOneSimplex (a + (m : ℝ) * (2 * Real.pi)) (b + (m : ℝ) * (2 * Real.pi)) =
      geodesicOneSimplex a b := by
  ext x
  simp only [geodesicOneSimplex_apply]
  rw [show (1 - x 1) * (a + (m : ℝ) * (2 * Real.pi)) + x 1 * (b + (m : ℝ) * (2 * Real.pi))
        = ((1 - x 1) * a + x 1 * b) + (m : ℝ) * (2 * Real.pi) by ring]
  exact (CircleLifting.trigCirclePoint_eq_iff _ _).mpr ⟨m, rfl⟩

/-- A geodesic (lift-affine) singular `2`-simplex: `x ↦ trigCirclePoint` of the
affine combination of three lift values `p, q, r`.  Its three faces are the
geodesics on the three pairs of vertices. -/
noncomputable def linearTwoSimplexMap (p q r : ℝ) : TwoSimplex where
  toFun x := trigCirclePoint ((1 - x 1 - x 2) * p + x 1 * q + x 2 * r)
  continuous_toFun := by
    have hc1 : Continuous (fun x : stdSimplex ℝ (Fin 3) => x 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    have hc2 : Continuous (fun x : stdSimplex ℝ (Fin 3) => x 2) :=
      (continuous_apply 2).comp continuous_subtype_val
    exact continuous_trigCirclePoint.comp
      (((((continuous_const.sub hc1).sub hc2).mul continuous_const).add
        (hc1.mul continuous_const)).add (hc2.mul continuous_const))

@[simp] theorem linearTwoSimplexMap_apply (p q r : ℝ) (x : stdSimplex ℝ (Fin 3)) :
    linearTwoSimplexMap p q r x =
      trigCirclePoint ((1 - x 1 - x 2) * p + x 1 * q + x 2 * r) := rfl

/-- The `δ₀` face of the lift-affine `2`-simplex is the geodesic from `q` to `r`. -/
theorem linearTwoSimplexMap_face_zero (p q r : ℝ) :
    face (linearTwoSimplexMap p q r) 0 = geodesicOneSimplex q r := by
  ext x
  simp only [face, ContinuousMap.comp_apply, linearTwoSimplexMap_apply,
    geodesicOneSimplex_apply]
  rw [faceMap_zero_coord_one, faceMap_zero_coord_two]
  have hsum : (x : Fin 2 → ℝ) 0 + (x : Fin 2 → ℝ) 1 = 1 := by
    have h := stdSimplex.sum_eq_one x
    rw [Fin.sum_univ_two] at h
    exact h
  congr 1
  have hx0 : (x : Fin 2 → ℝ) 0 = 1 - (x : Fin 2 → ℝ) 1 := by linarith
  rw [hx0]; ring

/-- The `δ₁` face of the lift-affine `2`-simplex is the geodesic from `p` to `r`. -/
theorem linearTwoSimplexMap_face_one (p q r : ℝ) :
    face (linearTwoSimplexMap p q r) 1 = geodesicOneSimplex p r := by
  ext x
  simp only [face, ContinuousMap.comp_apply, linearTwoSimplexMap_apply,
    geodesicOneSimplex_apply]
  rw [faceMap_one_coord_one, faceMap_one_coord_two]
  congr 1
  ring

/-- The `δ₂` face of the lift-affine `2`-simplex is the geodesic from `p` to `q`. -/
theorem linearTwoSimplexMap_face_two (p q r : ℝ) :
    face (linearTwoSimplexMap p q r) 2 = geodesicOneSimplex p q := by
  ext x
  simp only [face, ContinuousMap.comp_apply, linearTwoSimplexMap_apply,
    geodesicOneSimplex_apply]
  rw [faceMap_two_coord_one, faceMap_two_coord_two]
  congr 1
  ring

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The singular `2`-simplex carried by the lift-affine `2`-simplex. -/
noncomputable def linearSingularTwoSimplex (p q r : ℝ) : SingularTwoSimplex :=
  singularTwoSimplexOfMap (linearTwoSimplexMap p q r)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Geodesic composition law.**  The free boundary of the lift-affine
`2`-simplex on `(p, q, r)` is `geo(q,r) − geo(p,r) + geo(p,q)`.  In particular
`geo(p,q) + geo(q,r)` is homologous to `geo(p,r)`: geodesics compose additively
in `H₁`. -/
theorem singularTwoBoundaryFree_freeMk_linearSingularTwoSimplex (p q r : ℝ) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk (linearSingularTwoSimplex p q r)) =
      ModuleCat.freeMk (singularOneSimplexOfMap (geodesicOneSimplex q r)) -
        ModuleCat.freeMk (singularOneSimplexOfMap (geodesicOneSimplex p r)) +
        ModuleCat.freeMk (singularOneSimplexOfMap (geodesicOneSimplex p q)) := by
  unfold linearSingularTwoSimplex
  rw [singularTwoBoundaryFree_freeMk]
  rw [singularTwoSimplexOfMap_delta, singularTwoSimplexOfMap_delta,
    singularTwoSimplexOfMap_delta]
  rw [linearTwoSimplexMap_face_zero, linearTwoSimplexMap_face_one,
    linearTwoSimplexMap_face_two]

/-- The geodesic from `0` to `2π` is the fundamental once-around simplex map. -/
theorem geodesicOneSimplex_zero_twoPi :
    geodesicOneSimplex 0 (2 * Real.pi) =
      CircleFundamentalSimplex.fundamentalCirclePathMap := by
  ext x
  simp only [geodesicOneSimplex_apply]
  rw [show (1 - x 1) * 0 + x 1 * (2 * Real.pi) = 2 * Real.pi * x 1 by ring]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The singular simplex of the geodesic `0 → 2π` is the fundamental singular
`1`-simplex. -/
theorem singularOneSimplexOfMap_geodesic_zero_twoPi :
    singularOneSimplexOfMap (geodesicOneSimplex 0 (2 * Real.pi)) =
      CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex := by
  rw [geodesicOneSimplex_zero_twoPi]
  rfl

/-- The explicit real lift of the terminal-return side of the cone. -/
noncomputable def coneTerminalSideLift (γ : C(I, SphereOne)) : C(I, ℝ) where
  toFun t := (1 - (t : ℝ)) * pathLift γ 1 + (t : ℝ) * pathLift γ 0
  continuous_toFun := ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)

theorem coneTerminalSideLift_lifts (γ : C(I, SphereOne)) :
    trigCirclePoint ∘ ((coneTerminalSideLift γ) : I → ℝ) =
      oneSimplexPath (coneTerminalSide γ) := by
  funext t
  simp [coneTerminalSideLift, oneSimplexPath, coneTerminalSide, intervalToSimplex]
  rw [show ((stdSimplexHomeomorphUnitInterval.symm t : stdSimplex ℝ (Fin 2)) :
      Fin 2 → ℝ) 1 = (t : ℝ) by
    exact intervalToSimplex_coord_one t]

/-- The terminal-return side of the cone has displacement opposite to the base
path. -/
theorem pathDisplacement_coneTerminalSide (γ : C(I, SphereOne)) :
    pathDisplacement (oneSimplexPath (coneTerminalSide γ)) =
      - pathDisplacement γ := by
  rw [pathDisplacement_eq (oneSimplexPath (coneTerminalSide γ))
    (coneTerminalSideLift γ) (coneTerminalSideLift_lifts γ)]
  dsimp [coneTerminalSideLift, pathDisplacement]
  ring

/-- The terminal-return side has winding opposite to the base path displacement. -/
theorem simplexWinding_coneTerminalSide (γ : C(I, SphereOne)) :
    simplexWinding (coneTerminalSide γ) =
      - (pathDisplacement γ / (2 * Real.pi)) := by
  unfold simplexWinding simplexDisplacement
  rw [pathDisplacement_coneTerminalSide]
  ring

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Free-boundary shell for the cone over an arbitrary singular edge.  The boundary
is the terminal-return side minus the constant apex side plus the original edge.
The zero-winding loop theorem is the special case where the terminal-return side
equals the constant side. -/
theorem singularTwoBoundaryFree_freeMk_coneCircleMap
    (f : OneSimplex) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk
        (singularTwoSimplexOfMap
          (coneCircleMapOfContinuous (oneSimplexPath f)
            (continuous_coneCirclePoint (oneSimplexPath f))))) =
      ModuleCat.freeMk (singularOneSimplexOfMap (coneTerminalSide (oneSimplexPath f))) -
        ModuleCat.freeMk
          (singularOneSimplexOfMap (constantOneSimplex ((oneSimplexPath f) 0))) +
          ModuleCat.freeMk (singularOneSimplexOfMap f) := by
  rw [singularTwoBoundaryFree_freeMk]
  rw [singularTwoSimplexOfMap_delta, singularTwoSimplexOfMap_delta,
    singularTwoSimplexOfMap_delta]
  rw [coneCircleMapOfContinuous_face_zero, coneCircleMapOfContinuous_face_one,
    coneCircleMapOfContinuous_face_two]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Zero-winding specialization of the arbitrary cone boundary shell: the
terminal-return side equals the constant apex side, so the cone's free boundary is
just the original edge generator. -/
theorem singularTwoBoundaryFree_freeMk_coneCircleMap_of_simplexWinding_zero
    (f : OneSimplex) (hzero : simplexWinding f = 0) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk
        (singularTwoSimplexOfMap
          (coneCircleMapOfContinuous (oneSimplexPath f)
            (continuous_coneCirclePoint (oneSimplexPath f))))) =
      ModuleCat.freeMk (singularOneSimplexOfMap f) := by
  rw [singularTwoBoundaryFree_freeMk_coneCircleMap]
  have hside :
      coneTerminalSide (oneSimplexPath f) =
        constantOneSimplex ((oneSimplexPath f) 0) :=
    coneTerminalSide_eq_constantOneSimplex_of_simplexWinding_zero f hzero
  rw [hside]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The singular `2`-simplex obtained by coning an arbitrary unit-interval path to
its initial point. -/
noncomputable def coneSingularTwoSimplexOfPath (γ : C(I, SphereOne)) : SingularTwoSimplex :=
  singularTwoSimplexOfMap
    (coneCircleMapOfContinuous γ (continuous_coneCirclePoint γ))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Path-parametric cone boundary shell.  This is the primitive finite-prism brick:
the boundary of the cone over a path is terminal-return side minus constant apex
side plus the path as a concrete singular edge. -/
theorem singularTwoBoundaryFree_freeMk_coneSingularTwoSimplexOfPath
    (γ : C(I, SphereOne)) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk (coneSingularTwoSimplexOfPath γ)) =
      ModuleCat.freeMk (singularOneSimplexOfMap (coneTerminalSide γ)) -
        ModuleCat.freeMk (singularOneSimplexOfMap (constantOneSimplex (γ 0))) +
          ModuleCat.freeMk (singularOneSimplexOfMap (oneSimplexOfPath γ)) := by
  unfold coneSingularTwoSimplexOfPath
  rw [singularTwoBoundaryFree_freeMk]
  rw [singularTwoSimplexOfMap_delta, singularTwoSimplexOfMap_delta,
    singularTwoSimplexOfMap_delta]
  rw [coneCircleMapOfContinuous_face_zero, coneCircleMapOfContinuous_face_one,
    coneCircleMapOfContinuous_face_two_path]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Sum of cone `2`-simplices over a finite family of paths. -/
noncomputable def coneSingularTwoChainOfPathFamily {k : ℕ}
    (γ : Fin k → C(I, SphereOne)) : singularTwoChainFree :=
  ∑ i, ModuleCat.freeMk (coneSingularTwoSimplexOfPath (γ i))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Finite-family cone boundary shell.  The summed cone boundary is the sum of
terminal-return sides, minus the sum of constant apex sides, plus the sum of the
base path edges.  This is the algebraic target whose side terms must telescope in
the multi-edge prism. -/
theorem singularTwoBoundaryFree_coneSingularTwoChainOfPathFamily {k : ℕ}
    (γ : Fin k → C(I, SphereOne)) :
    ModuleCat.Hom.hom singularTwoBoundaryFree (coneSingularTwoChainOfPathFamily γ) =
      (∑ i, ModuleCat.freeMk (singularOneSimplexOfMap (coneTerminalSide (γ i)))) -
        (∑ i, ModuleCat.freeMk (singularOneSimplexOfMap (constantOneSimplex ((γ i) 0)))) +
          (∑ i, ModuleCat.freeMk (singularOneSimplexOfMap (oneSimplexOfPath (γ i)))) := by
  unfold coneSingularTwoChainOfPathFamily
  rw [map_sum]
  rw [Finset.sum_congr rfl
    (fun i _ => singularTwoBoundaryFree_freeMk_coneSingularTwoSimplexOfPath (γ i))]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **The winding number of an actual singular `1`-simplex** of `TopCat.sphere 1`,
defined directly on the singular simplicial set. -/
def singularWinding (s : SingularOneSimplex) : ℝ :=
  simplexWinding (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Transporting a concrete singular `1`-simplex into Mathlib's singular simplicial
set preserves the concrete winding number. -/
theorem singularWinding_singularOneSimplexOfMap (f : OneSimplex) :
    singularWinding (singularOneSimplexOfMap f) = simplexWinding f := by
  unfold singularWinding singularOneSimplexOfMap
  rw [Equiv.apply_symm_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The actual singular terminal-return side has winding opposite to the base
path displacement. -/
theorem singularWinding_coneTerminalSide (γ : C(I, SphereOne)) :
    singularWinding (singularOneSimplexOfMap (coneTerminalSide γ)) =
      - (pathDisplacement γ / (2 * Real.pi)) := by
  rw [singularWinding_singularOneSimplexOfMap, simplexWinding_coneTerminalSide]

/-- **The winding invariant kills the singular boundary.**  For every singular
`2`-simplex `s` in the actual singular simplicial set of `TopCat.sphere 1`, the
alternating sum of the winding numbers of its three simplicial faces vanishes.
This is the chain-level statement `W ∘ ∂₂ = 0` evaluated on a single generator:
the winding cochain annihilates boundaries. -/
theorem singularWinding_boundary (s : SingularTwoSimplex) :
    singularWinding ((TopCat.toSSet.obj (TopCat.sphere 1)).δ 0 s)
      - singularWinding ((TopCat.toSSet.obj (TopCat.sphere 1)).δ 1 s)
      + singularWinding ((TopCat.toSSet.obj (TopCat.sphere 1)).δ 2 s) = 0 := by
  simp only [singularWinding, toSSetObjEquiv_delta]
  exact simplexWinding_boundary _

/-- The `δ₀` face of an actual singular `1`-simplex is its terminal endpoint,
after transport through `TopCat.toSSetObjEquiv`. -/
theorem singularOneSimplex_delta_zero_endpoint (s : SingularOneSimplex) :
    (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))
        ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s))
        (stdSimplex.vertex (0 : Fin 1))
      = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s)
          (stdSimplex.vertex (1 : Fin 2)) := by
  dsimp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr]
  congr 1
  change Homeomorph.ulift.symm
      (stdSimplex.map (ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2)))
        (stdSimplex.vertex (0 : Fin 1))) =
    Homeomorph.ulift.symm (stdSimplex.vertex (1 : Fin 2))
  rw [stdSimplex.map_vertex]
  rfl

/-- The `δ₁` face of an actual singular `1`-simplex is its initial endpoint,
after transport through `TopCat.toSSetObjEquiv`. -/
theorem singularOneSimplex_delta_one_endpoint (s : SingularOneSimplex) :
    (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))
        ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s))
        (stdSimplex.vertex (0 : Fin 1))
      = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s)
          (stdSimplex.vertex (0 : Fin 2)) := by
  dsimp [TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr]
  congr 1
  change Homeomorph.ulift.symm
      (stdSimplex.map (ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2)))
        (stdSimplex.vertex (0 : Fin 1))) =
    Homeomorph.ulift.symm (stdSimplex.vertex (0 : Fin 2))
  rw [stdSimplex.map_vertex]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A concrete singular edge with equal geometric endpoints becomes an actual
closed singular `1`-simplex after transport through `TopCat.toSSetObjEquiv`. -/
theorem singularOneSimplexOfMap_faces_eq_of_endpoints (f : OneSimplex)
    (h :
      f (stdSimplex.vertex (1 : Fin 2)) =
        f (stdSimplex.vertex (0 : Fin 2))) :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
        (singularOneSimplexOfMap f) =
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
        (singularOneSimplexOfMap f) := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))).injective
  ext x
  have hx : x = stdSimplex.vertex (0 : Fin 1) := by
    ext i
    fin_cases i
    have hsum := stdSimplex.sum_eq_one x
    simpa using hsum
  rw [hx]
  rw [singularOneSimplex_delta_zero_endpoint, singularOneSimplex_delta_one_endpoint]
  unfold singularOneSimplexOfMap
  rw [Equiv.apply_symm_apply]
  exact h

/-- An actual singular `1`-simplex with equal simplicial faces has integer
winding.  This is the generator-level integrality input for proving
`cycleWinding_integral`. -/
theorem singularWinding_loop_integral (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s) :
    ∃ k : ℤ, singularWinding s = (k : ℝ) := by
  unfold singularWinding
  apply simplexWinding_loop_integral
  have hmap := congrArg
    (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))) hfaces
  have hpt := congrFun (congrArg ContinuousMap.toFun hmap) (stdSimplex.vertex (0 : Fin 1))
  calc
    (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s)
        (stdSimplex.vertex (1 : Fin 2))
        = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s))
            (stdSimplex.vertex (0 : Fin 1)) := (singularOneSimplex_delta_zero_endpoint s).symm
    _ = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s))
            (stdSimplex.vertex (0 : Fin 1)) := hpt
    _ = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s)
        (stdSimplex.vertex (0 : Fin 2)) := singularOneSimplex_delta_one_endpoint s

/-- The actual `S¹`-point carried by a singular `0`-simplex, obtained by
transporting it through `TopCat.toSSetObjEquiv` and evaluating at the unique
vertex of `Δ⁰`. -/
def vertexPoint (v : SingularZeroSimplex) : SphereOne :=
  (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0)) v)
    (stdSimplex.vertex (0 : Fin 1))

/-- A singular `1`-simplex of the chain complex, read as a path `I → S¹` in the
unit-interval parameterisation.  This is the bridge between the chain-level edge
and the path-level winding/displacement invariants. -/
def singularEdgePath (s : SingularOneSimplex) : C(I, SphereOne) :=
  oneSimplexPath (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Reading a singular edge as a unit-interval path and then back as a concrete
singular `1`-simplex returns the original singular generator. -/
theorem singularOneSimplexOfMap_oneSimplexOfPath_singularEdgePath
    (s : SingularOneSimplex) :
    singularOneSimplexOfMap (oneSimplexOfPath (singularEdgePath s)) = s := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).injective
  unfold singularOneSimplexOfMap singularEdgePath
  rw [Equiv.apply_symm_apply, oneSimplexOfPath_oneSimplexPath]

/-- The initial point of a singular edge's path is the `S¹`-point of its initial
`0`-face. -/
theorem singularEdgePath_zero (s : SingularOneSimplex) :
    singularEdgePath s 0 = vertexPoint (edgeInitial s) := by
  unfold singularEdgePath vertexPoint edgeInitial oneSimplexPath
  rw [ContinuousMap.comp_apply, intervalToSimplex_zero]
  exact (singularOneSimplex_delta_one_endpoint s).symm

/-- The terminal point of a singular edge's path is the `S¹`-point of its terminal
`0`-face. -/
theorem singularEdgePath_one (s : SingularOneSimplex) :
    singularEdgePath s 1 = vertexPoint (edgeTerminal s) := by
  unfold singularEdgePath vertexPoint edgeTerminal oneSimplexPath
  rw [ContinuousMap.comp_apply, intervalToSimplex_one]
  exact (singularOneSimplex_delta_zero_endpoint s).symm

/-- The winding of a singular edge is the displacement of its path, normalized by
one full turn. -/
theorem singularWinding_eq_pathDisplacement (s : SingularOneSimplex) :
    singularWinding s = pathDisplacement (singularEdgePath s) / (2 * Real.pi) := by
  unfold singularWinding simplexWinding simplexDisplacement singularEdgePath
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A closed singular edge with zero singular winding is homotopic rel endpoints
to the constant path at its basepoint.  This is the path-level null-homotopy
input needed by the remaining singular prism construction. -/
theorem singularEdgePath_homotopicRel_const_of_loop_winding_zero
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (hw : singularWinding s = 0) :
    (singularEdgePath s).HomotopicRel
      (ContinuousMap.const I (singularEdgePath s 0)) {0, 1} := by
  apply pathHomotopicRel_const_of_loop_winding_zero
  · rw [singularEdgePath_one, singularEdgePath_zero]
    exact congrArg vertexPoint hfaces
  · unfold pathWinding
    rw [← singularWinding_eq_pathDisplacement]
    exact hw

/-- **Closed-walk winding integrality (singular-edge form).**  If a finite family
of singular `1`-simplices forms a cyclically connected walk (terminal `0`-face of
`e i` equals initial `0`-face of `e (finRotate k i)`), then the total winding
around the walk is an integer.

This is the integrality engine for the `winding_integral` field of a multi-edge
cyclic edge-list piece: it reduces the integer winding of an extracted directed
cycle to the purely combinatorial fact that the cycle's `0`-faces chain up.  It
uses no prism/subdivision operator, only `displacementSum_cyclic_intMul` and the
endpoint identifications above. -/
theorem singularWindingSum_cyclic_integral {k : ℕ} (e : Fin k → SingularOneSimplex)
    (hconn : ∀ i : Fin k, edgeTerminal (e i) = edgeInitial (e (finRotate k i))) :
    ∃ n : ℤ, ∑ i, singularWinding (e i) = (n : ℝ) := by
  have hpathconn : ∀ i : Fin k,
      (singularEdgePath (e i)) 1 = (singularEdgePath (e (finRotate k i))) 0 := by
    intro i
    rw [singularEdgePath_one, singularEdgePath_zero]
    exact congrArg vertexPoint (hconn i)
  obtain ⟨m, hm⟩ :=
    displacementSum_cyclic_intMul (fun i => singularEdgePath (e i)) hpathconn
  refine ⟨m, ?_⟩
  have hsum :
      ∑ i, singularWinding (e i)
        = (∑ i, pathDisplacement (singularEdgePath (e i))) / (2 * Real.pi) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact singularWinding_eq_pathDisplacement (e i)
  rw [hsum, hm]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [mul_div_assoc, div_self hpi, mul_one]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Cyclic free-boundary vanishing (C₀ telescoping).**  The free edge-chain of a
cyclically connected family of singular `1`-simplices is a cycle: its explicit
free boundary vanishes.  This is the `C₀` companion of
`singularWindingSum_cyclic_integral`; it is the same `finRotate` reindexing
telescoping, now applied to the boundary `terminal − initial` instead of the
winding displacement.  It supplies the boundary-zero proof needed to lift a closed
edge-walk to an element of the degree-`1` cycles. -/
theorem cyclicEdgeFamily_freeBoundary_zero {k : ℕ} (e : Fin k → SingularOneSimplex)
    (hconn : ∀ i : Fin k, edgeTerminal (e i) = edgeInitial (e (finRotate k i))) :
    ModuleCat.Hom.hom singularOneBoundaryFree (∑ i, ModuleCat.freeMk (e i)) = 0 := by
  rw [map_sum]
  have hterm : ∀ i : Fin k,
      ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk (e i))
        = ModuleCat.freeMk (edgeTerminal (e i)) - ModuleCat.freeMk (edgeInitial (e i)) := by
    intro i
    rw [singularOneBoundaryFree_freeMk]; rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  have hreindex :
      (∑ i, ModuleCat.freeMk (edgeInitial (e i)) : singularZeroChainFree)
        = ∑ i, ModuleCat.freeMk (edgeTerminal (e i)) := by
    rw [← Equiv.sum_comp (finRotate k)
      (fun j => (ModuleCat.freeMk (edgeInitial (e j)) : singularZeroChainFree))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact congrArg ModuleCat.freeMk (hconn i).symm
  rw [hreindex, sub_self]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A singular `1`-simplex with equal endpoints is a cycle at the chain level.
This is the generator-level boundary-zero statement in the actual singular chain
complex. -/
theorem singularOneSimplexChain_boundary_zero_of_faces_eq (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s) :
    (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s)
      ≫ sphereOneSingularIntChainComplex.d 1 0 = 0 := by
  dsimp [sphereOneSingularIntChainComplex,
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
        ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s) +
      -Sigma.ι (fun x => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s) =
    0
  rw [hfaces]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Boundary of one singular `1`-simplex generator in explicit free-`C₀`
coordinates: terminal `0`-face minus initial `0`-face.  This is the raw
finite-support cancellation surface for the remaining cycle decomposition
theorem. -/
theorem singularOneSimplexChain_boundary_free (s : SingularOneSimplex) :
    Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫
        sphereOneSingularIntChainComplex.d 1 0 ≫ singularZeroChainToFree =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ singularZeroChainFree
        (ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s) -
          ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s))) := by
  dsimp [sphereOneSingularIntChainComplex,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex,
    sigmaConst]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  dsimp [AlgebraicTopology.AlternatingFaceMapComplex.objD]
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_zsmul, one_zsmul, Preadditive.comp_add, Preadditive.comp_neg,
    Preadditive.add_comp, Preadditive.neg_comp]
  simp only [CategoryTheory.SimplicialObject.δ]
  dsimp [sigmaConst]
  simp only [Sigma.ι_comp_map'_assoc, Category.id_comp]
  rw [singularZeroChainToFree]
  rw [Sigma.ι_desc, Sigma.ι_desc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_add, ModuleCat.hom_neg, ModuleCat.hom_ofHom,
    LinearMap.add_apply, LinearMap.neg_apply, LinearMap.toSpanSingleton_apply]
  simp [sub_eq_add_neg]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The Mathlib singular boundary, transported from explicit free `C₁` to
explicit free `C₀`, is the free boundary `terminal - initial`. -/
theorem singularOneChainFreeToChain_boundary_free :
    singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 ≫
        singularZeroChainToFree =
      singularOneBoundaryFree := by
  apply ModuleCat.free_hom_ext
  intro s
  change ModuleCat.Hom.hom
      (singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 ≫
        singularZeroChainToFree) (ModuleCat.freeMk s) =
    ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk s)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [singularOneChainFreeToChain_freeMk]
  change ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫
        sphereOneSingularIntChainComplex.d 1 0 ≫ singularZeroChainToFree) 1 =
    ModuleCat.Hom.hom singularOneBoundaryFree (ModuleCat.freeMk s)
  rw [singularOneSimplexChain_boundary_free]
  rw [singularOneBoundaryFree_freeMk]
  simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Transporting Mathlib's raw boundary along the explicit free `C₁` isomorphism
gives the explicit free boundary. -/
theorem singularOneChainToFree_boundary_free :
    singularOneChainToFree ≫ singularOneBoundaryFree =
      sphereOneSingularIntChainComplex.d 1 0 ≫ singularZeroChainToFree := by
  haveI : IsIso singularOneChainFreeToChain := by
    change IsIso singularOneChainFreeIso.inv
    infer_instance
  rw [← cancel_epi singularOneChainFreeToChain]
  calc
    singularOneChainFreeToChain ≫ singularOneChainToFree ≫ singularOneBoundaryFree
        = singularOneBoundaryFree := by
          exact singularOneChainFreeIso.inv_hom_id_assoc singularOneBoundaryFree
    _ = singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 ≫
          singularZeroChainToFree := singularOneChainFreeToChain_boundary_free.symm

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The actual cycle object element generated by a closed singular `1`-simplex. -/
noncomputable def closedSingularOneCycle (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s) :
    ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.cycles 1 :=
  sphereOneSingularIntChainComplex.liftCycles
    (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) 0 (by simp)
    (singularOneSimplexChain_boundary_zero_of_faces_eq s hfaces)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Including a closed singular generator cycle into `C₁` recovers the
corresponding coproduct generator. -/
theorem closedSingularOneCycle_iCycles (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s) :
    closedSingularOneCycle s hfaces ≫ sphereOneSingularIntChainComplex.iCycles 1 =
      Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s := by
  rw [closedSingularOneCycle, HomologicalComplex.liftCycles_i]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The constant singular `1`-simplex is closed. -/
theorem constantSingularOneSimplex_faces_eq (p : SphereOne) :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
        (constantSingularOneSimplex p) =
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
        (constantSingularOneSimplex p) := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))).injective
  dsimp [constantSingularOneSimplex,
    TopCat.toSSetObjEquiv, TopCat.toSSet,
    CategoryTheory.Presheaf.restrictedULiftYoneda,
    CategoryTheory.SimplicialObject.δ,
    CategoryTheory.ConcreteCategory.homEquiv,
    Homeomorph.continuousMapCongr]
  ext x
  rfl

/-! ## The winding chain map and the split-injective half of `H₁(S¹;ℤ) ≅ ℤ`

We assemble the singular winding numbers into an honest morphism of `ℤ`-modules
`W : C₁(S¹) → ℝ` out of the degree-`1` singular chain group, prove it annihilates
the singular boundary `∂₂` (so it descends to a homomorphism on `H₁`), and prove
it sends the fundamental cycle to `1`.

This is the split-injective half of `H₁(S¹;ℤ) ≅ ℤ`: the comparison map
`ℤ → H₁`, `n ↦ n·[fundamental]`, has a left inverse, so it is injective and
`[fundamental]` has infinite order.  The converse (every `1`-cycle is homologous
to an integer multiple of the fundamental cycle) is the generation half; it needs
the simplicial prism / subdivision operator, which Mathlib's singular homology
does not yet provide. -/

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The winding chain map** `W : C₁(S¹;ℤ) → ℝ`.  On the free generator indexed
by a singular `1`-simplex `s` it is `n ↦ n · (winding number of s)`. -/
noncomputable def windingChainMap :
    sphereOneSingularIntChainComplex.X 1 ⟶ ModuleCat.of ℤ ℝ :=
  Limits.Sigma.desc (fun s : SingularOneSimplex =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℝ (singularWinding s)))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding chain map evaluates each generator to its winding number. -/
theorem windingChainMap_ι (s : SingularOneSimplex) :
    Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫ windingChainMap
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℝ (singularWinding s)) :=
  Sigma.ι_desc _ s

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw boundary of a singular `2`-simplex generator in `C₁(S¹;ℤ)`: the
alternating sum of its three singular `1`-faces.  The explicit prism construction
for zero-winding cycles will use this equality before applying any invariant. -/
theorem singularTwoSimplex_boundary_ι (s : SingularTwoSimplex) :
    (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s)
      ≫ sphereOneSingularIntChainComplex.d 2 1 =
        Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) s) -
        Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) s) +
        Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) s) := by
  dsimp [sphereOneSingularIntChainComplex,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex, sigmaConst]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  dsimp [AlgebraicTopology.AlternatingFaceMapComplex.objD]
  simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    Fin.val_two, neg_one_sq, neg_zsmul]
  simp only [CategoryTheory.SimplicialObject.δ]
  dsimp [sigmaConst]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, Sigma.ι_comp_map', Category.id_comp]
  abel_nf

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Element-level form of `singularTwoSimplex_boundary_ι`, applied to the unit
generator of the singular `2`-simplex summand. -/
theorem singularTwoSimplex_boundary_apply (s : SingularTwoSimplex) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1)
      (ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s) 1) =
        ModuleCat.Hom.hom
          (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) s)) 1 -
        ModuleCat.Hom.hom
          (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) s)) 1 +
        ModuleCat.Hom.hom
          (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) s)) 1 := by
  have h := congrArg (fun f =>
      ModuleCat.Hom.hom f (1 : ModuleCat.of ℤ ℤ))
    (singularTwoSimplex_boundary_ι s)
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_add, ModuleCat.hom_sub, ModuleCat.hom_neg,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply] using h

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Mathlib's singular `C₂ → C₁` boundary, transported from explicit free `C₂`
to explicit free `C₁`, is exactly the free alternating-face boundary. -/
theorem singularTwoChainFreeToChain_boundary_free :
    singularTwoChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 2 1 ≫
        singularOneChainToFree =
      singularTwoBoundaryFree := by
  apply ModuleCat.free_hom_ext
  intro s
  change ModuleCat.Hom.hom
      (singularTwoChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 2 1 ≫
        singularOneChainToFree) (ModuleCat.freeMk s) =
      ModuleCat.Hom.hom singularTwoBoundaryFree (ModuleCat.freeMk s)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [singularTwoChainFreeToChain, ModuleCat.freeDesc_apply]
  rw [singularTwoSimplex_boundary_apply]
  rw [singularTwoBoundaryFree_freeMk]
  rw [map_add, map_sub]
  change ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) s) ≫
          singularOneChainToFree) 1 -
      ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) s) ≫
            singularOneChainToFree) 1 +
      ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) s) ≫
            singularOneChainToFree) 1 =
    ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) s) -
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) s) +
      ModuleCat.freeMk ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) s)
  rw [singularOneChainToFree_ι, singularOneChainToFree_ι, singularOneChainToFree_ι]
  simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If an explicit free `C₂` chain has a given free `C₁` boundary, then its raw
image in Mathlib's chain complex has the corresponding raw `C₁` boundary. -/
theorem rawBoundary_eq_of_singularTwoBoundaryFree_eq
    (B : singularTwoChainFree) (u : singularOneChainFree)
    (hB : ModuleCat.Hom.hom singularTwoBoundaryFree B = u) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1)
      (ModuleCat.Hom.hom singularTwoChainFreeToChain B) =
        ModuleCat.Hom.hom singularOneChainFreeToChain u := by
  have hinj_toFree : Function.Injective (ModuleCat.Hom.hom singularOneChainToFree) := by
    haveI : IsIso singularOneChainToFree := by
      change IsIso singularOneChainFreeIso.hom
      infer_instance
    haveI : Mono singularOneChainToFree := inferInstance
    exact (ModuleCat.mono_iff_injective singularOneChainToFree).mp inferInstance
  apply hinj_toFree
  have hcomp := congrArg (fun f => ModuleCat.Hom.hom f B)
    singularTwoChainFreeToChain_boundary_free
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcomp
  rw [hB] at hcomp
  have hround :
      ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom singularOneChainFreeToChain u) = u := by
    have hid := congrArg (fun f => ModuleCat.Hom.hom f u)
      singularOneChainFreeIso.inv_hom_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [hround]
  exact hcomp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw-chain form of `constantSingularOneSimplex_free_boundary`: the boundary of
the constant singular `2`-simplex is the raw generator corresponding to the
constant singular `1`-simplex. -/
theorem constantSingularOneSimplex_raw_boundary (p : SphereOne) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1)
      (ModuleCat.Hom.hom singularTwoChainFreeToChain
        (ModuleCat.freeMk (constantSingularTwoSimplex p))) =
      ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ)
          (constantSingularOneSimplex p)) 1 := by
  have hraw := rawBoundary_eq_of_singularTwoBoundaryFree_eq
    (ModuleCat.freeMk (constantSingularTwoSimplex p))
    (ModuleCat.freeMk (constantSingularOneSimplex p))
    (constantSingularOneSimplex_free_boundary p)
  rw [singularOneChainFreeToChain_freeMk] at hraw
  exact hraw

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The constant closed singular `1`-cycle bounds the constant singular
`2`-simplex at the cycle-object level. -/
theorem constantSingularOneCycle_bounds (p : SphereOne) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom
          (closedSingularOneCycle (constantSingularOneSimplex p)
            (constantSingularOneSimplex_faces_eq p)) 1 := by
  let b : sphereOneSingularIntChainComplex.X 2 :=
    ModuleCat.Hom.hom singularTwoChainFreeToChain
      (ModuleCat.freeMk (constantSingularTwoSimplex p))
  refine ⟨b, ?_⟩
  have hinj_iCycles :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  apply hinj_iCycles
  change ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1) b =
    ModuleCat.Hom.hom
      ((closedSingularOneCycle (constantSingularOneSimplex p)
          (constantSingularOneSimplex_faces_eq p)) ≫
        sphereOneSingularIntChainComplex.iCycles 1) 1
  rw [HomologicalComplex.toCycles_i]
  rw [constantSingularOneSimplex_raw_boundary p]
  rw [closedSingularOneCycle_iCycles]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Algebraic consumer for a hand-built free prism: if a closed singular
`1`-simplex generator is the explicit free boundary of a free `2`-chain, then
the corresponding cycle-object generator is a `toCycles` boundary.  The remaining
geometric task is therefore to construct such a free `2`-chain from a
rel-endpoint nullhomotopy. -/
theorem closedSingularOneCycle_bounds_of_free_boundary
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (B : singularTwoChainFree)
    (hB : ModuleCat.Hom.hom singularTwoBoundaryFree B = ModuleCat.freeMk s) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 := by
  let b : sphereOneSingularIntChainComplex.X 2 :=
    ModuleCat.Hom.hom singularTwoChainFreeToChain B
  refine ⟨b, ?_⟩
  have hraw := rawBoundary_eq_of_singularTwoBoundaryFree_eq B (ModuleCat.freeMk s) hB
  rw [singularOneChainFreeToChain_freeMk] at hraw
  have hinj_iCycles :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  apply hinj_iCycles
  change ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1) b =
    ModuleCat.Hom.hom
      ((closedSingularOneCycle s hfaces) ≫
        sphereOneSingularIntChainComplex.iCycles 1) 1
  rw [HomologicalComplex.toCycles_i]
  rw [hraw]
  rw [closedSingularOneCycle_iCycles]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw-chain version of `closedSingularOneCycle_bounds_of_free_boundary`.  A raw
singular `2`-chain whose boundary is the raw generator of a closed singular edge
already proves that the closed generator cycle bounds. -/
theorem closedSingularOneCycle_bounds_of_raw_boundary
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (b : sphereOneSingularIntChainComplex.X 2)
    (hb : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1) b =
      ModuleCat.Hom.hom
        (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s) 1) :
    ∃ c : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) c =
        ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 := by
  refine ⟨b, ?_⟩
  have hinj_iCycles :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  apply hinj_iCycles
  change ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1) b =
    ModuleCat.Hom.hom
      ((closedSingularOneCycle s hfaces) ≫
        sphereOneSingularIntChainComplex.iCycles 1) 1
  rw [HomologicalComplex.toCycles_i]
  rw [hb]
  rw [closedSingularOneCycle_iCycles]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A cone singular `2`-simplex over a closed singular edge proves that the
corresponding closed singular `1`-cycle bounds.  This is the smallest geometric
handoff needed after `singularEdgePath_homotopicRel_const_of_loop_winding_zero`:
construct such a cone simplex from the rel-endpoint nullhomotopy. -/
theorem closedSingularOneCycle_bounds_of_cone_simplex
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (sigma : SingularTwoSimplex)
    (hbase : (TopCat.toSSet.obj (TopCat.sphere 1)).δ (2 : Fin 3) sigma = s)
    (hsides :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 3) sigma =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 3) sigma) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 :=
  closedSingularOneCycle_bounds_of_free_boundary s hfaces (ModuleCat.freeMk sigma)
    (singularTwoBoundaryFree_freeMk_of_cone_faces sigma s hbase hsides)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Continuous-map handoff for the cone filling.  It is enough to build a
continuous `F : C(Δ²,S¹)` whose base face is a given `f : C(Δ¹,S¹)` and whose two
side faces agree.  After transporting `F` through `TopCat.toSSetObjEquiv`, the
corresponding closed singular generator bounds in the actual chain complex. -/
theorem closedSingularOneCycle_bounds_of_cone_map
    (f : OneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2)
          (singularOneSimplexOfMap f) =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2)
          (singularOneSimplexOfMap f))
    (F : TwoSimplex)
    (hbase : face F (2 : Fin 3) = f)
    (hsides : face F (0 : Fin 3) = face F (1 : Fin 3)) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom
          (closedSingularOneCycle (singularOneSimplexOfMap f) hfaces) 1 := by
  refine closedSingularOneCycle_bounds_of_cone_simplex
    (singularOneSimplexOfMap f) hfaces (singularTwoSimplexOfMap F) ?_ ?_
  · rw [singularTwoSimplexOfMap_delta, hbase]
  · rw [singularTwoSimplexOfMap_delta, singularTwoSimplexOfMap_delta, hsides]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Endpoint-form cone handoff.  To prove that a concrete closed edge bounds, it
is now enough to construct a continuous `2`-simplex whose base face is that edge
and whose two side faces agree.  This is the exact target left by the
zero-winding nullhomotopy: build the conical extension `F : C(Δ²,S¹)`. -/
theorem closedSingularOneCycle_bounds_of_closed_cone_map
    (f : OneSimplex)
    (hendpoints :
      f (stdSimplex.vertex (1 : Fin 2)) =
        f (stdSimplex.vertex (0 : Fin 2)))
    (F : TwoSimplex)
    (hbase : face F (2 : Fin 3) = f)
    (hsides : face F (0 : Fin 3) = face F (1 : Fin 3)) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom
          (closedSingularOneCycle (singularOneSimplexOfMap f)
            (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints)) 1 :=
  closedSingularOneCycle_bounds_of_cone_map f
    (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints) F hbase hsides

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Continuity-hypothesis form of the closed-edge cone filler.  After all
pointwise face identities above, the full singular `2`-chain boundary follows
from one remaining analytic theorem:
`Continuous (coneCirclePoint (oneSimplexPath f))`. -/
theorem closedSingularOneCycle_bounds_of_continuous_coneCirclePoint
    (f : OneSimplex)
    (hendpoints :
      f (stdSimplex.vertex (1 : Fin 2)) =
        f (stdSimplex.vertex (0 : Fin 2)))
    (hzero : simplexWinding f = 0)
    (hcont : Continuous (coneCirclePoint (oneSimplexPath f))) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom
          (closedSingularOneCycle (singularOneSimplexOfMap f)
            (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints)) 1 :=
  closedSingularOneCycle_bounds_of_closed_cone_map f hendpoints
    (coneCircleMapOfContinuous (oneSimplexPath f) hcont)
    (coneCircleMapOfContinuous_face_two f hcont)
    (coneCircleMapOfContinuous_side_faces_eq_of_winding_zero f hzero hcont)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A closed singular edge with zero winding bounds by the explicit continuous
cone over its lifted path.  This removes the last analytic hypothesis from the
single-edge zero-winding cone construction. -/
theorem closedSingularOneCycle_bounds_of_zero_winding_coneCirclePoint
    (f : OneSimplex)
    (hendpoints :
      f (stdSimplex.vertex (1 : Fin 2)) =
        f (stdSimplex.vertex (0 : Fin 2)))
    (hzero : simplexWinding f = 0) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom
          (closedSingularOneCycle (singularOneSimplexOfMap f)
            (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints)) 1 :=
  closedSingularOneCycle_bounds_of_continuous_coneCirclePoint f hendpoints hzero
    (continuous_coneCirclePoint (oneSimplexPath f))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Actual-singular-simplex form of the zero-winding cone theorem.  This removes
the `C(Δ¹,S¹)` presentation from the consumer side: any closed Mathlib singular
`1`-simplex with zero `singularWinding` bounds. -/
theorem closedSingularOneCycle_bounds_of_zero_singularWinding
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (hzero : singularWinding s = 0) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b =
        ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 := by
  let f : OneSimplex :=
    TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1)) s
  have hendpoints :
      f (stdSimplex.vertex (1 : Fin 2)) = f (stdSimplex.vertex (0 : Fin 2)) := by
    have hcong :=
      congrArg (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))) hfaces
    have happ := congrFun (congrArg ContinuousMap.toFun hcong) (stdSimplex.vertex (0 : Fin 1))
    calc
      f (stdSimplex.vertex (1 : Fin 2))
          = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s))
              (stdSimplex.vertex (0 : Fin 1)) := by
            exact (singularOneSimplex_delta_zero_endpoint s).symm
      _ = (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 0))
            ((TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s))
              (stdSimplex.vertex (0 : Fin 1)) := happ
      _ = f (stdSimplex.vertex (0 : Fin 2)) := by
            exact singularOneSimplex_delta_one_endpoint s
  have hzero_f : simplexWinding f = 0 := by
    simpa [f, singularWinding] using hzero
  obtain ⟨b, hb⟩ :=
    closedSingularOneCycle_bounds_of_zero_winding_coneCirclePoint f hendpoints hzero_f
  refine ⟨b, ?_⟩
  have hs : singularOneSimplexOfMap f = s := by
    unfold f singularOneSimplexOfMap
    rw [Equiv.symm_apply_apply]
  have hcycles :
      ModuleCat.Hom.hom
          (closedSingularOneCycle (singularOneSimplexOfMap f)
            (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints)) 1 =
        ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 := by
    have hinj_iCycles :
        Function.Injective
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
      (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
    apply hinj_iCycles
    change ModuleCat.Hom.hom
        ((closedSingularOneCycle (singularOneSimplexOfMap f)
            (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints)) ≫
          sphereOneSingularIntChainComplex.iCycles 1) 1 =
      ModuleCat.Hom.hom ((closedSingularOneCycle s hfaces) ≫
          sphereOneSingularIntChainComplex.iCycles 1) 1
    rw [closedSingularOneCycle_iCycles, closedSingularOneCycle_iCycles]
    rw [hs]
  rw [← hcycles]
  exact hb

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Scalar form of the zero-winding closed-generator cone theorem.  Any integer
multiple of a zero-winding closed singular generator bounds. -/
theorem closedSingularOneCycle_zsmul_bounds_of_zero_singularWinding
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (hzero : singularWinding s = 0) (n : ModuleCat.of ℤ ℤ) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) n =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b := by
  obtain ⟨b, hb⟩ := closedSingularOneCycle_bounds_of_zero_singularWinding s hfaces hzero
  refine ⟨n • b, ?_⟩
  rw [map_zsmul]
  have hlin :
      ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) n =
        n • ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) (1 : ℤ) := by
    conv_lhs => rw [show n = n • (1 : ModuleCat.of ℤ ℤ) by simp]
    rw [map_zsmul]
  rw [hlin, ← hb]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Converse transport for `C₂`: if a raw singular `2`-chain has raw boundary
equal to the image of a free `C₁` chain, then its free-coordinate representative
has that free boundary.  This closes the representational gap between raw-prism
and free-prism witnesses; the remaining mathematical work is to build the raw
prism itself. -/
theorem singularTwoBoundaryFree_eq_of_rawBoundary_eq
    (b : sphereOneSingularIntChainComplex.X 2) (u : singularOneChainFree)
    (hb : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1) b =
      ModuleCat.Hom.hom singularOneChainFreeToChain u) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.Hom.hom singularTwoChainToFree b) = u := by
  have hcomp := congrArg (fun f =>
      ModuleCat.Hom.hom f (ModuleCat.Hom.hom singularTwoChainToFree b))
    singularTwoChainFreeToChain_boundary_free
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcomp
  have htwo :
      ModuleCat.Hom.hom singularTwoChainFreeToChain
        (ModuleCat.Hom.hom singularTwoChainToFree b) = b := by
    have hid := congrArg (fun f => ModuleCat.Hom.hom f b)
      singularTwoChainFreeIso.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [htwo, hb] at hcomp
  have hround :
      ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom singularOneChainFreeToChain u) = u := by
    have hid := congrArg (fun f => ModuleCat.Hom.hom f u)
      singularOneChainFreeIso.inv_hom_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [hround] at hcomp
  exact hcomp.symm

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Element-level exactness for a `ModuleCat` cokernel cofork: an element killed
by the cokernel projection lies in the range of the previous map. -/
theorem exists_preimage_of_isColimit_cokernel_eq_zero
    {R : Type} [Ring R] {M N Q : ModuleCat R} {f : M ⟶ N} {p : N ⟶ Q}
    {w : f ≫ p = 0} (hcol : IsColimit (CokernelCofork.ofπ p w))
    (x : N) (hx : ModuleCat.Hom.hom p x = 0) :
    ∃ m : M, ModuleCat.Hom.hom f m = x := by
  let desc : Q ⟶ ModuleCat.of R (N ⧸ LinearMap.range (ModuleCat.Hom.hom f)) :=
    hcol.desc (ModuleCat.cokernelCocone f)
  have hpdesc : p ≫ desc = (ModuleCat.cokernelCocone f).π := by
    simpa [desc, ModuleCat.cokernelCocone, CokernelCofork.ofπ] using
      hcol.fac (ModuleCat.cokernelCocone f) WalkingParallelPair.one
  have hq : Submodule.Quotient.mk x = (0 : N ⧸ LinearMap.range (ModuleCat.Hom.hom f)) := by
    have hxdesc : ModuleCat.Hom.hom (p ≫ desc) x = 0 := by
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hx, map_zero]
    rw [hpdesc] at hxdesc
    simpa [ModuleCat.cokernelCocone] using hxdesc
  have hxrange : x ∈ LinearMap.range (ModuleCat.Hom.hom f) := by
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (ModuleCat.Hom.hom f))).mp hq
  rcases LinearMap.mem_range.mp hxrange with ⟨m, hm⟩
  exact ⟨m, hm⟩

/-- In the downward natural-number chain-complex shape, the predecessor of degree
`1` is degree `2`. -/
theorem down_prev_one_eq_two : (ComplexShape.down ℕ).prev 1 = 2 := by
  unfold ComplexShape.prev
  split
  · rename_i h
    apply (ComplexShape.down ℕ).prev_eq
    · exact h.choose_spec
    · rw [ComplexShape.down_Rel]; norm_num
  · rename_i h
    exfalso
    apply h
    exact ⟨2, by rw [ComplexShape.down_Rel]; norm_num⟩

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A degree-`1` cycle whose homology class is zero is explicitly a degree-`2`
boundary.  This is the element-level exactness of the homology cokernel
specialized to the circle singular chain complex. -/
theorem cycle_eq_boundary_of_homologyπ_eq_zero
    (z : sphereOneSingularIntChainComplex.cycles 1)
    (hz : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1) z = 0) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      z = ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b := by
  let S := sphereOneSingularIntChainComplex.sc 1
  have hcol := ShortComplex.homologyIsCokernel S
  have hex := exists_preimage_of_isColimit_cokernel_eq_zero hcol z hz
  change ∃ b : sphereOneSingularIntChainComplex.X ((ComplexShape.down ℕ).prev 1),
      ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.toCycles ((ComplexShape.down ℕ).prev 1) 1) b = z at hex
  rw [down_prev_one_eq_two] at hex
  rcases hex with ⟨b, hb⟩
  exact ⟨b, hb.symm⟩

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding chain map annihilates the boundary of every singular `2`-simplex
generator.  This is the per-generator form of `∂₂ ≫ W = 0`. -/
theorem windingChainMap_boundary_generator (s : SingularTwoSimplex) :
    (Sigma.ι (fun _ : SingularTwoSimplex => ModuleCat.of ℤ ℤ) s)
      ≫ sphereOneSingularIntChainComplex.d 2 1 ≫ windingChainMap = 0 := by
  dsimp [sphereOneSingularIntChainComplex,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex, sigmaConst]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  dsimp [AlgebraicTopology.AlternatingFaceMapComplex.objD]
  simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    Fin.val_two, neg_one_sq, neg_zsmul, Preadditive.comp_add, Preadditive.comp_neg,
    Preadditive.add_comp, Preadditive.neg_comp]
  simp only [CategoryTheory.SimplicialObject.δ]
  dsimp [sigmaConst]
  simp only [Sigma.ι_comp_map'_assoc, Category.id_comp]
  rw [windingChainMap_ι, windingChainMap_ι, windingChainMap_ι]
  have hb := singularWinding_boundary s
  simp only [CategoryTheory.SimplicialObject.δ] at hb
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_add, ModuleCat.hom_neg, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  linarith [hb]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The winding chain map descends to homology.**  It annihilates the entire
degree-`2` boundary `∂₂`, hence factors through `H₁(S¹;ℤ)`. -/
theorem windingChainMap_boundary :
    sphereOneSingularIntChainComplex.d 2 1 ≫ windingChainMap = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  simp only [Limits.comp_zero]
  exact windingChainMap_boundary_generator s

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding number of the fundamental singular `1`-simplex is `1`. -/
theorem singularWinding_fundamentalSimplex :
    singularWinding CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex = 1 := by
  rw [singularWinding,
    show TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))
          CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex
        = CircleFundamentalSimplex.fundamentalCirclePathMap from
      (TopCat.toSSetObjEquiv (TopCat.sphere 1) (op (SimplexCategory.mk 1))).apply_symm_apply _]
  exact simplexWinding_fundamental

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The winding chain map sends the fundamental cycle to `1`.**  Together with
`windingChainMap_boundary` this exhibits the integer comparison map
`ℤ → H₁(S¹;ℤ)` as split-injective: `[fundamental]` has infinite order. -/
theorem windingChainMap_fundamental :
    CircleH1Computation.fundamentalSphereOneSingularOneChain ≫ windingChainMap
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℝ 1) := by
  rw [CircleH1Computation.fundamentalSphereOneSingularOneChain, windingChainMap_ι,
    singularWinding_fundamentalSimplex]

/-! ### Descent to homology: the fundamental class has infinite order

The chain-level data above is exactly what is needed to descend the winding
number to a homomorphism `H₁(S¹;ℤ) → ℝ` and to exhibit the integer comparison
map `ℤ → H₁(S¹;ℤ)`, `n ↦ n·[fundamental]`, as a (split) monomorphism.  This is
the *injective* half of `H₁(S¹;ℤ) ≅ ℤ`: distinct integer multiples of the
fundamental loop are never homologous, i.e. `[fundamental]` has infinite order.
The *surjective* (generation) half, that every singular `1`-cycle is homologous
to an integer multiple of the fundamental cycle, is **not** proved here; it
requires the simplicial prism / barycentric subdivision operator, which
Mathlib's singular homology does not provide. -/

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The winding number descends to homology** `H₁(S¹;ℤ) → ℝ`.  Because the
winding chain map annihilates `∂₂` (`windingChainMap_boundary`), it factors
through the degree-`1` opcycles and hence through `H₁`. -/
noncomputable def windingHomologyMap :
    sphereOneSingularIntChainComplex.homology 1 ⟶ ModuleCat.of ℤ ℝ :=
  sphereOneSingularIntChainComplex.homologyι 1
    ≫ sphereOneSingularIntChainComplex.descOpcycles windingChainMap 2 (by simp)
        windingChainMap_boundary

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The fundamental singular `1`-chain, lifted to the cycle object using its
zero-boundary proof. -/
noncomputable def fundamentalCycle :
    ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.cycles 1 :=
  sphereOneSingularIntChainComplex.liftCycles
      CircleH1Computation.fundamentalSphereOneSingularOneChain 0 (by simp)
      CircleH1Computation.fundamentalSphereOneSingularOneChain_boundary_zero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Generation-shaped form of the zero-winding closed-edge cone theorem.  The
integer coefficient of the fundamental cycle is `0`; all of the edge is accounted
for by the explicit cone boundary. -/
theorem closedSingularOneCycle_boundary_generate_of_zero_winding_coneCirclePoint
    (f : OneSimplex)
    (hendpoints :
      f (stdSimplex.vertex (1 : Fin 2)) =
        f (stdSimplex.vertex (0 : Fin 2)))
    (hzero : simplexWinding f = 0) :
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      ModuleCat.Hom.hom
        (closedSingularOneCycle (singularOneSimplexOfMap f)
          (singularOneSimplexOfMap_faces_eq_of_endpoints f hendpoints)) 1 =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n := by
  obtain ⟨b, hb⟩ :=
    closedSingularOneCycle_bounds_of_zero_winding_coneCirclePoint f hendpoints hzero
  refine ⟨0, b, ?_⟩
  rw [map_zero]
  simp
  exact hb.symm

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Algebraic consumer for a closed-edge prism to an integer multiple of the
fundamental cycle.  If a free `2`-chain has boundary equal to the closed edge
generator minus the free-coordinate image of `n` times the fundamental cycle,
then the closed edge cycle is generated by the fundamental cycle modulo a
`2`-boundary. -/
theorem closedSingularOneCycle_boundary_generate_of_freePrismToFundamental
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (n : ModuleCat.of ℤ ℤ) (B : singularTwoChainFree)
    (hB : ModuleCat.Hom.hom singularTwoBoundaryFree B =
      ModuleCat.freeMk s -
        ModuleCat.Hom.hom singularOneChainToFree
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n))) :
    ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 =
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1)
        (ModuleCat.Hom.hom singularTwoChainFreeToChain B) +
        ModuleCat.Hom.hom fundamentalCycle n := by
  have hraw := rawBoundary_eq_of_singularTwoBoundaryFree_eq B
    (ModuleCat.freeMk s -
      ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n))) hB
  have hround :
      ModuleCat.Hom.hom singularOneChainFreeToChain
        (ModuleCat.Hom.hom singularOneChainToFree
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n))) =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n) := by
    have hid := congrArg
      (fun f => ModuleCat.Hom.hom f
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n)))
      singularOneChainFreeIso.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [map_sub, singularOneChainFreeToChain_freeMk, hround] at hraw
  have hinj_iCycles :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  apply hinj_iCycles
  rw [map_add]
  change ModuleCat.Hom.hom
      ((closedSingularOneCycle s hfaces) ≫ sphereOneSingularIntChainComplex.iCycles 1) 1 =
    ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom singularTwoChainFreeToChain B) +
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom fundamentalCycle n)
  rw [closedSingularOneCycle_iCycles, HomologicalComplex.toCycles_i, hraw]
  rw [sub_add_cancel]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw-chain version of
`closedSingularOneCycle_boundary_generate_of_freePrismToFundamental`. -/
theorem closedSingularOneCycle_boundary_generate_of_rawPrismToFundamental
    (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2)
    (hb : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1) b =
      ModuleCat.Hom.hom singularOneChainFreeToChain (ModuleCat.freeMk s) -
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n)) :
    ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) 1 =
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
        ModuleCat.Hom.hom fundamentalCycle n := by
  have hinj_iCycles :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  apply hinj_iCycles
  rw [map_add]
  change ModuleCat.Hom.hom
      ((closedSingularOneCycle s hfaces) ≫ sphereOneSingularIntChainComplex.iCycles 1) 1 =
    ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1) b +
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom fundamentalCycle n)
  rw [closedSingularOneCycle_iCycles, HomologicalComplex.toCycles_i, hb,
    singularOneChainFreeToChain_freeMk]
  rw [sub_add_cancel]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The integer comparison map** `ℤ → H₁(S¹;ℤ)`, `n ↦ n·[fundamental]`.  The
fundamental singular `1`-chain is a cycle (`fundamentalSphereOneSingularOneChain_boundary_zero`),
so it lifts to the degree-`1` cycles and projects to a homology class. -/
noncomputable def fundamentalHomologyClass :
    ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.homology 1 :=
  fundamentalCycle ≫ sphereOneSingularIntChainComplex.homologyπ 1

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The winding homomorphism is a retraction of the comparison map.**  The
composite `ℤ → H₁(S¹;ℤ) → ℝ` is the standard inclusion `n ↦ n·1`.  This is the
homology-level form of "the winding number is inverse to the fundamental loop
class": it pins `[fundamental]` to the real number `1`. -/
theorem fundamentalHomologyClass_comp_windingHomologyMap :
    fundamentalHomologyClass ≫ windingHomologyMap
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℝ 1) := by
  rw [fundamentalHomologyClass, fundamentalCycle, windingHomologyMap, Category.assoc,
    HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles,
    HomologicalComplex.liftCycles_i_assoc]
  exact windingChainMap_fundamental

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **`ℤ → H₁(S¹;ℤ)`, `n ↦ n·[fundamental]`, is a monomorphism.**  The fundamental
class has infinite order: distinct integer multiples of the once-around loop are
never homologous.  This is the injective half of `H₁(S¹;ℤ) ≅ ℤ`, proved by hand
from the covering-space winding invariant with no axioms and no `sorry`.

It is *not* the full isomorphism: surjectivity (that the fundamental loop
*generates* `H₁`) is the separate generation theorem and is left open. -/
theorem fundamentalHomologyClass_mono : Mono fundamentalHomologyClass := by
  have hmono : Mono (fundamentalHomologyClass ≫ windingHomologyMap) := by
    rw [fundamentalHomologyClass_comp_windingHomologyMap, ModuleCat.mono_iff_injective]
    intro a b hab
    have hcast : (a : ℝ) = (b : ℝ) := by
      simpa [LinearMap.toSpanSingleton_apply, zsmul_eq_mul] using hab
    exact_mod_cast hcast
  exact mono_of_mono fundamentalHomologyClass windingHomologyMap

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **`H₁(S¹;ℤ)` is nonzero, unconditionally.**  The fundamental loop is a nonzero
homology class: the winding retraction sends it to the real number `1`
(`fundamentalHomologyClass_comp_windingHomologyMap`).  Were the homology the zero
module, that comparison morphism would be the zero map, forcing `1 = 0` in `ℝ`.

The decisive point: nonvanishing needs only the *existence* of one nonzero class,
which is exactly the injective half already in hand (`fundamentalHomologyClass_mono`).
It does **not** use the surjectivity/generation theorem, so it is axiom-free and
`sorry`-free, and independent of `zeroWindingCycles_bound`. -/
theorem homologyOne_nonzero :
    ¬ IsZero (sphereOneSingularIntChainComplex.homology 1) := by
  intro hzero
  have hfz : fundamentalHomologyClass = 0 := hzero.eq_zero_of_tgt _
  have h0 : fundamentalHomologyClass ≫ windingHomologyMap = 0 := by
    rw [hfz, zero_comp]
  rw [fundamentalHomologyClass_comp_windingHomologyMap] at h0
  have h1 := congrArg
    (fun g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℝ => ModuleCat.Hom.hom g (1 : ℤ)) h0
  simp [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply] at h1

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The strict-T8 Mathlib nonvanishing target, discharged unconditionally.**
`MathlibCohomologyBridge.circleH1Z` is `rfl`-equal to
`sphereOneSingularIntChainComplex.homology 1`
(`CircleH1Computation.singularHomologyFunctorSphereOneInt_eq_homologyOne`), so the
nonvanishing of the imported Mathlib singular `H₁(S¹;ℤ)` object is exactly
`homologyOne_nonzero`.  This is the concrete circle-H1 computation the strict
T-1-to-T8 frontier closure was waiting on. -/
theorem circleH1ZNonzero_unconditional :
    MathlibCohomologyBridge.circleH1ZNonzero := by
  intro hzero
  exact homologyOne_nonzero
    (hzero.of_iso CircleH1Computation.singularHomologyFunctorSphereOneIntIsoHomologyOne.symm)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The Mathlib circle-linking backend object now exists unconditionally, built
straight from `circleH1ZNonzero_unconditional`. -/
theorem mathlibCircleLinkingBackend_unconditional :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZNonzero
    circleH1ZNonzero_unconditional

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The exact remaining generation statement, in homology-level form.  It says
that every degree-`1` homology class is an integer multiple of the fundamental
circle class.  This is deliberately stated as surjectivity of the already-built
comparison morphism `fundamentalHomologyClass`; proving this is the remaining
surjective half of `H₁(S¹;ℤ) ≅ ℤ`.

Note: this is **not** needed for the strict T-1-to-T8 frontier closure, which only
requires nonvanishing (`circleH1ZNonzero_unconditional`).  Surjectivity is the
stronger statement that upgrades nonvanishing to the full isomorphism. -/
def fundamentalHomologyClass_surjective : Prop :=
  Function.Surjective (ModuleCat.Hom.hom fundamentalHomologyClass)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the fundamental circle class generates first homology, then the
homology-level winding map is injective.  The proof uses the already-proved
identity `fundamentalHomologyClass ≫ windingHomologyMap = (n ↦ n)`. -/
theorem windingHomologyMap_mono_of_fundamentalHomologyClass_surjective
    (hsurj : fundamentalHomologyClass_surjective) :
    Mono windingHomologyMap := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  have hcomp :
      ModuleCat.Hom.hom (fundamentalHomologyClass ≫ windingHomologyMap) a =
        ModuleCat.Hom.hom (fundamentalHomologyClass ≫ windingHomologyMap) b := by
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using hxy
  rw [fundamentalHomologyClass_comp_windingHomologyMap] at hcomp
  have hcast : (a : ℝ) = (b : ℝ) := by
    simpa [LinearMap.toSpanSingleton_apply, zsmul_eq_mul] using hcomp
  have hab : a = b := by
    exact_mod_cast hcast
  rw [hab]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Winding already proves injectivity, so the remaining generation statement
upgrades the fundamental-class comparison map to a bijection of underlying
modules. -/
theorem fundamentalHomologyClass_bijective_of_surjective
    (hsurj : fundamentalHomologyClass_surjective) :
    Function.Bijective (ModuleCat.Hom.hom fundamentalHomologyClass) := by
  constructor
  · haveI : Mono fundamentalHomologyClass := fundamentalHomologyClass_mono
    exact (ModuleCat.mono_iff_injective fundamentalHomologyClass).mp inferInstance
  · exact hsurj

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the fundamental class generates first homology, then the comparison
`ℤ → H₁(S¹;ℤ)` is an isomorphism in `ModuleCat`.  The proof is purely categorical:
generation gives `Epi`; winding gives `Mono`; modules are balanced, so mono+epi is
an isomorphism. -/
noncomputable def fundamentalHomologyClassIso_of_surjective
    (hsurj : fundamentalHomologyClass_surjective) :
    ModuleCat.of ℤ ℤ ≅ sphereOneSingularIntChainComplex.homology 1 := by
  haveI : Mono fundamentalHomologyClass := fundamentalHomologyClass_mono
  haveI : Epi fundamentalHomologyClass :=
    (ModuleCat.epi_iff_surjective fundamentalHomologyClass).mpr hsurj
  haveI : IsIso fundamentalHomologyClass := isIso_of_mono_of_epi fundamentalHomologyClass
  exact asIso fundamentalHomologyClass

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Final handoff criterion for the remaining Mathlib element.**  The exact
Mathlib target `H₁(TopCat.sphere 1;ℤ) ≅ ℤ` follows from the single still-open
generation theorem that the fundamental class is surjective on first homology. -/
theorem circleH1ZIsoInt_of_fundamentalHomologyClass_surjective
    (hsurj : fundamentalHomologyClass_surjective) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  ⟨(fundamentalHomologyClassIso_of_surjective hsurj).symm⟩

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The concrete cycle-representative generation statement.  Every cycle
representative of a degree-`1` homology class has the same homology class as some
integer multiple of the fundamental cycle.

This is closer to the geometric missing theorem than bare surjectivity of
`fundamentalHomologyClass`: the remaining work is to prove this by showing that
the difference between a cycle and its matching winding multiple bounds. -/
def fundamentalCycleClass_generates : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    ∃ n : ModuleCat.of ℤ ℤ,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1) z =
        ModuleCat.Hom.hom fundamentalHomologyClass n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Cycle-representative generation implies surjectivity of the fundamental
homology class map.  Mathlib's `homologyπ` is an epimorphism, so every homology
class has a cycle representative; the generation statement then identifies that
representative's class with an integer multiple of the fundamental class. -/
theorem fundamentalHomologyClass_surjective_of_cycleClass_generates
    (hgen : fundamentalCycleClass_generates) :
    fundamentalHomologyClass_surjective := by
  intro y
  have hπsurj :
      Function.Surjective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1)) :=
    (ModuleCat.epi_iff_surjective (sphereOneSingularIntChainComplex.homologyπ 1)).mp inferInstance
  obtain ⟨z, hz⟩ := hπsurj y
  obtain ⟨n, hn⟩ := hgen z
  exact ⟨n, by rw [← hz, hn]⟩

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the concrete cycle-representative generation
statement.  This is now the exact next theorem to prove geometrically. -/
theorem circleH1ZIsoInt_of_fundamentalCycleClass_generates
    (hgen : fundamentalCycleClass_generates) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_fundamentalHomologyClass_surjective
    (fundamentalHomologyClass_surjective_of_cycleClass_generates hgen)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The fully concrete chain-level generation statement inside the cycle object:
every degree-`1` cycle is a lifted singular `2`-boundary plus an integer multiple
of the lifted fundamental cycle.

This is now the geometric work left to prove.  A proof should construct the
`b : C₂(S¹;ℤ)` witness, usually by subdivision/prism machinery or an equivalent
singular filling of the zero-winding remainder. -/
def fundamentalCycle_boundary_generates : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      z =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A concrete boundary decomposition of every cycle implies cycle-class
generation.  The `toCycles 2 1` term dies under `homologyπ`, so the homology class
of the cycle is exactly the class of the corresponding integer multiple of the
fundamental cycle. -/
theorem fundamentalCycleClass_generates_of_boundary_generates
    (hgen : fundamentalCycle_boundary_generates) :
    fundamentalCycleClass_generates := by
  intro z
  obtain ⟨n, b, hz⟩ := hgen z
  refine ⟨n, ?_⟩
  rw [hz, map_add]
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
      sphereOneSingularIntChainComplex.homologyπ 1) b +
    ModuleCat.Hom.hom (fundamentalCycle ≫ sphereOneSingularIntChainComplex.homologyπ 1) n =
      ModuleCat.Hom.hom fundamentalHomologyClass n
  rw [sphereOneSingularIntChainComplex.toCycles_comp_homologyπ]
  simp [fundamentalHomologyClass]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the concrete boundary-generation theorem. -/
theorem circleH1ZIsoInt_of_fundamentalCycle_boundary_generates
    (hgen : fundamentalCycle_boundary_generates) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_fundamentalCycleClass_generates
    (fundamentalCycleClass_generates_of_boundary_generates hgen)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Winding of a degree-`1` cycle, computed by including it into `C₁(S¹;ℤ)` and
applying the winding chain map. -/
noncomputable def cycleWinding
    (z : sphereOneSingularIntChainComplex.cycles 1) : ℝ :=
  ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) z

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Applying the descended homology-level winding map to the homology class of a
cycle recovers the chain-level winding of that cycle. -/
theorem homologyπ_windingHomologyMap_apply
    (z : sphereOneSingularIntChainComplex.cycles 1) :
    ModuleCat.Hom.hom windingHomologyMap
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1) z) =
        cycleWinding z := by
  unfold cycleWinding windingHomologyMap
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1 ≫
      sphereOneSingularIntChainComplex.homologyι 1 ≫
        sphereOneSingularIntChainComplex.descOpcycles windingChainMap 2 (by simp)
          windingChainMap_boundary) z =
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) z
  rw [HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The lifted fundamental cycle has winding equal to its integer coefficient. -/
theorem cycleWinding_fundamentalCycle (n : ModuleCat.of ℤ ℤ) :
    cycleWinding (ModuleCat.Hom.hom fundamentalCycle n) = (n : ℝ) := by
  unfold cycleWinding
  change ModuleCat.Hom.hom
      (fundamentalCycle ≫ sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) n =
    (n : ℝ)
  rw [fundamentalCycle, HomologicalComplex.liftCycles_i_assoc]
  rw [windingChainMap_fundamental]
  simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Winding of a closed singular generator cycle is the integer coefficient times
the winding of the underlying singular simplex. -/
theorem cycleWinding_closedSingularOneCycle (s : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) s =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) s)
    (n : ModuleCat.of ℤ ℤ) :
    cycleWinding (ModuleCat.Hom.hom (closedSingularOneCycle s hfaces) n) =
      (n : ℝ) * singularWinding s := by
  unfold cycleWinding
  change ModuleCat.Hom.hom
      (closedSingularOneCycle s hfaces ≫
        sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) n =
    (n : ℝ) * singularWinding s
  rw [closedSingularOneCycle, HomologicalComplex.liftCycles_i_assoc]
  rw [windingChainMap_ι]
  simp [LinearMap.toSpanSingleton_apply]

/-- A single finite-sum term in a closed-generator decomposition of a cycle. -/
structure ClosedSingularOneCycleTerm where
  simplex : SingularOneSimplex
  faces_eq :
    (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) simplex =
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) simplex
  coeff : ModuleCat.of ℤ ℤ

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The cycle represented by one closed-generator term. -/
noncomputable def ClosedSingularOneCycleTerm.cycle
    (t : ClosedSingularOneCycleTerm) :
    sphereOneSingularIntChainComplex.cycles 1 :=
  ModuleCat.Hom.hom (closedSingularOneCycle t.simplex t.faces_eq) t.coeff

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The cycle represented by a finite list of closed-generator terms. -/
noncomputable def closedSingularOneCycleList :
    List ClosedSingularOneCycleTerm → sphereOneSingularIntChainComplex.cycles 1
  | [] => 0
  | t :: ts => t.cycle + closedSingularOneCycleList ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The underlying `C₁` chain represented by one closed-generator term. -/
noncomputable def ClosedSingularOneCycleTerm.chain
    (t : ClosedSingularOneCycleTerm) :
    sphereOneSingularIntChainComplex.X 1 :=
  ModuleCat.Hom.hom
    (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) t.simplex) t.coeff

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The underlying `C₁` chain represented by a finite list of closed-generator
terms. -/
noncomputable def closedSingularOneChainList :
    List ClosedSingularOneCycleTerm → sphereOneSingularIntChainComplex.X 1
  | [] => 0
  | t :: ts => t.chain + closedSingularOneChainList ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Including a one-term closed-generator cycle into `C₁` gives the corresponding
raw singular-chain generator with its coefficient. -/
theorem ClosedSingularOneCycleTerm.cycle_iCycles
    (t : ClosedSingularOneCycleTerm) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) t.cycle =
      t.chain := by
  rw [ClosedSingularOneCycleTerm.cycle, ClosedSingularOneCycleTerm.chain]
  change ModuleCat.Hom.hom
      (closedSingularOneCycle t.simplex t.faces_eq ≫
        sphereOneSingularIntChainComplex.iCycles 1) t.coeff =
    ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) t.simplex) t.coeff
  rw [closedSingularOneCycle_iCycles]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Including a finite closed-generator cycle list into `C₁` gives the matching
finite raw chain list. -/
theorem closedSingularOneCycleList_iCycles :
    ∀ ts : List ClosedSingularOneCycleTerm,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (closedSingularOneCycleList ts) = closedSingularOneChainList ts
  | [] => by
      unfold closedSingularOneCycleList closedSingularOneChainList
      simp
  | t :: ts => by
      unfold closedSingularOneCycleList closedSingularOneChainList
      rw [map_add, t.cycle_iCycles, closedSingularOneCycleList_iCycles ts]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw-chain closed-generator spanning: every cycle, after inclusion into `C₁`,
is a finite raw sum of closed singular generators.  This is closer to the actual
finite-support cancellation theorem than `closedSingularOneCycleList_spans`. -/
def closedSingularOneChainList_spansCycles : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    ∃ ts : List ClosedSingularOneCycleTerm,
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) z =
        closedSingularOneChainList ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The remaining finite graph/cancellation theorem in explicit free-module
coordinates: every element of the free edge module whose free boundary is zero is
a finite sum of closed singular edge cycles. -/
def freeBoundaryKernel_decomposes : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      ∃ ts : List ClosedSingularOneCycleTerm,
        c = ModuleCat.Hom.hom singularOneChainToFree (closedSingularOneChainList ts)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-boundary kernel decomposition theorem implies the raw-chain spanning
statement for actual cycle representatives. -/
theorem closedSingularOneChainList_spansCycles_of_freeBoundaryKernel_decomposes
    (hker : freeBoundaryKernel_decomposes) :
    closedSingularOneChainList_spansCycles := by
  intro z
  let c : singularOneChainFree :=
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) z)
  have hc0 : ModuleCat.Hom.hom singularOneBoundaryFree c = 0 := by
    unfold c
    change ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.iCycles 1 ≫ singularOneChainToFree ≫
          singularOneBoundaryFree) z = 0
    rw [singularOneChainToFree_boundary_free]
    rw [← Category.assoc, HomologicalComplex.iCycles_d]
    simp
  obtain ⟨ts, hts⟩ := hker c hc0
  refine ⟨ts, ?_⟩
  have hinj : Function.Injective (ModuleCat.Hom.hom singularOneChainToFree) := by
    haveI : IsIso singularOneChainToFree := by
      change IsIso singularOneChainFreeIso.hom
      infer_instance
    haveI : Mono singularOneChainToFree := inferInstance
    exact (ModuleCat.mono_iff_injective singularOneChainToFree).mp inferInstance
  apply hinj
  unfold c at hts
  rw [hts]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A single closed-generator term has integer winding. -/
theorem ClosedSingularOneCycleTerm.cycleWinding_integral
    (t : ClosedSingularOneCycleTerm) :
    ∃ n : ModuleCat.of ℤ ℤ, cycleWinding t.cycle = (n : ℝ) := by
  obtain ⟨k, hk⟩ := singularWinding_loop_integral t.simplex t.faces_eq
  refine ⟨t.coeff * k, ?_⟩
  rw [ClosedSingularOneCycleTerm.cycle, cycleWinding_closedSingularOneCycle, hk]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A closed-generator term whose underlying singular edge has zero winding
bounds, including its integer coefficient.  This is the list-ready scalar
consumer of the explicit cone construction. -/
theorem ClosedSingularOneCycleTerm.bounds_of_zero_singularWinding
    (t : ClosedSingularOneCycleTerm) (hzero : singularWinding t.simplex = 0) :
    ∃ b : sphereOneSingularIntChainComplex.X 2,
      t.cycle = ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b := by
  exact closedSingularOneCycle_zsmul_bounds_of_zero_singularWinding
    t.simplex t.faces_eq hzero t.coeff

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A finite list of zero-winding closed-generator terms bounds by summing the
single-edge cone witnesses.  This is the first finite-sum consumer of the cone
construction. -/
theorem closedSingularOneCycleList_bounds_of_forall_zero_singularWinding :
    ∀ (ts : List ClosedSingularOneCycleTerm),
      (∀ t ∈ ts, singularWinding t.simplex = 0) →
        ∃ b : sphereOneSingularIntChainComplex.X 2,
          closedSingularOneCycleList ts =
            ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b
  | [] => by
      intro _
      refine ⟨0, ?_⟩
      unfold closedSingularOneCycleList
      simp
  | t :: ts => by
      intro hzero
      have htzero : singularWinding t.simplex = 0 := hzero t (by simp)
      have htszero : ∀ u ∈ ts, singularWinding u.simplex = 0 := by
        intro u hu
        exact hzero u (by simp [hu])
      obtain ⟨b₁, hb₁⟩ := t.bounds_of_zero_singularWinding htzero
      obtain ⟨b₂, hb₂⟩ :=
        closedSingularOneCycleList_bounds_of_forall_zero_singularWinding ts htszero
      refine ⟨b₁ + b₂, ?_⟩
      unfold closedSingularOneCycleList
      rw [hb₁, hb₂, map_add]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Any finite list of closed-generator terms has integer winding. -/
theorem closedSingularOneCycleList_winding_integral :
    ∀ ts : List ClosedSingularOneCycleTerm,
      ∃ n : ModuleCat.of ℤ ℤ, cycleWinding (closedSingularOneCycleList ts) = (n : ℝ)
  | [] => by
      refine ⟨0, ?_⟩
      unfold closedSingularOneCycleList cycleWinding
      simp
  | t :: ts => by
      obtain ⟨n₁, hn₁⟩ := t.cycleWinding_integral
      obtain ⟨n₂, hn₂⟩ := closedSingularOneCycleList_winding_integral ts
      refine ⟨n₁ + n₂, ?_⟩
      unfold closedSingularOneCycleList
      unfold cycleWinding at hn₁ hn₂ ⊢
      rw [map_add, hn₁, hn₂]
      simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- For a finite closed-generator list, subtracting the integer multiple of the
fundamental cycle matching its winding produces a zero-winding residual.  This is
the algebraic shell around the remaining geometric filling problem. -/
theorem closedSingularOneCycleList_zeroWinding_residual
    (ts : List ClosedSingularOneCycleTerm) :
    ∃ n : ModuleCat.of ℤ ℤ,
      cycleWinding (closedSingularOneCycleList ts) = (n : ℝ) ∧
        cycleWinding
          (closedSingularOneCycleList ts - ModuleCat.Hom.hom fundamentalCycle n) = 0 := by
  obtain ⟨n, hn⟩ := closedSingularOneCycleList_winding_integral ts
  refine ⟨n, hn, ?_⟩
  unfold cycleWinding at hn ⊢
  rw [map_sub]
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap)
      (closedSingularOneCycleList ts) -
    cycleWinding (ModuleCat.Hom.hom fundamentalCycle n) = 0
  rw [hn, cycleWinding_fundamentalCycle]
  ring

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the zero-winding residual of a closed-generator list bounds, then the list
is generated by the fundamental cycle modulo a boundary. -/
theorem closedSingularOneCycleList_boundary_generate_of_residual_bound
    (ts : List ClosedSingularOneCycleTerm) (n : ModuleCat.of ℤ ℤ)
    (b : sphereOneSingularIntChainComplex.X 2)
    (hres :
      closedSingularOneCycleList ts - ModuleCat.Hom.hom fundamentalCycle n =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b) :
    closedSingularOneCycleList ts =
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
        ModuleCat.Hom.hom fundamentalCycle n := by
  rw [← hres]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Finite closed-generator list spanning: every cycle is a finite sum of closed
singular generator cycles.  This is the finite-chain combinatorial statement
left for proving `cycleWinding_integral`. -/
def closedSingularOneCycleList_spans : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    ∃ ts : List ClosedSingularOneCycleTerm, z = closedSingularOneCycleList ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw-chain closed-generator spanning implies cycle-object closed-generator
spanning, because `iCycles` is a monomorphism. -/
theorem closedSingularOneCycleList_spans_of_chainList_spansCycles
    (hspan : closedSingularOneChainList_spansCycles) :
    closedSingularOneCycleList_spans := by
  intro z
  obtain ⟨ts, hz⟩ := hspan z
  refine ⟨ts, ?_⟩
  have hinc : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) z =
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (closedSingularOneCycleList ts) := by
    rw [hz, closedSingularOneCycleList_iCycles ts]
  have hinj :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  exact hinj hinc

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- First concrete geometric subtarget: every singular `1`-cycle has an integer
winding number.  This should follow from endpoint cancellation in a finite
integer chain. -/
def cycleWinding_integral : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    ∃ n : ModuleCat.of ℤ ℤ, cycleWinding z = (n : ℝ)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A general directed cycle piece in free-chain coordinates.  Unlike
`ClosedSingularOneCycleTerm`, this is not restricted to one closed edge: a piece
may represent a multi-edge directed cycle.  The fields record exactly what the
finite graph theorem must construct from a balanced finite edge flow. -/
structure DirectedCycleFreeTerm where
  cycle : sphereOneSingularIntChainComplex.cycles 1
  chain : singularOneChainFree
  chain_eq :
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) cycle) = chain
  winding_integral : ∃ n : ModuleCat.of ℤ ℤ, cycleWinding cycle = (n : ℝ)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The raw `C₁ → C₀` boundary of the chain represented by a free edge-chain
vanishes whenever the explicit free boundary of that edge-chain vanishes.  This
transports a free-`C₀` boundary computation back to the raw chain group using the
injectivity of `singularZeroChainToFree`. -/
theorem d_singularOneChainFreeToChain_eq_zero_of_freeBoundary_zero
    (cFree : singularOneChainFree)
    (hb : ModuleCat.Hom.hom singularOneBoundaryFree cFree = 0) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 1 0)
      (ModuleCat.Hom.hom singularOneChainFreeToChain cFree) = 0 := by
  apply singularZeroChainToFree_injective
  rw [map_zero]
  have hcomp := congrArg (fun f => ModuleCat.Hom.hom f cFree)
    singularOneChainFreeToChain_boundary_free
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcomp
  rw [hb] at hcomp
  exact hcomp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Transporting a free edge-chain into the raw chain group and back recovers it:
`singularOneChainToFree ∘ singularOneChainFreeToChain = id`. -/
theorem singularOneChainToFree_freeToChain (c : singularOneChainFree) :
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom singularOneChainFreeToChain c) = c := by
  have hid := congrArg (fun f => ModuleCat.Hom.hom f c) singularOneChainFreeIso.inv_hom_id
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.id_coe, id_eq] at hid
  exact hid

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding chain map evaluated on the raw chain of one free generator is the
winding of that singular `1`-simplex. -/
theorem windingChainMap_singularOneChainFreeToChain_freeMk (s : SingularOneSimplex) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain (ModuleCat.freeMk s)) =
      singularWinding s := by
  rw [singularOneChainFreeToChain_freeMk]
  change ModuleCat.Hom.hom
      (Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) s ≫ windingChainMap) 1 =
    singularWinding s
  rw [windingChainMap_ι]
  simp [LinearMap.toSpanSingleton_apply]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Constant singular `1`-simplices have zero winding because each is the boundary
of a constant singular `2`-simplex. -/
theorem windingChainMap_constantSingularOneSimplex (p : SphereOne) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain
        (ModuleCat.freeMk (constantSingularOneSimplex p))) = 0 := by
  rw [singularOneChainFreeToChain_freeMk]
  rw [← constantSingularOneSimplex_raw_boundary p]
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1 ≫ windingChainMap)
    (ModuleCat.Hom.hom singularTwoChainFreeToChain
      (ModuleCat.freeMk (constantSingularTwoSimplex p))) = 0
  rw [windingChainMap_boundary]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding chain map evaluated on the raw chain of a finite free edge-family
is the total winding of the family. -/
theorem windingChainMap_singularOneChainFreeToChain_sum {k : ℕ}
    (e : Fin k → SingularOneSimplex) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, ModuleCat.freeMk (e i))) =
      ∑ i, singularWinding (e i) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact windingChainMap_singularOneChainFreeToChain_freeMk (e i)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The homological content of cyclic extraction, packaged.**  A cyclically
connected finite family of singular `1`-simplices assembles into a
`DirectedCycleFreeTerm`: its free edge-chain `∑ᵢ ⟨eᵢ⟩` lifts to a genuine
degree-`1` cycle (boundary vanishes by `cyclicEdgeFamily_freeBoundary_zero`), and
that cycle has integer winding (by `singularWindingSum_cyclic_integral`).  This
discharges the entire homological/winding obligation of cyclic extraction; the
only content left in the finite-flow decomposition is the *combinatorial* task of
exhibiting such a family inside a balanced flow. -/
noncomputable def directedCycleFreeTerm_of_cyclicFamily {k : ℕ}
    (e : Fin k → SingularOneSimplex)
    (hconn : ∀ i : Fin k, edgeTerminal (e i) = edgeInitial (e (finRotate k i))) :
    DirectedCycleFreeTerm := by
  have hb : ModuleCat.Hom.hom singularOneBoundaryFree (∑ i, ModuleCat.freeMk (e i)) = 0 :=
    cyclicEdgeFamily_freeBoundary_zero e hconn
  have hd : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 1 0)
      (ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, ModuleCat.freeMk (e i))) = 0 :=
    d_singularOneChainFreeToChain_eq_zero_of_freeBoundary_zero _ hb
  -- Route the lift `ℤ → X 1` through the free module (which carries a clean `ℤ`-module
  -- instance), avoiding the `ℤ`-module diamond on the raw chain group `X 1`.
  let φfree : ModuleCat.of ℤ ℤ ⟶ singularOneChainFree :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ singularOneChainFree (∑ i, ModuleCat.freeMk (e i)))
  let ψ : ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.X 1 :=
    φfree ≫ singularOneChainFreeToChain
  have hψ1 : ModuleCat.Hom.hom ψ 1 =
      ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, ModuleCat.freeMk (e i)) := by
    simp only [ψ, φfree, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  -- The raw boundary `freeToChain ≫ ∂` equals the explicit free boundary transported back
  -- through the (iso) `C₀` comparison; this is `singularOneChainFreeToChain_boundary_free`
  -- post-composed with the inverse of the `C₀` iso.
  have htofree : singularZeroChainToFree ≫ singularZeroChainFreeToChain
      = 𝟙 (sphereOneSingularIntChainComplex.X 0) := singularZeroChainFreeIso.hom_inv_id
  have hbridge : singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0
      = singularOneBoundaryFree ≫ singularZeroChainFreeToChain := by
    have h : (singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 ≫
        singularZeroChainToFree) ≫ singularZeroChainFreeToChain
        = singularOneBoundaryFree ≫ singularZeroChainFreeToChain := by
      rw [singularOneChainFreeToChain_boundary_free]
    rw [Category.assoc, Category.assoc, htofree, Category.comp_id] at h
    exact h
  -- `ψ ≫ ∂ = (φfree ≫ ∂_free) ≫ freeToChain₀ = 0` because the free boundary kills `∑ᵢ ⟨eᵢ⟩`.
  have hφb : φfree ≫ singularOneBoundaryFree = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [φfree, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    exact hb
  have hψ : ψ ≫ sphereOneSingularIntChainComplex.d 1 0 = 0 := by
    calc ψ ≫ sphereOneSingularIntChainComplex.d 1 0
        = φfree ≫ singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 := by
          simp only [ψ, Category.assoc]
      _ = φfree ≫ singularOneBoundaryFree ≫ singularZeroChainFreeToChain := by rw [hbridge]
      _ = (φfree ≫ singularOneBoundaryFree) ≫ singularZeroChainFreeToChain := by
          rw [Category.assoc]
      _ = 0 := by rw [hφb, Limits.zero_comp]
  let cycMap : ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.cycles 1 :=
    sphereOneSingularIntChainComplex.liftCycles ψ 0 (by simp) hψ
  have hiC : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
      (ModuleCat.Hom.hom cycMap 1) =
      ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, ModuleCat.freeMk (e i)) := by
    change ModuleCat.Hom.hom (cycMap ≫ sphereOneSingularIntChainComplex.iCycles 1) 1 = _
    rw [HomologicalComplex.liftCycles_i]
    exact hψ1
  refine
    { cycle := ModuleCat.Hom.hom cycMap 1
      chain := ∑ i, ModuleCat.freeMk (e i)
      chain_eq := ?_
      winding_integral := ?_ }
  · rw [hiC, singularOneChainToFree_freeToChain]
  · obtain ⟨n, hn⟩ := singularWindingSum_cyclic_integral e hconn
    refine ⟨n, ?_⟩
    unfold cycleWinding
    change ModuleCat.Hom.hom windingChainMap
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom cycMap 1)) = (n : ℝ)
    rw [hiC, windingChainMap_singularOneChainFreeToChain_sum]
    exact hn

/-! ### Oriented closed-walk engine

The combinatorial extraction follows *sign-selected* orientations (a supported
edge is read forward when its coefficient is positive, backward when negative),
so the closed walks it produces are families of `OrientedSingularEdge`s, not bare
forward simplices.  The lemmas below generalise the forward engine
(`directedCycleFreeTerm_of_cyclicFamily`) to oriented families: a backward
occurrence contributes the reversed path (negating displacement and winding) and
the chain `-⟨e⟩`.  This is the keystone the walk extraction feeds. -/

/-- Winding contribution of an oriented edge occurrence: the underlying singular
winding, negated for backward traversal. -/
noncomputable def orientedWinding (o : OrientedSingularEdge) : ℝ :=
  match o.orientation with
  | .forward => singularWinding o.edge
  | .backward => - singularWinding o.edge

/-- The path traced by an oriented edge occurrence (reversed for backward). -/
noncomputable def orientedEdgePath (o : OrientedSingularEdge) : C(I, SphereOne) :=
  match o.orientation with
  | .forward => singularEdgePath o.edge
  | .backward => CircleWinding.reversePath (singularEdgePath o.edge)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Forward oriented edges need no path-base correction: the path-parametric base
edge is definitionally the original signed free generator after the standard
`Δ¹ ≃ I` round trip. -/
theorem OrientedSingularEdge.pathBase_eq_chain_of_forward
    (o : OrientedSingularEdge) (h : o.orientation = EdgeOrientation.forward) :
    ModuleCat.freeMk
      (singularOneSimplexOfMap (oneSimplexOfPath (orientedEdgePath o))) =
        o.chain := by
  rcases o with ⟨e, ori⟩
  cases ori
  · simp only [orientedEdgePath, OrientedSingularEdge.chain]
    rw [singularOneSimplexOfMap_oneSimplexOfPath_singularEdgePath]
  · simp at h

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Local path-base residual of one oriented singular edge.  Forward edges have
zero residual; backward edges leave the standard reparameterisation prism target. -/
noncomputable def OrientedSingularEdge.pathBaseCorrectionBoundary
    (o : OrientedSingularEdge) : singularOneChainFree :=
  ModuleCat.freeMk (singularOneSimplexOfMap (oneSimplexOfPath (orientedEdgePath o))) -
    o.chain

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Forward oriented edges have zero local path-base residual. -/
theorem OrientedSingularEdge.pathBaseCorrectionBoundary_eq_zero_of_forward
    (o : OrientedSingularEdge) (h : o.orientation = EdgeOrientation.forward) :
    o.pathBaseCorrectionBoundary = 0 := by
  unfold OrientedSingularEdge.pathBaseCorrectionBoundary
  rw [o.pathBase_eq_chain_of_forward h]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Backward oriented edges have a concrete path-base correction: the triangular
backtrack prism over the edge path, plus the constant `2`-simplex that cancels the
middle constant face. -/
theorem OrientedSingularEdge.pathBaseCorrectionBoundary_bounds_of_backward
    (o : OrientedSingularEdge) (h : o.orientation = EdgeOrientation.backward) :
    ∃ K : singularTwoChainFree,
      ModuleCat.Hom.hom singularTwoBoundaryFree K = o.pathBaseCorrectionBoundary := by
  rcases o with ⟨e, ori⟩
  cases ori
  · simp at h
  · refine ⟨ModuleCat.freeMk (pathBacktrackSingularTwoSimplex (singularEdgePath e)) +
        ModuleCat.freeMk (constantSingularTwoSimplex ((singularEdgePath e) 0)), ?_⟩
    rw [map_add, singularTwoBoundaryFree_freeMk_pathBacktrack,
      constantSingularOneSimplex_free_boundary]
    unfold OrientedSingularEdge.pathBaseCorrectionBoundary orientedEdgePath
      OrientedSingularEdge.chain
    rw [singularOneSimplexOfMap_oneSimplexOfPath_singularEdgePath]
    simp
    abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Every oriented singular edge has a local path-base correction.  The forward
case is zero; the backward case is the backtrack prism. -/
theorem OrientedSingularEdge.pathBaseCorrectionBoundary_bounds
    (o : OrientedSingularEdge) :
    ∃ K : singularTwoChainFree,
      ModuleCat.Hom.hom singularTwoBoundaryFree K = o.pathBaseCorrectionBoundary := by
  cases h : o.orientation with
  | forward =>
      refine ⟨0, ?_⟩
      rw [map_zero, o.pathBaseCorrectionBoundary_eq_zero_of_forward h]
  | backward =>
      exact o.pathBaseCorrectionBoundary_bounds_of_backward h

/-- Initial point of an oriented edge's path is the `S¹`-point of its oriented
initial vertex. -/
theorem orientedEdgePath_zero (o : OrientedSingularEdge) :
    orientedEdgePath o 0 = vertexPoint o.initial := by
  rcases o with ⟨e, ori⟩
  cases ori
  · simp only [orientedEdgePath, OrientedSingularEdge.initial]
    rw [singularEdgePath_zero]
  · simp only [orientedEdgePath, OrientedSingularEdge.initial,
      CircleWinding.reversePath_apply, unitInterval.symm_zero]
    rw [singularEdgePath_one]

/-- Terminal point of an oriented edge's path is the `S¹`-point of its oriented
terminal vertex. -/
theorem orientedEdgePath_one (o : OrientedSingularEdge) :
    orientedEdgePath o 1 = vertexPoint o.terminal := by
  rcases o with ⟨e, ori⟩
  cases ori
  · simp only [orientedEdgePath, OrientedSingularEdge.terminal]
    rw [singularEdgePath_one]
  · simp only [orientedEdgePath, OrientedSingularEdge.terminal,
      CircleWinding.reversePath_apply, unitInterval.symm_one]
    rw [singularEdgePath_zero]

/-- The oriented winding is the displacement of the oriented path, normalised by
one full turn. -/
theorem orientedWinding_eq_pathDisplacement (o : OrientedSingularEdge) :
    orientedWinding o = pathDisplacement (orientedEdgePath o) / (2 * Real.pi) := by
  rcases o with ⟨e, ori⟩
  cases ori
  · simp only [orientedWinding, orientedEdgePath]
    exact singularWinding_eq_pathDisplacement e
  · simp only [orientedWinding, orientedEdgePath]
    rw [CircleWinding.pathDisplacement_reverse, neg_div]
    rw [← singularWinding_eq_pathDisplacement]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The terminal-return side of an oriented edge has winding opposite to the
oriented edge winding. -/
theorem OrientedSingularEdge.singularWinding_terminalReturnSide
    (o : OrientedSingularEdge) :
    singularWinding
      (singularOneSimplexOfMap (coneTerminalSide (orientedEdgePath o))) =
        - orientedWinding o := by
  rw [singularWinding_coneTerminalSide, orientedWinding_eq_pathDisplacement]

/-- **Closed-walk winding integrality (oriented form).**  A cyclically connected
family of oriented edge occurrences (oriented terminal of `o i` equals oriented
initial of `o (finRotate k i)`) has integer total oriented winding. -/
theorem orientedWindingSum_cyclic_integral {k : ℕ} (o : Fin k → OrientedSingularEdge)
    (hconn : ∀ i : Fin k, (o i).terminal = (o (finRotate k i)).initial) :
    ∃ n : ℤ, ∑ i, orientedWinding (o i) = (n : ℝ) := by
  have hpathconn : ∀ i : Fin k,
      (orientedEdgePath (o i)) 1 = (orientedEdgePath (o (finRotate k i))) 0 := by
    intro i
    rw [orientedEdgePath_one, orientedEdgePath_zero]
    exact congrArg vertexPoint (hconn i)
  obtain ⟨m, hm⟩ :=
    displacementSum_cyclic_intMul (fun i => orientedEdgePath (o i)) hpathconn
  refine ⟨m, ?_⟩
  have hsum :
      ∑ i, orientedWinding (o i)
        = (∑ i, pathDisplacement (orientedEdgePath (o i))) / (2 * Real.pi) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact orientedWinding_eq_pathDisplacement (o i)
  rw [hsum, hm]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [mul_div_assoc, div_self hpi, mul_one]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Cyclic free-boundary vanishing (oriented form).**  The free edge-chain of a
cyclically connected oriented walk is a cycle: its explicit free boundary
vanishes (oriented telescoping of `terminal − initial`). -/
theorem cyclicOrientedFamily_freeBoundary_zero {k : ℕ} (o : Fin k → OrientedSingularEdge)
    (hconn : ∀ i : Fin k, (o i).terminal = (o (finRotate k i)).initial) :
    ModuleCat.Hom.hom singularOneBoundaryFree (∑ i, (o i).chain) = 0 := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun i _ => (o i).boundary_free), Finset.sum_sub_distrib]
  have hreindex :
      (∑ i, ModuleCat.freeMk (o i).initial : singularZeroChainFree)
        = ∑ i, ModuleCat.freeMk (o i).terminal := by
    rw [← Equiv.sum_comp (finRotate k)
      (fun j => (ModuleCat.freeMk (o j).initial : singularZeroChainFree))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact congrArg ModuleCat.freeMk (hconn i).symm
  rw [hreindex, sub_self]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding chain map on the raw chain of one oriented edge occurrence is its
oriented winding. -/
theorem windingChainMap_freeToChain_orientedChain (o : OrientedSingularEdge) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain o.chain) = orientedWinding o := by
  rcases o with ⟨e, ori⟩
  cases ori
  · simp only [orientedWinding, OrientedSingularEdge.chain]
    exact windingChainMap_singularOneChainFreeToChain_freeMk e
  · simp only [orientedWinding, OrientedSingularEdge.chain]
    rw [map_neg, map_neg, windingChainMap_singularOneChainFreeToChain_freeMk]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding chain map on the raw chain of an oriented walk is its total
oriented winding. -/
theorem windingChainMap_freeToChain_orientedChain_sum {k : ℕ}
    (o : Fin k → OrientedSingularEdge) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (o i).chain)) =
      ∑ i, orientedWinding (o i) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact windingChainMap_freeToChain_orientedChain (o i)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The homological content of oriented cyclic extraction, packaged.**  A
cyclically connected finite family of oriented edge occurrences assembles into a
`DirectedCycleFreeTerm`: its signed free edge-chain `∑ᵢ (oᵢ).chain` lifts to a
genuine degree-`1` cycle, with integer winding.  This generalises
`directedCycleFreeTerm_of_cyclicFamily` to the sign-selected orientations the
balanced-flow walk extraction produces. -/
noncomputable def directedCycleFreeTerm_of_orientedCyclicFamily {k : ℕ}
    (o : Fin k → OrientedSingularEdge)
    (hconn : ∀ i : Fin k, (o i).terminal = (o (finRotate k i)).initial) :
    DirectedCycleFreeTerm := by
  have hb : ModuleCat.Hom.hom singularOneBoundaryFree (∑ i, (o i).chain) = 0 :=
    cyclicOrientedFamily_freeBoundary_zero o hconn
  have hd : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 1 0)
      (ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (o i).chain)) = 0 :=
    d_singularOneChainFreeToChain_eq_zero_of_freeBoundary_zero _ hb
  let φfree : ModuleCat.of ℤ ℤ ⟶ singularOneChainFree :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ singularOneChainFree (∑ i, (o i).chain))
  let ψ : ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.X 1 :=
    φfree ≫ singularOneChainFreeToChain
  have hψ1 : ModuleCat.Hom.hom ψ 1 =
      ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (o i).chain) := by
    simp only [ψ, φfree, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  have htofree : singularZeroChainToFree ≫ singularZeroChainFreeToChain
      = 𝟙 (sphereOneSingularIntChainComplex.X 0) := singularZeroChainFreeIso.hom_inv_id
  have hbridge : singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0
      = singularOneBoundaryFree ≫ singularZeroChainFreeToChain := by
    have h : (singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 ≫
        singularZeroChainToFree) ≫ singularZeroChainFreeToChain
        = singularOneBoundaryFree ≫ singularZeroChainFreeToChain := by
      rw [singularOneChainFreeToChain_boundary_free]
    rw [Category.assoc, Category.assoc, htofree, Category.comp_id] at h
    exact h
  have hφb : φfree ≫ singularOneBoundaryFree = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [φfree, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    exact hb
  have hψ : ψ ≫ sphereOneSingularIntChainComplex.d 1 0 = 0 := by
    calc ψ ≫ sphereOneSingularIntChainComplex.d 1 0
        = φfree ≫ singularOneChainFreeToChain ≫ sphereOneSingularIntChainComplex.d 1 0 := by
          simp only [ψ, Category.assoc]
      _ = φfree ≫ singularOneBoundaryFree ≫ singularZeroChainFreeToChain := by rw [hbridge]
      _ = (φfree ≫ singularOneBoundaryFree) ≫ singularZeroChainFreeToChain := by
          rw [Category.assoc]
      _ = 0 := by rw [hφb, Limits.zero_comp]
  let cycMap : ModuleCat.of ℤ ℤ ⟶ sphereOneSingularIntChainComplex.cycles 1 :=
    sphereOneSingularIntChainComplex.liftCycles ψ 0 (by simp) hψ
  have hiC : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
      (ModuleCat.Hom.hom cycMap 1) =
      ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (o i).chain) := by
    change ModuleCat.Hom.hom (cycMap ≫ sphereOneSingularIntChainComplex.iCycles 1) 1 = _
    rw [HomologicalComplex.liftCycles_i]
    exact hψ1
  refine
    { cycle := ModuleCat.Hom.hom cycMap 1
      chain := ∑ i, (o i).chain
      chain_eq := ?_
      winding_integral := ?_ }
  · rw [hiC, singularOneChainToFree_freeToChain]
  · obtain ⟨n, hn⟩ := orientedWindingSum_cyclic_integral o hconn
    refine ⟨n, ?_⟩
    unfold cycleWinding
    change ModuleCat.Hom.hom windingChainMap
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom cycMap 1)) = (n : ℝ)
    rw [hiC, windingChainMap_freeToChain_orientedChain_sum]
    exact hn

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The cycle-object sum represented by a finite list of directed cycle pieces. -/
noncomputable def directedCycleFreeTermListCycle :
    List DirectedCycleFreeTerm → sphereOneSingularIntChainComplex.cycles 1
  | [] => 0
  | t :: ts => t.cycle + directedCycleFreeTermListCycle ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free-chain sum represented by a finite list of directed cycle
pieces. -/
noncomputable def directedCycleFreeTermListChain :
    List DirectedCycleFreeTerm → singularOneChainFree
  | [] => 0
  | t :: ts => t.chain + directedCycleFreeTermListChain ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-chain image of the cycle-object list is the corresponding explicit
free-chain list. -/
theorem directedCycleFreeTermList_chain_eq :
    ∀ ts : List DirectedCycleFreeTerm,
      ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (directedCycleFreeTermListCycle ts)) =
        directedCycleFreeTermListChain ts
  | [] => by
      unfold directedCycleFreeTermListCycle directedCycleFreeTermListChain
      simp
  | t :: ts => by
      unfold directedCycleFreeTermListCycle directedCycleFreeTermListChain
      rw [map_add, map_add, t.chain_eq, directedCycleFreeTermList_chain_eq ts]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A finite list of directed cycle pieces has integer winding. -/
theorem directedCycleFreeTermList_winding_integral :
    ∀ ts : List DirectedCycleFreeTerm,
      ∃ n : ModuleCat.of ℤ ℤ, cycleWinding (directedCycleFreeTermListCycle ts) = (n : ℝ)
  | [] => by
      refine ⟨0, ?_⟩
      unfold directedCycleFreeTermListCycle cycleWinding
      simp
  | t :: ts => by
      obtain ⟨n₁, hn₁⟩ := t.winding_integral
      obtain ⟨n₂, hn₂⟩ := directedCycleFreeTermList_winding_integral ts
      refine ⟨n₁ + n₂, ?_⟩
      unfold directedCycleFreeTermListCycle
      unfold cycleWinding at hn₁ hn₂ ⊢
      rw [map_add, hn₁, hn₂]
      simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Including a packaged directed-cycle term back into raw `C₁` recovers the raw
chain obtained from its explicit free-chain representative. -/
theorem DirectedCycleFreeTerm.iCycles_eq_freeToChain (t : DirectedCycleFreeTerm) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) t.cycle =
      ModuleCat.Hom.hom singularOneChainFreeToChain t.chain := by
  have hinj_toFree : Function.Injective (ModuleCat.Hom.hom singularOneChainToFree) := by
    haveI : IsIso singularOneChainToFree := by
      change IsIso singularOneChainFreeIso.hom
      infer_instance
    haveI : Mono singularOneChainToFree := inferInstance
    exact (ModuleCat.mono_iff_injective singularOneChainToFree).mp inferInstance
  apply hinj_toFree
  rw [t.chain_eq, singularOneChainToFree_freeToChain]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding of a packaged directed-cycle term can be computed from its
explicit free-chain representative. -/
theorem DirectedCycleFreeTerm.cycleWinding_eq_freeChain (t : DirectedCycleFreeTerm) :
    cycleWinding t.cycle =
      ModuleCat.Hom.hom windingChainMap
        (ModuleCat.Hom.hom singularOneChainFreeToChain t.chain) := by
  unfold cycleWinding
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [t.iCycles_eq_freeToChain]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Correct general finite graph target: every free edge-chain in the kernel of
the explicit boundary decomposes into finitely many directed cycle pieces. -/
def freeBoundaryKernel_decomposesIntoDirectedCycles : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      ∃ ts : List DirectedCycleFreeTerm, c = directedCycleFreeTermListChain ts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The general directed-cycle kernel decomposition theorem implies integer
winding for all singular `1`-cycles. -/
theorem cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoDirectedCycles
    (hker : freeBoundaryKernel_decomposesIntoDirectedCycles) :
    cycleWinding_integral := by
  intro z
  let c : singularOneChainFree :=
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) z)
  have hc0 : ModuleCat.Hom.hom singularOneBoundaryFree c = 0 := by
    unfold c
    change ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.iCycles 1 ≫ singularOneChainToFree ≫
          singularOneBoundaryFree) z = 0
    rw [singularOneChainToFree_boundary_free]
    rw [← Category.assoc, HomologicalComplex.iCycles_d]
    simp
  obtain ⟨ts, hts⟩ := hker c hc0
  have hcycle : z = directedCycleFreeTermListCycle ts := by
    have hinj_toFree : Function.Injective (ModuleCat.Hom.hom singularOneChainToFree) := by
      haveI : IsIso singularOneChainToFree := by
        change IsIso singularOneChainFreeIso.hom
        infer_instance
      haveI : Mono singularOneChainToFree := inferInstance
      exact (ModuleCat.mono_iff_injective singularOneChainToFree).mp inferInstance
    have hinj_iCycles :
        Function.Injective
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
      (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
    apply hinj_iCycles
    apply hinj_toFree
    unfold c at hts
    rw [hts, directedCycleFreeTermList_chain_eq ts]
  obtain ⟨n, hn⟩ := directedCycleFreeTermList_winding_integral ts
  refine ⟨n, ?_⟩
  rw [hcycle, hn]

/-! ### ℓ¹ size of a free edge-chain and its bookkeeping

The unconditional directed-cycle decomposition is proved by induction on the
ℓ¹ size `∑ |coeff|` of the free edge-chain.  Each extraction step peels a
directed cycle (an oriented closed walk through the support) and subtracts it,
which lowers the magnitude of every edge on the walk by exactly one and leaves
all other coefficients unchanged.  The lemmas in this section make that ℓ¹
decrease precise. -/

/-- ℓ¹ size of a free edge-chain: the sum of the absolute values of its
coefficients. -/
noncomputable def chainL1 (c : singularOneChainFree) : ℕ :=
  ∑ e ∈ edgeSupport c, (edgeCoeff c e).natAbs

/-- The coefficient of a difference of free edge-chains is the difference of the
coefficients. -/
theorem edgeCoeff_sub (c d : singularOneChainFree) (e : SingularOneSimplex) :
    edgeCoeff (c - d) e = edgeCoeff c e - edgeCoeff d e := by
  show (c - d).toFun e = c.toFun e - d.toFun e
  exact Finsupp.sub_apply c d e

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A supported peel that exactly cancels at least one supported edge strictly
shrinks support.  This is the generic support-cardinality bookkeeping needed by
any one-step cyclic extraction proof. -/
theorem edgeSupportCard_sub_lt_of_supported_exact_cancel
    [DecidableEq SingularOneSimplex]
    (c p : singularOneChainFree)
    (hpsupp : edgeSupport p ⊆ edgeSupport c)
    (hcancel : ∃ e, e ∈ edgeSupport p ∧ edgeCoeff p e = edgeCoeff c e) :
    edgeSupportCard (c - p) < edgeSupportCard c := by
  have hsubs : edgeSupport (c - p) ⊆ edgeSupport c := by
    intro e he
    by_contra hnotc
    have hc0 : edgeCoeff c e = 0 :=
      Classical.not_not.mp (mt (mem_edgeSupport_iff c e).mpr hnotc)
    have hp0 : edgeCoeff p e = 0 := by
      have hnotp : e ∉ edgeSupport p := fun hp => hnotc (hpsupp hp)
      exact Classical.not_not.mp (mt (mem_edgeSupport_iff p e).mpr hnotp)
    have hres0 : edgeCoeff (c - p) e = 0 := by
      rw [edgeCoeff_sub, hc0, hp0, sub_zero]
    exact (mem_edgeSupport_iff (c - p) e).mp he hres0
  obtain ⟨e, hep, hcoeff⟩ := hcancel
  have hec : e ∈ edgeSupport c := hpsupp hep
  have hnotres : e ∉ edgeSupport (c - p) := by
    intro heres
    have hne : edgeCoeff (c - p) e ≠ 0 :=
      (mem_edgeSupport_iff (c - p) e).mp heres
    have hzero : edgeCoeff (c - p) e = 0 := by
      rw [edgeCoeff_sub, hcoeff, sub_self]
    exact hne hzero
  unfold edgeSupportCard
  have hproper : edgeSupport (c - p) ⊂ edgeSupport c := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsubs, ?_⟩
    intro hsame
    exact hnotres (by rw [hsame]; exact hec)
  exact Finset.card_lt_card hproper

/-- The coefficient of a sum of free edge-chains is the sum of the coefficients. -/
theorem edgeCoeff_add (c d : singularOneChainFree) (e : SingularOneSimplex) :
    edgeCoeff (c + d) e = edgeCoeff c e + edgeCoeff d e := by
  show (c + d).toFun e = c.toFun e + d.toFun e
  exact Finsupp.add_apply c d e

/-- The coefficient of an integer multiple of a free edge-chain is the matching
integer multiple of the coefficient. -/
theorem edgeCoeff_zsmul (n : ℤ) (c : singularOneChainFree) (e : SingularOneSimplex) :
    edgeCoeff (n • c) e = n * edgeCoeff c e := by
  show (n • c).toFun e = n * c.toFun e
  rfl

/-- The free-chain contribution of one sign-selected oriented edge is the single
generator with coefficient `+1` (forward) or `-1` (backward). -/
theorem orientedEdgeOfCoeff_chain_eq_single
    (c : singularOneChainFree) (e : SingularOneSimplex) :
    (orientedEdgeOfCoeff c e).chain =
      Finsupp.single e (if 0 < edgeCoeff c e then (1 : ℤ) else -1) := by
  by_cases hp : 0 < edgeCoeff c e
  · have horient : orientedEdgeOfCoeff c e = { edge := e, orientation := .forward } := by
      simp only [orientedEdgeOfCoeff, orientationOfCoeff, if_pos hp]
    rw [horient]
    show ModuleCat.freeMk e = _
    rw [if_pos hp, ModuleCat.freeMk]
  · have horient : orientedEdgeOfCoeff c e = { edge := e, orientation := .backward } := by
      simp only [orientedEdgeOfCoeff, orientationOfCoeff, if_neg hp]
    rw [horient]
    show -ModuleCat.freeMk e = _
    rw [if_neg hp, ModuleCat.freeMk, Finsupp.single_neg]

/-- The unit coefficient chosen by an edge's sign has absolute value one. -/
theorem natAbs_sign_unit (a : ℤ) : (if 0 < a then (1 : ℤ) else -1).natAbs = 1 := by
  by_cases hp : 0 < a
  · rw [if_pos hp]; decide
  · rw [if_neg hp]; decide

/-- An integer of absolute value one is exactly its sign-unit. -/
theorem eq_sign_unit_of_natAbs_eq_one (a : ℤ) (ha : a.natAbs = 1) :
    (if 0 < a then (1 : ℤ) else -1) = a := by
  by_cases hp : 0 < a
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- Multiplying the sign-unit by the absolute value recovers the integer. -/
theorem intNatAbs_mul_signUnit_eq_self (a : ℤ) :
    ((a.natAbs : ℤ) * (if 0 < a then (1 : ℤ) else -1)) = a := by
  by_cases hp : 0 < a
  · rw [if_pos hp]
    omega
  · rw [if_neg hp]
    omega

/-- Subtracting the sign-unit from a nonzero integer drops its absolute value by
exactly one.  This is the per-edge ℓ¹ decrease of one directed-cycle peel. -/
theorem natAbs_sub_sign_unit (a : ℤ) (ha : a ≠ 0) :
    a.natAbs = (a - (if 0 < a then (1 : ℤ) else -1)).natAbs + 1 := by
  by_cases hp : 0 < a
  · rw [if_pos hp]; omega
  · rw [if_neg hp]
    have hneg : a < 0 := by omega
    omega

/-- The sign-unit chosen by an edge's coefficient is never zero. -/
theorem sign_unit_ne_zero (a : ℤ) : (if 0 < a then (1 : ℤ) else -1) ≠ 0 := by
  by_cases hp : 0 < a <;> simp [hp]

/-- Coefficient of a single generator: the value at the chosen point, zero
elsewhere. -/
theorem edgeCoeff_single [DecidableEq SingularOneSimplex]
    (a : SingularOneSimplex) (b : ℤ) (e : SingularOneSimplex) :
    edgeCoeff (Finsupp.single a b) e = if a = e then b else 0 := by
  show (Finsupp.single a b).toFun e = _
  rw [← Finsupp.single_apply]
  rfl

/-- Coefficient of a finite sum of free edge-chains distributes over the sum. -/
theorem edgeCoeff_sum {k : ℕ} (f : Fin k → singularOneChainFree) (e : SingularOneSimplex) :
    edgeCoeff (∑ i, f i) e = ∑ i, edgeCoeff (f i) e := by
  show (Finsupp.applyAddHom e) (∑ i, f i) = ∑ i, (Finsupp.applyAddHom e) (f i)
  exact map_sum (Finsupp.applyAddHom e) f Finset.univ

/-- A sum of `if`-selected values over an injective family collapses to the
selected value when the test point lies in the image, and to zero otherwise. -/
theorem sum_ite_image_of_injective [DecidableEq SingularOneSimplex] {k : ℕ}
    (g : Fin k → SingularOneSimplex) (hg : Function.Injective g)
    (F : SingularOneSimplex → ℤ) (e : SingularOneSimplex) :
    (∑ i : Fin k, (if g i = e then F (g i) else 0)) =
      if e ∈ Finset.image g Finset.univ then F e else 0 := by
  by_cases he : e ∈ Finset.image g Finset.univ
  · rw [if_pos he]
    obtain ⟨i₀, _, hi₀⟩ := Finset.mem_image.mp he
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
      (fun j _ hj => by
        have hne : g j ≠ e := fun h => hj (hg (h.trans hi₀.symm))
        rw [if_neg hne])]
    rw [if_pos hi₀, hi₀]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    have hne : g i ≠ e := fun h => he (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩)
    rw [if_neg hne]

/-- The free edge-chain of an oriented closed walk through an injective family of
supported edges. -/
noncomputable def orientedCyclicChain {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex) : singularOneChainFree :=
  ∑ i, (orientedEdgeOfCoeff c (g i)).chain

/-- Pointwise coefficient of an oriented closed walk: on the walk it is the
sign-unit of the underlying flow, and off the walk it is zero. -/
theorem edgeCoeff_orientedCyclicChain [DecidableEq SingularOneSimplex] {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex)
    (hg : Function.Injective g) (e : SingularOneSimplex) :
    edgeCoeff (orientedCyclicChain c g) e =
      if e ∈ Finset.image g Finset.univ then
        (if 0 < edgeCoeff c e then (1 : ℤ) else -1) else 0 := by
  unfold orientedCyclicChain
  rw [edgeCoeff_sum]
  have hterm : ∀ i : Fin k, edgeCoeff ((orientedEdgeOfCoeff c (g i)).chain) e
      = if g i = e then (if 0 < edgeCoeff c (g i) then (1 : ℤ) else -1) else 0 := by
    intro i
    rw [orientedEdgeOfCoeff_chain_eq_single, edgeCoeff_single]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [sum_ite_image_of_injective g hg (fun x => if 0 < edgeCoeff c x then (1 : ℤ) else -1) e]

/-- The support of an oriented closed walk is exactly the image of its edge
family. -/
theorem edgeSupport_orientedCyclicChain [DecidableEq SingularOneSimplex] {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex)
    (hg : Function.Injective g) :
    edgeSupport (orientedCyclicChain c g) = Finset.image g Finset.univ := by
  ext e
  rw [mem_edgeSupport_iff, edgeCoeff_orientedCyclicChain c g hg e]
  by_cases he : e ∈ Finset.image g Finset.univ
  · rw [if_pos he]
    simp only [iff_true, he]
    exact sign_unit_ne_zero _
  · rw [if_neg he]
    simp [he]

/-- If a sign-selected oriented closed walk hits a unit coefficient of the ambient
flow, then subtracting that walk strictly shrinks support.  This isolates the
support-cardinality part of large-support extraction from the separate problem of
encoding mixed-orientation walks in the old one-scalar cyclic-edge-list format. -/
theorem edgeSupportCard_sub_orientedCyclic_lt_of_unitCoeff
    [DecidableEq SingularOneSimplex] {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex)
    (hg : Function.Injective g) (hmem : ∀ i, g i ∈ edgeSupport c)
    (hunit : ∃ i : Fin k, (edgeCoeff c (g i)).natAbs = 1) :
    edgeSupportCard (c - orientedCyclicChain c g) < edgeSupportCard c := by
  apply edgeSupportCard_sub_lt_of_supported_exact_cancel
  · rw [edgeSupport_orientedCyclicChain c g hg]
    exact Finset.image_subset_iff.mpr (fun i _ => hmem i)
  · obtain ⟨i, hi⟩ := hunit
    refine ⟨g i, ?_, ?_⟩
    · rw [edgeSupport_orientedCyclicChain c g hg]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · rw [edgeCoeff_orientedCyclicChain c g hg]
      have himg : g i ∈ Finset.image g Finset.univ :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      rw [if_pos himg]
      exact eq_sign_unit_of_natAbs_eq_one (edgeCoeff c (g i)) hi

/-- Scaling a sign-selected oriented closed walk by the minimum absolute
coefficient on the walk strictly shrinks support.  This is the support-cardinality
bookkeeping needed for a true exact cyclic peel: the minimum-coefficient edge is
cancelled exactly, while no new edge outside the original support appears. -/
theorem edgeSupportCard_sub_scaled_orientedCyclic_lt
    [DecidableEq SingularOneSimplex] {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex)
    (hk : 0 < k) (hg : Function.Injective g) (hmem : ∀ i, g i ∈ edgeSupport c) :
    ∃ m : ℤ, 0 < m ∧
      edgeSupportCard (c - m • orientedCyclicChain c g) < edgeSupportCard c := by
  let coeffAbs : Fin k → ℕ := fun i => (edgeCoeff c (g i)).natAbs
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, _hi₀_mem, hi₀_min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin k)) coeffAbs Finset.univ_nonempty
  let mN : ℕ := coeffAbs i₀
  let m : ℤ := (mN : ℤ)
  have hce_ne : edgeCoeff c (g i₀) ≠ 0 :=
    (mem_edgeSupport_iff c (g i₀)).mp (hmem i₀)
  have hmN_ne : mN ≠ 0 := by
    intro hzero
    apply hce_ne
    exact Int.natAbs_eq_zero.mp hzero
  have hm_pos_cast : (0 : ℤ) < (mN : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero hmN_ne
  have hm_pos : 0 < m := hm_pos_cast
  refine ⟨m, hm_pos, ?_⟩
  apply edgeSupportCard_sub_lt_of_supported_exact_cancel
  · intro e he
    have hcoeff_ne : edgeCoeff (m • orientedCyclicChain c g) e ≠ 0 :=
      (mem_edgeSupport_iff (m • orientedCyclicChain c g) e).mp he
    have hP_ne : edgeCoeff (orientedCyclicChain c g) e ≠ 0 := by
      intro hP_zero
      apply hcoeff_ne
      rw [edgeCoeff_zsmul, hP_zero, mul_zero]
    have heP : e ∈ edgeSupport (orientedCyclicChain c g) :=
      (mem_edgeSupport_iff (orientedCyclicChain c g) e).mpr hP_ne
    rw [edgeSupport_orientedCyclicChain c g hg] at heP
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp heP
    exact hmem i
  · refine ⟨g i₀, ?_, ?_⟩
    · have hcoeff_eq :
          edgeCoeff (m • orientedCyclicChain c g) (g i₀) = edgeCoeff c (g i₀) := by
        rw [edgeCoeff_zsmul, edgeCoeff_orientedCyclicChain c g hg]
        have himg : g i₀ ∈ Finset.image g Finset.univ :=
          Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩
        rw [if_pos himg]
        exact intNatAbs_mul_signUnit_eq_self (edgeCoeff c (g i₀))
      exact (mem_edgeSupport_iff (m • orientedCyclicChain c g) (g i₀)).mpr
        (by rw [hcoeff_eq]; exact hce_ne)
    · rw [edgeCoeff_zsmul, edgeCoeff_orientedCyclicChain c g hg]
      have himg : g i₀ ∈ Finset.image g Finset.univ :=
        Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩
      rw [if_pos himg]
      exact intNatAbs_mul_signUnit_eq_self (edgeCoeff c (g i₀))

/-- The ℓ¹ size of an oriented closed walk through an injective family of `k`
edges is exactly `k`. -/
theorem chainL1_orientedCyclicChain [DecidableEq SingularOneSimplex] {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex)
    (hg : Function.Injective g) :
    chainL1 (orientedCyclicChain c g) = k := by
  unfold chainL1
  rw [edgeSupport_orientedCyclicChain c g hg]
  have hone : ∀ e ∈ Finset.image g Finset.univ,
      (edgeCoeff (orientedCyclicChain c g) e).natAbs = 1 := by
    intro e he
    rw [edgeCoeff_orientedCyclicChain c g hg e, if_pos he]
    exact natAbs_sign_unit _
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_image_of_injective Finset.univ hg, Finset.card_univ, Fintype.card_fin]

/-- **The ℓ¹ decrease of one directed-cycle peel.**  Subtracting an oriented
closed walk through `k` distinct supported edges from a balanced flow lowers the
ℓ¹ size by exactly `k`: every edge on the walk loses one unit of magnitude (its
sign is aligned with the flow, so the magnitudes subtract), and all other
coefficients are unchanged. -/
theorem chainL1_sub_orientedCyclic [DecidableEq SingularOneSimplex] {k : ℕ}
    (c : singularOneChainFree) (g : Fin k → SingularOneSimplex)
    (hg : Function.Injective g) (hmem : ∀ i, g i ∈ edgeSupport c) :
    chainL1 (c - orientedCyclicChain c g) + k = chainL1 c := by
  set P := orientedCyclicChain c g with hP
  have himg_sub : Finset.image g Finset.univ ⊆ edgeSupport c :=
    Finset.image_subset_iff.mpr (fun i _ => hmem i)
  -- pointwise additivity of natAbs on the support of `c`
  have hpt : ∀ e ∈ edgeSupport c,
      (edgeCoeff c e).natAbs
        = (edgeCoeff (c - P) e).natAbs + (edgeCoeff P e).natAbs := by
    intro e he
    have hce : edgeCoeff c e ≠ 0 := (mem_edgeSupport_iff c e).mp he
    rw [edgeCoeff_sub]
    rw [hP, edgeCoeff_orientedCyclicChain c g hg e]
    by_cases himg : e ∈ Finset.image g Finset.univ
    · rw [if_pos himg, natAbs_sign_unit]
      exact natAbs_sub_sign_unit (edgeCoeff c e) hce
    · rw [if_neg himg]
      simp
  -- supports of `c - P` and `P` are contained in the support of `c`
  have hPsupp : edgeSupport P ⊆ edgeSupport c := by
    rw [hP, edgeSupport_orientedCyclicChain c g hg]; exact himg_sub
  have hCPsupp : edgeSupport (c - P) ⊆ edgeSupport c := by
    intro e he
    by_contra hnotc
    have hc0 : edgeCoeff c e = 0 :=
      Classical.not_not.mp (mt (mem_edgeSupport_iff c e).mpr hnotc)
    have hP0 : edgeCoeff P e = 0 := by
      have : e ∉ edgeSupport P := fun hmem' => hnotc (hPsupp hmem')
      exact Classical.not_not.mp (mt (mem_edgeSupport_iff P e).mpr this)
    have : edgeCoeff (c - P) e = 0 := by rw [edgeCoeff_sub, hc0, hP0, sub_zero]
    exact (mem_edgeSupport_iff (c - P) e).mp he this
  -- extend the two residual/walk sums from their own supports to `edgeSupport c`
  have hsum_cP : ∑ e ∈ edgeSupport c, (edgeCoeff (c - P) e).natAbs = chainL1 (c - P) := by
    unfold chainL1
    refine (Finset.sum_subset hCPsupp (fun x _ hx => ?_)).symm
    have hx0 : edgeCoeff (c - P) x = 0 :=
      Classical.not_not.mp (mt (mem_edgeSupport_iff (c - P) x).mpr hx)
    rw [hx0]; rfl
  have hsum_P : ∑ e ∈ edgeSupport c, (edgeCoeff P e).natAbs = chainL1 P := by
    unfold chainL1
    refine (Finset.sum_subset hPsupp (fun x _ hx => ?_)).symm
    have hx0 : edgeCoeff P x = 0 :=
      Classical.not_not.mp (mt (mem_edgeSupport_iff P x).mpr hx)
    rw [hx0]; rfl
  have hP_k : chainL1 P = k := by rw [hP]; exact chainL1_orientedCyclicChain c g hg
  calc chainL1 (c - P) + k
      = chainL1 (c - P) + chainL1 P := by rw [hP_k]
    _ = (∑ e ∈ edgeSupport c, (edgeCoeff (c - P) e).natAbs)
          + (∑ e ∈ edgeSupport c, (edgeCoeff P e).natAbs) := by rw [hsum_cP, hsum_P]
    _ = ∑ e ∈ edgeSupport c,
          ((edgeCoeff (c - P) e).natAbs + (edgeCoeff P e).natAbs) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ e ∈ edgeSupport c, (edgeCoeff c e).natAbs := (Finset.sum_congr rfl hpt).symm
    _ = chainL1 c := rfl

/-! ### Existence of an oriented closed walk in a balanced nonzero flow

A nonzero balanced free edge-flow always contains an oriented closed walk through
distinct supported edges.  If some supported edge is a loop (its two endpoints
coincide) the walk is that single edge.  Otherwise the balance condition lets us
take a successor edge from every supported edge (its initial vertex matches the
current edge's terminal vertex); iterating this successor on the finite support
must return to a periodic point, and the minimal period gives a simple closed
walk. -/

open Function in
/-- **Oriented closed walk extraction.**  Every nonzero balanced free edge-flow
admits an oriented closed walk: a positive number `k` of distinct supported
edges `g : Fin k → SingularOneSimplex` whose sign-selected orientations connect
terminal-to-initial cyclically. -/
theorem exists_orientedCyclicFamily_of_balanced_nonzero
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (c : singularOneChainFree)
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    (hne : c ≠ 0) :
    ∃ (k : ℕ) (g : Fin k → SingularOneSimplex),
      0 < k ∧ Function.Injective g ∧ (∀ i, g i ∈ edgeSupport c) ∧
        (∀ i, (orientedEdgeOfCoeff c (g i)).terminal
          = (orientedEdgeOfCoeff c (g (finRotate k i))).initial) := by
  by_cases hloopex : ∃ e ∈ edgeSupport c,
      (orientedEdgeOfCoeff c e).initial = (orientedEdgeOfCoeff c e).terminal
  · obtain ⟨e, he, hloop⟩ := hloopex
    refine ⟨1, fun _ => e, Nat.one_pos, ?_, ?_, ?_⟩
    · intro a b _; exact Subsingleton.elim a b
    · intro _; exact he
    · intro _; exact hloop.symm
  · push_neg at hloopex
    have hsupp_ne : (edgeSupport c).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; exact hne ((edgeSupport_eq_empty_iff c).mp h)
    obtain ⟨e₀, he₀⟩ := hsupp_ne
    haveI : Fintype {x // x ∈ edgeSupport c} := FinsetCoe.fintype _
    let y₀ : {x // x ∈ edgeSupport c} := ⟨e₀, he₀⟩
    let nextSupp : {x // x ∈ edgeSupport c} → {x // x ∈ edgeSupport c} := fun s =>
      ⟨(exists_next_orientedEdge_from_terminal hzero s.2 (hloopex s.1 s.2)).choose,
       (exists_next_orientedEdge_from_terminal hzero s.2 (hloopex s.1 s.2)).choose_spec.1⟩
    have nextSupp_spec : ∀ s : {x // x ∈ edgeSupport c},
        (orientedEdgeOfCoeff c (nextSupp s).val).initial
          = (orientedEdgeOfCoeff c s.val).terminal := fun s =>
      (exists_next_orientedEdge_from_terminal hzero s.2 (hloopex s.1 s.2)).choose_spec.2
    -- a periodic point exists by pigeonhole on the finite support
    have hper : (Function.periodicPts nextSupp).Nonempty := by
      obtain ⟨i, j, hij, hijeq⟩ :=
        Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => nextSupp^[n] y₀)
      rcases Nat.lt_or_ge i j with hlt | hge
      · refine ⟨nextSupp^[i] y₀, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) ?_⟩
        show nextSupp^[j - i] (nextSupp^[i] y₀) = nextSupp^[i] y₀
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
        exact hijeq.symm
      · have hlt : j < i := lt_of_le_of_ne hge hij.symm
        refine ⟨nextSupp^[j] y₀, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) ?_⟩
        show nextSupp^[i - j] (nextSupp^[j] y₀) = nextSupp^[j] y₀
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
        exact hijeq
    obtain ⟨y, hy⟩ := hper
    have hp_pos : 0 < Function.minimalPeriod nextSupp y :=
      Function.minimalPeriod_pos_of_mem_periodicPts hy
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hp_pos.ne'
    have hp_iter : nextSupp^[m + 1] y = y := by
      have h := Function.iterate_minimalPeriod (f := nextSupp) (x := y)
      rwa [hm] at h
    have hinjOn : Set.InjOn (fun n => nextSupp^[n] y) (Set.Iio (m + 1)) := by
      have h := Function.iterate_injOn_Iio_minimalPeriod (f := nextSupp) (x := y)
      rwa [hm] at h
    refine ⟨m + 1, fun i => (nextSupp^[i.val] y).val, Nat.succ_pos m, ?_, ?_, ?_⟩
    · intro i j hgij
      apply Fin.ext
      exact hinjOn (Set.mem_Iio.mpr i.isLt) (Set.mem_Iio.mpr j.isLt) (Subtype.ext hgij)
    · intro i; exact (nextSupp^[i.val] y).property
    · intro i
      have hrot : nextSupp^[(finRotate (m + 1) i).val] y = nextSupp (nextSupp^[i.val] y) := by
        rw [finRotate_succ_apply, Fin.val_add_one]
        split
        · rename_i hlast
          have hival : i.val = m := by rw [hlast]; simp
          rw [hival, Function.iterate_zero_apply]
          have hsucc : nextSupp (nextSupp^[m] y) = nextSupp^[m + 1] y :=
            (Function.iterate_succ_apply' nextSupp m y).symm
          rw [hsucc, hp_iter]
        · rw [Function.iterate_succ_apply']
      show (orientedEdgeOfCoeff c (nextSupp^[i.val] y).val).terminal
        = (orientedEdgeOfCoeff c (nextSupp^[(finRotate (m + 1) i).val] y).val).initial
      rw [hrot]
      exact (nextSupp_spec (nextSupp^[i.val] y)).symm

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **One-step directed-cycle extraction (unconditional).**  Every nonzero
balanced free edge-flow splits as one directed-cycle piece plus a balanced
residual of strictly smaller ℓ¹ size.  The piece is the oriented closed walk of
`exists_orientedCyclicFamily_of_balanced_nonzero`, packaged through the oriented
homological engine; the ℓ¹ decrease is `chainL1_sub_orientedCyclic`. -/
theorem directedCycleExtraction
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (c : singularOneChainFree)
    (hcbd : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    (hne : c ≠ 0) :
    ∃ (t : DirectedCycleFreeTerm) (r : singularOneChainFree),
      c = t.chain + r ∧
        ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
          chainL1 r < chainL1 c := by
  obtain ⟨k, g, hk, hg_inj, hg_mem, hconn⟩ :=
    exists_orientedCyclicFamily_of_balanced_nonzero c hcbd hne
  let o : Fin k → OrientedSingularEdge := fun i => orientedEdgeOfCoeff c (g i)
  have hconn' : ∀ i, (o i).terminal = (o (finRotate k i)).initial := hconn
  let t := directedCycleFreeTerm_of_orientedCyclicFamily o hconn'
  have ht_chain : t.chain = orientedCyclicChain c g := rfl
  have hbd_t : ModuleCat.Hom.hom singularOneBoundaryFree t.chain = 0 := by
    rw [ht_chain]; unfold orientedCyclicChain
    exact cyclicOrientedFamily_freeBoundary_zero o hconn'
  refine ⟨t, c - t.chain, ?_, ?_, ?_⟩
  · abel
  · rw [map_sub, hcbd, hbd_t, sub_zero]
  · have hkey := chainL1_sub_orientedCyclic c g hg_inj hg_mem
    rw [ht_chain]
    omega

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The unconditional directed-cycle kernel decomposition.**  Every free
edge-chain in the kernel of the explicit boundary is a finite sum of
directed-cycle pieces.  Proved by strong induction on the ℓ¹ size, peeling one
oriented closed walk at a time with `directedCycleExtraction`.  This discharges
the hypothesis of `circleH1ZIsoInt_of_directedCycles_of_zeroWinding_bounds`
without any axiom or `sorry`. -/
theorem freeBoundaryKernel_decomposesIntoDirectedCycles_holds
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex] :
    freeBoundaryKernel_decomposesIntoDirectedCycles := by
  intro c hc
  suffices H : ∀ n, ∀ c : singularOneChainFree, chainL1 c = n →
      ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
        ∃ ts : List DirectedCycleFreeTerm, c = directedCycleFreeTermListChain ts by
    exact H (chainL1 c) c rfl hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hcL1 hcbd
    by_cases hzero : c = 0
    · exact ⟨[], by rw [hzero]; rfl⟩
    · obtain ⟨t, r, hdecomp, hrbd, hrlt⟩ := directedCycleExtraction c hcbd hzero
      rw [hcL1] at hrlt
      obtain ⟨ts, hts⟩ := ih (chainL1 r) hrlt r rfl hrbd
      refine ⟨t :: ts, ?_⟩
      show c = t.chain + directedCycleFreeTermListChain ts
      rw [hdecomp, hts]

/-! ### Directed-cycle generation reduction

The finite-flow theorem reduces every cycle to a finite sum of
`DirectedCycleFreeTerm`s.  The remaining geometric filling problem can therefore
be localized: prove boundary-generation for one directed closed walk, then sum
the witnesses. -/

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Local remaining geometric target: each directed-cycle term is homologous, at
the chain level, to an integer multiple of the fundamental cycle. -/
def directedCycleTerms_boundary_generate : Prop :=
  ∀ t : DirectedCycleFreeTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      t.cycle =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If every directed-cycle term is generated by the fundamental cycle modulo a
boundary, then every finite directed-cycle list is. -/
theorem directedCycleFreeTermList_boundary_generates
    (hterm : directedCycleTerms_boundary_generate) :
    ∀ ts : List DirectedCycleFreeTerm,
      ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
        directedCycleFreeTermListCycle ts =
          ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
            ModuleCat.Hom.hom fundamentalCycle n
  | [] => by
      refine ⟨0, 0, ?_⟩
      unfold directedCycleFreeTermListCycle
      simp
  | t :: ts => by
      obtain ⟨n₁, b₁, ht⟩ := hterm t
      obtain ⟨n₂, b₂, hts⟩ := directedCycleFreeTermList_boundary_generates hterm ts
      refine ⟨n₁ + n₂, b₁ + b₂, ?_⟩
      unfold directedCycleFreeTermListCycle
      rw [ht, hts, map_add, map_add]
      abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Boundary-generation for individual directed-cycle terms implies the global
circle chain-level generation theorem.  Combined with
`zeroWindingCycles_bound_iff_fundamentalCycle_boundary_generates`, this is the
next minimal geometric target: fill one directed closed walk. -/
theorem fundamentalCycle_boundary_generates_of_directedCycleTerms
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hterm : directedCycleTerms_boundary_generate) :
    fundamentalCycle_boundary_generates := by
  intro z
  let c : singularOneChainFree :=
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) z)
  have hc0 : ModuleCat.Hom.hom singularOneBoundaryFree c = 0 := by
    unfold c
    change ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.iCycles 1 ≫ singularOneChainToFree ≫
          singularOneBoundaryFree) z = 0
    rw [singularOneChainToFree_boundary_free]
    rw [← Category.assoc, HomologicalComplex.iCycles_d]
    simp
  obtain ⟨ts, hts⟩ := freeBoundaryKernel_decomposesIntoDirectedCycles_holds c hc0
  have hcycle : z = directedCycleFreeTermListCycle ts := by
    have hinj_toFree : Function.Injective (ModuleCat.Hom.hom singularOneChainToFree) := by
      haveI : IsIso singularOneChainToFree := by
        change IsIso singularOneChainFreeIso.hom
        infer_instance
      haveI : Mono singularOneChainToFree := inferInstance
      exact (ModuleCat.mono_iff_injective singularOneChainToFree).mp inferInstance
    have hinj_iCycles :
        Function.Injective
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
      (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
    apply hinj_iCycles
    apply hinj_toFree
    unfold c at hts
    rw [hts, directedCycleFreeTermList_chain_eq ts]
  obtain ⟨n, b, hlist⟩ := directedCycleFreeTermList_boundary_generates hterm ts
  refine ⟨n, b, ?_⟩
  rw [hcycle, hlist]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The one-directed-cycle generation theorem is enough for the final Mathlib
circle H₁ computation. -/
theorem circleH1ZIsoInt_of_directedCycleTerms
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hterm : directedCycleTerms_boundary_generate) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_fundamentalCycle_boundary_generates
    (fundamentalCycle_boundary_generates_of_directedCycleTerms hterm)

/-! ### Oriented-family generation reduction

The local prism construction needs the actual closed walk, not just a packaged
cycle object.  This structure retains that geometric data. -/

/-- A concrete oriented cyclic family: a finite sign-oriented closed walk in the
singular `1`-simplices. -/
structure OrientedCyclicFamilyTerm where
  k : ℕ
  o : Fin k → OrientedSingularEdge
  hconn : ∀ i : Fin k, (o i).terminal = (o (finRotate k i)).initial

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Package an oriented cyclic family as a directed-cycle term. -/
noncomputable def OrientedCyclicFamilyTerm.toDirectedCycleFreeTerm
    (T : OrientedCyclicFamilyTerm) : DirectedCycleFreeTerm :=
  directedCycleFreeTerm_of_orientedCyclicFamily T.o T.hconn

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Including a concrete oriented cyclic family into raw `C₁` is exactly the raw
chain of its oriented edges. -/
theorem OrientedCyclicFamilyTerm.iCycles_eq_orientedChain
    (T : OrientedCyclicFamilyTerm) :
    ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
      T.toDirectedCycleFreeTerm.cycle =
        ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (T.o i).chain) := by
  rw [DirectedCycleFreeTerm.iCycles_eq_freeToChain]
  rfl

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The winding of a concrete oriented cyclic family is the sum of the oriented
winding contributions of its edges. -/
theorem OrientedCyclicFamilyTerm.cycleWinding_eq_sum
    (T : OrientedCyclicFamilyTerm) :
    cycleWinding T.toDirectedCycleFreeTerm.cycle =
      ∑ i, orientedWinding (T.o i) := by
  rw [DirectedCycleFreeTerm.cycleWinding_eq_freeChain]
  change ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (T.o i).chain)) =
    ∑ i, orientedWinding (T.o i)
  exact windingChainMap_freeToChain_orientedChain_sum T.o

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Sum of path-cones over the oriented edge paths of a concrete cyclic family. -/
noncomputable def OrientedCyclicFamilyTerm.pathConeChain
    (T : OrientedCyclicFamilyTerm) : singularTwoChainFree :=
  coneSingularTwoChainOfPathFamily (fun i : Fin T.k => orientedEdgePath (T.o i))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free `C₁` boundary of the summed path-cones over an oriented
cyclic family.  The next geometric cancellation target is the difference between
the terminal-return side sum and the constant-apex side sum, together with the
fundamental-cycle correction. -/
theorem OrientedCyclicFamilyTerm.pathConeChain_boundary
    (T : OrientedCyclicFamilyTerm) :
    ModuleCat.Hom.hom singularTwoBoundaryFree T.pathConeChain =
      (∑ i, ModuleCat.freeMk
          (singularOneSimplexOfMap (coneTerminalSide (orientedEdgePath (T.o i))))) -
        (∑ i, ModuleCat.freeMk
          (singularOneSimplexOfMap (constantOneSimplex ((orientedEdgePath (T.o i)) 0)))) +
          (∑ i, ModuleCat.freeMk
            (singularOneSimplexOfMap (oneSimplexOfPath (orientedEdgePath (T.o i))))) := by
  unfold OrientedCyclicFamilyTerm.pathConeChain
  exact singularTwoBoundaryFree_coneSingularTwoChainOfPathFamily
    (fun i : Fin T.k => orientedEdgePath (T.o i))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- In a cyclic oriented family, the sum of constant apex edges at each oriented
initial point is the same as the sum at each oriented terminal point.  This is the
index-shift skeleton for cancelling side chains in the multi-edge cone prism. -/
theorem OrientedCyclicFamilyTerm.constantApexSide_reindex_terminal
    (T : OrientedCyclicFamilyTerm) :
    (∑ i, ModuleCat.freeMk
        (singularOneSimplexOfMap (constantOneSimplex ((orientedEdgePath (T.o i)) 0))) :
        singularOneChainFree) =
      ∑ i, ModuleCat.freeMk
        (singularOneSimplexOfMap (constantOneSimplex ((orientedEdgePath (T.o i)) 1))) := by
  rw [← Equiv.sum_comp (finRotate T.k)
    (fun j => (ModuleCat.freeMk
      (singularOneSimplexOfMap (constantOneSimplex ((orientedEdgePath (T.o j)) 0))) :
        singularOneChainFree))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply congrArg ModuleCat.freeMk
  apply congrArg singularOneSimplexOfMap
  apply congrArg constantOneSimplex
  rw [orientedEdgePath_zero, orientedEdgePath_one]
  exact congrArg vertexPoint (T.hconn i).symm

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A concrete oriented cyclic family has an integer total winding, and
subtracting that multiple of the fundamental cycle leaves a zero-winding residual.
This is the cycle-object version of the prism target. -/
theorem OrientedCyclicFamilyTerm.zeroWinding_residual
    (T : OrientedCyclicFamilyTerm) :
    ∃ n : ModuleCat.of ℤ ℤ,
      (∑ i, orientedWinding (T.o i)) = (n : ℝ) ∧
        cycleWinding
          (T.toDirectedCycleFreeTerm.cycle - ModuleCat.Hom.hom fundamentalCycle n) = 0 := by
  obtain ⟨n, hn⟩ := T.toDirectedCycleFreeTerm.winding_integral
  refine ⟨n, ?_, ?_⟩
  · rw [← T.cycleWinding_eq_sum, hn]
  · unfold cycleWinding at hn ⊢
    rw [map_sub]
    change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap)
        T.toDirectedCycleFreeTerm.cycle -
      cycleWinding (ModuleCat.Hom.hom fundamentalCycle n) = 0
    rw [hn, cycleWinding_fundamentalCycle]
    ring

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- In any boundary-generation witness for a concrete oriented cyclic family,
the integer coefficient is forced to be the total oriented winding. -/
theorem OrientedCyclicFamilyTerm.generation_coeff_eq_winding
    (T : OrientedCyclicFamilyTerm)
    (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2)
    (h :
      T.toDirectedCycleFreeTerm.cycle =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n) :
    ∑ i, orientedWinding (T.o i) = (n : ℝ) := by
  have hboundary_winding :
      cycleWinding (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b) = 0 := by
    unfold cycleWinding
    change ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) b = 0
    rw [HomologicalComplex.toCycles_i_assoc, windingChainMap_boundary]
    simp
  calc ∑ i, orientedWinding (T.o i)
      = cycleWinding T.toDirectedCycleFreeTerm.cycle :=
        (T.cycleWinding_eq_sum).symm
    _ = cycleWinding
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n) := by rw [h]
    _ = (n : ℝ) := by
        unfold cycleWinding
        rw [map_add]
        change cycleWinding (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b) +
          cycleWinding (ModuleCat.Hom.hom fundamentalCycle n) = (n : ℝ)
        rw [hboundary_winding, cycleWinding_fundamentalCycle]
        simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Chain represented by a list of concrete oriented cyclic families. -/
noncomputable def orientedCyclicFamilyTermListChain
    (ts : List OrientedCyclicFamilyTerm) : singularOneChainFree :=
  directedCycleFreeTermListChain (ts.map OrientedCyclicFamilyTerm.toDirectedCycleFreeTerm)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Cycle represented by a list of concrete oriented cyclic families. -/
noncomputable def orientedCyclicFamilyTermListCycle
    (ts : List OrientedCyclicFamilyTerm) :
    sphereOneSingularIntChainComplex.cycles 1 :=
  directedCycleFreeTermListCycle (ts.map OrientedCyclicFamilyTerm.toDirectedCycleFreeTerm)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- One-step extraction retaining the actual oriented cyclic family data. -/
theorem orientedCyclicFamilyExtraction
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (c : singularOneChainFree)
    (hcbd : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    (hne : c ≠ 0) :
    ∃ (T : OrientedCyclicFamilyTerm) (r : singularOneChainFree),
      c = T.toDirectedCycleFreeTerm.chain + r ∧
        ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
          chainL1 r < chainL1 c := by
  obtain ⟨k, g, hk, hg_inj, hg_mem, hconn⟩ :=
    exists_orientedCyclicFamily_of_balanced_nonzero c hcbd hne
  let o : Fin k → OrientedSingularEdge := fun i => orientedEdgeOfCoeff c (g i)
  have hconn' : ∀ i, (o i).terminal = (o (finRotate k i)).initial := hconn
  let T : OrientedCyclicFamilyTerm := { k := k, o := o, hconn := hconn' }
  have hT_chain : T.toDirectedCycleFreeTerm.chain = orientedCyclicChain c g := rfl
  have hbd_T : ModuleCat.Hom.hom singularOneBoundaryFree T.toDirectedCycleFreeTerm.chain = 0 := by
    rw [hT_chain]; unfold orientedCyclicChain
    exact cyclicOrientedFamily_freeBoundary_zero o hconn'
  refine ⟨T, c - T.toDirectedCycleFreeTerm.chain, ?_, ?_, ?_⟩
  · abel
  · rw [map_sub, hcbd, hbd_T, sub_zero]
  · have hkey := chainL1_sub_orientedCyclic c g hg_inj hg_mem
    rw [hT_chain]
    omega

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Support-cardinality version of oriented extraction.  The extracted oriented
closed walk is scaled by the minimum absolute coefficient on that walk, so the
residual is still balanced and has strictly smaller support.  This is the exact
finite-flow theorem needed before translating signed oriented cycles into the
older one-scalar `CyclicSingularEdgeListTerm` interface. -/
def largeSupportOrientedScaledExtractionStep : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      c ≠ 0 →
        1 < edgeSupportCard c →
          ∃ (T : OrientedCyclicFamilyTerm) (m : ℤ) (r : singularOneChainFree),
            0 < m ∧
              c = m • T.toDirectedCycleFreeTerm.chain + r ∧
                ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
                  edgeSupportCard r < edgeSupportCard c

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The support-cardinality oriented extraction step is unconditional.  The
`1 < support` hypothesis is retained to match the large-support interface, but
the proof only needs nonzero balanced flow. -/
theorem largeSupportOrientedScaledExtractionStep_holds
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex] :
    largeSupportOrientedScaledExtractionStep := by
  intro c hcbd hne _hlarge
  obtain ⟨k, g, hk, hg_inj, hg_mem, hconn⟩ :=
    exists_orientedCyclicFamily_of_balanced_nonzero c hcbd hne
  let o : Fin k → OrientedSingularEdge := fun i => orientedEdgeOfCoeff c (g i)
  have hconn' : ∀ i, (o i).terminal = (o (finRotate k i)).initial := hconn
  let T : OrientedCyclicFamilyTerm := { k := k, o := o, hconn := hconn' }
  have hT_chain : T.toDirectedCycleFreeTerm.chain = orientedCyclicChain c g := rfl
  have hbd_T : ModuleCat.Hom.hom singularOneBoundaryFree T.toDirectedCycleFreeTerm.chain = 0 := by
    rw [hT_chain]; unfold orientedCyclicChain
    exact cyclicOrientedFamily_freeBoundary_zero o hconn'
  obtain ⟨m, hm_pos, hsupport⟩ :=
    edgeSupportCard_sub_scaled_orientedCyclic_lt c g hk hg_inj hg_mem
  refine ⟨T, m, c - m • T.toDirectedCycleFreeTerm.chain, hm_pos, ?_, ?_, ?_⟩
  · abel
  · rw [map_sub, map_zsmul, hbd_T, smul_zero, sub_zero]
    exact hcbd
  · rw [hT_chain]
    exact hsupport

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Every balanced free edge-chain decomposes into concrete oriented cyclic
families. -/
theorem freeBoundaryKernel_decomposesIntoOrientedCyclicFamilies_holds
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex] :
    ∀ c : singularOneChainFree,
      ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
        ∃ ts : List OrientedCyclicFamilyTerm, c = orientedCyclicFamilyTermListChain ts := by
  intro c hc
  suffices H : ∀ n, ∀ c : singularOneChainFree, chainL1 c = n →
      ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
        ∃ ts : List OrientedCyclicFamilyTerm, c = orientedCyclicFamilyTermListChain ts by
    exact H (chainL1 c) c rfl hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hcL1 hcbd
    by_cases hzero : c = 0
    · exact ⟨[], by rw [hzero]; rfl⟩
    · obtain ⟨T, r, hdecomp, hrbd, hrlt⟩ := orientedCyclicFamilyExtraction c hcbd hzero
      rw [hcL1] at hrlt
      obtain ⟨ts, hts⟩ := ih (chainL1 r) hrlt r rfl hrbd
      refine ⟨T :: ts, ?_⟩
      show c = T.toDirectedCycleFreeTerm.chain + orientedCyclicFamilyTermListChain ts
      rw [hdecomp, hts]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Local geometric target with the walk data retained: every concrete oriented
closed walk is homologous to an integer multiple of the fundamental cycle. -/
def orientedCyclicFamilies_boundary_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      T.toDirectedCycleFreeTerm.cycle =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw-chain form of the remaining prism target.  This is the form an explicit
singular prism construction should naturally prove: the `C₁` boundary of a
singular `2`-chain is the oriented closed walk minus the corresponding multiple
of the fundamental cycle. -/
def orientedCyclicFamilies_rawPrism_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1) b =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          T.toDirectedCycleFreeTerm.cycle -
          ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Fully explicit raw-chain form of the remaining prism target: construct a
singular `2`-chain whose boundary is the raw oriented edge sum minus the matching
fundamental-cycle multiple. -/
def orientedCyclicFamilies_explicitRawPrism_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1) b =
        ModuleCat.Hom.hom singularOneChainFreeToChain (∑ i, (T.o i).chain) -
          ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Free-coordinate prism target: construct an explicit free `C₂` chain whose
free boundary is the oriented edge sum minus the free-coordinate image of the
matching fundamental cycle.  This is the cleanest target for a hand-built finite
prism construction. -/
def orientedCyclicFamilies_freePrism_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (B : singularTwoChainFree),
      ModuleCat.Hom.hom singularTwoBoundaryFree B =
        (∑ i, (T.o i).chain) -
          ModuleCat.Hom.hom singularOneChainToFree
            (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
              (ModuleCat.Hom.hom fundamentalCycle n))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Free-coordinate image of an integer multiple of the fundamental cycle. -/
noncomputable def fundamentalCycleFreeChain (n : ModuleCat.of ℤ ℤ) : singularOneChainFree :=
  ModuleCat.Hom.hom singularOneChainToFree
    (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
      (ModuleCat.Hom.hom fundamentalCycle n))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-coordinate image of the fundamental cycle has winding equal to its
integer coefficient. -/
theorem windingChainMap_fundamentalCycleFreeChain (n : ModuleCat.of ℤ ℤ) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain (fundamentalCycleFreeChain n)) =
        (n : ℝ) := by
  unfold fundamentalCycleFreeChain
  have hround :
      ModuleCat.Hom.hom singularOneChainFreeToChain
        (ModuleCat.Hom.hom singularOneChainToFree
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n))) =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n) := by
    have hid := congrArg
      (fun f => ModuleCat.Hom.hom f
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n)))
      singularOneChainFreeIso.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [hround]
  exact cycleWinding_fundamentalCycle n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The desired free `C₁` boundary in the oriented-family free-prism target. -/
noncomputable def OrientedCyclicFamilyTerm.desiredFreePrismBoundary
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ) : singularOneChainFree :=
  (∑ i, (T.o i).chain) - fundamentalCycleFreeChain n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Sum of the terminal-return sides in the path-cone boundary for an oriented
cyclic family. -/
noncomputable def OrientedCyclicFamilyTerm.terminalReturnSideChain
    (T : OrientedCyclicFamilyTerm) : singularOneChainFree :=
  ∑ i, ModuleCat.freeMk
    (singularOneSimplexOfMap (coneTerminalSide (orientedEdgePath (T.o i))))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The terminal-return side chain has winding equal to the negative total
oriented winding of the original cyclic family. -/
theorem OrientedCyclicFamilyTerm.winding_terminalReturnSideChain
    (T : OrientedCyclicFamilyTerm) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain T.terminalReturnSideChain) =
        - ∑ i, orientedWinding (T.o i) := by
  unfold OrientedCyclicFamilyTerm.terminalReturnSideChain
  rw [map_sum, map_sum]
  calc
    (∑ i, ModuleCat.Hom.hom windingChainMap
        (ModuleCat.Hom.hom singularOneChainFreeToChain
          (ModuleCat.freeMk
            (singularOneSimplexOfMap (coneTerminalSide (orientedEdgePath (T.o i)))))))
        = ∑ i, - orientedWinding (T.o i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [windingChainMap_singularOneChainFreeToChain_freeMk]
          exact (T.o i).singularWinding_terminalReturnSide
    _ = - ∑ i, orientedWinding (T.o i) := by
          rw [Finset.sum_neg_distrib]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Sum of the initial constant-apex sides in the path-cone boundary for an
oriented cyclic family. -/
noncomputable def OrientedCyclicFamilyTerm.constantApexInitialSideChain
    (T : OrientedCyclicFamilyTerm) : singularOneChainFree :=
  ∑ i, ModuleCat.freeMk
    (singularOneSimplexOfMap (constantOneSimplex ((orientedEdgePath (T.o i)) 0)))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Sum of the terminal constant-apex sides in the path-cone boundary for an
oriented cyclic family. -/
noncomputable def OrientedCyclicFamilyTerm.constantApexTerminalSideChain
    (T : OrientedCyclicFamilyTerm) : singularOneChainFree :=
  ∑ i, ModuleCat.freeMk
    (singularOneSimplexOfMap (constantOneSimplex ((orientedEdgePath (T.o i)) 1)))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The terminal constant-apex side chain has zero winding. -/
theorem OrientedCyclicFamilyTerm.winding_constantApexTerminalSideChain
    (T : OrientedCyclicFamilyTerm) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain T.constantApexTerminalSideChain) =
        0 := by
  unfold OrientedCyclicFamilyTerm.constantApexTerminalSideChain
  rw [map_sum, map_sum]
  rw [Finset.sum_eq_zero]
  intro i _
  rw [singularOneSimplexOfMap_constantOneSimplex]
  exact windingChainMap_constantSingularOneSimplex ((orientedEdgePath (T.o i)) 1)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The cyclic connection reindexes the initial constant-apex side sum as the
terminal constant-apex side sum. -/
theorem OrientedCyclicFamilyTerm.constantApexInitialSideChain_eq_terminal
    (T : OrientedCyclicFamilyTerm) :
    T.constantApexInitialSideChain = T.constantApexTerminalSideChain := by
  unfold OrientedCyclicFamilyTerm.constantApexInitialSideChain
    OrientedCyclicFamilyTerm.constantApexTerminalSideChain
  exact T.constantApexSide_reindex_terminal

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Sum of the path-parametric base edges appearing in the path-cone boundary. -/
noncomputable def OrientedCyclicFamilyTerm.pathBaseEdgeChain
    (T : OrientedCyclicFamilyTerm) : singularOneChainFree :=
  ∑ i, ModuleCat.freeMk
    (singularOneSimplexOfMap (oneSimplexOfPath (orientedEdgePath (T.o i))))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The signed free edge-chain of the oriented cyclic family. -/
noncomputable def OrientedCyclicFamilyTerm.orientedEdgeChain
    (T : OrientedCyclicFamilyTerm) : singularOneChainFree :=
  ∑ i, (T.o i).chain

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free `C₁` residual between the currently constructed path-cone boundary
and the desired free-prism boundary.  Filling this residual is exactly what turns
the finite path-cone skeleton into the final `freePrism` witness. -/
noncomputable def OrientedCyclicFamilyTerm.pathConeResidualBoundary
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ) : singularOneChainFree :=
  ModuleCat.Hom.hom singularTwoBoundaryFree T.pathConeChain -
    T.desiredFreePrismBoundary n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Concrete expansion of the path-cone residual.  The remaining geometry is now
visible as a side-chain correction plus the difference between path-parametric
base edges and the signed oriented edge-chain, with the fundamental correction
carried explicitly. -/
theorem OrientedCyclicFamilyTerm.pathConeResidualBoundary_eq_explicit
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ) :
    T.pathConeResidualBoundary n =
      T.terminalReturnSideChain - T.constantApexInitialSideChain +
        T.pathBaseEdgeChain - (T.orientedEdgeChain - fundamentalCycleFreeChain n) := by
  unfold OrientedCyclicFamilyTerm.pathConeResidualBoundary
    OrientedCyclicFamilyTerm.desiredFreePrismBoundary
    OrientedCyclicFamilyTerm.terminalReturnSideChain
    OrientedCyclicFamilyTerm.constantApexInitialSideChain
    OrientedCyclicFamilyTerm.pathBaseEdgeChain
    OrientedCyclicFamilyTerm.orientedEdgeChain
  rw [T.pathConeChain_boundary]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Terminal-side form of the residual.  After cyclic reindexing, the residual
splits into the terminal-return side correction and the path-edge-to-oriented-edge
correction. -/
theorem OrientedCyclicFamilyTerm.pathConeResidualBoundary_eq_terminalSide
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ) :
    T.pathConeResidualBoundary n =
      T.terminalReturnSideChain - T.constantApexTerminalSideChain +
        T.pathBaseEdgeChain - (T.orientedEdgeChain - fundamentalCycleFreeChain n) := by
  rw [T.pathConeResidualBoundary_eq_explicit]
  rw [T.constantApexInitialSideChain_eq_terminal]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The terminal-side boundary expression left after the path-base correction has
been removed. -/
noncomputable def OrientedCyclicFamilyTerm.terminalSideCorrectionBoundary
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ) : singularOneChainFree :=
  T.terminalReturnSideChain - T.constantApexTerminalSideChain +
    fundamentalCycleFreeChain n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Winding of the terminal-side correction boundary.  Choosing `n` to be the total
oriented winding makes this obstruction vanish. -/
theorem OrientedCyclicFamilyTerm.winding_terminalSideCorrectionBoundary
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain
        (T.terminalSideCorrectionBoundary n)) =
        - ∑ i, orientedWinding (T.o i) + (n : ℝ) := by
  unfold OrientedCyclicFamilyTerm.terminalSideCorrectionBoundary
  rw [map_add, map_sub]
  rw [map_add, map_sub]
  change ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain T.terminalReturnSideChain) -
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain T.constantApexTerminalSideChain) +
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain (fundamentalCycleFreeChain n)) =
      - ∑ i, orientedWinding (T.o i) + (n : ℝ)
  rw [T.winding_terminalReturnSideChain, T.winding_constantApexTerminalSideChain,
    windingChainMap_fundamentalCycleFreeChain]
  ring

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The terminal-side correction boundary has zero winding when its fundamental
coefficient is the total oriented winding of the cyclic family. -/
theorem OrientedCyclicFamilyTerm.winding_terminalSideCorrectionBoundary_eq_zero
    (T : OrientedCyclicFamilyTerm) (n : ModuleCat.of ℤ ℤ)
    (hn : ∑ i, orientedWinding (T.o i) = (n : ℝ)) :
    ModuleCat.Hom.hom windingChainMap
      (ModuleCat.Hom.hom singularOneChainFreeToChain
        (T.terminalSideCorrectionBoundary n)) = 0 := by
  rw [T.winding_terminalSideCorrectionBoundary, hn]
  ring

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Correction target left after summing the path-cones over an oriented cyclic
family.  A witness is a `2`-chain whose boundary is the residual between the
summed path-cone boundary and the desired free-prism boundary. -/
def orientedCyclicFamilies_pathConeCorrection_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (K : singularTwoChainFree),
      ModuleCat.Hom.hom singularTwoBoundaryFree K =
        T.pathConeResidualBoundary n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Terminal-side correction target.  It asks for a `2`-chain whose boundary
turns the sum of terminal-return sides into the terminal constant sides, up to
the correct fundamental-cycle multiple. -/
def orientedCyclicFamilies_terminalSideCorrection_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ (n : ModuleCat.of ℤ ℤ) (Ks : singularTwoChainFree),
      ModuleCat.Hom.hom singularTwoBoundaryFree Ks =
        T.terminalSideCorrectionBoundary n

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Path-base correction target.  It asks for a `2`-chain whose boundary replaces
the path-parametric base edges by the signed oriented singular-edge chain. -/
def orientedCyclicFamilies_pathBaseCorrection_generate : Prop :=
  ∀ T : OrientedCyclicFamilyTerm,
    ∃ Kp : singularTwoChainFree,
      ModuleCat.Hom.hom singularTwoBoundaryFree Kp =
        T.pathBaseEdgeChain - T.orientedEdgeChain

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The family path-base residual is the sum of the local oriented-edge residuals. -/
theorem OrientedCyclicFamilyTerm.pathBaseCorrectionBoundary_sum
    (T : OrientedCyclicFamilyTerm) :
    T.pathBaseEdgeChain - T.orientedEdgeChain =
      ∑ i, (T.o i).pathBaseCorrectionBoundary := by
  unfold OrientedCyclicFamilyTerm.pathBaseEdgeChain
    OrientedCyclicFamilyTerm.orientedEdgeChain
    OrientedSingularEdge.pathBaseCorrectionBoundary
  rw [Finset.sum_sub_distrib]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Edge-local path-base corrections imply the family path-base correction target. -/
theorem orientedCyclicFamilies_pathBaseCorrection_generate_of_localEdges
    (hlocal : ∀ o : OrientedSingularEdge,
      ∃ K : singularTwoChainFree,
        ModuleCat.Hom.hom singularTwoBoundaryFree K =
          o.pathBaseCorrectionBoundary) :
    orientedCyclicFamilies_pathBaseCorrection_generate := by
  intro T
  choose K hK using hlocal
  refine ⟨∑ i, K (T.o i), ?_⟩
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun i _ => hK (T.o i))]
  exact T.pathBaseCorrectionBoundary_sum.symm

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The path-base correction target is closed: every reversed oriented edge is
filled by the triangular backtrack prism, and every forward edge has zero
residual. -/
theorem orientedCyclicFamilies_pathBaseCorrection_generate_holds :
    orientedCyclicFamilies_pathBaseCorrection_generate :=
  orientedCyclicFamilies_pathBaseCorrection_generate_of_localEdges
    OrientedSingularEdge.pathBaseCorrectionBoundary_bounds

/-! ### Geodesic free-chain calculus for the terminal-side correction

The terminal-return sides are geodesics, so the terminal-side correction lives
entirely in the geodesic free-chain calculus.  We need three facts, each an
explicit boundary identity: the composition law, the `2π`-shift winding step,
and the identification of the fundamental free chain with `n` copies of the
geodesic `0 → 2π`. -/

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Free `C₁` generator of a geodesic (lift-linear) singular edge. -/
noncomputable def geodesicFreeChain (a b : ℝ) : singularOneChainFree :=
  ModuleCat.freeMk (singularOneSimplexOfMap (geodesicOneSimplex a b))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Composition law in free `C₁`: the boundary of the lift-affine `2`-simplex on
`(p, q, r)` is `geo(q,r) − geo(p,r) + geo(p,q)`. -/
theorem singularTwoBoundaryFree_geodesicFreeChain (p q r : ℝ) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
      (ModuleCat.freeMk (linearSingularTwoSimplex p q r)) =
      geodesicFreeChain q r - geodesicFreeChain p r + geodesicFreeChain p q :=
  singularTwoBoundaryFree_freeMk_linearSingularTwoSimplex p q r

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A `2π·ℤ` shift of both lift endpoints leaves the geodesic free chain
unchanged. -/
theorem geodesicFreeChain_shift (a b : ℝ) (m : ℤ) :
    geodesicFreeChain (a + (m : ℝ) * (2 * Real.pi)) (b + (m : ℝ) * (2 * Real.pi)) =
      geodesicFreeChain a b := by
  unfold geodesicFreeChain
  rw [geodesicOneSimplex_shift]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A degenerate geodesic (equal endpoints) bounds a constant `2`-simplex. -/
theorem geodesicFreeChain_self_bounds (a : ℝ) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
        (ModuleCat.freeMk (constantSingularTwoSimplex (trigCirclePoint a))) =
      geodesicFreeChain a a := by
  unfold geodesicFreeChain
  rw [geodesicOneSimplex_self, singularOneSimplexOfMap_constantOneSimplex]
  exact constantSingularOneSimplex_free_boundary (trigCirclePoint a)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The geodesic `0 → 2π` free chain is the fundamental free generator. -/
theorem geodesicFreeChain_zero_twoPi_eq_fundamental :
    geodesicFreeChain 0 (2 * Real.pi) =
      ModuleCat.freeMk CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex := by
  unfold geodesicFreeChain
  rw [singularOneSimplexOfMap_geodesic_zero_twoPi]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Fundamental free chain identification.**  The free-coordinate image of `n`
times the fundamental cycle is `n` copies of the geodesic `0 → 2π`. -/
theorem fundamentalCycleFreeChain_eq_zsmul (n : ModuleCat.of ℤ ℤ) :
    fundamentalCycleFreeChain n = (n : ℤ) • geodesicFreeChain 0 (2 * Real.pi) := by
  rw [geodesicFreeChain_zero_twoPi_eq_fundamental]
  unfold fundamentalCycleFreeChain
  have hcomp : fundamentalCycle ≫ sphereOneSingularIntChainComplex.iCycles 1 =
      CircleH1Computation.fundamentalSphereOneSingularOneChain := by
    rw [fundamentalCycle, HomologicalComplex.liftCycles_i]
  have hiC : ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom fundamentalCycle n) =
      ModuleCat.Hom.hom CircleH1Computation.fundamentalSphereOneSingularOneChain n := by
    have h := congrArg (fun f => ModuleCat.Hom.hom f n) hcomp
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using h
  have hcomp2 : CircleH1Computation.fundamentalSphereOneSingularOneChain ≫ singularOneChainToFree =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ singularOneChainFree
        (ModuleCat.freeMk CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex)) :=
    singularOneChainToFree_ι CircleFundamentalSimplex.fundamentalSphereOneSingularOneSimplex
  have hfinal := congrArg (fun f => ModuleCat.Hom.hom f n) hcomp2
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.toSpanSingleton_apply] at hfinal
  rw [hiC]
  exact hfinal

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- One-turn geodesic boundary: `∂(linear 0 2π (z+2π)) = geo(0,z) − geo(0,z+2π)
+ geo(0,2π)`, using shift invariance to fold the `(2π, z+2π)` side onto
`(0, z)`. -/
theorem singularTwoBoundaryFree_linear_step (z : ℝ) :
    ModuleCat.Hom.hom singularTwoBoundaryFree
        (ModuleCat.freeMk (linearSingularTwoSimplex 0 (2 * Real.pi) (z + 2 * Real.pi))) =
      geodesicFreeChain 0 z - geodesicFreeChain 0 (z + 2 * Real.pi)
        + geodesicFreeChain 0 (2 * Real.pi) := by
  rw [singularTwoBoundaryFree_geodesicFreeChain]
  have hshift : geodesicFreeChain (2 * Real.pi) (z + 2 * Real.pi) = geodesicFreeChain 0 z := by
    have h := geodesicFreeChain_shift 0 z 1
    simpa using h
  rw [hshift]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Geodesic winding step.**  Shifting the terminal lift endpoint by `m` full
turns adds `m` fundamental loops to the geodesic, modulo an explicit
`2`-boundary. -/
theorem geodesicFreeChain_step (y : ℝ) (m : ℤ) :
    ∃ K : singularTwoChainFree,
      ModuleCat.Hom.hom singularTwoBoundaryFree K =
        geodesicFreeChain 0 (y + (m : ℝ) * (2 * Real.pi)) - geodesicFreeChain 0 y
          - (m : ℤ) • geodesicFreeChain 0 (2 * Real.pi) := by
  induction m using Int.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    simp
  | succ i ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨K - ModuleCat.freeMk
        (linearSingularTwoSimplex 0 (2 * Real.pi) (y + (i : ℝ) * (2 * Real.pi) + 2 * Real.pi)), ?_⟩
    rw [map_sub, hK, singularTwoBoundaryFree_linear_step (y + (i : ℝ) * (2 * Real.pi))]
    push_cast
    rw [show y + (i : ℝ) * (2 * Real.pi) + 2 * Real.pi = y + ((i : ℝ) + 1) * (2 * Real.pi) by ring,
      add_smul, one_smul]
    abel
  | pred i ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨K + ModuleCat.freeMk
        (linearSingularTwoSimplex 0 (2 * Real.pi)
          (y + (-(i : ℝ) - 1) * (2 * Real.pi) + 2 * Real.pi)), ?_⟩
    rw [map_add, hK, singularTwoBoundaryFree_linear_step (y + (-(i : ℝ) - 1) * (2 * Real.pi))]
    push_cast
    rw [show y + (-(i : ℝ) - 1) * (2 * Real.pi) + 2 * Real.pi
          = y + (-(i : ℝ)) * (2 * Real.pi) by ring]
    rw [show (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) by ring, add_smul, neg_one_smul]
    push_cast
    abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The terminal-side correction target is closed unconditionally.**

For a concrete oriented cyclic family `T`, the terminal-return sides are
geodesics, each from the terminal lift of one edge to the initial lift of the
next.  The cyclic connectivity `T.hconn` forces those lift endpoints to agree
modulo `2π·ℤ`; collecting the per-edge integer shifts gives the total winding
`n = ∑ m i`.  The bounding `2`-chain is assembled from three explicit families:
the lift-affine cones `linear 0 (bᵢ) (aᵢ)` (composition law), the winding-step
chains `Kstep i` (one per edge, from `geodesicFreeChain_step`), and the constant
apex `2`-simplices.  Telescoping with the index reindex `∑ geo(0,a(σ i)) =
∑ geo(0,a i)` and `∑ (m i)•g = n•g` leaves exactly
`terminalReturnSide − constantApexTerminalSide + n·(fundamental cycle)`. -/
theorem orientedCyclicFamilies_terminalSideCorrection_generate_holds :
    orientedCyclicFamilies_terminalSideCorrection_generate := by
  classical
  intro T
  -- Lift-level connectivity: terminal lift of edge `i` agrees with initial lift
  -- of edge `σ i` modulo a full turn.
  have hex : ∀ i : Fin T.k, ∃ m : ℤ,
      pathLift (orientedEdgePath (T.o i)) 1
        = pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0 + (m : ℝ) * (2 * Real.pi) := by
    intro i
    have h1 : trigCirclePoint (pathLift (orientedEdgePath (T.o i)) 1)
        = (orientedEdgePath (T.o i)) 1 :=
      congrFun (pathLift_lifts (orientedEdgePath (T.o i))) 1
    have h0 : trigCirclePoint (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0)
        = (orientedEdgePath (T.o (finRotate T.k i))) 0 :=
      congrFun (pathLift_lifts (orientedEdgePath (T.o (finRotate T.k i)))) 0
    have hfib : trigCirclePoint (pathLift (orientedEdgePath (T.o i)) 1)
        = trigCirclePoint (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0) := by
      rw [h1, h0, orientedEdgePath_one, orientedEdgePath_zero]
      exact congrArg vertexPoint (T.hconn i)
    exact (CircleLifting.trigCirclePoint_eq_iff _ _).1 hfib
  choose m hm using hex
  -- One winding-step chain per edge, from `geodesicFreeChain_step`.
  have hstep : ∀ i : Fin T.k, ∃ K : singularTwoChainFree,
      ModuleCat.Hom.hom singularTwoBoundaryFree K =
        geodesicFreeChain 0
            (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0 + (m i : ℝ) * (2 * Real.pi))
          - geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0)
          - (m i : ℤ) • geodesicFreeChain 0 (2 * Real.pi) := fun i =>
    geodesicFreeChain_step (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0) (m i)
  choose Kstep hKstep using hstep
  refine ⟨(∑ i, m i : ℤ),
      (∑ i, ModuleCat.freeMk (linearSingularTwoSimplex 0
          (pathLift (orientedEdgePath (T.o i)) 1) (pathLift (orientedEdgePath (T.o i)) 0)))
        - (∑ i, Kstep i)
        - (∑ i, ModuleCat.freeMk (constantSingularTwoSimplex
            (trigCirclePoint (pathLift (orientedEdgePath (T.o i)) 1)))), ?_⟩
  -- Rewrite the three target side-chains into geodesic free chains.
  have hret : T.terminalReturnSideChain
      = ∑ i, geodesicFreeChain (pathLift (orientedEdgePath (T.o i)) 1)
          (pathLift (orientedEdgePath (T.o i)) 0) := by
    unfold OrientedCyclicFamilyTerm.terminalReturnSideChain
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold geodesicFreeChain
    rw [coneTerminalSide_eq_geodesic]
  have hcon : T.constantApexTerminalSideChain
      = ∑ i, geodesicFreeChain (pathLift (orientedEdgePath (T.o i)) 1)
          (pathLift (orientedEdgePath (T.o i)) 1) := by
    unfold OrientedCyclicFamilyTerm.constantApexTerminalSideChain
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hlift1 : trigCirclePoint (pathLift (orientedEdgePath (T.o i)) 1)
        = (orientedEdgePath (T.o i)) 1 :=
      congrFun (pathLift_lifts (orientedEdgePath (T.o i))) 1
    unfold geodesicFreeChain
    rw [geodesicOneSimplex_self, hlift1]
  -- Index reindex along the cyclic rotation and the scalar-sum identity.
  have hreindex :
      (∑ i, geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0))
        = ∑ i, geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o i)) 0) :=
    Equiv.sum_comp (finRotate T.k)
      (fun j => geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o j)) 0))
  -- Per-edge boundary evaluations.
  have hL1 : (∑ i, ModuleCat.Hom.hom singularTwoBoundaryFree
        (ModuleCat.freeMk (linearSingularTwoSimplex 0
          (pathLift (orientedEdgePath (T.o i)) 1) (pathLift (orientedEdgePath (T.o i)) 0))))
      = ∑ i, (geodesicFreeChain (pathLift (orientedEdgePath (T.o i)) 1)
            (pathLift (orientedEdgePath (T.o i)) 0)
          - geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o i)) 0)
          + geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o i)) 1)) :=
    Finset.sum_congr rfl (fun i _ =>
      singularTwoBoundaryFree_geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o i)) 1)
        (pathLift (orientedEdgePath (T.o i)) 0))
  have hL2 : (∑ i, ModuleCat.Hom.hom singularTwoBoundaryFree (Kstep i))
      = ∑ i, (geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o i)) 1)
          - geodesicFreeChain 0 (pathLift (orientedEdgePath (T.o (finRotate T.k i))) 0)
          - (m i : ℤ) • geodesicFreeChain 0 (2 * Real.pi)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hKstep i, ← hm i]
  have hL3 : (∑ i, ModuleCat.Hom.hom singularTwoBoundaryFree
        (ModuleCat.freeMk (constantSingularTwoSimplex
          (trigCirclePoint (pathLift (orientedEdgePath (T.o i)) 1)))))
      = ∑ i, geodesicFreeChain (pathLift (orientedEdgePath (T.o i)) 1)
          (pathLift (orientedEdgePath (T.o i)) 1) :=
    Finset.sum_congr rfl (fun i _ =>
      geodesicFreeChain_self_bounds (pathLift (orientedEdgePath (T.o i)) 1))
  -- Assemble.
  unfold OrientedCyclicFamilyTerm.terminalSideCorrectionBoundary
  rw [hret, hcon, fundamentalCycleFreeChain_eq_zsmul]
  rw [map_sub, map_sub, map_sum, map_sum, map_sum, hL1, hL2, hL3]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hreindex, ← Finset.sum_smul]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The terminal-side and path-base correction targets together fill the full
path-cone residual. -/
theorem orientedCyclicFamilies_pathConeCorrection_generate_of_splitCorrections
    (hside : orientedCyclicFamilies_terminalSideCorrection_generate)
    (hpath : orientedCyclicFamilies_pathBaseCorrection_generate) :
    orientedCyclicFamilies_pathConeCorrection_generate := by
  intro T
  obtain ⟨n, Ks, hKs⟩ := hside T
  obtain ⟨Kp, hKp⟩ := hpath T
  refine ⟨n, Ks + Kp, ?_⟩
  rw [map_add, hKs, hKp, T.pathConeResidualBoundary_eq_terminalSide]
  unfold OrientedCyclicFamilyTerm.terminalSideCorrectionBoundary
  abel_nf

/-- Filling the path-cone residual for every oriented cyclic family proves the
free-coordinate prism target named in the Phase 5 checklist. -/
theorem orientedCyclicFamilies_freePrism_generate_of_pathConeCorrection
    (hcorr : orientedCyclicFamilies_pathConeCorrection_generate) :
    orientedCyclicFamilies_freePrism_generate := by
  intro T
  obtain ⟨n, K, hK⟩ := hcorr T
  refine ⟨n, T.pathConeChain - K, ?_⟩
  rw [map_sub, hK]
  unfold OrientedCyclicFamilyTerm.pathConeResidualBoundary
    OrientedCyclicFamilyTerm.desiredFreePrismBoundary fundamentalCycleFreeChain
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The two split correction targets are enough for the Phase 5 free-prism
generation target. -/
theorem orientedCyclicFamilies_freePrism_generate_of_splitCorrections
    (hside : orientedCyclicFamilies_terminalSideCorrection_generate)
    (hpath : orientedCyclicFamilies_pathBaseCorrection_generate) :
    orientedCyclicFamilies_freePrism_generate :=
  orientedCyclicFamilies_freePrism_generate_of_pathConeCorrection
    (orientedCyclicFamilies_pathConeCorrection_generate_of_splitCorrections hside hpath)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A free-coordinate prism construction gives the fully explicit raw prism
target after transporting the free `C₂` boundary through Mathlib's raw chain
complex. -/
theorem orientedCyclicFamilies_explicitRawPrism_generate_of_freePrism
    (hfree : orientedCyclicFamilies_freePrism_generate) :
    orientedCyclicFamilies_explicitRawPrism_generate := by
  intro T
  obtain ⟨n, B, hB⟩ := hfree T
  refine ⟨n, ModuleCat.Hom.hom singularTwoChainFreeToChain B, ?_⟩
  have hraw := rawBoundary_eq_of_singularTwoBoundaryFree_eq B
    ((∑ i, (T.o i).chain) -
      ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n))) hB
  have hround :
      ModuleCat.Hom.hom singularOneChainFreeToChain
        (ModuleCat.Hom.hom singularOneChainToFree
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n))) =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n) := by
    have hid := congrArg
      (fun f => ModuleCat.Hom.hom f
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n)))
      singularOneChainFreeIso.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [map_sub, hround] at hraw
  exact hraw

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Conversely, the fully explicit raw prism target gives the free-coordinate
prism target.  The proof uses the degree-`2` raw/free isomorphism and therefore
shows that `orientedCyclicFamilies_freePrism_generate` is not stronger in
substance than constructing the raw singular `2`-chain. -/
theorem orientedCyclicFamilies_freePrism_generate_of_explicitRawPrism
    (hexplicit : orientedCyclicFamilies_explicitRawPrism_generate) :
    orientedCyclicFamilies_freePrism_generate := by
  intro T
  obtain ⟨n, b, hb⟩ := hexplicit T
  let u : singularOneChainFree :=
    (∑ i, (T.o i).chain) -
      ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n))
  refine ⟨n, ModuleCat.Hom.hom singularTwoChainToFree b, ?_⟩
  apply singularTwoBoundaryFree_eq_of_rawBoundary_eq b u
  unfold u
  rw [hb, map_sub]
  have hround :
      ModuleCat.Hom.hom singularOneChainFreeToChain
        (ModuleCat.Hom.hom singularOneChainToFree
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
            (ModuleCat.Hom.hom fundamentalCycle n))) =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n) := by
    have hid := congrArg
      (fun f => ModuleCat.Hom.hom f
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (ModuleCat.Hom.hom fundamentalCycle n)))
      singularOneChainFreeIso.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    exact hid
  rw [hround]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The fully explicit raw prism target implies the packaged raw prism target. -/
theorem orientedCyclicFamilies_rawPrism_generate_of_explicit
    (hexplicit : orientedCyclicFamilies_explicitRawPrism_generate) :
    orientedCyclicFamilies_rawPrism_generate := by
  intro T
  obtain ⟨n, b, hb⟩ := hexplicit T
  refine ⟨n, b, ?_⟩
  rw [T.iCycles_eq_orientedChain]
  exact hb

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The packaged raw prism target is equivalent to the fully explicit raw-chain
target.  The equivalence is only the already-proved identification between an
oriented cyclic family's cycle object and its concrete signed edge sum. -/
theorem orientedCyclicFamilies_explicitRawPrism_generate_of_rawPrism
    (hraw : orientedCyclicFamilies_rawPrism_generate) :
    orientedCyclicFamilies_explicitRawPrism_generate := by
  intro T
  obtain ⟨n, b, hb⟩ := hraw T
  refine ⟨n, b, ?_⟩
  rw [← T.iCycles_eq_orientedChain]
  exact hb

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-coordinate prism target and the fully explicit raw-prism target are
equivalent.  This packages the degree-`2` raw/free transport added above. -/
theorem orientedCyclicFamilies_freePrism_generate_iff_explicitRawPrism_generate :
    orientedCyclicFamilies_freePrism_generate ↔
      orientedCyclicFamilies_explicitRawPrism_generate := by
  constructor
  · exact orientedCyclicFamilies_explicitRawPrism_generate_of_freePrism
  · exact orientedCyclicFamilies_freePrism_generate_of_explicitRawPrism

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-coordinate prism target and the packaged raw-prism target are
equivalent.  After this theorem, the only unsolved content is the actual
geometric prism construction, not the choice of raw/free coordinates. -/
theorem orientedCyclicFamilies_freePrism_generate_iff_rawPrism_generate :
    orientedCyclicFamilies_freePrism_generate ↔
      orientedCyclicFamilies_rawPrism_generate := by
  constructor
  · intro hfree
    exact orientedCyclicFamilies_rawPrism_generate_of_explicit
      (orientedCyclicFamilies_explicitRawPrism_generate_of_freePrism hfree)
  · intro hraw
    exact orientedCyclicFamilies_freePrism_generate_of_explicitRawPrism
      (orientedCyclicFamilies_explicitRawPrism_generate_of_rawPrism hraw)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Raw prism generation implies the cycle-object generation target.  This is a
pure categorical transport through `toCycles`; the remaining work is therefore
only to construct the raw prism `2`-chain. -/
theorem orientedCyclicFamilies_boundary_generate_of_rawPrism
    (hraw : orientedCyclicFamilies_rawPrism_generate) :
    orientedCyclicFamilies_boundary_generate := by
  intro T
  obtain ⟨n, b, hb⟩ := hraw T
  refine ⟨n, b, ?_⟩
  have hinj_iCycles :
      Function.Injective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
    (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
  apply hinj_iCycles
  rw [map_add]
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
      T.toDirectedCycleFreeTerm.cycle =
    ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1) b +
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom fundamentalCycle n)
  rw [HomologicalComplex.toCycles_i]
  rw [hb]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Cycle-object generation gives the packaged raw-chain prism equality by
including the cycle equality into `C₁`. -/
theorem orientedCyclicFamilies_rawPrism_generate_of_boundary_generate
    (hterm : orientedCyclicFamilies_boundary_generate) :
    orientedCyclicFamilies_rawPrism_generate := by
  intro T
  obtain ⟨n, b, hT⟩ := hterm T
  refine ⟨n, b, ?_⟩
  rw [hT, map_add]
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.d 2 1) b =
    ModuleCat.Hom.hom
      (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
        sphereOneSingularIntChainComplex.iCycles 1) b +
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom fundamentalCycle n) -
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
        (ModuleCat.Hom.hom fundamentalCycle n)
  rw [HomologicalComplex.toCycles_i]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Cycle-object generation gives the fully explicit raw-chain prism equality. -/
theorem orientedCyclicFamilies_explicitRawPrism_generate_of_boundary_generate
    (hterm : orientedCyclicFamilies_boundary_generate) :
    orientedCyclicFamilies_explicitRawPrism_generate := by
  intro T
  obtain ⟨n, b, hb⟩ :=
    orientedCyclicFamilies_rawPrism_generate_of_boundary_generate hterm T
  refine ⟨n, b, ?_⟩
  rw [← T.iCycles_eq_orientedChain]
  exact hb

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If each concrete oriented cyclic family is generated by the fundamental
cycle modulo a boundary, then every finite list of such families is. -/
theorem orientedCyclicFamilyTermList_boundary_generates
    (hterm : orientedCyclicFamilies_boundary_generate) :
    ∀ ts : List OrientedCyclicFamilyTerm,
      ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
        orientedCyclicFamilyTermListCycle ts =
          ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
            ModuleCat.Hom.hom fundamentalCycle n
  | [] => by
      refine ⟨0, 0, ?_⟩
      unfold orientedCyclicFamilyTermListCycle directedCycleFreeTermListCycle
      simp
  | T :: ts => by
      obtain ⟨n₁, b₁, hT⟩ := hterm T
      obtain ⟨n₂, b₂, hts⟩ := orientedCyclicFamilyTermList_boundary_generates hterm ts
      refine ⟨n₁ + n₂, b₁ + b₂, ?_⟩
      change T.toDirectedCycleFreeTerm.cycle + orientedCyclicFamilyTermListCycle ts =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) (b₁ + b₂) +
          ModuleCat.Hom.hom fundamentalCycle (n₁ + n₂)
      rw [hT, hts, map_add, map_add]
      abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Filling each concrete oriented cyclic family proves the global chain-level
generation theorem. -/
theorem fundamentalCycle_boundary_generates_of_orientedCyclicFamilies
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hterm : orientedCyclicFamilies_boundary_generate) :
    fundamentalCycle_boundary_generates := by
  intro z
  let c : singularOneChainFree :=
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) z)
  have hc0 : ModuleCat.Hom.hom singularOneBoundaryFree c = 0 := by
    unfold c
    change ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.iCycles 1 ≫ singularOneChainToFree ≫
          singularOneBoundaryFree) z = 0
    rw [singularOneChainToFree_boundary_free]
    rw [← Category.assoc, HomologicalComplex.iCycles_d]
    simp
  obtain ⟨ts, hts⟩ := freeBoundaryKernel_decomposesIntoOrientedCyclicFamilies_holds c hc0
  have hcycle : z = orientedCyclicFamilyTermListCycle ts := by
    have hinj_toFree : Function.Injective (ModuleCat.Hom.hom singularOneChainToFree) := by
      haveI : IsIso singularOneChainToFree := by
        change IsIso singularOneChainFreeIso.hom
        infer_instance
      haveI : Mono singularOneChainToFree := inferInstance
      exact (ModuleCat.mono_iff_injective singularOneChainToFree).mp inferInstance
    have hinj_iCycles :
        Function.Injective
          (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)) :=
      (ModuleCat.mono_iff_injective (sphereOneSingularIntChainComplex.iCycles 1)).mp inferInstance
    apply hinj_iCycles
    apply hinj_toFree
    unfold c at hts
    rw [hts]
    unfold orientedCyclicFamilyTermListChain orientedCyclicFamilyTermListCycle
    rw [directedCycleFreeTermList_chain_eq]
  obtain ⟨n, b, hlist⟩ := orientedCyclicFamilyTermList_boundary_generates hterm ts
  refine ⟨n, b, ?_⟩
  rw [hcycle, hlist]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The concrete oriented-family filling target is enough for the final Mathlib
circle H₁ computation. -/
theorem circleH1ZIsoInt_of_orientedCyclicFamilies
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hterm : orientedCyclicFamilies_boundary_generate) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_fundamentalCycle_boundary_generates
    (fundamentalCycle_boundary_generates_of_orientedCyclicFamilies hterm)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit free `C₁` chain represented by a finite list of singular
`1`-simplices, each with coefficient `1`. -/
noncomputable def singularEdgeListChain :
    List SingularOneSimplex → singularOneChainFree
  | [] => 0
  | e :: es => ModuleCat.freeMk e + singularEdgeListChain es

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A forward edge-list has nonnegative coefficient at every singular edge before
the global scalar of a `CyclicSingularEdgeListTerm` is applied. -/
theorem edgeCoeff_singularEdgeListChain_nonneg [DecidableEq SingularOneSimplex]
    (es : List SingularOneSimplex) (e : SingularOneSimplex) :
    0 ≤ edgeCoeff (singularEdgeListChain es) e := by
  induction es with
  | nil =>
      unfold singularEdgeListChain edgeCoeff
      rfl
  | cons a as ih =>
      unfold singularEdgeListChain
      rw [edgeCoeff_add]
      by_cases ha : a = e
      · subst a
        rw [edgeCoeff_freeMk_self]
        omega
      · have hfree : edgeCoeff (ModuleCat.freeMk a) e = 0 := by
          rw [ModuleCat.freeMk, edgeCoeff_single a (1 : ℤ) e, if_neg ha]
        rw [hfree]
        omega

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-chain represented by `List.ofFn e` is the finite sum of the
corresponding free generators. -/
theorem singularEdgeListChain_ofFn {k : ℕ} (e : Fin k → SingularOneSimplex) :
    singularEdgeListChain (List.ofFn e) = ∑ i, ModuleCat.freeMk (e i) := by
  induction k with
  | zero =>
      simp [singularEdgeListChain]
  | succ k ih =>
      rw [List.ofFn_succ]
      unfold singularEdgeListChain
      rw [ih (fun i : Fin k => e i.succ)]
      rw [Fin.sum_univ_succ]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A concrete cyclic edge-list piece.  It records an actual finite list of
singular `1`-simplices, a global integer coefficient for that listed cycle, and
the certified cycle object whose raw free-chain image is that coefficient times
the listed edge sum. -/
structure CyclicSingularEdgeListTerm where
  edges : List SingularOneSimplex
  coeff : ModuleCat.of ℤ ℤ
  cycle : sphereOneSingularIntChainComplex.cycles 1
  chain_eq :
    ModuleCat.Hom.hom singularOneChainToFree
      (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1) cycle) =
        coeff • singularEdgeListChain edges
  winding_integral : ∃ n : ModuleCat.of ℤ ℤ, cycleWinding cycle = (n : ℝ)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A genuinely forward cyclic family packages into the old concrete cyclic
edge-list interface.  This lemma marks the exact compatibility surface between
the older forward-only extraction target and the newer oriented-cycle engine. -/
noncomputable def cyclicSingularEdgeListTerm_of_cyclicFamily {k : ℕ}
    (e : Fin k → SingularOneSimplex)
    (hconn : ∀ i : Fin k, edgeTerminal (e i) = edgeInitial (e (finRotate k i))) :
    CyclicSingularEdgeListTerm where
  edges := List.ofFn e
  coeff := 1
  cycle := (directedCycleFreeTerm_of_cyclicFamily e hconn).cycle
  chain_eq := by
    have hchain := (directedCycleFreeTerm_of_cyclicFamily e hconn).chain_eq
    change ModuleCat.Hom.hom singularOneChainToFree
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.iCycles 1)
          (directedCycleFreeTerm_of_cyclicFamily e hconn).cycle) =
          (directedCycleFreeTerm_of_cyclicFamily e hconn).chain at hchain
    rw [hchain]
    change (∑ i, ModuleCat.freeMk (e i)) = (1 : ModuleCat.of ℤ ℤ) •
      singularEdgeListChain (List.ofFn e)
    rw [singularEdgeListChain_ofFn]
    simp
  winding_integral := (directedCycleFreeTerm_of_cyclicFamily e hconn).winding_integral

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If a concrete oriented cyclic family is everywhere forward, then it is a
concrete cyclic edge-list term in the older forward-only interface. -/
noncomputable def OrientedCyclicFamilyTerm.toCyclicSingularEdgeListTerm_of_all_forward
    (T : OrientedCyclicFamilyTerm)
    (hforward : ∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.forward) :
    CyclicSingularEdgeListTerm :=
  cyclicSingularEdgeListTerm_of_cyclicFamily
    (fun i : Fin T.k => (T.o i).edge)
    (by
      intro i
      have hconn := T.hconn i
      simpa [OrientedSingularEdge.terminal, OrientedSingularEdge.initial,
        hforward i, hforward (finRotate T.k i)] using hconn)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A concrete cyclic edge-list piece is, in particular, a directed-cycle piece
in the abstract free-boundary kernel decomposition interface. -/
noncomputable def CyclicSingularEdgeListTerm.toDirectedCycleFreeTerm
    (t : CyclicSingularEdgeListTerm) : DirectedCycleFreeTerm where
  cycle := t.cycle
  chain := t.coeff • singularEdgeListChain t.edges
  chain_eq := t.chain_eq
  winding_integral := t.winding_integral

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-chain sum represented by a finite list of concrete cyclic edge-list
pieces. -/
noncomputable def cyclicSingularEdgeListTermListChain :
    List CyclicSingularEdgeListTerm → singularOneChainFree
  | [] => 0
  | t :: ts => t.coeff • singularEdgeListChain t.edges +
      cyclicSingularEdgeListTermListChain ts

/-- The free-chain contribution of one concrete cyclic edge-list term. -/
noncomputable def CyclicSingularEdgeListTerm.chain
    (t : CyclicSingularEdgeListTerm) : singularOneChainFree :=
  t.coeff • singularEdgeListChain t.edges

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Scale a concrete cyclic edge-list term by an integer without changing its
underlying edge list. -/
noncomputable def CyclicSingularEdgeListTerm.zsmul
    (n : ℤ) (t : CyclicSingularEdgeListTerm) : CyclicSingularEdgeListTerm where
  edges := t.edges
  coeff := n * t.coeff
  cycle := n • t.cycle
  chain_eq := by
    rw [map_zsmul, map_zsmul, t.chain_eq]
    change n • (t.coeff • singularEdgeListChain t.edges) =
      (n * t.coeff) • singularEdgeListChain t.edges
    rw [smul_smul]
  winding_integral := by
    obtain ⟨k, hk⟩ := t.winding_integral
    refine ⟨n * k, ?_⟩
    unfold cycleWinding at hk ⊢
    rw [map_zsmul, hk]
    simp [zsmul_eq_mul]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-chain contribution of a scaled cyclic edge-list term is the scaled
free-chain contribution. -/
theorem CyclicSingularEdgeListTerm.zsmul_chain
    (n : ℤ) (t : CyclicSingularEdgeListTerm) :
    (t.zsmul n).chain = n • t.chain := by
  unfold CyclicSingularEdgeListTerm.zsmul CyclicSingularEdgeListTerm.chain
  change (n * t.coeff) • singularEdgeListChain t.edges =
    n • (t.coeff • singularEdgeListChain t.edges)
  rw [smul_smul]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free chain represented by a concrete cyclic edge-list term has zero
explicit boundary. -/
theorem CyclicSingularEdgeListTerm.boundary_chain_zero
    (t : CyclicSingularEdgeListTerm) :
    ModuleCat.Hom.hom singularOneBoundaryFree t.chain = 0 := by
  unfold CyclicSingularEdgeListTerm.chain
  rw [← t.chain_eq]
  change ModuleCat.Hom.hom
    (sphereOneSingularIntChainComplex.iCycles 1 ≫ singularOneChainToFree ≫
      singularOneBoundaryFree) t.cycle = 0
  rw [singularOneChainToFree_boundary_free]
  rw [← Category.assoc, HomologicalComplex.iCycles_d]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The all-forward conversion preserves the exact free-chain contribution of the
oriented cyclic family. -/
theorem OrientedCyclicFamilyTerm.toCyclicSingularEdgeListTerm_of_all_forward_chain
    (T : OrientedCyclicFamilyTerm)
    (hforward : ∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.forward) :
    (T.toCyclicSingularEdgeListTerm_of_all_forward hforward).chain =
      T.toDirectedCycleFreeTerm.chain := by
  unfold OrientedCyclicFamilyTerm.toCyclicSingularEdgeListTerm_of_all_forward
  unfold CyclicSingularEdgeListTerm.chain
  change (1 : ModuleCat.of ℤ ℤ) •
      singularEdgeListChain (List.ofFn (fun i : Fin T.k => (T.o i).edge)) =
    ∑ i, (T.o i).chain
  rw [singularEdgeListChain_ofFn]
  simp
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [OrientedSingularEdge.chain, hforward i]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If a concrete oriented cyclic family is everywhere backward, then it is also
a concrete cyclic edge-list term in the older one-scalar interface, with global
coefficient `-1`. -/
noncomputable def OrientedCyclicFamilyTerm.toCyclicSingularEdgeListTerm_of_all_backward
    (T : OrientedCyclicFamilyTerm)
    (hbackward : ∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.backward) :
    CyclicSingularEdgeListTerm where
  edges := List.ofFn (fun i : Fin T.k => (T.o i).edge)
  coeff := -1
  cycle := T.toDirectedCycleFreeTerm.cycle
  chain_eq := by
    rw [DirectedCycleFreeTerm.iCycles_eq_freeToChain, singularOneChainToFree_freeToChain]
    rw [singularEdgeListChain_ofFn]
    rw [neg_one_zsmul]
    change (∑ i, (T.o i).chain) =
      - (∑ i, ModuleCat.freeMk (T.o i).edge : singularOneChainFree)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [OrientedSingularEdge.chain, hbackward i]
  winding_integral := T.toDirectedCycleFreeTerm.winding_integral

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The all-backward conversion preserves the exact free-chain contribution of
the oriented cyclic family. -/
theorem OrientedCyclicFamilyTerm.toCyclicSingularEdgeListTerm_of_all_backward_chain
    (T : OrientedCyclicFamilyTerm)
    (hbackward : ∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.backward) :
    (T.toCyclicSingularEdgeListTerm_of_all_backward hbackward).chain =
      T.toDirectedCycleFreeTerm.chain := by
  unfold OrientedCyclicFamilyTerm.toCyclicSingularEdgeListTerm_of_all_backward
  unfold CyclicSingularEdgeListTerm.chain
  change (-1 : ModuleCat.of ℤ ℤ) •
      singularEdgeListChain (List.ofFn (fun i : Fin T.k => (T.o i).edge)) =
    ∑ i, (T.o i).chain
  rw [singularEdgeListChain_ofFn]
  rw [neg_one_zsmul]
  change - (∑ i, ModuleCat.freeMk (T.o i).edge : singularOneChainFree) =
    ∑ i, (T.o i).chain
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [OrientedSingularEdge.chain, hbackward i]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the global scalar of a concrete cyclic edge-list term is nonnegative, then
every raw edge coefficient in its represented free chain is nonnegative. -/
theorem CyclicSingularEdgeListTerm.edgeCoeff_chain_nonneg_of_coeff_nonneg
    [DecidableEq SingularOneSimplex]
    (t : CyclicSingularEdgeListTerm) (hcoeff : 0 ≤ t.coeff)
    (e : SingularOneSimplex) :
    0 ≤ edgeCoeff t.chain e := by
  unfold CyclicSingularEdgeListTerm.chain
  rw [edgeCoeff_zsmul]
  exact mul_nonneg hcoeff (edgeCoeff_singularEdgeListChain_nonneg t.edges e)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the global scalar of a concrete cyclic edge-list term is nonpositive, then
every raw edge coefficient in its represented free chain is nonpositive. -/
theorem CyclicSingularEdgeListTerm.edgeCoeff_chain_nonpos_of_coeff_nonpos
    [DecidableEq SingularOneSimplex]
    (t : CyclicSingularEdgeListTerm) (hcoeff : t.coeff ≤ 0)
    (e : SingularOneSimplex) :
    edgeCoeff t.chain e ≤ 0 := by
  unfold CyclicSingularEdgeListTerm.chain
  rw [edgeCoeff_zsmul]
  exact mul_nonpos_of_nonpos_of_nonneg hcoeff
    (edgeCoeff_singularEdgeListChain_nonneg t.edges e)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A concrete cyclic edge-list term cannot represent a free edge-chain with both
a positive and a negative raw edge coefficient.  This is the formal obstruction
created by the old one-scalar edge-list interface: its represented chain is
globally sign-locked by `coeff`. -/
theorem CyclicSingularEdgeListTerm.chain_ne_of_mixed_sign
    [DecidableEq SingularOneSimplex]
    (t : CyclicSingularEdgeListTerm) (c : singularOneChainFree)
    {e f : SingularOneSimplex}
    (hepos : 0 < edgeCoeff c e) (hfneg : edgeCoeff c f < 0) :
    t.chain ≠ c := by
  intro ht
  by_cases hcoeff : 0 ≤ t.coeff
  · have hf_nonneg := t.edgeCoeff_chain_nonneg_of_coeff_nonneg hcoeff f
    rw [ht] at hf_nonneg
    omega
  · have hcoeff_neg : t.coeff < 0 := lt_of_not_ge hcoeff
    have hcoeff_nonpos : t.coeff ≤ 0 := le_of_lt hcoeff_neg
    have he_nonpos := t.edgeCoeff_chain_nonpos_of_coeff_nonpos hcoeff_nonpos e
    rw [ht] at he_nonpos
    omega

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A single singular edge whose two endpoints agree is already a cyclic
edge-list term.  This closes the loop-edge subcase of the finite-flow extraction
argument: no successor search is needed when the selected supported edge is
itself closed. -/
noncomputable def cyclicSingularEdgeListTerm_of_loop
    (e : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) e =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) e)
    (n : ModuleCat.of ℤ ℤ) :
    CyclicSingularEdgeListTerm where
  edges := [e]
  coeff := n
  cycle := ModuleCat.Hom.hom (closedSingularOneCycle e hfaces) n
  chain_eq := by
    have hcomp :
        closedSingularOneCycle e hfaces ≫
          sphereOneSingularIntChainComplex.iCycles 1 ≫
          singularOneChainToFree =
        Sigma.ι (fun _ : SingularOneSimplex => ModuleCat.of ℤ ℤ) e ≫
          singularOneChainToFree := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ singularOneChainToFree)
          (closedSingularOneCycle_iCycles e hfaces)
    change ModuleCat.Hom.hom
        (closedSingularOneCycle e hfaces ≫
          sphereOneSingularIntChainComplex.iCycles 1 ≫
          singularOneChainToFree) n =
        n • singularEdgeListChain [e]
    rw [hcomp]
    rw [singularOneChainToFree_ι]
    simp [singularEdgeListChain, LinearMap.toSpanSingleton_apply]
  winding_integral := by
    obtain ⟨k, hk⟩ := singularWinding_loop_integral e hfaces
    refine ⟨n * k, ?_⟩
    rw [cycleWinding_closedSingularOneCycle, hk]
    simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A nonzero single-edge free flow with zero boundary has equal endpoints. -/
theorem singleEdgeFlow_zero_boundary_faces_eq
    (e : SingularOneSimplex) (n : ModuleCat.of ℤ ℤ)
    (hn : n ≠ 0)
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree (n • ModuleCat.freeMk e) = 0) :
    edgeTerminal e = edgeInitial e := by
  by_contra hne
  have hboundary :
      n • (ModuleCat.freeMk (edgeTerminal e) - ModuleCat.freeMk (edgeInitial e)) =
        (0 : singularZeroChainFree) := by
    rw [← hzero]
    rw [map_zsmul, singularOneBoundaryFree_freeMk]
    rfl
  have hcoeff := congrArg (fun z : singularZeroChainFree => z.toFun (edgeTerminal e)) hboundary
  change (n • (ModuleCat.freeMk (edgeTerminal e) - ModuleCat.freeMk (edgeInitial e)) :
      SingularZeroSimplex →₀ ℤ) (edgeTerminal e) = 0 at hcoeff
  have hn0 : n = 0 := by
    have hne' : edgeInitial e ≠ edgeTerminal e := fun h => hne h.symm
    rw [Finsupp.smul_apply, Finsupp.sub_apply] at hcoeff
    simpa [ModuleCat.freeMk, hne'] using hcoeff
  exact hn hn0

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If a balanced free edge-chain has singleton support, that single supported
edge is a loop.  This is the residual obstruction needed in the parallel-edge
case: a one-edge balanced residual cannot sit on a non-loop edge. -/
theorem singletonSupport_zero_boundary_faces_eq
    [DecidableEq SingularOneSimplex]
    (c : singularOneChainFree) (e : SingularOneSimplex)
    (hsupp : edgeSupport c = {e})
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0) :
    edgeTerminal e = edgeInitial e := by
  have he_mem : e ∈ edgeSupport c := by
    rw [hsupp]
    simp
  have hcoeff_ne : edgeCoeff c e ≠ 0 :=
    (mem_edgeSupport_iff c e).mp he_mem
  have hc : c = edgeCoeff c e • ModuleCat.freeMk e :=
    eq_zsmul_freeMk_of_edgeSupport_eq_single c e hsupp
  rw [hc] at hzero
  exact singleEdgeFlow_zero_boundary_faces_eq e (edgeCoeff c e) hcoeff_ne hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The two-edge parallel-flow obstruction shape: one singular edge with
coefficient `+1` and a second with coefficient `-1`. -/
noncomputable def parallelTwoEdgeFlow
    (e f : SingularOneSimplex) : singularOneChainFree :=
  ModuleCat.freeMk e - ModuleCat.freeMk f

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The positive edge in a two-edge parallel flow has coefficient `+1`. -/
theorem parallelTwoEdgeFlow_coeff_left
    [DecidableEq SingularOneSimplex]
    {e f : SingularOneSimplex} (hne : e ≠ f) :
    edgeCoeff (parallelTwoEdgeFlow e f) e = 1 := by
  unfold parallelTwoEdgeFlow
  rw [edgeCoeff_sub, edgeCoeff_freeMk_self]
  have hf : edgeCoeff (ModuleCat.freeMk f) e = 0 := by
    rw [ModuleCat.freeMk, edgeCoeff_single f (1 : ℤ) e,
      if_neg (fun h : f = e => hne h.symm)]
  rw [hf]
  norm_num

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The negative edge in a two-edge parallel flow has coefficient `-1`. -/
theorem parallelTwoEdgeFlow_coeff_right
    [DecidableEq SingularOneSimplex]
    {e f : SingularOneSimplex} (hne : e ≠ f) :
    edgeCoeff (parallelTwoEdgeFlow e f) f = -1 := by
  unfold parallelTwoEdgeFlow
  rw [edgeCoeff_sub, edgeCoeff_freeMk_self]
  have he : edgeCoeff (ModuleCat.freeMk e) f = 0 := by
    rw [ModuleCat.freeMk, edgeCoeff_single e (1 : ℤ) f]
    simp [hne]
  rw [he]
  norm_num

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If two distinct singular edges have the same endpoints, their signed
two-edge flow is balanced. -/
theorem parallelTwoEdgeFlow_boundary_zero
    {e f : SingularOneSimplex}
    (hterm : edgeTerminal e = edgeTerminal f)
    (hinit : edgeInitial e = edgeInitial f) :
    ModuleCat.Hom.hom singularOneBoundaryFree (parallelTwoEdgeFlow e f) = 0 := by
  unfold parallelTwoEdgeFlow
  rw [map_sub, singularOneBoundaryFree_freeMk, singularOneBoundaryFree_freeMk]
  change ModuleCat.freeMk (edgeTerminal e) - ModuleCat.freeMk (edgeInitial e) -
      (ModuleCat.freeMk (edgeTerminal f) - ModuleCat.freeMk (edgeInitial f)) = 0
  rw [hterm, hinit]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The support of a distinct two-edge parallel flow is exactly the two listed
edges. -/
theorem parallelTwoEdgeFlow_support
    [DecidableEq SingularOneSimplex]
    {e f : SingularOneSimplex} (hne : e ≠ f) :
    edgeSupport (parallelTwoEdgeFlow e f) = {e, f} := by
  ext x
  rw [mem_edgeSupport_iff]
  unfold parallelTwoEdgeFlow
  rw [edgeCoeff_sub]
  rw [ModuleCat.freeMk, edgeCoeff_single e (1 : ℤ) x]
  rw [ModuleCat.freeMk, edgeCoeff_single f (1 : ℤ) x]
  by_cases he : e = x
  · by_cases hf : f = x
    · subst x
      exact False.elim (hne hf.symm)
    · subst x
      simp [hf]
  · by_cases hf : f = x
    · subst x
      simp [hne]
    · have hxe : x ≠ e := fun h => he h.symm
      have hxf : x ≠ f := fun h => hf h.symm
      simp [he, hf, hxe, hxf]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A distinct two-edge parallel flow has support-cardinality two. -/
theorem parallelTwoEdgeFlow_supportCard
    [DecidableEq SingularOneSimplex]
    {e f : SingularOneSimplex} (hne : e ≠ f) :
    edgeSupportCard (parallelTwoEdgeFlow e f) = 2 := by
  change (edgeSupport (parallelTwoEdgeFlow e f)).card = 2
  rw [parallelTwoEdgeFlow_support hne]
  simp [hne]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A distinct two-edge parallel flow is nonzero. -/
theorem parallelTwoEdgeFlow_ne_zero
    [DecidableEq SingularOneSimplex]
    {e f : SingularOneSimplex} (hne : e ≠ f) :
    parallelTwoEdgeFlow e f ≠ 0 := by
  intro hzero
  have hcoeff := parallelTwoEdgeFlow_coeff_left (e := e) (f := f) hne
  rw [hzero] at hcoeff
  change edgeCoeff (0 : singularOneChainFree) e = 1 at hcoeff
  change (0 : ℤ) = 1 at hcoeff
  norm_num at hcoeff

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A distinct two-edge parallel flow lies in the large-support branch. -/
theorem parallelTwoEdgeFlow_largeSupport
    [DecidableEq SingularOneSimplex]
    {e f : SingularOneSimplex} (hne : e ≠ f) :
    1 < edgeSupportCard (parallelTwoEdgeFlow e f) := by
  rw [parallelTwoEdgeFlow_supportCard hne]
  norm_num

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A nonzero single-edge free flow with zero boundary is already a cyclic
edge-list decomposition.  This is the support-cardinality-one subcase of the
finite-flow extraction theorem. -/
theorem singleEdgeFlow_decomposesIntoCyclicEdgeLists
    (e : SingularOneSimplex) (n : ModuleCat.of ℤ ℤ)
    (hn : n ≠ 0)
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree (n • ModuleCat.freeMk e) = 0) :
    ∃ ts : List CyclicSingularEdgeListTerm,
      n • ModuleCat.freeMk e = cyclicSingularEdgeListTermListChain ts := by
  have hfaces : edgeTerminal e = edgeInitial e :=
    singleEdgeFlow_zero_boundary_faces_eq e n hn hzero
  let t := cyclicSingularEdgeListTerm_of_loop e hfaces n
  refine ⟨[t], ?_⟩
  change n • ModuleCat.freeMk e =
    t.coeff • singularEdgeListChain t.edges + cyclicSingularEdgeListTermListChain []
  simp [t, cyclicSingularEdgeListTerm_of_loop, singularEdgeListChain,
    cyclicSingularEdgeListTermListChain]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Any balanced free edge-flow with singleton support is a one-term cyclic
edge-list.  This packages the support-cardinality-one case in the native
`edgeSupport` language used by the support-decreasing induction. -/
theorem singletonSupportFlow_decomposesIntoCyclicEdgeLists
    (c : singularOneChainFree) (e : SingularOneSimplex)
    (hsupp : edgeSupport c = {e})
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0) :
    ∃ ts : List CyclicSingularEdgeListTerm,
      c = cyclicSingularEdgeListTermListChain ts := by
  have he_mem : e ∈ edgeSupport c := by
    rw [hsupp]
    simp
  have hn : edgeCoeff c e ≠ 0 := (mem_edgeSupport_iff c e).mp he_mem
  have hc_single : c = (Finsupp.single e (edgeCoeff c e) : singularOneChainFree) := by
    apply Finsupp.ext
    intro x
    by_cases hx : x = e
    · subst x
      change c.toFun e = (Finsupp.single e (c.toFun e) : singularOneChainFree) e
      rw [Finsupp.single_eq_same]
    · have hx_not_mem : x ∉ edgeSupport c := by
        rw [hsupp]
        simp [hx]
      have hcx : edgeCoeff c x = 0 := by
        exact Classical.not_not.mp (mt (mem_edgeSupport_iff c x).mpr hx_not_mem)
      unfold edgeCoeff at hcx
      change c.toFun x = (Finsupp.single e (edgeCoeff c e) : singularOneChainFree) x
      rw [hcx]
      rw [Finsupp.single_eq_of_ne hx]
  have hsmul : (Finsupp.single e (edgeCoeff c e) : singularOneChainFree) =
      edgeCoeff c e • ModuleCat.freeMk e := by
    rw [ModuleCat.freeMk]
    rw [Finsupp.smul_single]
    simp
  rw [hc_single, hsmul] at hzero ⊢
  exact singleEdgeFlow_decomposesIntoCyclicEdgeLists e (edgeCoeff c e) hn hzero

/-- A singleton cyclic-edge-list chain is its term's chain. -/
theorem cyclicSingularEdgeListTermListChain_single
    (t : CyclicSingularEdgeListTerm) :
    cyclicSingularEdgeListTermListChain [t] = t.chain := by
  simp [cyclicSingularEdgeListTermListChain, CyclicSingularEdgeListTerm.chain]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Mapping concrete cyclic edge-list terms to abstract directed-cycle terms
preserves the represented free-chain sum. -/
theorem directedCycleListChain_of_cyclicEdgeList :
    ∀ ts : List CyclicSingularEdgeListTerm,
      directedCycleFreeTermListChain (ts.map CyclicSingularEdgeListTerm.toDirectedCycleFreeTerm) =
        cyclicSingularEdgeListTermListChain ts
  | [] => by
      unfold directedCycleFreeTermListChain cyclicSingularEdgeListTermListChain
      rfl
  | t :: ts => by
      unfold directedCycleFreeTermListChain cyclicSingularEdgeListTermListChain
      change t.coeff • singularEdgeListChain t.edges +
          directedCycleFreeTermListChain (ts.map CyclicSingularEdgeListTerm.toDirectedCycleFreeTerm) =
        t.coeff • singularEdgeListChain t.edges + cyclicSingularEdgeListTermListChain ts
      rw [directedCycleListChain_of_cyclicEdgeList ts]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- More concrete remaining finite graph target: every balanced free edge-flow
decomposes into finitely many cyclic edge-list pieces. -/
def freeBoundaryKernel_decomposesIntoCyclicEdgeLists : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      ∃ ts : List CyclicSingularEdgeListTerm, c = cyclicSingularEdgeListTermListChain ts

/-- One-step extraction target for the support-decreasing proof: every nonzero
balanced free edge-flow splits into one cyclic edge-list piece plus a balanced
residual whose edge support is strictly smaller. -/
def cyclicEdgeListExtractionStep : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      c ≠ 0 →
        ∃ (t : CyclicSingularEdgeListTerm) (r : singularOneChainFree),
          c = t.chain + r ∧
            ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
              edgeSupportCard r < edgeSupportCard c

/-- A support-decreasing one-step cyclic extraction proves the full finite cyclic
edge-list decomposition by strong induction on support cardinality. -/
theorem freeBoundaryKernel_decomposesIntoCyclicEdgeLists_of_extractionStep
    (hstep : cyclicEdgeListExtractionStep) :
    freeBoundaryKernel_decomposesIntoCyclicEdgeLists := by
  intro c hc
  let P : ℕ → Prop := fun n =>
    ∀ c : singularOneChainFree,
      edgeSupportCard c = n →
        ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
          ∃ ts : List CyclicSingularEdgeListTerm, c = cyclicSingularEdgeListTermListChain ts
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcCard hcBoundary
      by_cases hzero : c = 0
      · refine ⟨[], ?_⟩
        rw [hzero]
        rfl
      · obtain ⟨t, r, hdecomp, hrBoundary, hrLt⟩ := hstep c hcBoundary hzero
        have hrLtN : edgeSupportCard r < n := by
          simpa [hcCard] using hrLt
        obtain ⟨ts, hts⟩ := ih (edgeSupportCard r) hrLtN r rfl hrBoundary
        refine ⟨t :: ts, ?_⟩
        unfold cyclicSingularEdgeListTermListChain
        rw [← hts]
        exact hdecomp
  exact hP (edgeSupportCard c) c rfl hc

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The zero free edge-flow decomposes as the empty cyclic edge-list.  This is the
base case for the support-decreasing finite-flow induction. -/
theorem zeroFlow_decomposesIntoCyclicEdgeLists :
    ∃ ts : List CyclicSingularEdgeListTerm,
      (0 : singularOneChainFree) = cyclicSingularEdgeListTermListChain ts := by
  exact ⟨[], rfl⟩

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A free edge-flow with support-cardinality zero has the empty cyclic
edge-list decomposition. -/
theorem supportCard_zero_decomposesIntoCyclicEdgeLists
    (c : singularOneChainFree) (hcard : edgeSupportCard c = 0) :
    ∃ ts : List CyclicSingularEdgeListTerm, c = cyclicSingularEdgeListTermListChain ts := by
  have hzero : c = 0 := (edgeSupportCard_eq_zero_iff c).mp hcard
  rw [hzero]
  exact zeroFlow_decomposesIntoCyclicEdgeLists

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Any balanced free edge-flow with support-cardinality at most one decomposes
into cyclic edge-list pieces.  This packages the zero and singleton support base
cases for the support-decreasing induction. -/
theorem supportCard_le_one_decomposesIntoCyclicEdgeLists
    (c : singularOneChainFree)
    (hcard : edgeSupportCard c ≤ 1)
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0) :
    ∃ ts : List CyclicSingularEdgeListTerm, c = cyclicSingularEdgeListTermListChain ts := by
  have hcases : edgeSupportCard c = 0 ∨ edgeSupportCard c = 1 := by
    omega
  rcases hcases with h0 | h1
  · exact supportCard_zero_decomposesIntoCyclicEdgeLists c h0
  · have hsupp_card : (edgeSupport c).card = 1 := h1
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hsupp_card
    exact singletonSupportFlow_decomposesIntoCyclicEdgeLists c e he hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Any nonzero balanced free edge-flow with support-cardinality at most one
admits the one-step extraction required by `cyclicEdgeListExtractionStep`. -/
theorem supportCard_le_one_extractionStep
    (c : singularOneChainFree)
    (hcard : edgeSupportCard c ≤ 1)
    (hzero : ModuleCat.Hom.hom singularOneBoundaryFree c = 0)
    (hne : c ≠ 0) :
    ∃ (t : CyclicSingularEdgeListTerm) (r : singularOneChainFree),
      c = t.chain + r ∧
        ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
          edgeSupportCard r < edgeSupportCard c := by
  have hnot0 : edgeSupportCard c ≠ 0 := by
    intro h0
    exact hne ((edgeSupportCard_eq_zero_iff c).mp h0)
  have h1 : edgeSupportCard c = 1 := by omega
  have hsupp_card : (edgeSupport c).card = 1 := h1
  obtain ⟨e, hsupp⟩ := Finset.card_eq_one.mp hsupp_card
  have he_mem : e ∈ edgeSupport c := by
    rw [hsupp]
    simp
  have hn : edgeCoeff c e ≠ 0 := (mem_edgeSupport_iff c e).mp he_mem
  have hc_single : c = (Finsupp.single e (edgeCoeff c e) : singularOneChainFree) := by
    apply Finsupp.ext
    intro x
    by_cases hx : x = e
    · subst x
      change c.toFun e = (Finsupp.single e (c.toFun e) : singularOneChainFree) e
      rw [Finsupp.single_eq_same]
    · have hx_not_mem : x ∉ edgeSupport c := by
        rw [hsupp]
        simp [hx]
      have hcx : edgeCoeff c x = 0 := by
        exact Classical.not_not.mp (mt (mem_edgeSupport_iff c x).mpr hx_not_mem)
      unfold edgeCoeff at hcx
      change c.toFun x = (Finsupp.single e (edgeCoeff c e) : singularOneChainFree) x
      rw [hcx]
      rw [Finsupp.single_eq_of_ne hx]
  have hsmul : (Finsupp.single e (edgeCoeff c e) : singularOneChainFree) =
      edgeCoeff c e • ModuleCat.freeMk e := by
    rw [ModuleCat.freeMk]
    rw [Finsupp.smul_single]
    simp
  have hzero_single :
      ModuleCat.Hom.hom singularOneBoundaryFree (edgeCoeff c e • ModuleCat.freeMk e) = 0 := by
    rw [← hsmul, ← hc_single]
    exact hzero
  have hfaces : edgeTerminal e = edgeInitial e :=
    singleEdgeFlow_zero_boundary_faces_eq e (edgeCoeff c e) hn hzero_single
  let t := cyclicSingularEdgeListTerm_of_loop e hfaces (edgeCoeff c e)
  refine ⟨t, 0, ?_, ?_, ?_⟩
  · rw [hc_single, hsmul]
    simp [CyclicSingularEdgeListTerm.chain, t, cyclicSingularEdgeListTerm_of_loop,
      singularEdgeListChain]
  · simp
  · have hzero_card : edgeSupportCard (0 : singularOneChainFree) = 0 :=
      (edgeSupportCard_eq_zero_iff (0 : singularOneChainFree)).mpr rfl
    rw [hzero_card, h1]
    norm_num

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If a loop edge is peeled off and the residual is already decomposed, then the
whole flow is decomposed.  This is the loop-edge branch needed by the future
support-decreasing extraction proof. -/
theorem loopEdge_plus_residual_decomposesIntoCyclicEdgeLists
    (e : SingularOneSimplex)
    (hfaces :
      (TopCat.toSSet.obj (TopCat.sphere 1)).δ (0 : Fin 2) e =
        (TopCat.toSSet.obj (TopCat.sphere 1)).δ (1 : Fin 2) e)
    (n : ModuleCat.of ℤ ℤ)
    (r : singularOneChainFree)
    (hres : ∃ ts : List CyclicSingularEdgeListTerm,
      r = cyclicSingularEdgeListTermListChain ts) :
    ∃ ts : List CyclicSingularEdgeListTerm,
      n • ModuleCat.freeMk e + r = cyclicSingularEdgeListTermListChain ts := by
  obtain ⟨ts, hts⟩ := hres
  let t := cyclicSingularEdgeListTerm_of_loop e hfaces n
  refine ⟨t :: ts, ?_⟩
  unfold cyclicSingularEdgeListTermListChain
  rw [← hts]
  simp [t, cyclicSingularEdgeListTerm_of_loop, singularEdgeListChain]

/-- Remaining finite-flow extraction target after the zero/singleton/loop-edge
branches are closed: a balanced nonzero flow with support-cardinality greater
than one can be split into one cyclic edge-list piece plus a balanced residual
with strictly smaller support. -/
def largeSupportCyclicEdgeListExtractionStep : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      c ≠ 0 →
        1 < edgeSupportCard c →
          ∃ (t : CyclicSingularEdgeListTerm) (r : singularOneChainFree),
            c = t.chain + r ∧
              ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
                edgeSupportCard r < edgeSupportCard c

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Stronger but cleaner large-support peel target: find a concrete cyclic
edge-list term whose chain is supported inside the current flow and exactly
cancels at least one supported edge.  The generic support lemma then supplies the
strict support-cardinality drop. -/
def largeSupportSupportedExactCyclicPeelStep : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      c ≠ 0 →
        1 < edgeSupportCard c →
          ∃ t : CyclicSingularEdgeListTerm,
            edgeSupport t.chain ⊆ edgeSupport c ∧
              ∃ e, e ∈ edgeSupport t.chain ∧ edgeCoeff t.chain e = edgeCoeff c e

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A supported exact cyclic peel proves the literal large-support extraction
target.  This packages the residual as `c - t.chain`, gets boundary-zero from the
cyclic term, and gets the strict support drop from
`edgeSupportCard_sub_lt_of_supported_exact_cancel`. -/
theorem largeSupportCyclicEdgeListExtractionStep_of_supportedExactPeel
    [DecidableEq SingularOneSimplex]
    (hpeel : largeSupportSupportedExactCyclicPeelStep) :
    largeSupportCyclicEdgeListExtractionStep := by
  intro c hbd hne hlarge
  obtain ⟨t, htsupp, hcancel⟩ := hpeel c hbd hne hlarge
  refine ⟨t, c - t.chain, ?_, ?_, ?_⟩
  · abel
  · rw [map_sub, hbd, t.boundary_chain_zero, sub_zero]
  · exact edgeSupportCard_sub_lt_of_supported_exact_cancel c t.chain htsupp hcancel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Uniform-orientation variant of the large-support extraction step.  This is the
exact extra condition needed to feed the older one-scalar cyclic-edge-list
interface from the newer oriented closed-walk extraction machinery. -/
def largeSupportUniformOrientedExtractionStep : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      c ≠ 0 →
        1 < edgeSupportCard c →
          ∃ (T : OrientedCyclicFamilyTerm) (r : singularOneChainFree),
            c = T.toDirectedCycleFreeTerm.chain + r ∧
              ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
                edgeSupportCard r < edgeSupportCard c ∧
                  ((∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.forward) ∨
                    (∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.backward))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Scaled uniform-orientation variant of the large-support extraction step.  This
matches the support-decreasing oriented theorem: the cyclic piece may need to be
multiplied by the minimum coefficient on the closed walk before support strictly
drops. -/
def largeSupportUniformOrientedScaledExtractionStep : Prop :=
  ∀ c : singularOneChainFree,
    ModuleCat.Hom.hom singularOneBoundaryFree c = 0 →
      c ≠ 0 →
        1 < edgeSupportCard c →
          ∃ (T : OrientedCyclicFamilyTerm) (m : ℤ) (r : singularOneChainFree),
            0 < m ∧
              c = m • T.toDirectedCycleFreeTerm.chain + r ∧
                ModuleCat.Hom.hom singularOneBoundaryFree r = 0 ∧
                  edgeSupportCard r < edgeSupportCard c ∧
                    ((∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.forward) ∨
                      (∀ i : Fin T.k, (T.o i).orientation = EdgeOrientation.backward))

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A scaled large-support extraction whose oriented cycle is uniformly forward
or uniformly backward proves the older concrete cyclic-edge-list extraction
target. -/
theorem largeSupportCyclicEdgeListExtractionStep_of_uniformOrientedScaled
    (huniform : largeSupportUniformOrientedScaledExtractionStep) :
    largeSupportCyclicEdgeListExtractionStep := by
  intro c hbd hne hlarge
  obtain ⟨T, m, r, _hm, hdecomp, hrbd, hrlt, hunif⟩ := huniform c hbd hne hlarge
  rcases hunif with hforward | hbackward
  · let base := T.toCyclicSingularEdgeListTerm_of_all_forward hforward
    let t := base.zsmul m
    refine ⟨t, r, ?_, hrbd, hrlt⟩
    rw [hdecomp]
    change m • T.toDirectedCycleFreeTerm.chain + r = (base.zsmul m).chain + r
    rw [CyclicSingularEdgeListTerm.zsmul_chain, T.toCyclicSingularEdgeListTerm_of_all_forward_chain hforward]
  · let base := T.toCyclicSingularEdgeListTerm_of_all_backward hbackward
    let t := base.zsmul m
    refine ⟨t, r, ?_, hrbd, hrlt⟩
    rw [hdecomp]
    change m • T.toDirectedCycleFreeTerm.chain + r = (base.zsmul m).chain + r
    rw [CyclicSingularEdgeListTerm.zsmul_chain, T.toCyclicSingularEdgeListTerm_of_all_backward_chain hbackward]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A large-support extraction whose oriented cycle is uniformly forward or
uniformly backward proves the older concrete cyclic-edge-list extraction target.
This theorem isolates the remaining finite-flow obstruction to the uniformity of
the extracted sign-selected cycle. -/
theorem largeSupportCyclicEdgeListExtractionStep_of_uniformOriented
    (huniform : largeSupportUniformOrientedExtractionStep) :
    largeSupportCyclicEdgeListExtractionStep := by
  intro c hbd hne hlarge
  obtain ⟨T, r, hdecomp, hrbd, hrlt, hunif⟩ := huniform c hbd hne hlarge
  rcases hunif with hforward | hbackward
  · let t := T.toCyclicSingularEdgeListTerm_of_all_forward hforward
    refine ⟨t, r, ?_, hrbd, hrlt⟩
    rw [hdecomp]
    rw [T.toCyclicSingularEdgeListTerm_of_all_forward_chain hforward]
  · let t := T.toCyclicSingularEdgeListTerm_of_all_backward hbackward
    refine ⟨t, r, ?_, hrbd, hrlt⟩
    rw [hdecomp]
    rw [T.toCyclicSingularEdgeListTerm_of_all_backward_chain hbackward]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The full support-decreasing extraction theorem is reduced to the genuine
remaining case: support-cardinality greater than one.  The support-cardinality
`≤ 1` cases are already closed by
`supportCard_le_one_decomposesIntoCyclicEdgeLists`; this theorem packages the
logical handoff so later work only has to prove the repeated-vertex extraction
for large support. -/
theorem cyclicEdgeListExtractionStep_of_largeSupport
    (hlarge : largeSupportCyclicEdgeListExtractionStep) :
    cyclicEdgeListExtractionStep := by
  intro c hzero hne
  by_cases hsmall : edgeSupportCard c ≤ 1
  · exact supportCard_le_one_extractionStep c hsmall hzero hne
  · have hlarge_card : 1 < edgeSupportCard c := by omega
    exact hlarge c hzero hne hlarge_card

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The full finite cyclic edge-list decomposition follows from the single
remaining large-support repeated-vertex extraction theorem. -/
theorem freeBoundaryKernel_decomposesIntoCyclicEdgeLists_of_largeSupport
    (hlarge : largeSupportCyclicEdgeListExtractionStep) :
    freeBoundaryKernel_decomposesIntoCyclicEdgeLists :=
  freeBoundaryKernel_decomposesIntoCyclicEdgeLists_of_extractionStep
    (cyclicEdgeListExtractionStep_of_largeSupport hlarge)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Concrete cyclic edge-list decomposition implies the abstract directed-cycle
decomposition target. -/
theorem freeBoundaryKernel_decomposesIntoDirectedCycles_of_cyclicEdgeLists
    (hker : freeBoundaryKernel_decomposesIntoCyclicEdgeLists) :
    freeBoundaryKernel_decomposesIntoDirectedCycles := by
  intro c hc
  obtain ⟨ts, hts⟩ := hker c hc
  refine ⟨ts.map CyclicSingularEdgeListTerm.toDirectedCycleFreeTerm, ?_⟩
  rw [directedCycleListChain_of_cyclicEdgeList ts]
  exact hts

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The concrete cyclic edge-list decomposition theorem gives integer winding for
all singular `1`-cycles. -/
theorem cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoCyclicEdgeLists
    (hker : freeBoundaryKernel_decomposesIntoCyclicEdgeLists) :
    cycleWinding_integral :=
  cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoDirectedCycles
    (freeBoundaryKernel_decomposesIntoDirectedCycles_of_cyclicEdgeLists hker)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If every cycle is a finite sum of closed singular generator cycles, then every
cycle has integer winding. -/
theorem cycleWinding_integral_of_closedSingularOneCycleList_spans
    (hspan : closedSingularOneCycleList_spans) :
    cycleWinding_integral := by
  intro z
  obtain ⟨ts, hz⟩ := hspan z
  obtain ⟨n, hn⟩ := closedSingularOneCycleList_winding_integral ts
  refine ⟨n, ?_⟩
  rw [hz, hn]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Second concrete geometric subtarget: every zero-winding singular `1`-cycle is
a singular `2`-boundary.  This is the filling theorem that should be supplied by
subdivision/prism machinery or an equivalent singular-chain construction. -/
def zeroWindingCycles_bound : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    cycleWinding z = 0 →
      ∃ b : sphereOneSingularIntChainComplex.X 2,
        z = ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If zero-winding cycles bound, every finite closed-generator list is generated
by the fundamental cycle modulo a boundary: choose the list's integer winding,
subtract that multiple of the fundamental cycle, and fill the zero-winding
residual. -/
theorem closedSingularOneCycleList_boundary_generates_of_zeroWindingCycles_bound
    (hzero : zeroWindingCycles_bound) (ts : List ClosedSingularOneCycleTerm) :
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      closedSingularOneCycleList ts =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n := by
  obtain ⟨n, _hn, hreszero⟩ := closedSingularOneCycleList_zeroWinding_residual ts
  obtain ⟨b, hb⟩ :=
    hzero (closedSingularOneCycleList ts - ModuleCat.Hom.hom fundamentalCycle n) hreszero
  exact ⟨n, b, closedSingularOneCycleList_boundary_generate_of_residual_bound ts n b hb⟩

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Closed-generator list spanning plus zero-winding filling gives the full
fundamental-cycle boundary-generation theorem.  This separates the remaining
work into a finite-support spanning theorem and the zero-winding filling theorem. -/
theorem fundamentalCycle_boundary_generates_of_closedSingularOneCycleList_spans
    (hspan : closedSingularOneCycleList_spans) (hzero : zeroWindingCycles_bound) :
    fundamentalCycle_boundary_generates := by
  intro z
  obtain ⟨ts, hz⟩ := hspan z
  obtain ⟨n, b, hts⟩ := closedSingularOneCycleList_boundary_generates_of_zeroWindingCycles_bound hzero ts
  refine ⟨n, b, ?_⟩
  rw [hz, hts]

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Local oriented-family consumer for zero-winding filling: subtract the integer
total winding multiple of the fundamental cycle, fill the zero-winding residual,
and recover the requested boundary-plus-fundamental decomposition. -/
theorem OrientedCyclicFamilyTerm.boundary_generate_of_zeroWindingCycles_bound
    (T : OrientedCyclicFamilyTerm) (hzero : zeroWindingCycles_bound) :
    ∃ (n : ModuleCat.of ℤ ℤ) (b : sphereOneSingularIntChainComplex.X 2),
      T.toDirectedCycleFreeTerm.cycle =
        ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1) b +
          ModuleCat.Hom.hom fundamentalCycle n := by
  obtain ⟨n, _hn, hreszero⟩ := T.zeroWinding_residual
  obtain ⟨b, hb⟩ :=
    hzero (T.toDirectedCycleFreeTerm.cycle - ModuleCat.Hom.hom fundamentalCycle n) hreszero
  refine ⟨n, b, ?_⟩
  rw [← hb]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Homology-level zero-winding target: every cycle with zero winding represents
the zero first-homology class.  By `cycle_eq_boundary_of_homologyπ_eq_zero`, this
is enough to produce the explicit singular `2`-boundary required by
`zeroWindingCycles_bound`. -/
def zeroWindingCycles_homologyClass_zero : Prop :=
  ∀ z : sphereOneSingularIntChainComplex.cycles 1,
    cycleWinding z = 0 →
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1) z = 0

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If zero winding kills the homology class, then zero-winding cycles bound
explicit singular `2`-chains. -/
theorem zeroWindingCycles_bound_of_homologyClass_zero
    (hzeroClass : zeroWindingCycles_homologyClass_zero) :
    zeroWindingCycles_bound := by
  intro z hz
  exact cycle_eq_boundary_of_homologyπ_eq_zero z (hzeroClass z hz)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the homology-level winding map is monic, then every zero-winding cycle has
zero homology class. -/
theorem zeroWindingCycles_homologyClass_zero_of_windingHomologyMap_mono
    (hmono : Mono windingHomologyMap) :
    zeroWindingCycles_homologyClass_zero := by
  intro z hz
  have hinj : Function.Injective (ModuleCat.Hom.hom windingHomologyMap) :=
    (ModuleCat.mono_iff_injective windingHomologyMap).mp hmono
  apply hinj
  rw [homologyπ_windingHomologyMap_apply, hz]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit zero-winding filling theorem implies the homology-class version:
boundaries die under the homology projection. -/
theorem zeroWindingCycles_homologyClass_zero_of_zeroWindingCycles_bound
    (hzero : zeroWindingCycles_bound) :
    zeroWindingCycles_homologyClass_zero := by
  intro z hz
  obtain ⟨b, hb⟩ := hzero z hz
  rw [hb]
  change ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
      sphereOneSingularIntChainComplex.homologyπ 1) b = 0
  rw [sphereOneSingularIntChainComplex.toCycles_comp_homologyπ]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The homology-class zero-winding theorem is equivalent to injectivity of the
homology-level winding map. -/
theorem windingHomologyMap_mono_of_zeroWindingCycles_homologyClass_zero
    (hzeroClass : zeroWindingCycles_homologyClass_zero) :
    Mono windingHomologyMap := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have hπsurj :
      Function.Surjective
        (ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1)) :=
    (ModuleCat.epi_iff_surjective (sphereOneSingularIntChainComplex.homologyπ 1)).mp inferInstance
  obtain ⟨zx, hzx⟩ := hπsurj x
  obtain ⟨zy, hzy⟩ := hπsurj y
  have hπdiff :
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1) (zx - zy) =
        x - y := by
    rw [map_sub, hzx, hzy]
  have hWdiff :
      ModuleCat.Hom.hom windingHomologyMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcycleZero : cycleWinding (zx - zy) = 0 := by
    rw [← homologyπ_windingHomologyMap_apply (zx - zy), hπdiff, hWdiff]
  have hhomZero :
      ModuleCat.Hom.hom (sphereOneSingularIntChainComplex.homologyπ 1) (zx - zy) = 0 :=
    hzeroClass (zx - zy) hcycleZero
  have hsub : x - y = 0 := by
    rw [← hπdiff]
    exact hhomZero
  exact sub_eq_zero.mp hsub

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The chain-level zero-winding filling theorem is equivalent to injectivity of
the homology-level winding map. -/
theorem zeroWindingCycles_bound_iff_windingHomologyMap_mono :
    zeroWindingCycles_bound ↔ Mono windingHomologyMap := by
  constructor
  · intro hzero
    exact windingHomologyMap_mono_of_zeroWindingCycles_homologyClass_zero
      (zeroWindingCycles_homologyClass_zero_of_zeroWindingCycles_bound hzero)
  · intro hmono
    exact zeroWindingCycles_bound_of_homologyClass_zero
      (zeroWindingCycles_homologyClass_zero_of_windingHomologyMap_mono hmono)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A monic homology-level winding map closes the zero-winding filling target. -/
theorem zeroWindingCycles_bound_of_windingHomologyMap_mono
    (hmono : Mono windingHomologyMap) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_homologyClass_zero
    (zeroWindingCycles_homologyClass_zero_of_windingHomologyMap_mono hmono)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Surjectivity of the fundamental class map closes the zero-winding filling
target, via injectivity of the homology-level winding map. -/
theorem zeroWindingCycles_bound_of_fundamentalHomologyClass_surjective
    (hsurj : fundamentalHomologyClass_surjective) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_windingHomologyMap_mono
    (windingHomologyMap_mono_of_fundamentalHomologyClass_surjective hsurj)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Homology-level generation by the fundamental circle class closes the
zero-winding filling target. -/
theorem zeroWindingCycles_bound_of_fundamentalCycleClass_generates
    (hgen : fundamentalCycleClass_generates) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_fundamentalHomologyClass_surjective
    (fundamentalHomologyClass_surjective_of_cycleClass_generates hgen)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- If the concrete boundary-generation theorem is supplied directly, then the
zero-winding filling theorem follows.  Indeed, write `z = ∂b + n·γ`; winding
kills `∂b` and sends the fundamental cycle `γ` to `1`, so `W(z)=0` forces
`n = 0`.  Thus `z = ∂b`.

This isolates the remaining geometric work: it is enough to prove the
circle-only chain-level generation theorem `fundamentalCycle_boundary_generates`.
-/
theorem zeroWindingCycles_bound_of_fundamentalCycle_boundary_generates
    (hgen : fundamentalCycle_boundary_generates) :
    zeroWindingCycles_bound := by
  intro z hz0
  obtain ⟨n, b, hz⟩ := hgen z
  have hboundary_winding :
      ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
          sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) b = 0 := by
    rw [HomologicalComplex.toCycles_i_assoc, windingChainMap_boundary]
    simp
  have hwind_n : cycleWinding z = (n : ℝ) := by
    rw [hz]
    unfold cycleWinding
    rw [map_add]
    change ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.toCycles 2 1 ≫
          sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) b +
        cycleWinding (ModuleCat.Hom.hom fundamentalCycle n) = (n : ℝ)
    rw [hboundary_winding, cycleWinding_fundamentalCycle]
    simp
  have hn_real : (n : ℝ) = 0 := by
    rw [← hwind_n]
    exact hz0
  have hn : n = 0 := by
    exact_mod_cast hn_real
  refine ⟨b, ?_⟩
  rw [hz, hn]
  simp

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The one-directed-cycle generation theorem closes the zero-winding filling
target. -/
theorem zeroWindingCycles_bound_of_directedCycleTerms
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hterm : directedCycleTerms_boundary_generate) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_fundamentalCycle_boundary_generates
    (fundamentalCycle_boundary_generates_of_directedCycleTerms hterm)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Filling each concrete oriented cyclic family closes the zero-winding filling
target. -/
theorem zeroWindingCycles_bound_of_orientedCyclicFamilies
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hterm : orientedCyclicFamilies_boundary_generate) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_fundamentalCycle_boundary_generates
    (fundamentalCycle_boundary_generates_of_orientedCyclicFamilies hterm)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A raw prism filling for each concrete oriented cyclic family closes the
zero-winding filling target. -/
theorem zeroWindingCycles_bound_of_rawPrism
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hraw : orientedCyclicFamilies_rawPrism_generate) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_orientedCyclicFamilies
    (orientedCyclicFamilies_boundary_generate_of_rawPrism hraw)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A fully explicit raw prism filling for each concrete oriented cyclic family
closes the zero-winding filling target. -/
theorem zeroWindingCycles_bound_of_explicitRawPrism
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hexplicit : orientedCyclicFamilies_explicitRawPrism_generate) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_rawPrism
    (orientedCyclicFamilies_rawPrism_generate_of_explicit hexplicit)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A free-coordinate prism construction closes the zero-winding filling target. -/
theorem zeroWindingCycles_bound_of_freePrism
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hfree : orientedCyclicFamilies_freePrism_generate) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_explicitRawPrism
    (orientedCyclicFamilies_explicitRawPrism_generate_of_freePrism hfree)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A raw prism filling for each concrete oriented cyclic family is enough for
the final Mathlib circle H₁ computation. -/
theorem circleH1ZIsoInt_of_rawPrism
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hraw : orientedCyclicFamilies_rawPrism_generate) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_orientedCyclicFamilies
    (orientedCyclicFamilies_boundary_generate_of_rawPrism hraw)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A fully explicit raw prism filling for each concrete oriented cyclic family
is enough for the final Mathlib circle H₁ computation. -/
theorem circleH1ZIsoInt_of_explicitRawPrism
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hexplicit : orientedCyclicFamilies_explicitRawPrism_generate) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_rawPrism
    (orientedCyclicFamilies_rawPrism_generate_of_explicit hexplicit)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- A free-coordinate prism construction is enough for the final Mathlib circle
H₁ computation. -/
theorem circleH1ZIsoInt_of_freePrism
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hfree : orientedCyclicFamilies_freePrism_generate) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_explicitRawPrism
    (orientedCyclicFamilies_explicitRawPrism_generate_of_freePrism hfree)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The path-cone residual correction target closes the zero-winding filling
theorem. -/
theorem zeroWindingCycles_bound_of_pathConeCorrection
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hcorr : orientedCyclicFamilies_pathConeCorrection_generate) :
    zeroWindingCycles_bound :=
  zeroWindingCycles_bound_of_freePrism
    (orientedCyclicFamilies_freePrism_generate_of_pathConeCorrection hcorr)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The path-cone residual correction target is enough for the full Mathlib circle
`H₁(S¹;ℤ) ≅ ℤ` computation. -/
theorem circleH1ZIsoInt_of_pathConeCorrection
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex]
    (hcorr : orientedCyclicFamilies_pathConeCorrection_generate) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_freePrism
    (orientedCyclicFamilies_freePrism_generate_of_pathConeCorrection hcorr)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Integer-valued winding together with filling of zero-winding cycles gives the
fully concrete boundary-generation statement.  For a cycle `z`, choose the
integer `n` equal to its winding, subtract `n` times the fundamental cycle, and
fill the resulting zero-winding cycle. -/
theorem fundamentalCycle_boundary_generates_of_integral_winding_of_zeroWinding_bounds
    (hint : cycleWinding_integral) (hzero : zeroWindingCycles_bound) :
    fundamentalCycle_boundary_generates := by
  intro z
  obtain ⟨n, hn⟩ := hint z
  let r : sphereOneSingularIntChainComplex.cycles 1 :=
    z - ModuleCat.Hom.hom fundamentalCycle n
  have hrw : cycleWinding r = 0 := by
    unfold r
    unfold cycleWinding at hn ⊢
    rw [map_sub]
    have hfund : ModuleCat.Hom.hom
        (sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap)
        (ModuleCat.Hom.hom fundamentalCycle n) = (n : ℝ) := by
      change ModuleCat.Hom.hom
          (fundamentalCycle ≫ sphereOneSingularIntChainComplex.iCycles 1 ≫ windingChainMap) n =
        (n : ℝ)
      rw [fundamentalCycle, HomologicalComplex.liftCycles_i_assoc]
      rw [windingChainMap_fundamental]
      simp [LinearMap.toSpanSingleton_apply]
    rw [hfund, hn]
    abel
  obtain ⟨b, hb⟩ := hzero r hrw
  refine ⟨n, b, ?_⟩
  unfold r at hb
  rw [← hb]
  abel

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- With integer-valued winding already proved, the two remaining geometric
formulations are equivalent: zero-winding cycles bound iff every cycle is a
boundary plus an integer multiple of the fundamental cycle. -/
theorem zeroWindingCycles_bound_iff_fundamentalCycle_boundary_generates :
    zeroWindingCycles_bound ↔ fundamentalCycle_boundary_generates := by
  constructor
  · intro hzero
    exact fundamentalCycle_boundary_generates_of_integral_winding_of_zeroWinding_bounds
      (by
        classical
        exact cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoDirectedCycles
          freeBoundaryKernel_decomposesIntoDirectedCycles_holds)
      hzero
  · exact zeroWindingCycles_bound_of_fundamentalCycle_boundary_generates

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Zero-winding filling implies the local oriented-family generation target:
apply the equivalent global fundamental-cycle generation theorem to the packaged
cycle of the oriented family. -/
theorem orientedCyclicFamilies_boundary_generate_of_zeroWindingCycles_bound
    (hzero : zeroWindingCycles_bound) :
    orientedCyclicFamilies_boundary_generate := by
  intro T
  exact T.boundary_generate_of_zeroWindingCycles_bound hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The explicit oriented-family local target is equivalent to zero-winding
filling.  This pins the remaining geometric work to one concrete closed-walk
filling theorem without changing the final H₁ statement. -/
theorem orientedCyclicFamilies_boundary_generate_iff_zeroWindingCycles_bound :
    orientedCyclicFamilies_boundary_generate ↔ zeroWindingCycles_bound := by
  classical
  constructor
  · intro hterm
    exact zeroWindingCycles_bound_of_orientedCyclicFamilies hterm
  · exact orientedCyclicFamilies_boundary_generate_of_zeroWindingCycles_bound

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Zero-winding filling gives the fully explicit raw-prism target. -/
theorem orientedCyclicFamilies_explicitRawPrism_generate_of_zeroWindingCycles_bound
    (hzero : zeroWindingCycles_bound) :
    orientedCyclicFamilies_explicitRawPrism_generate :=
  orientedCyclicFamilies_explicitRawPrism_generate_of_boundary_generate
    (orientedCyclicFamilies_boundary_generate_of_zeroWindingCycles_bound hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The fully explicit raw-prism target is equivalent to zero-winding filling. -/
theorem orientedCyclicFamilies_explicitRawPrism_generate_iff_zeroWindingCycles_bound
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex] :
    orientedCyclicFamilies_explicitRawPrism_generate ↔ zeroWindingCycles_bound := by
  constructor
  · intro hexplicit
    exact zeroWindingCycles_bound_of_explicitRawPrism hexplicit
  · exact orientedCyclicFamilies_explicitRawPrism_generate_of_zeroWindingCycles_bound

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The free-coordinate prism target named in the Phase 5 checklist is equivalent
to the actual zero-winding filling theorem.  This uses the raw/free `C₂`
transport, so the only remaining gap is the geometric filling construction
itself. -/
theorem orientedCyclicFamilies_freePrism_generate_iff_zeroWindingCycles_bound
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex] :
    orientedCyclicFamilies_freePrism_generate ↔ zeroWindingCycles_bound := by
  constructor
  · intro hfree
    exact
      (orientedCyclicFamilies_explicitRawPrism_generate_iff_zeroWindingCycles_bound).mp
        (orientedCyclicFamilies_explicitRawPrism_generate_of_freePrism hfree)
  · intro hzero
    exact orientedCyclicFamilies_freePrism_generate_of_explicitRawPrism
      (orientedCyclicFamilies_explicitRawPrism_generate_of_zeroWindingCycles_bound hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The packaged raw-prism target is also equivalent to zero-winding filling. -/
theorem orientedCyclicFamilies_rawPrism_generate_iff_zeroWindingCycles_bound
    [DecidableEq SingularZeroSimplex] [DecidableEq SingularOneSimplex] :
    orientedCyclicFamilies_rawPrism_generate ↔ zeroWindingCycles_bound := by
  constructor
  · intro hraw
    exact
      (orientedCyclicFamilies_explicitRawPrism_generate_iff_zeroWindingCycles_bound).mp
        (orientedCyclicFamilies_explicitRawPrism_generate_of_rawPrism hraw)
  · intro hzero
    exact orientedCyclicFamilies_rawPrism_generate_of_explicit
      (orientedCyclicFamilies_explicitRawPrism_generate_of_zeroWindingCycles_bound hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the two concrete geometric subtargets: integer
winding on cycles and filling of zero-winding cycles. -/
theorem circleH1ZIsoInt_of_integral_winding_of_zeroWinding_bounds
    (hint : cycleWinding_integral) (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_fundamentalCycle_boundary_generates
    (fundamentalCycle_boundary_generates_of_integral_winding_of_zeroWinding_bounds
      hint hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the abstract directed-cycle decomposition of
balanced free edge-flows plus filling of zero-winding cycles. -/
theorem circleH1ZIsoInt_of_directedCycles_of_zeroWinding_bounds
    (hcycles : freeBoundaryKernel_decomposesIntoDirectedCycles)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_integral_winding_of_zeroWinding_bounds
    (cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoDirectedCycles hcycles)
    hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Integer-valued winding on all singular `1`-cycles, with no finite-flow
hypothesis left.  The proof is the unconditional directed-cycle decomposition
above, supplied with classical decidable equality for the actual singular
simplices. -/
theorem cycleWinding_integral_unconditional : cycleWinding_integral := by
  classical
  exact cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoDirectedCycles
    freeBoundaryKernel_decomposesIntoDirectedCycles_holds

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure after discharging the finite-flow half
unconditionally.  The only remaining geometric input is the zero-winding filling
theorem `zeroWindingCycles_bound`. -/
theorem circleH1ZIsoInt_of_zeroWinding_bounds
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_integral_winding_of_zeroWinding_bounds
    cycleWinding_integral_unconditional hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The real finite-flow theorem plus injectivity of the homology-level winding
map computes the circle's first singular homology as `ℤ`.  This bypasses the old
one-scalar cyclic-edge-list interface: the finite-flow half is already closed by
the directed-cycle decomposition. -/
theorem circleH1ZIsoInt_of_windingHomologyMap_mono
    (hmono : Mono windingHomologyMap) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_zeroWinding_bounds
    (zeroWindingCycles_bound_of_windingHomologyMap_mono hmono)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Injectivity of the homology-level winding map is enough to build the Mathlib
circle-linking backend required by the strict T8 replacement. -/
theorem mathlibCircleLinkingBackend_of_windingHomologyMap_mono
    (hmono : Mono windingHomologyMap) :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (circleH1ZIsoInt_of_windingHomologyMap_mono hmono)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the two remaining concrete theorem obligations:
finite cyclic edge-list decomposition of balanced free edge-flows, and filling of
zero-winding cycles. -/
theorem circleH1ZIsoInt_of_cyclicEdgeLists_of_zeroWinding_bounds
    (hcycles : freeBoundaryKernel_decomposesIntoCyclicEdgeLists)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_integral_winding_of_zeroWinding_bounds
    (cycleWinding_integral_of_freeBoundaryKernel_decomposesIntoCyclicEdgeLists hcycles)
    hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the support-decreasing cyclic extraction step
and filling of zero-winding cycles. -/
theorem circleH1ZIsoInt_of_extractionStep_of_zeroWinding_bounds
    (hstep : cyclicEdgeListExtractionStep)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_cyclicEdgeLists_of_zeroWinding_bounds
    (freeBoundaryKernel_decomposesIntoCyclicEdgeLists_of_extractionStep hstep)
    hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Final Mathlib H₁ closure from the exact remaining finite-flow target and
zero-winding filling.  All zero/singleton/loop-edge extraction branches are
already closed; the only finite-flow input here is the support-cardinality `> 1`
repeated-vertex extraction theorem. -/
theorem circleH1ZIsoInt_of_largeSupport_of_zeroWinding_bounds
    (hlarge : largeSupportCyclicEdgeListExtractionStep)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_cyclicEdgeLists_of_zeroWinding_bounds
    (freeBoundaryKernel_decomposesIntoCyclicEdgeLists_of_largeSupport hlarge)
    hzero

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The same concrete cyclic-edge-list and zero-winding filling obligations also
produce the nonzero H₁ target used by the Mathlib linking backend. -/
theorem circleH1ZNonzero_of_cyclicEdgeLists_of_zeroWinding_bounds
    (hcycles : freeBoundaryKernel_decomposesIntoCyclicEdgeLists)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZNonzero :=
  MathlibCohomologyBridge.circleH1ZNonzero_of_iso_int
    (circleH1ZIsoInt_of_cyclicEdgeLists_of_zeroWinding_bounds hcycles hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Nonzero H₁ after the finite-flow half has been discharged unconditionally.
Only `zeroWindingCycles_bound` remains. -/
theorem circleH1ZNonzero_of_zeroWinding_bounds
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZNonzero :=
  MathlibCohomologyBridge.circleH1ZNonzero_of_iso_int
    (circleH1ZIsoInt_of_zeroWinding_bounds hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The support-decreasing cyclic extraction step and zero-winding filling also
produce the nonzero H₁ target used by the Mathlib linking backend. -/
theorem circleH1ZNonzero_of_extractionStep_of_zeroWinding_bounds
    (hstep : cyclicEdgeListExtractionStep)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZNonzero :=
  MathlibCohomologyBridge.circleH1ZNonzero_of_iso_int
    (circleH1ZIsoInt_of_extractionStep_of_zeroWinding_bounds hstep hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The exact two remaining targets also produce the nonzero H₁ backend target. -/
theorem circleH1ZNonzero_of_largeSupport_of_zeroWinding_bounds
    (hlarge : largeSupportCyclicEdgeListExtractionStep)
    (hzero : zeroWindingCycles_bound) :
    MathlibCohomologyBridge.circleH1ZNonzero :=
  MathlibCohomologyBridge.circleH1ZNonzero_of_iso_int
    (circleH1ZIsoInt_of_largeSupport_of_zeroWinding_bounds hlarge hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The concrete cyclic-edge-list and zero-winding filling obligations build the
Mathlib circle-linking backend required by the strict T8 replacement. -/
theorem mathlibCircleLinkingBackend_of_cyclicEdgeLists_of_zeroWinding_bounds
    (hcycles : freeBoundaryKernel_decomposesIntoCyclicEdgeLists)
    (hzero : zeroWindingCycles_bound) :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (circleH1ZIsoInt_of_cyclicEdgeLists_of_zeroWinding_bounds hcycles hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- Mathlib circle-linking backend after the finite-flow half has been discharged
unconditionally.  Only `zeroWindingCycles_bound` remains. -/
theorem mathlibCircleLinkingBackend_of_zeroWinding_bounds
    (hzero : zeroWindingCycles_bound) :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (circleH1ZIsoInt_of_zeroWinding_bounds hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The support-decreasing cyclic extraction step and zero-winding filling build
the Mathlib circle-linking backend required by the strict T8 replacement. -/
theorem mathlibCircleLinkingBackend_of_extractionStep_of_zeroWinding_bounds
    (hstep : cyclicEdgeListExtractionStep)
    (hzero : zeroWindingCycles_bound) :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (circleH1ZIsoInt_of_extractionStep_of_zeroWinding_bounds hstep hzero)

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- The exact two remaining targets build the Mathlib circle-linking backend
required by the strict T8 replacement. -/
theorem mathlibCircleLinkingBackend_of_largeSupport_of_zeroWinding_bounds
    (hlarge : largeSupportCyclicEdgeListExtractionStep)
    (hzero : zeroWindingCycles_bound) :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_of_circleH1ZIsoInt
    (circleH1ZIsoInt_of_largeSupport_of_zeroWinding_bounds hlarge hzero)

/-! ### Unconditional Phase-5 closure

The terminal-side correction (`orientedCyclicFamilies_terminalSideCorrection_generate_holds`)
and the path-base correction (`orientedCyclicFamilies_pathBaseCorrection_generate_holds`)
are both proved with no remaining hypotheses, so the free-coordinate prism target,
the zero-winding filling theorem, and the full Mathlib computation
`H₁(S¹;ℤ) ≅ ℤ` all hold unconditionally. -/

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The free-coordinate prism generation target holds unconditionally.**  Both
correction halves are closed, so every concrete oriented cyclic family bounds the
desired free-prism residual. -/
theorem orientedCyclicFamilies_freePrism_generate_holds :
    orientedCyclicFamilies_freePrism_generate :=
  orientedCyclicFamilies_freePrism_generate_of_splitCorrections
    orientedCyclicFamilies_terminalSideCorrection_generate_holds
    orientedCyclicFamilies_pathBaseCorrection_generate_holds

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **Zero-winding cycles bound, unconditionally.**  Every zero-winding singular
`1`-cycle on `S¹` is a boundary, via the unconditional free-prism construction. -/
theorem zeroWindingCycles_bound_holds : zeroWindingCycles_bound := by
  classical
  exact (orientedCyclicFamilies_freePrism_generate_iff_zeroWindingCycles_bound).mp
    orientedCyclicFamilies_freePrism_generate_holds

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **`H₁(S¹;ℤ) ≅ ℤ`, unconditionally.**  Integer-valued winding on cycles is
already closed; zero-winding filling is now closed too, so the full Mathlib
first-homology computation holds with no remaining hypotheses, axioms, or
`sorry`. -/
theorem circleH1ZIsoInt_holds : MathlibCohomologyBridge.circleH1ZIsoInt :=
  circleH1ZIsoInt_of_zeroWinding_bounds zeroWindingCycles_bound_holds

open CategoryTheory.Limits AlgebraicTopology CircleH1Computation in
/-- **The Mathlib circle-linking backend exists unconditionally**, as required by
the strict T8 dimension replacement. -/
theorem mathlibCircleLinkingBackend_holds :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend :=
  mathlibCircleLinkingBackend_of_zeroWinding_bounds zeroWindingCycles_bound_holds

end

end CircleWindingChain
end Foundation
end IndisputableMonolith
