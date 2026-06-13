import IndisputableMonolith.Geometry.FreudenthalCubeTriangulation

/-!
# Periodic Freudenthal Torus Model

This module gives the scalable target shape for an arbitrary periodic
Freudenthal tiling.  It does not enumerate a concrete `n × m × k` finite
mesh yet; instead it defines the typed periodic vertex/edge/tetrahedron
model and proves that any finite `Triangulation3D` encoding this model has
the global `IncidenceEdgeSlotPartition` needed by the nonlinear Regge
first-variation theorem.

The point is to isolate the remaining work: a finite encoder from the typed
periodic torus into `Fin nV`, `Fin nE`, `Fin nT`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace PeriodicFreudenthalTorus

open ReggeTriangulation3D
open Triangulation3DConsistency
open ReggeActionFirstVariation

noncomputable section

/-- Periodic cubic vertices. -/
abbrev Vertex (Nx Ny Nz : ℕ) := Fin Nx × Fin Ny × Fin Nz

def bit : Bool → ℕ
  | false => 0
  | true => 1

def addBit {N : ℕ} [NeZero N] (i : Fin N) (b : Bool) : Fin N :=
  ⟨(i.val + bit b) % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩

@[simp] theorem addBit_false {N : ℕ} [NeZero N] (i : Fin N) :
    addBit i false = i := by
  ext
  simp [addBit, bit, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem addBit_true_eq_mk {N : ℕ} [NeZero N] (i : Fin N) :
    addBit i true =
      ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩ := by
  rfl

@[simp] theorem addBit_false_after_true {N : ℕ} [NeZero N] (i : Fin N) :
    addBit (addBit i true) false = addBit i true := by
  simp

@[simp] theorem addBit_true_after_false {N : ℕ} [NeZero N] (i : Fin N) :
    addBit (addBit i false) true = addBit i true := by
  simp

theorem addBit_true_ne_self {N : ℕ} [NeZero N] (hN : 2 < N) (i : Fin N) :
    addBit i true ≠ i := by
  intro h
  have hval : (i.val + 1) % N = i.val := by
    simpa [addBit, bit] using congrArg Fin.val h
  have hcases : i.val + 1 < N ∨ i.val + 1 = N := by
    omega
  cases hcases with
  | inl hlt =>
      have hmod : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt
      omega
  | inr heq =>
      have hmod : (i.val + 1) % N = 0 := by
        rw [heq, Nat.mod_self]
      omega

def addBits {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (v : Vertex Nx Ny Nz) (dx dy dz : Bool) : Vertex Nx Ny Nz :=
  (addBit v.1 dx, addBit v.2.1 dy, addBit v.2.2 dz)

/-- Nonzero positive cube displacements. -/
def dispBits : Fin 7 → Bool × Bool × Bool
  | 0 => (true, false, false)
  | 1 => (false, true, false)
  | 2 => (false, false, true)
  | 3 => (true, true, false)
  | 4 => (true, false, true)
  | 5 => (false, true, true)
  | 6 => (true, true, true)

/-- Local cube vertex offsets, using binary cube labels. -/
def vertexBits : Fin 8 → Bool × Bool × Bool
  | 0 => (false, false, false)
  | 1 => (true, false, false)
  | 2 => (false, true, false)
  | 3 => (true, true, false)
  | 4 => (false, false, true)
  | 5 => (true, false, true)
  | 6 => (false, true, true)
  | 7 => (true, true, true)

def addVertexBits {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (v : Vertex Nx Ny Nz) (a : Fin 8) : Vertex Nx Ny Nz :=
  let b := vertexBits a
  addBits v b.1 b.2.1 b.2.2

theorem addBit_true_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun i : Fin N => addBit i true) := by
  intro i j h
  ext
  have hval : (i.val + 1) % N = (j.val + 1) % N := by
    simpa [addBit, bit] using congrArg Fin.val h
  have hi : i.val + 1 < N ∨ i.val + 1 = N := by
    omega
  have hj : j.val + 1 < N ∨ j.val + 1 = N := by
    omega
  cases hi with
  | inl hi_lt =>
      have himod : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hi_lt
      cases hj with
      | inl hj_lt =>
          have hjmod : (j.val + 1) % N = j.val + 1 := Nat.mod_eq_of_lt hj_lt
          omega
      | inr hj_eq =>
          have hjmod : (j.val + 1) % N = 0 := by
            rw [hj_eq, Nat.mod_self]
          omega
  | inr hi_eq =>
      have himod : (i.val + 1) % N = 0 := by
        rw [hi_eq, Nat.mod_self]
      cases hj with
      | inl hj_lt =>
          have hjmod : (j.val + 1) % N = j.val + 1 := Nat.mod_eq_of_lt hj_lt
          omega
      | inr hj_eq =>
          omega

theorem addBit_injective {N : ℕ} [NeZero N] (b : Bool) :
    Function.Injective (fun i : Fin N => addBit i b) := by
  cases b
  · intro i j h
    simpa using h
  · exact addBit_true_injective

theorem addBits_injective
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (dx dy dz : Bool) :
    Function.Injective (fun v : Vertex Nx Ny Nz => addBits v dx dy dz) := by
  intro v w h
  rcases v with ⟨vx, vy, vz⟩
  rcases w with ⟨wx, wy, wz⟩
  simp [addBits] at h ⊢
  exact ⟨addBit_injective dx h.1, addBit_injective dy h.2.1,
    addBit_injective dz h.2.2⟩

theorem addVertexBits_injective
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) :
    Function.Injective (fun v : Vertex Nx Ny Nz => addVertexBits v a) := by
  intro v w h
  unfold addVertexBits at h
  exact addBits_injective _ _ _ h

theorem addVertexBits_surjective
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) :
    Function.Surjective (fun v : Vertex Nx Ny Nz => addVertexBits v a) :=
  Finite.surjective_of_injective (addVertexBits_injective a)

theorem existsUnique_addVertexBits_eq
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) (target : Vertex Nx Ny Nz) :
    ∃! cell : Vertex Nx Ny Nz, target = addVertexBits cell a := by
  rcases addVertexBits_surjective a target with ⟨cell, hcell⟩
  refine ⟨cell, hcell.symm, ?_⟩
  intro other hother
  exact addVertexBits_injective a (hother.symm.trans hcell.symm)

/-- Summing a constant over the unique periodic cell solving a translated
base-vertex equation returns that constant. -/
theorem sum_ite_eq_of_addVertexBits
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) (target : Vertex Nx Ny Nz) (c : ℝ) :
    (∑ cell : Vertex Nx Ny Nz,
      if target = addVertexBits cell a then c else 0) = c := by
  classical
  rcases addVertexBits_surjective a target with ⟨cell0, hcell0⟩
  rw [Finset.sum_eq_single cell0]
  · simp [hcell0]
  · intro cell _ hne
    have hneq : target ≠ addVertexBits cell a := by
      intro h
      apply hne
      exact addVertexBits_injective a (h.symm.trans hcell0.symm)
    simp [hneq]
  · intro hnot
    exact (hnot (Finset.mem_univ cell0)).elim

/-- A positive-displacement periodic edge, represented by its lower/base
vertex and one of the seven positive cube displacements. -/
structure PeriodicEdge (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] where
  base : Vertex Nx Ny Nz
  disp : Fin 7
deriving DecidableEq, Fintype

/-- Endpoints of a positive-displacement periodic edge. -/
def PeriodicEdge.endpoints {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : PeriodicEdge Nx Ny Nz) : Vertex Nx Ny Nz × Vertex Nx Ny Nz :=
  let d := dispBits e.disp
  (e.base, addBits e.base d.1 d.2.1 d.2.2)

theorem PeriodicEdge.endpoints_ne
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (e : PeriodicEdge Nx Ny Nz) :
    e.endpoints.1 ≠ e.endpoints.2 := by
  cases e with
  | mk base disp =>
      fin_cases disp
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hx base.1 ((congrArg Prod.fst h).symm)
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hy base.2.1
          ((congrArg (fun v : Vertex Nx Ny Nz => v.2.1) h).symm)
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hz base.2.2
          ((congrArg (fun v : Vertex Nx Ny Nz => v.2.2) h).symm)
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hx base.1 ((congrArg Prod.fst h).symm)
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hx base.1 ((congrArg Prod.fst h).symm)
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hy base.2.1
          ((congrArg (fun v : Vertex Nx Ny Nz => v.2.1) h).symm)
      · intro h
        simp [PeriodicEdge.endpoints, dispBits, addBits] at h
        exact addBit_true_ne_self hx base.1 ((congrArg Prod.fst h).symm)

/-- Base local cube vertex for each of the 19 one-cube Freudenthal edge
representatives. -/
def cubeEdgeBase : Fin 19 → Fin 8
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 3
  | 14 => 4
  | 15 => 4
  | 16 => 4
  | 17 => 5
  | 18 => 6
  | ⟨n+19, h⟩ => absurd h (by omega)

/-- Positive displacement for each one-cube Freudenthal edge representative. -/
def cubeEdgeDisp : Fin 19 → Fin 7
  | 0 => 0  -- x
  | 1 => 1  -- y
  | 2 => 2  -- z
  | 3 => 3  -- x+y
  | 4 => 4  -- x+z
  | 5 => 5  -- y+z
  | 6 => 6  -- x+y+z
  | 7 => 1
  | 8 => 2
  | 9 => 5
  | 10 => 0
  | 11 => 2
  | 12 => 4
  | 13 => 2
  | 14 => 0
  | 15 => 1
  | 16 => 3
  | 17 => 1
  | 18 => 0
  | ⟨n+19, h⟩ => absurd h (by omega)

/-- The translated global edge of a local Freudenthal tetrahedral edge slot. -/
def localEdgeOf {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (f : Fin 6) :
    PeriodicEdge Nx Ny Nz :=
  let e := FreudenthalCubeTriangulation.localEdgeOf tet f
  { base := addVertexBits cell (cubeEdgeBase e), disp := cubeEdgeDisp e }

/-- Periodic Freudenthal tetrahedra: one of the six Freudenthal tetrahedra
inside each periodic cubic cell. -/
abbrev PeriodicTet (Nx Ny Nz : ℕ) := Vertex Nx Ny Nz × Fin 6

/-- Canonical finite index set for periodic vertices.  This is the first
concrete encoder ingredient: every periodic vertex is now indexed by a `Fin`
type of the right cardinality. -/
noncomputable def vertexFinEquiv
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    Fin (Fintype.card (Vertex Nx Ny Nz)) ≃ Vertex Nx Ny Nz :=
  (Fintype.equivFin (Vertex Nx Ny Nz)).symm

/-- Canonical finite index set for positive-displacement periodic edges. -/
noncomputable def edgeFinEquiv
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    Fin (Fintype.card (PeriodicEdge Nx Ny Nz)) ≃ PeriodicEdge Nx Ny Nz :=
  (Fintype.equivFin (PeriodicEdge Nx Ny Nz)).symm

/-- Canonical finite index set for periodic Freudenthal tetrahedra. -/
noncomputable def tetFinEquiv
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    Fin (Fintype.card (PeriodicTet Nx Ny Nz)) ≃ PeriodicTet Nx Ny Nz :=
  (Fintype.equivFin (PeriodicTet Nx Ny Nz)).symm

/-- Computable local edge-slot lookup for the canonical periodic skeleton. -/
def canonicalEdgeSlot?
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : PeriodicEdge Nx Ny Nz) (cell : Vertex Nx Ny Nz) (tet : Fin 6) :
    Option (Fin 6) :=
  if e = localEdgeOf cell tet 0 then some 0
  else if e = localEdgeOf cell tet 1 then some 1
  else if e = localEdgeOf cell tet 2 then some 2
  else if e = localEdgeOf cell tet 3 then some 3
  else if e = localEdgeOf cell tet 4 then some 4
  else if e = localEdgeOf cell tet 5 then some 5
  else none

theorem canonicalEdgeSlot_eq_some_implies
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {e : PeriodicEdge Nx Ny Nz} {cell : Vertex Nx Ny Nz}
    {tet : Fin 6} {f : Fin 6}
    (h : canonicalEdgeSlot? e cell tet = some f) :
    e = localEdgeOf cell tet f := by
  unfold canonicalEdgeSlot? at h
  split_ifs at h with h0 h1 h2 h3 h4 h5
  · cases h
    exact h0
  · cases h
    exact h1
  · cases h
    exact h2
  · cases h
    exact h3
  · cases h
    exact h4
  · cases h
    exact h5

/-- Reverse edge-slot implication, reduced to the local no-duplication theorem.
The remaining arithmetic content is proving `CanonicalPeriodicLocalEdgeNoDup`
from the side-length assumptions `Nx,Ny,Nz > 2`. -/
theorem canonicalEdgeSlot_eq_some_of_noDup
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {e : PeriodicEdge Nx Ny Nz} {cell : Vertex Nx Ny Nz}
    {tet : Fin 6} {f : Fin 6}
    (hNoDup :
      ∀ f g : Fin 6, localEdgeOf cell tet f = localEdgeOf cell tet g → f = g)
    (h : e = localEdgeOf cell tet f) :
    canonicalEdgeSlot? e cell tet = some f := by
  subst e
  unfold canonicalEdgeSlot?
  split_ifs with h0 h1 h2 h3 h4 h5
  · have hf : f = 0 := hNoDup f 0 h0
    subst f
    rfl
  · have hf : f = 1 := hNoDup f 1 h1
    subst f
    rfl
  · have hf : f = 2 := hNoDup f 2 h2
    subst f
    rfl
  · have hf : f = 3 := hNoDup f 3 h3
    subst f
    rfl
  · have hf : f = 4 := hNoDup f 4 h4
    subst f
    rfl
  · have hf : f = 5 := hNoDup f 5 h5
    subst f
    rfl
  · fin_cases f <;> simp at h0 h1 h2 h3 h4 h5

/-- Canonical endpoint map for positive-displacement periodic edges, expressed
in the finite vertex index set. -/
def canonicalEdgeVerts
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz))) :
    Fin (Fintype.card (Vertex Nx Ny Nz)) ×
      Fin (Fintype.card (Vertex Nx Ny Nz)) :=
  let edge := edgeFinEquiv Nx Ny Nz e
  let endpoints := edge.endpoints
  ((vertexFinEquiv Nx Ny Nz).symm endpoints.1,
    (vertexFinEquiv Nx Ny Nz).symm endpoints.2)

/-- Canonical tetrahedron vertex map for the six-tetrahedron Freudenthal
decomposition in every periodic cube. -/
def canonicalTetVerts
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) (k : Fin 4) :
    Fin (Fintype.card (Vertex Nx Ny Nz)) :=
  let cellTet := tetFinEquiv Nx Ny Nz τ
  let localVertex := FreudenthalCubeTriangulation.tetVerts cellTet.2 k
  (vertexFinEquiv Nx Ny Nz).symm (addVertexBits cellTet.1 localVertex)

/-- Canonical edge-in-tetrahedron lookup for the finite periodic skeleton. -/
def canonicalEdgeInTet
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz)))
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) : Option (Fin 6) :=
  let cellTet := tetFinEquiv Nx Ny Nz τ
  canonicalEdgeSlot? (edgeFinEquiv Nx Ny Nz e) cellTet.1 cellTet.2

theorem canonicalEdgeInTet_eq_some_implies
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz)))
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) {f : Fin 6}
    (h : canonicalEdgeInTet Nx Ny Nz e τ = some f) :
    edgeFinEquiv Nx Ny Nz e =
      localEdgeOf (tetFinEquiv Nx Ny Nz τ).1 (tetFinEquiv Nx Ny Nz τ).2 f := by
  unfold canonicalEdgeInTet at h
  exact canonicalEdgeSlot_eq_some_implies h

/-- Remaining wraparound/no-duplication target for turning the canonical
periodic skeleton into a full `EncodedPeriodicFreudenthalTorus`. -/
def CanonicalPeriodicLocalEdgeNoDup
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ (cell : Vertex Nx Ny Nz) (tet : Fin 6) (f g : Fin 6),
    localEdgeOf cell tet f = localEdgeOf cell tet g → f = g

theorem canonicalPeriodicLocalEdgeNoDup
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicLocalEdgeNoDup Nx Ny Nz := by
  intro cell tet f g h
  fin_cases tet <;> fin_cases f <;> fin_cases g <;>
    simp [localEdgeOf, FreudenthalCubeTriangulation.localEdgeOf,
      cubeEdgeDisp] at h ⊢

theorem canonicalEdgeInTet_iff_of_noDup
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hNoDup : CanonicalPeriodicLocalEdgeNoDup Nx Ny Nz)
    (e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz)))
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) (f : Fin 6) :
    canonicalEdgeInTet Nx Ny Nz e τ = some f ↔
      edgeFinEquiv Nx Ny Nz e =
        localEdgeOf (tetFinEquiv Nx Ny Nz τ).1 (tetFinEquiv Nx Ny Nz τ).2 f := by
  constructor
  · intro h
    exact canonicalEdgeInTet_eq_some_implies Nx Ny Nz e τ h
  · intro h
    unfold canonicalEdgeInTet
    exact canonicalEdgeSlot_eq_some_of_noDup
      (fun f g hg => hNoDup (tetFinEquiv Nx Ny Nz τ).1
        (tetFinEquiv Nx Ny Nz τ).2 f g hg)
      h

/-- Squared edge length determined only by the positive displacement class. -/
def periodicDispSqEdge : Fin 7 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3

def canonicalGlobalSqEdge
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz))) : ℝ :=
  periodicDispSqEdge ((edgeFinEquiv Nx Ny Nz e).disp)

theorem freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (cell : Vertex Nx Ny Nz) (tet f : Fin 6) :
    FreudenthalCubeTriangulation.freudenthalTet.sqEdge f =
      periodicDispSqEdge ((localEdgeOf cell tet f).disp) := by
  fin_cases tet <;> fin_cases f <;>
    simp [localEdgeOf, FreudenthalCubeTriangulation.localEdgeOf,
      FreudenthalCubeTriangulation.freudenthalTet,
      FreudenthalCubeTriangulation.freudenthalTetSqEdges,
      cubeEdgeDisp, periodicDispSqEdge]

theorem canonicalLocalSqEdge_eq_global
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz)))
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) (f : Fin 6)
    (h : canonicalEdgeInTet Nx Ny Nz e τ = some f) :
    FreudenthalCubeTriangulation.freudenthalTet.sqEdge f =
      canonicalGlobalSqEdge Nx Ny Nz e := by
  have he := canonicalEdgeInTet_eq_some_implies Nx Ny Nz e τ h
  unfold canonicalGlobalSqEdge
  rw [he]
  exact freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf
    (tetFinEquiv Nx Ny Nz τ).1 (tetFinEquiv Nx Ny Nz τ).2 f

theorem canonicalLocalEdge_complete
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hNoDup : CanonicalPeriodicLocalEdgeNoDup Nx Ny Nz)
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) (f : Fin 6) :
    ∃ e : Fin (Fintype.card (PeriodicEdge Nx Ny Nz)),
      canonicalEdgeInTet Nx Ny Nz e τ = some f := by
  let edge := localEdgeOf (tetFinEquiv Nx Ny Nz τ).1 (tetFinEquiv Nx Ny Nz τ).2 f
  refine ⟨(edgeFinEquiv Nx Ny Nz).symm edge, ?_⟩
  have hEdge :
      edgeFinEquiv Nx Ny Nz ((edgeFinEquiv Nx Ny Nz).symm edge) =
        localEdgeOf (tetFinEquiv Nx Ny Nz τ).1 (tetFinEquiv Nx Ny Nz τ).2 f := by
    simp [edge]
  exact (canonicalEdgeInTet_iff_of_noDup Nx Ny Nz hNoDup
    ((edgeFinEquiv Nx Ny Nz).symm edge) τ f).2 hEdge

/-- The concrete finite periodic Freudenthal triangulation skeleton.  This is
not yet the full encoded torus certificate because incidence consistency still
requires the wraparound no-duplication and local/global squared-edge proofs. -/
def canonicalPeriodicTriangulation
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    Triangulation3D where
  nV := Fintype.card (Vertex Nx Ny Nz)
  nE := Fintype.card (PeriodicEdge Nx Ny Nz)
  nT := Fintype.card (PeriodicTet Nx Ny Nz)
  edgeVerts := canonicalEdgeVerts Nx Ny Nz
  tetVerts := canonicalTetVerts Nx Ny Nz
  edgeInTet := canonicalEdgeInTet Nx Ny Nz
  tet := fun _ => FreudenthalCubeTriangulation.freudenthalTet

def canonicalPeriodicEdgeEquiv
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    Fin (canonicalPeriodicTriangulation Nx Ny Nz).nE ≃
      PeriodicEdge Nx Ny Nz :=
  edgeFinEquiv Nx Ny Nz

def canonicalPeriodicTetEquiv
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    Fin (canonicalPeriodicTriangulation Nx Ny Nz).nT ≃
      PeriodicTet Nx Ny Nz :=
  tetFinEquiv Nx Ny Nz

/-- Remaining endpoint-orientation condition for the canonical periodic
skeleton.  This is the modular-arithmetic part of incidence consistency:
local Freudenthal edge endpoints must match the global periodic edge endpoints
up to orientation. -/
def CanonicalPeriodicEndpointIncidence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ e τ f, canonicalEdgeInTet Nx Ny Nz e τ = some f →
    let ev := canonicalEdgeVerts Nx Ny Nz e
    let tv := ReggeRigorousFoundation.edgeVertices f
    (canonicalTetVerts Nx Ny Nz τ tv.1 = ev.1 ∧
      canonicalTetVerts Nx Ny Nz τ tv.2 = ev.2) ∨
      (canonicalTetVerts Nx Ny Nz τ tv.1 = ev.2 ∧
        canonicalTetVerts Nx Ny Nz τ tv.2 = ev.1)

theorem localEdgeOf_endpoints_match_tetVerts
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (cell : Vertex Nx Ny Nz) (tet f : Fin 6) :
      let edge := localEdgeOf cell tet f
      let ev := edge.endpoints
      let tv := ReggeRigorousFoundation.edgeVertices f
      (addVertexBits cell (FreudenthalCubeTriangulation.tetVerts tet tv.1) = ev.1 ∧
        addVertexBits cell (FreudenthalCubeTriangulation.tetVerts tet tv.2) = ev.2) ∨
        (addVertexBits cell (FreudenthalCubeTriangulation.tetVerts tet tv.1) = ev.2 ∧
          addVertexBits cell (FreudenthalCubeTriangulation.tetVerts tet tv.2) = ev.1) := by
  fin_cases tet <;> fin_cases f <;>
    simp [localEdgeOf, PeriodicEdge.endpoints,
      FreudenthalCubeTriangulation.localEdgeOf,
      FreudenthalCubeTriangulation.tetVerts,
      ReggeRigorousFoundation.edgeVertices,
      cubeEdgeBase, cubeEdgeDisp, dispBits, vertexBits, addVertexBits, addBits]

theorem canonicalPeriodicEndpointIncidence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicEndpointIncidence Nx Ny Nz := by
  intro e τ f h
  have he := canonicalEdgeInTet_eq_some_implies Nx Ny Nz e τ h
  let cell := (tetFinEquiv Nx Ny Nz τ).1
  let tet := (tetFinEquiv Nx Ny Nz τ).2
  have hlocal := localEdgeOf_endpoints_match_tetVerts (Nx := Nx) (Ny := Ny) (Nz := Nz)
    cell tet f
  dsimp [CanonicalPeriodicEndpointIncidence, canonicalEdgeVerts, canonicalTetVerts]
  rw [he]
  rcases hlocal with hdir | hrev
  · left
    constructor
    · exact congrArg (vertexFinEquiv Nx Ny Nz).symm hdir.1
    · exact congrArg (vertexFinEquiv Nx Ny Nz).symm hdir.2
  · right
    constructor
    · exact congrArg (vertexFinEquiv Nx Ny Nz).symm hrev.1
    · exact congrArg (vertexFinEquiv Nx Ny Nz).symm hrev.2

def canonicalPeriodicIncidenceConsistent_of_endpoint
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hEndpoint : CanonicalPeriodicEndpointIncidence Nx Ny Nz) :
    IncidenceConsistent (canonicalPeriodicTriangulation Nx Ny Nz) where
  globalSqEdge := canonicalGlobalSqEdge Nx Ny Nz
  edgeInTet_vertices := by
    intro e τ f h
    exact hEndpoint e τ f h
  local_sqEdge_eq_global := by
    intro e τ f h
    exact canonicalLocalSqEdge_eq_global Nx Ny Nz e τ f h
  localEdge_complete := by
    intro τ f
    exact canonicalLocalEdge_complete Nx Ny Nz
      (canonicalPeriodicLocalEdgeNoDup Nx Ny Nz) τ f
  local_schlaefli := by
    intro τ
    exact SchlaefliTetrahedronProof.schlaefliTetrahedronClosedForm
      FreudenthalCubeTriangulation.freudenthalTet

def canonicalPeriodicIncidenceConsistent
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    IncidenceConsistent (canonicalPeriodicTriangulation Nx Ny Nz) :=
  canonicalPeriodicIncidenceConsistent_of_endpoint Nx Ny Nz
    (canonicalPeriodicEndpointIncidence Nx Ny Nz)

/-- A finite `Triangulation3D` encoding of the typed periodic Freudenthal
torus.  The side-length hypotheses rule out degenerate `+1 = -1`
wraparound identifications; the actual finite encoder supplies equivalences
from `Fin` indices to typed cells and positive-displacement edges. -/
structure EncodedPeriodicFreudenthalTorus
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] where
  side_x_gt_two : 2 < Nx
  side_y_gt_two : 2 < Ny
  side_z_gt_two : 2 < Nz
  K : Triangulation3D
  hK : IncidenceConsistent K
  tetEquiv : Fin K.nT ≃ (Vertex Nx Ny Nz × Fin 6)
  edgeEquiv : Fin K.nE ≃ PeriodicEdge Nx Ny Nz
  edgeInTet_iff :
    ∀ e τ f,
      K.edgeInTet e τ = some f ↔
        edgeEquiv e =
          localEdgeOf (tetEquiv τ).1 (tetEquiv τ).2 f

def canonicalEncodedPeriodicFreudenthalTorus_of_incidence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hK : IncidenceConsistent (canonicalPeriodicTriangulation Nx Ny Nz))
    (hNoDup : CanonicalPeriodicLocalEdgeNoDup Nx Ny Nz) :
    EncodedPeriodicFreudenthalTorus Nx Ny Nz where
  side_x_gt_two := hx
  side_y_gt_two := hy
  side_z_gt_two := hz
  K := canonicalPeriodicTriangulation Nx Ny Nz
  hK := hK
  tetEquiv := canonicalPeriodicTetEquiv Nx Ny Nz
  edgeEquiv := canonicalPeriodicEdgeEquiv Nx Ny Nz
  edgeInTet_iff := by
    intro e τ f
    exact canonicalEdgeInTet_iff_of_noDup Nx Ny Nz hNoDup e τ f

def canonicalEncodedPeriodicFreudenthalTorus_of_endpoint
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hEndpoint : CanonicalPeriodicEndpointIncidence Nx Ny Nz) :
    EncodedPeriodicFreudenthalTorus Nx Ny Nz :=
  canonicalEncodedPeriodicFreudenthalTorus_of_incidence Nx Ny Nz hx hy hz
    (canonicalPeriodicIncidenceConsistent_of_endpoint Nx Ny Nz hEndpoint)
    (canonicalPeriodicLocalEdgeNoDup Nx Ny Nz)

def canonicalEncodedPeriodicFreudenthalTorus
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    EncodedPeriodicFreudenthalTorus Nx Ny Nz :=
  canonicalEncodedPeriodicFreudenthalTorus_of_endpoint Nx Ny Nz hx hy hz
    (canonicalPeriodicEndpointIncidence Nx Ny Nz)

theorem canonicalEncodedPeriodic_K_tetVerts_eq
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz))) (k : Fin 4) :
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.tetVerts τ k =
      canonicalTetVerts Nx Ny Nz τ k := by
  dsimp [canonicalEncodedPeriodicFreudenthalTorus, canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence, canonicalPeriodicTriangulation]

theorem canonicalEncodedPeriodic_tetEquiv_eq
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).tetEquiv =
      canonicalPeriodicTetEquiv Nx Ny Nz := by
  dsimp [canonicalEncodedPeriodicFreudenthalTorus, canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence, canonicalPeriodicTetEquiv]

theorem canonicalEncodedPeriodic_tetVerts_addVertexBits
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (v : Fin 4) :
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.tetVerts
        ((canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).tetEquiv.symm (cell, tet)) v =
      (vertexFinEquiv Nx Ny Nz).symm
        (addVertexBits cell (FreudenthalCubeTriangulation.tetVerts tet v)) := by
  rw [canonicalEncodedPeriodic_tetEquiv_eq, canonicalEncodedPeriodic_K_tetVerts_eq]
  dsimp only [canonicalTetVerts, canonicalPeriodicTetEquiv]
  generalize hdef : (tetFinEquiv Nx Ny Nz) ((tetFinEquiv Nx Ny Nz).symm (cell, tet)) = cellTet
  have hcellTet : cellTet = (cell, tet) :=
    hdef.symm.trans ((tetFinEquiv Nx Ny Nz).apply_symm_apply (cell, tet))
  rw [hcellTet]

def edgeSlotPartition_of_encodedPeriodicFreudenthalTorus
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    IncidenceEdgeSlotPartition P.K P.hK where
  localEdgeOf := fun τ f =>
    P.edgeEquiv.symm (localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f)
  edgeInTet_iff := by
    intro e τ f
    constructor
    · intro h
      apply P.edgeEquiv.injective
      simpa using (P.edgeInTet_iff e τ f).1 h
    · intro h
      apply (P.edgeInTet_iff e τ f).2
      rw [h]
      simp

def edgeSlotBookkeeping_of_encodedPeriodicFreudenthalTorus
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    IncidenceEdgeSlotBookkeeping P.K P.hK :=
  incidenceEdgeSlotBookkeeping_of_partition P.K P.hK
    (edgeSlotPartition_of_encodedPeriodicFreudenthalTorus P)

end

end PeriodicFreudenthalTorus
end Geometry
end IndisputableMonolith
