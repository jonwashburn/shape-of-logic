import IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure
import IndisputableMonolith.Geometry.PeriodicFreudenthalTorus

/-!
# Seven Gaps, Phase 2b lane O: path-sum probes C3 and C6

## Status: PROBES ONLY (provenance record + landmine check).

This module is NON-flag-bearing.  It makes NO claim about measures, limits,
continuum behavior, or the value of any path sum.  It records two cheap
honest facts connecting the canonical periodic Freudenthal torus
(`Geometry.PeriodicFreudenthalTorus`) to the scoped path-sum state space
(`PathSumMeasure.BoundedComplex`):

**PROBE C3 (diagonal embedding; provenance framing ONLY).**
`freudenthalBoundedComplex N` packages the canonical periodic Freudenthal
torus at side `N` (any `N ≥ 1`, via `[NeZero N]`) as an element of
`BoundedComplex (7 * N ^ 3)`.  This ATTACHES the torus to the path-sum
state space and claims nothing about measures or limits.
* PRESERVED: the vertex/edge/tet counts (`nV = N ^ 3`, `nE = 7 * N ^ 3`,
  `nT = 6 * N ^ 3`, proved), the edge-endpoint incidence map `edgeVerts`,
  and the tetrahedron-corner incidence map `tetVerts`, all definitionally
  equal to the corresponding fields of `canonicalPeriodicTriangulation N N N`
  (`freudenthalBoundedComplex_matches_canonical`).
* DROPPED (incidence-shape mismatch, recorded honestly): `BoundedComplex`
  carries no `edgeInTet` field, so the edge-slot-in-tetrahedron assignment
  of `Triangulation3D` is lost; it carries no per-tetrahedron metric field,
  so the `tet` squared-edge geometry is lost (the scoped class is
  equilateral-at-fixed-scale by MODEL convention); neither shape carries a
  2-face (triangle) list.  Simpliciality of the image
  (`IsSimplicial (freudenthalBoundedComplex N)`) is NOT proved here and is
  not claimed.

**PROBE C6 (Aut vacuity landmine check).  Outcome: branch (a), the
translations EMBED.**
The translation group `Z_N^3` (the additive group `Vertex N N N`
`= Fin N × Fin N × Fin N` under componentwise mod-`N` addition) embeds into
the relabeling automorphisms of the torus image:
`translationAut N : Vertex N N N → Aut (freudenthalBoundedComplex N)` is
injective (`translationAut_injective`), sends `0` to the identity
relabeling (`translationAut_zero`), and sends sums to composites
(`translationAut_add`).  Consequences (each proved below):
* `autCard_ge_translations` : `N ^ 3 ≤ |Aut(T_N)|`;
* `mu_freudenthal_le_inv_cube` : `μ(T_N) ≤ 1 / N ^ 3`;
* `unnormalized_torus_weight_suppressed` : the μ-weighted unitary torus
  summand has modulus `≤ 1 / N ^ 3` for ANY action.

LANDMINE RECORD (panel-mandated): because the translations embed, every
future-wave claim of the form "the unnormalized contribution
`μ(T_N) · exp(i·S(T_N))` is nonvanishing / dominant" MUST be rejected as
potentially `0 = 0` unless it explicitly accounts for the
`1/|Aut| ≤ N⁻³` suppression.  The boolean outcome is recorded either way in
`pathSumProbesStatus` (`translations_embed := true`,
`unnormalized_mu_torus_claims_admissible := false`, both rfl-forced).

## Proof notes (honesty disclosure)
* Zero `sorry`, zero `admit`, zero new axioms, zero `native_decide`.
* `decide` is used EXACTLY ONCE, for the concrete finite inequality
  `(1, 0, 0) ≠ 0` in `Fin 3 × Fin 3 × Fin 3` (the nontriviality witness at
  the concrete side `N = 3`, `nontrivial_aut_three`).  Everything else is
  symbolic (general `N` with `[NeZero N]`).
* No `True` shells; all status flags are rfl-forced.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace PathSumProbes

open PathSumMeasure
open Geometry.PeriodicFreudenthalTorus

/-! ## §1. Cardinalities of the canonical periodic torus index types -/

/-- The periodic vertex set at side `N` has `N ^ 3` elements. -/
theorem card_vertex (N : ℕ) : Fintype.card (Vertex N N N) = N ^ 3 := by
  have h : Fintype.card (Fin N × Fin N × Fin N) = N ^ 3 := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    ring
  exact h

/-- A positive-displacement periodic edge is exactly a (base vertex,
displacement class) pair. -/
def periodicEdgeEquivProd (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    PeriodicEdge Nx Ny Nz ≃ Vertex Nx Ny Nz × Fin 7 where
  toFun e := (e.base, e.disp)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The periodic edge set at side `N` has `7 * N ^ 3` elements. -/
theorem card_periodicEdge (N : ℕ) [NeZero N] :
    Fintype.card (PeriodicEdge N N N) = 7 * N ^ 3 := by
  rw [Fintype.card_congr (periodicEdgeEquivProd N N N), Fintype.card_prod,
    card_vertex, Fintype.card_fin]
  ring

/-- The periodic tetrahedron set at side `N` has `6 * N ^ 3` elements. -/
theorem card_periodicTet (N : ℕ) : Fintype.card (PeriodicTet N N N) = 6 * N ^ 3 := by
  have h : Fintype.card (Vertex N N N × Fin 6) = 6 * N ^ 3 := by
    rw [Fintype.card_prod, card_vertex, Fintype.card_fin]
    ring
  exact h

/-! ## §2. PROBE C3: the torus as an element of the path-sum state space

Provenance framing ONLY: this attaches the canonical torus to the scoped
configuration class `BoundedComplex (7 * N ^ 3)`; it claims nothing about
measures or limits.  See the module docstring for the exact preserved /
dropped data. -/

/-- **PROBE C3.**  The canonical periodic Freudenthal torus at side `N` as
an element of the path-sum state space at cap `B = 7 * N ^ 3`.  Counts and
both incidence maps are inherited verbatim from
`canonicalPeriodicTriangulation N N N`; the `edgeInTet` slot assignment and
the per-tet metric are dropped (shape mismatch, recorded in the module
docstring and `pathSumProbesStatus`). -/
noncomputable def freudenthalBoundedComplex (N : ℕ) [NeZero N] :
    BoundedComplex (7 * N ^ 3) where
  nV := Fintype.card (Vertex N N N)
  nE := Fintype.card (PeriodicEdge N N N)
  nT := Fintype.card (PeriodicTet N N N)
  hV := by
    rw [card_vertex]
    calc N ^ 3 = 1 * N ^ 3 := (one_mul _).symm
      _ ≤ 7 * N ^ 3 := Nat.mul_le_mul (by norm_num) (le_refl _)
  hE := le_of_eq (card_periodicEdge N)
  hT := by
    rw [card_periodicTet]
    exact Nat.mul_le_mul (by norm_num) (le_refl _)
  edgeVerts := canonicalEdgeVerts N N N
  tetVerts := canonicalTetVerts N N N

/-- Vertex count of the embedded torus: `N ^ 3`. -/
theorem freudenthalBoundedComplex_nV (N : ℕ) [NeZero N] :
    (freudenthalBoundedComplex N).nV = N ^ 3 := card_vertex N

/-- Edge count of the embedded torus: `7 * N ^ 3` (the cap is met exactly). -/
theorem freudenthalBoundedComplex_nE (N : ℕ) [NeZero N] :
    (freudenthalBoundedComplex N).nE = 7 * N ^ 3 := card_periodicEdge N

/-- Tetrahedron count of the embedded torus: `6 * N ^ 3`. -/
theorem freudenthalBoundedComplex_nT (N : ℕ) [NeZero N] :
    (freudenthalBoundedComplex N).nT = 6 * N ^ 3 := card_periodicTet N

/-- The embedded torus is not the empty configuration: it has tetrahedra. -/
theorem freudenthalBoundedComplex_nT_pos (N : ℕ) [NeZero N] :
    0 < (freudenthalBoundedComplex N).nT := by
  rw [freudenthalBoundedComplex_nT]
  have hN : 0 < N := Nat.pos_of_neZero N
  have h3 : 0 < N ^ 3 := pow_pos hN 3
  omega

/-- Edge-endpoint incidence is inherited verbatim from the canonical
encoder. -/
theorem freudenthalBoundedComplex_edgeVerts (N : ℕ) [NeZero N] :
    (freudenthalBoundedComplex N).edgeVerts = canonicalEdgeVerts N N N := rfl

/-- Tetrahedron-corner incidence is inherited verbatim from the canonical
encoder. -/
theorem freudenthalBoundedComplex_tetVerts (N : ℕ) [NeZero N] :
    (freudenthalBoundedComplex N).tetVerts = canonicalTetVerts N N N := rfl

/-- **PROBE C3 provenance record.**  All five fields shared by the two
incidence shapes (`nV`, `nE`, `nT`, `edgeVerts`, `tetVerts`) agree
definitionally with `canonicalPeriodicTriangulation N N N`.  What is NOT
carried over (because `BoundedComplex` has no such fields) is the
`edgeInTet` slot map and the per-tet metric; see the module docstring. -/
theorem freudenthalBoundedComplex_matches_canonical (N : ℕ) [NeZero N] :
    (freudenthalBoundedComplex N).nV =
        (canonicalPeriodicTriangulation N N N).nV ∧
    (freudenthalBoundedComplex N).nE =
        (canonicalPeriodicTriangulation N N N).nE ∧
    (freudenthalBoundedComplex N).nT =
        (canonicalPeriodicTriangulation N N N).nT ∧
    (freudenthalBoundedComplex N).edgeVerts =
        (canonicalPeriodicTriangulation N N N).edgeVerts ∧
    (freudenthalBoundedComplex N).tetVerts =
        (canonicalPeriodicTriangulation N N N).tetVerts :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §3. Translation machinery

The additive group `Vertex N N N = Fin N × Fin N × Fin N` (componentwise
`Fin` addition mod `N`) acts on vertices, positive-displacement edges, and
tetrahedra by translating the base point and fixing the displacement /
local-tet data.  The key arithmetic fact is that translation commutes with
the `addBit`/`addBits`/`addVertexBits` offset maps of the Freudenthal
encoding. -/

/-- Translation by `t` on periodic vertices. -/
def translateVertex {N : ℕ} [NeZero N] (t : Vertex N N N) :
    Vertex N N N ≃ Vertex N N N where
  toFun v := v + t
  invFun v := v - t
  left_inv v := by
    show v + t - t = v
    rw [add_sub_assoc, sub_self, add_zero]
  right_inv v := by
    show v - t + t = v
    rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

@[simp] theorem translateVertex_apply {N : ℕ} [NeZero N] (t v : Vertex N N N) :
    translateVertex t v = v + t := rfl

/-- Translation by `t` on positive-displacement periodic edges (translate
the base, keep the displacement class). -/
def translateEdge {N : ℕ} [NeZero N] (t : Vertex N N N) :
    PeriodicEdge N N N ≃ PeriodicEdge N N N :=
  (periodicEdgeEquivProd N N N).trans
    ((Equiv.prodCongr (translateVertex t) (Equiv.refl (Fin 7))).trans
      (periodicEdgeEquivProd N N N).symm)

@[simp] theorem translateEdge_apply {N : ℕ} [NeZero N] (t : Vertex N N N)
    (e : PeriodicEdge N N N) :
    translateEdge t e = ⟨e.base + t, e.disp⟩ := rfl

/-- Translation by `t` on periodic tetrahedra (translate the cell, keep the
local Freudenthal tet index). -/
def translateTet {N : ℕ} [NeZero N] (t : Vertex N N N) :
    PeriodicTet N N N ≃ PeriodicTet N N N :=
  Equiv.prodCongr (translateVertex t) (Equiv.refl (Fin 6))

@[simp] theorem translateTet_apply {N : ℕ} [NeZero N] (t : Vertex N N N)
    (p : PeriodicTet N N N) :
    translateTet t p = (p.1 + t, p.2) := rfl

/-- `addBit` commutes with translation on a `Fin N` coordinate. -/
theorem addBit_add_right {N : ℕ} [NeZero N] (i s : Fin N) (b : Bool) :
    addBit (i + s) b = addBit i b + s := by
  ext
  simp only [Geometry.PeriodicFreudenthalTorus.addBit, Fin.add_def,
    Nat.mod_add_mod]
  rw [add_right_comm]

/-- `addBits` commutes with translation on periodic vertices. -/
theorem addBits_add_right {N : ℕ} [NeZero N] (v t : Vertex N N N)
    (dx dy dz : Bool) :
    addBits (v + t) dx dy dz = addBits v dx dy dz + t := by
  have h1 : (v + t).1 = v.1 + t.1 := rfl
  have h2 : (v + t).2.1 = v.2.1 + t.2.1 := rfl
  have h3 : (v + t).2.2 = v.2.2 + t.2.2 := rfl
  unfold Geometry.PeriodicFreudenthalTorus.addBits
  rw [h1, h2, h3, addBit_add_right, addBit_add_right, addBit_add_right]
  rfl

/-- `addVertexBits` (the local cube-corner offset) commutes with
translation. -/
theorem addVertexBits_add_right {N : ℕ} [NeZero N] (v t : Vertex N N N)
    (a : Fin 8) :
    addVertexBits (v + t) a = addVertexBits v a + t := by
  unfold Geometry.PeriodicFreudenthalTorus.addVertexBits
  exact addBits_add_right v t _ _ _

/-- Translating an edge translates both endpoints. -/
theorem translateEdge_endpoints {N : ℕ} [NeZero N] (t : Vertex N N N)
    (e : PeriodicEdge N N N) :
    (translateEdge t e).endpoints = (e.endpoints.1 + t, e.endpoints.2 + t) := by
  show (e.base + t,
      addBits (e.base + t) (dispBits e.disp).1 (dispBits e.disp).2.1
        (dispBits e.disp).2.2) =
    (e.base + t,
      addBits e.base (dispBits e.disp).1 (dispBits e.disp).2.1
        (dispBits e.disp).2.2 + t)
  rw [addBits_add_right]

/-- Translation by `0` is the identity on vertices. -/
theorem translateVertex_zero {N : ℕ} [NeZero N] :
    translateVertex (0 : Vertex N N N) = Equiv.refl _ := by
  apply Equiv.ext
  intro v
  show v + 0 = v
  rw [add_zero]

/-- Translation by `0` is the identity on edges. -/
theorem translateEdge_zero {N : ℕ} [NeZero N] :
    translateEdge (0 : Vertex N N N) = Equiv.refl _ := by
  apply Equiv.ext
  intro e
  show (⟨e.base + 0, e.disp⟩ : PeriodicEdge N N N) = e
  rw [add_zero]

/-- Translation by `0` is the identity on tetrahedra. -/
theorem translateTet_zero {N : ℕ} [NeZero N] :
    translateTet (0 : Vertex N N N) = Equiv.refl _ := by
  apply Equiv.ext
  intro p
  show (p.1 + 0, p.2) = p
  rw [add_zero]

/-- Translations compose on vertices. -/
theorem translateVertex_trans {N : ℕ} [NeZero N] (t s : Vertex N N N) :
    (translateVertex t).trans (translateVertex s) = translateVertex (t + s) := by
  apply Equiv.ext
  intro v
  show v + t + s = v + (t + s)
  rw [add_assoc]

/-- Translations compose on edges. -/
theorem translateEdge_trans {N : ℕ} [NeZero N] (t s : Vertex N N N) :
    (translateEdge t).trans (translateEdge s) = translateEdge (t + s) := by
  apply Equiv.ext
  intro e
  show (⟨e.base + t + s, e.disp⟩ : PeriodicEdge N N N) = ⟨e.base + (t + s), e.disp⟩
  rw [add_assoc]

/-- Translations compose on tetrahedra. -/
theorem translateTet_trans {N : ℕ} [NeZero N] (t s : Vertex N N N) :
    (translateTet t).trans (translateTet s) = translateTet (t + s) := by
  apply Equiv.ext
  intro p
  show (p.1 + t + s, p.2) = (p.1 + (t + s), p.2)
  rw [add_assoc]

/-! ### Conjugation through an indexing equivalence -/

/-- Conjugating the identity through an indexing equivalence gives the
identity. -/
theorem conj_refl {α β : Type*} (E : α ≃ β) :
    E.trans ((Equiv.refl β).trans E.symm) = Equiv.refl α := by
  apply Equiv.ext
  intro x
  show E.symm (E x) = x
  rw [Equiv.symm_apply_apply]

/-- Conjugation through an indexing equivalence preserves composition. -/
theorem conj_trans {α β : Type*} (E : α ≃ β) (σ τ : β ≃ β) :
    (E.trans (σ.trans E.symm)).trans (E.trans (τ.trans E.symm)) =
      E.trans ((σ.trans τ).trans E.symm) := by
  apply Equiv.ext
  intro x
  show E.symm (τ (E (E.symm (σ (E x))))) = E.symm (τ (σ (E x)))
  rw [Equiv.apply_symm_apply]

/-! ## §4. PROBE C6: translations embed into the relabeling automorphisms -/

/-- **PROBE C6, branch (a).**  Translation by `t ∈ Z_N^3` as a relabeling
automorphism of the embedded torus: conjugate the typed translation through
the canonical `Fin`-indexings.  Both commutation fields are proved from the
`addBits`-translation compatibility; no finite enumeration is used. -/
noncomputable def translationAut (N : ℕ) [NeZero N] (t : Vertex N N N) :
    Aut (freudenthalBoundedComplex N) where
  vEquiv := (vertexFinEquiv N N N).trans
    ((translateVertex t).trans (vertexFinEquiv N N N).symm)
  eEquiv := (edgeFinEquiv N N N).trans
    ((translateEdge t).trans (edgeFinEquiv N N N).symm)
  tEquiv := (tetFinEquiv N N N).trans
    ((translateTet t).trans (tetFinEquiv N N N).symm)
  edge_comm := by
    intro e
    show ((vertexFinEquiv N N N).symm
        ((edgeFinEquiv N N N) ((edgeFinEquiv N N N).symm
          (translateEdge t ((edgeFinEquiv N N N) e)))).endpoints.1,
      (vertexFinEquiv N N N).symm
        ((edgeFinEquiv N N N) ((edgeFinEquiv N N N).symm
          (translateEdge t ((edgeFinEquiv N N N) e)))).endpoints.2) =
      ((vertexFinEquiv N N N).symm (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm
          ((edgeFinEquiv N N N) e).endpoints.1))),
      (vertexFinEquiv N N N).symm (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm
          ((edgeFinEquiv N N N) e).endpoints.2))))
    rw [Equiv.apply_symm_apply (edgeFinEquiv N N N), translateEdge_endpoints]
    show ((vertexFinEquiv N N N).symm
        (((edgeFinEquiv N N N) e).endpoints.1 + t),
      (vertexFinEquiv N N N).symm
        (((edgeFinEquiv N N N) e).endpoints.2 + t)) =
      ((vertexFinEquiv N N N).symm (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm
          ((edgeFinEquiv N N N) e).endpoints.1))),
      (vertexFinEquiv N N N).symm (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm
          ((edgeFinEquiv N N N) e).endpoints.2))))
    rw [Equiv.apply_symm_apply (vertexFinEquiv N N N),
      Equiv.apply_symm_apply (vertexFinEquiv N N N),
      translateVertex_apply, translateVertex_apply]
  tet_comm := by
    intro τ i
    show (vertexFinEquiv N N N).symm (addVertexBits
        ((tetFinEquiv N N N) ((tetFinEquiv N N N).symm
          (translateTet t ((tetFinEquiv N N N) τ)))).1
        (Geometry.FreudenthalCubeTriangulation.tetVerts
          ((tetFinEquiv N N N) ((tetFinEquiv N N N).symm
            (translateTet t ((tetFinEquiv N N N) τ)))).2 i)) =
      (vertexFinEquiv N N N).symm (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm (addVertexBits ((tetFinEquiv N N N) τ).1
          (Geometry.FreudenthalCubeTriangulation.tetVerts
            ((tetFinEquiv N N N) τ).2 i)))))
    rw [Equiv.apply_symm_apply (tetFinEquiv N N N)]
    show (vertexFinEquiv N N N).symm
        (addVertexBits (((tetFinEquiv N N N) τ).1 + t)
          (Geometry.FreudenthalCubeTriangulation.tetVerts
            ((tetFinEquiv N N N) τ).2 i)) =
      (vertexFinEquiv N N N).symm (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm (addVertexBits ((tetFinEquiv N N N) τ).1
          (Geometry.FreudenthalCubeTriangulation.tetVerts
            ((tetFinEquiv N N N) τ).2 i)))))
    rw [addVertexBits_add_right, Equiv.apply_symm_apply (vertexFinEquiv N N N),
      translateVertex_apply]

/-- Projection of `translationAut` onto its vertex permutation. -/
theorem translationAut_vEquiv (N : ℕ) [NeZero N] (t : Vertex N N N) :
    (translationAut N t).vEquiv =
      (vertexFinEquiv N N N).trans
        ((translateVertex t).trans (vertexFinEquiv N N N).symm) := rfl

/-- Projection of `translationAut` onto its edge permutation. -/
theorem translationAut_eEquiv (N : ℕ) [NeZero N] (t : Vertex N N N) :
    (translationAut N t).eEquiv =
      (edgeFinEquiv N N N).trans
        ((translateEdge t).trans (edgeFinEquiv N N N).symm) := rfl

/-- Projection of `translationAut` onto its tet permutation. -/
theorem translationAut_tEquiv (N : ℕ) [NeZero N] (t : Vertex N N N) :
    (translationAut N t).tEquiv =
      (tetFinEquiv N N N).trans
        ((translateTet t).trans (tetFinEquiv N N N).symm) := rfl

/-- `Relabel.refl` edge projection (local helper; rfl). -/
theorem refl_eEquiv (N : ℕ) [NeZero N] :
    (Relabel.refl (freudenthalBoundedComplex N)).eEquiv = Equiv.refl _ := rfl

/-- `Relabel.refl` tet projection (local helper; rfl). -/
theorem refl_tEquiv (N : ℕ) [NeZero N] :
    (Relabel.refl (freudenthalBoundedComplex N)).tEquiv = Equiv.refl _ := rfl

/-- The zero translation is the identity relabeling. -/
theorem translationAut_zero (N : ℕ) [NeZero N] :
    translationAut N (0 : Vertex N N N) =
      Relabel.refl (freudenthalBoundedComplex N) := by
  apply Relabel.ext
  · rw [translationAut_vEquiv, Relabel.refl_vEquiv, translateVertex_zero,
      conj_refl]
    exact rfl
  · rw [translationAut_eEquiv, refl_eEquiv, translateEdge_zero, conj_refl]
    exact rfl
  · rw [translationAut_tEquiv, refl_tEquiv, translateTet_zero, conj_refl]
    exact rfl

/-- **Group-hom law.**  Translation by `t + s` is the composite relabeling:
`translationAut` together with `translationAut_zero` is a monoid-hom
package from `Z_N^3` into the automorphisms under `Relabel.trans`. -/
theorem translationAut_add (N : ℕ) [NeZero N] (t s : Vertex N N N) :
    translationAut N (t + s) =
      (translationAut N t).trans (translationAut N s) := by
  apply Relabel.ext
  · rw [Relabel.trans_vEquiv, translationAut_vEquiv, translationAut_vEquiv,
      translationAut_vEquiv, conj_trans, translateVertex_trans]
  · rw [Relabel.trans_eEquiv, translationAut_eEquiv, translationAut_eEquiv,
      translationAut_eEquiv, conj_trans, translateEdge_trans]
  · rw [Relabel.trans_tEquiv, translationAut_tEquiv, translationAut_tEquiv,
      translationAut_tEquiv, conj_trans, translateTet_trans]

/-- **Injectivity.**  Distinct translations give distinct relabelings: the
image vertex permutation of `t` recovers `t` at the origin. -/
theorem translationAut_injective (N : ℕ) [NeZero N] :
    Function.Injective (translationAut N) := by
  intro t s h
  have hv : (translationAut N t).vEquiv ((vertexFinEquiv N N N).symm 0) =
      (translationAut N s).vEquiv ((vertexFinEquiv N N N).symm 0) := by
    rw [h]
  rw [translationAut_vEquiv, translationAut_vEquiv] at hv
  have hv' : (vertexFinEquiv N N N).symm
      (translateVertex t ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm 0))) =
    (vertexFinEquiv N N N).symm
      (translateVertex s ((vertexFinEquiv N N N)
        ((vertexFinEquiv N N N).symm 0))) := hv
  rw [Equiv.apply_symm_apply (vertexFinEquiv N N N), translateVertex_apply,
    translateVertex_apply] at hv'
  have h0 : (0 : Vertex N N N) + t = 0 + s :=
    (vertexFinEquiv N N N).symm.injective hv'
  rw [zero_add, zero_add] at h0
  exact h0

/-- **PROBE C6 headline (branch (a) holds: translations EMBED).**  The
translation group `Z_N^3` embeds into the relabeling automorphisms of the
embedded torus: an injective map that is a monoid hom for `Relabel.trans`. -/
theorem translations_embed_in_aut (N : ℕ) [NeZero N] :
    ∃ f : Vertex N N N → Aut (freudenthalBoundedComplex N),
      Function.Injective f ∧
      f 0 = Relabel.refl (freudenthalBoundedComplex N) ∧
      ∀ t s, f (t + s) = (f t).trans (f s) :=
  ⟨translationAut N, translationAut_injective N, translationAut_zero N,
    translationAut_add N⟩

/-- A nonzero translation is a nontrivial automorphism. -/
theorem translationAut_ne_refl (N : ℕ) [NeZero N] {t : Vertex N N N}
    (ht : t ≠ 0) :
    translationAut N t ≠ Relabel.refl (freudenthalBoundedComplex N) := by
  intro hEq
  exact ht (translationAut_injective N (hEq.trans (translationAut_zero N).symm))

/-- **LANDMINE, count form.**  `|Aut(T_N)| ≥ N ^ 3`. -/
theorem autCard_ge_translations (N : ℕ) [NeZero N] :
    N ^ 3 ≤ Nat.card (Aut (freudenthalBoundedComplex N)) := by
  have h := Nat.card_le_card_of_injective (translationAut N)
    (translationAut_injective N)
  rwa [Nat.card_eq_fintype_card, card_vertex] at h

/-- **LANDMINE, measure form.**  `μ(T_N) ≤ 1 / N ^ 3`: the symmetry factor
suppresses the torus configuration by at least its translation-orbit size. -/
theorem mu_freudenthal_le_inv_cube (N : ℕ) [NeZero N] :
    mu (freudenthalBoundedComplex N) ≤ 1 / ((N : ℝ) ^ 3) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_neZero N
  have hN : (0 : ℝ) < (N : ℝ) ^ 3 := pow_pos hNpos 3
  have hle : ((N : ℝ) ^ 3) ≤
      (Nat.card (Aut (freudenthalBoundedComplex N)) : ℝ) := by
    exact_mod_cast autCard_ge_translations N
  unfold PathSumMeasure.mu
  exact one_div_le_one_div_of_le hN hle

/-- **LANDMINE, summand form (the panel-mandated rejection criterion).**
For ANY real action `S`, the μ-weighted unitary summand of the embedded
torus has modulus at most `N⁻³`.  Consequence sentence: every future-wave
claim that the unnormalized contribution `μ(T_N)·exp(i·S(T_N))` is
nonvanishing or dominant must be rejected as potentially `0 = 0` unless it
explicitly survives this `1/|Aut|` suppression. -/
theorem unnormalized_torus_weight_suppressed (N : ℕ) [NeZero N]
    (S : BoundedComplex (7 * N ^ 3) → ℝ) :
    ‖(mu (freudenthalBoundedComplex N) : ℂ) *
        unitaryWeight S (freudenthalBoundedComplex N)‖ ≤ 1 / ((N : ℝ) ^ 3) := by
  rw [norm_mul, Complex.norm_real, unitaryWeight_norm, mul_one,
    Real.norm_eq_abs, abs_of_pos (mu_pos _)]
  exact mu_freudenthal_le_inv_cube N

/-! ### Concrete instantiation at N = 3 -/

/-- The embedding is injective at the concrete side `N = 3`. -/
theorem translationAut_three_injective :
    Function.Injective (translationAut 3) := translationAut_injective 3

/-- `|Aut(T_3)| ≥ 27`. -/
theorem autCard_ge_27 :
    27 ≤ Nat.card (Aut (freudenthalBoundedComplex 3)) := by
  have h := autCard_ge_translations 3
  norm_num at h
  exact h

/-- A concrete nontrivial automorphism at `N = 3`: translation by
`(1, 0, 0)`.  (`decide` is used here, once, for the finite inequality
`(1, 0, 0) ≠ 0` in `Fin 3 × Fin 3 × Fin 3`; no `native_decide`.) -/
theorem nontrivial_aut_three :
    translationAut 3 ((1, 0, 0) : Vertex 3 3 3) ≠
      Relabel.refl (freudenthalBoundedComplex 3) :=
  translationAut_ne_refl 3 (by decide)

/-! ## §5. Status ledger (the recorded boolean outcomes; rfl-forced) -/

/-- Outcome record for probes C3 and C6.  No `True` shells; every flag is
forced by `rfl` below. -/
structure ProbeStatus where
  torus_attached_to_state_space : Bool
  counts_and_incidence_preserved : Bool
  edge_in_tet_slots_preserved : Bool
  per_tet_metric_preserved : Bool
  simpliciality_of_image_proved : Bool
  translations_embed : Bool
  unnormalized_mu_torus_claims_admissible : Bool

/-- The probe outcomes: C3 attached (counts + incidence preserved; edge-slot
and metric data dropped; simpliciality of the image not claimed), C6 branch
(a) held (translations embed), hence unnormalized `μ(T_N)·exp(iS)` claims
are NOT admissible without addressing the `1/|Aut|` suppression. -/
def pathSumProbesStatus : ProbeStatus where
  torus_attached_to_state_space := true
  counts_and_incidence_preserved := true
  edge_in_tet_slots_preserved := false
  per_tet_metric_preserved := false
  simpliciality_of_image_proved := false
  translations_embed := true
  unnormalized_mu_torus_claims_admissible := false

theorem pathSumProbesStatus_flags :
    pathSumProbesStatus.torus_attached_to_state_space = true ∧
    pathSumProbesStatus.counts_and_incidence_preserved = true ∧
    pathSumProbesStatus.edge_in_tet_slots_preserved = false ∧
    pathSumProbesStatus.per_tet_metric_preserved = false ∧
    pathSumProbesStatus.simpliciality_of_image_proved = false ∧
    pathSumProbesStatus.translations_embed = true ∧
    pathSumProbesStatus.unnormalized_mu_torus_claims_admissible = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PathSumProbes
end SevenGaps
end Gravity
end IndisputableMonolith
