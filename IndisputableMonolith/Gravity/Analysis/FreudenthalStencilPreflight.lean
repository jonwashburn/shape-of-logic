import Mathlib
import IndisputableMonolith.Geometry.PeriodicFreudenthalTorus
import IndisputableMonolith.Geometry.ReggeActionConcrete

/-!
# Freudenthal stencil preflight: exact general-N stencil identity and moment tensor

QG full-theory campaign, Phase 2b, panel-locked Test G stage 1 (candidate C8,
tensor-first anisotropic action continuum limit).

Scope statement (panel-mandated): this module and its stage-2 companion
(`FreudenthalEnergyLimit`) develop the action-level continuum limit of the
frozen quadratic energy on the canonical Freudenthal family; scoped partial;
the pillar-2 path-sum flag stays red (flipping it requires the
refinement-indexed measure-weighted sum over inequivalent triangulation
classes).

## Status: THEOREM (everything below is proved, axiom-clean; no sorry, no
## admit, no native_decide, no `: True` shells).

## What this module proves

Stage 1 of Test G, for EVERY side length `N > 2` (not just the `N = 5`
certificates of `FreudenthalAxisStencilCoeffCert`):

* `hessianQuadratic_canonical_eq_freudenthalStencil`: the quadratic form of
  the canonical Regge Hessian `canonicalReggeHessian` on the canonical
  periodic Freudenthal triangulation at side `N` is EXACTLY the seven-class
  nearest-displacement stencil sum
  `Σ_x Σ_{d : Fin 7} c_d · (u(x+d) − u(x))²`
  with weights `c_d = √(ℓ²_d)` read off the Hessian's incidence dual weights
  (`ℓ²` = 1,1,1,2,2,2,3 for the three axis, three face-diagonal, and one
  body-diagonal displacement classes). Derived, never postulated: the chain
  is `canonicalReggeHessian_quadratic_eq_dirichlet` (frozen quadratic form =
  graph Dirichlet energy), then the no-self-loop edge-stencil reindexing of
  `ReggeActionConcrete`, then the periodic-edge / (base, displacement)
  product reindexing.
* `freudenthal_stencil_identity`: the panel-locked normalized identity
  `ρ(N) · Q_N(u) = h³ · Σ_x Σ_d c_d · ((u(x+d) − u(x))/h)²` with `h = 1/N`
  and `ρ(N) = 1/N` stated A PRIORI (`stencilNormalization`, declared with
  its dimensional justification before any limit computation; nothing is
  fitted after the fact).
* `stencilMomentTensor_eq`: the moment tensor `A₀ = Σ_d c_d · d dᵀ` is
  computed exactly:
  `A₀ = (1 + √2)·I + (√2 + √3)·J` (`J` = all-ones matrix), i.e. every
  diagonal entry is `1 + 2√2 + √3` and every off-diagonal entry is
  `√2 + √3`. The entries live in `ℚ[√2, √3]`, not `ℚ`; the brief's
  "rational symmetric matrix" expectation is corrected by this exact
  kernel-checked value.
* `stencilMomentTensor_psd` / `stencilMomentTensor_diag_pos`: `A₀` is
  positive semidefinite (kernel-proved via the exact sum-of-squares
  decomposition `vᵀA₀v = Σ_d c_d ⟨d, v⟩²`) and nonzero.
* `stencilMomentTensor_not_isotropic`: FINDING — `A₀` is NOT isotropic:
  the off-diagonal entry `√2 + √3` is strictly positive, so `A₀ ≠ c·I` for
  every `c`. The Freudenthal frozen quadratic energy carries an anisotropic
  continuum quadratic form; its spectrum is `1 + √2` (multiplicity 2,
  orthogonal to `(1,1,1)`) and `1 + 4√2 + 3√3` (direction `(1,1,1)`).

Stage 2 (`FreudenthalEnergyLimit`) consumes `scaledCanonicalEnergy` and
`stencilMomentTensor` from this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace FreudenthalStencilPreflight

open Geometry.PeriodicFreudenthalTorus
open Geometry.ReggeActionConcrete
open Geometry.ReggeHessian3D

noncomputable section

variable (N : ℕ) [NeZero N]

/-! ## §1. The stencil data, read off the canonical Hessian -/

/-- Displacement-class stencil weight: the square root of the squared edge
length of displacement class `d`. This is DEFINITIONAL from the canonical
Hessian: `canonicalDualWeight` sums `√(globalSqEdge e)` over incident edges,
and on the canonical periodic triangulation `globalSqEdge` is
`periodicDispSqEdge` of the edge's displacement class. -/
def stencilWeight (d : Fin 7) : ℝ := Real.sqrt (periodicDispSqEdge d)

/-- The stencil weight is exactly the Hessian dual-weight length factor of
any canonical periodic edge in displacement class `d`: definitional
transparency of `stencilWeight` (proof is `rfl`). -/
theorem stencilWeight_eq_sqrt_globalSqEdge
    (e : Fin (canonicalPeriodicTriangulation N N N).nE) :
    Real.sqrt ((canonicalPeriodicIncidenceConsistent N N N).globalSqEdge e) =
      stencilWeight ((edgeFinEquiv N N N e).disp) := rfl

/-- Explicit values of the seven stencil weights:
`√1, √1, √1, √2, √2, √2, √3` for the three axis classes, the three
face-diagonal classes, and the body-diagonal class. -/
theorem stencilWeight_values :
    stencilWeight 0 = 1 ∧ stencilWeight 1 = 1 ∧ stencilWeight 2 = 1 ∧
      stencilWeight 3 = Real.sqrt 2 ∧ stencilWeight 4 = Real.sqrt 2 ∧
      stencilWeight 5 = Real.sqrt 2 ∧ stencilWeight 6 = Real.sqrt 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [stencilWeight, periodicDispSqEdge, Real.sqrt_one]

theorem stencilWeight_nonneg (d : Fin 7) : 0 ≤ stencilWeight d :=
  Real.sqrt_nonneg _

/-- Vertex shifted by one displacement class: `x + d` on the periodic torus.
Definitional match with `PeriodicEdge.endpoints`: the edge with base `x` and
class `d` has endpoints `(x, shiftVertex x d)`. -/
def shiftVertex (x : Vertex N N N) (d : Fin 7) : Vertex N N N :=
  addBits x (dispBits d).1 (dispBits d).2.1 (dispBits d).2.2

theorem periodicEdge_endpoints_eq (edge : PeriodicEdge N N N) :
    edge.endpoints = (edge.base, shiftVertex N edge.base edge.disp) := rfl

/-- The seven-class Freudenthal stencil energy on arbitrary vertex data:
`Σ_x Σ_{d ∈ D} c_d · (u(x+d) − u(x))²` over all `N³` base vertices and all
seven displacement classes. -/
def freudenthalStencilEnergy (u : Vertex N N N → ℝ) : ℝ :=
  ∑ x : Vertex N N N, ∑ d : Fin 7,
    stencilWeight d * (u (shiftVertex N x d) - u x) ^ (2 : ℕ)

/-- Transport of vertex data along the canonical finite vertex indexing. -/
def toPotential (u : Vertex N N N → ℝ) :
    VertexPotential (canonicalPeriodicTriangulation N N N) :=
  fun i => u (vertexFinEquiv N N N i)

theorem toPotential_symm_apply (u : Vertex N N N → ℝ) (v : Vertex N N N) :
    toPotential N u ((vertexFinEquiv N N N).symm v) = u v := by
  unfold toPotential
  rw [Equiv.apply_symm_apply]

/-! ## §2. General-N derivation of the stencil identity from the Hessian -/

theorem canonical_globalSqEdge_eq
    (e : Fin (canonicalPeriodicTriangulation N N N).nE) :
    (canonicalPeriodicIncidenceConsistent N N N).globalSqEdge e =
      periodicDispSqEdge ((edgeFinEquiv N N N e).disp) := rfl

theorem canonical_edgeVerts_eq
    (e : Fin (canonicalPeriodicTriangulation N N N).nE) :
    (canonicalPeriodicTriangulation N N N).edgeVerts e =
      ((vertexFinEquiv N N N).symm (edgeFinEquiv N N N e).endpoints.1,
        (vertexFinEquiv N N N).symm (edgeFinEquiv N N N e).endpoints.2) := rfl

/-- For `N > 2` the canonical periodic triangulation has no self-loop edges:
the side-length assumption rules out `x + d = x` wraparound. -/
theorem canonicalPeriodic_noSelfLoopEdges (hN : 2 < N) :
    NoSelfLoopEdges (canonicalPeriodicTriangulation N N N) := by
  intro e h
  rw [canonical_edgeVerts_eq] at h
  exact PeriodicEdge.endpoints_ne hN hN hN (edgeFinEquiv N N N e)
    ((vertexFinEquiv N N N).symm.injective h)

/-- Bookkeeping equivalence between periodic edges and (base, class) pairs. -/
def periodicEdgeProdEquiv : PeriodicEdge N N N ≃ Vertex N N N × Fin 7 where
  toFun e := (e.base, e.disp)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical edge-stencil Dirichlet energy of the periodic Freudenthal
triangulation is exactly the seven-class stencil energy, for every `N`. -/
theorem canonicalEdgeStencil_eq_freudenthalStencil (u : Vertex N N N → ℝ) :
    canonicalEdgeStencilDirichletEnergy (canonicalPeriodicTriangulation N N N)
        (canonicalPeriodicIncidenceConsistent N N N) (toPotential N u) =
      freudenthalStencilEnergy N u := by
  classical
  have h1 : canonicalEdgeStencilDirichletEnergy
      (canonicalPeriodicTriangulation N N N)
      (canonicalPeriodicIncidenceConsistent N N N) (toPotential N u) =
      ∑ edge : PeriodicEdge N N N,
        stencilWeight edge.disp *
          (u edge.endpoints.1 - u edge.endpoints.2) ^ (2 : ℕ) := by
    unfold canonicalEdgeStencilDirichletEnergy
    refine Fintype.sum_equiv (edgeFinEquiv N N N) _ _ fun e => ?_
    rw [canonical_globalSqEdge_eq, canonical_edgeVerts_eq]
    dsimp only
    rw [toPotential_symm_apply, toPotential_symm_apply]
    rfl
  have h2 : (∑ edge : PeriodicEdge N N N,
      stencilWeight edge.disp *
        (u edge.endpoints.1 - u edge.endpoints.2) ^ (2 : ℕ)) =
      ∑ p : Vertex N N N × Fin 7,
        stencilWeight p.2 *
          (u (shiftVertex N p.1 p.2) - u p.1) ^ (2 : ℕ) := by
    refine Fintype.sum_equiv (periodicEdgeProdEquiv N) _ _ fun edge => ?_
    rw [periodicEdge_endpoints_eq]
    dsimp only [periodicEdgeProdEquiv, Equiv.coe_fn_mk]
    ring
  rw [h1, h2, Fintype.sum_prod_type]
  rfl

/-- General-N stage-1 core identity, DERIVED from the canonical Regge
Hessian (never postulated): the frozen quadratic form
`hessianQuadratic (canonicalReggeHessian …)` of the canonical periodic
Freudenthal triangulation at any side `N > 2` equals the seven-class
stencil energy `Σ_x Σ_d c_d (u(x+d) − u(x))²`.

Derivation chain: `canonicalReggeHessian_quadratic_eq_dirichlet`
(Hessian quadratic form = graph Dirichlet energy), the no-self-loop
edge-stencil reindexing of `ReggeActionConcrete`
(`canonicalDirichletEqualsEdgeStencil_of_sumComm_and_reindex`), and the
periodic-edge product reindexing above. -/
theorem hessianQuadratic_canonical_eq_freudenthalStencil
    (hN : 2 < N) (u : Vertex N N N → ℝ) :
    hessianQuadratic
        (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
          (canonicalPeriodicIncidenceConsistent N N N))
        (toPotential N u) =
      freudenthalStencilEnergy N u := by
  rw [canonicalReggeHessian_quadratic_eq_dirichlet]
  rw [canonicalDirichletEqualsEdgeStencil_of_sumComm_and_reindex
    (canonicalPeriodicTriangulation N N N)
    (canonicalPeriodicIncidenceConsistent N N N)
    (canonicalEdgeStencilSumComm _ _)
    (canonicalEdgePairWeightReindex_of_noSelfLoop _ _
      (canonicalPeriodic_noSelfLoopEdges N hN))
    (toPotential N u)]
  exact canonicalEdgeStencil_eq_freudenthalStencil N u

/-! ## §3. The a-priori normalization and the panel-locked identity -/

/-- A-PRIORI normalization `ρ(N) = 1/N`, declared before any limit
computation. Dimensional derivation (not a fit): each Hessian summand
carries exactly one hinge-measure length factor `√(ℓ²_d)` at lattice
spacing `h = 1/N`, so the physical energy density
`h³ · Σ c_d ((Δu)/h)² = h · Σ c_d (Δu)²` differs from the raw quadratic
form by exactly one power of `h = 1/N`. -/
def stencilNormalization (N : ℕ) : ℝ := 1 / (N : ℝ)

/-- Lattice spacing `h = 1/N` of the side-`N` canonical periodic family on
the unit 3-torus. -/
def meshSize (N : ℕ) : ℝ := 1 / (N : ℝ)

/-- Panel-locked stage-1 observable, for ALL `N > 2` and arbitrary vertex
data `u`:

`ρ(N) · Q_N(u) = h³ · Σ_x Σ_{d ∈ D} c_d · ((u(x+d) − u(x))/h)²`, `h = 1/N`,

where `Q_N` is the canonical Regge-Hessian quadratic form
(`hessianQuadratic (canonicalReggeHessian …)`), `D` is the full
seven-element displacement-class set, the weights `c_d` are the
definitional Hessian dual weights (`stencilWeight`), and
`ρ(N) = stencilNormalization N = 1/N` was declared a priori above. -/
theorem freudenthal_stencil_identity (hN : 2 < N) (u : Vertex N N N → ℝ) :
    stencilNormalization N *
      hessianQuadratic
        (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
          (canonicalPeriodicIncidenceConsistent N N N))
        (toPotential N u) =
      meshSize N ^ (3 : ℕ) *
        ∑ x : Vertex N N N, ∑ d : Fin 7,
          stencilWeight d *
            ((u (shiftVertex N x d) - u x) / meshSize N) ^ (2 : ℕ) := by
  rw [hessianQuadratic_canonical_eq_freudenthalStencil N hN u]
  unfold freudenthalStencilEnergy stencilNormalization meshSize
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
  field_simp

/-- The `ρ(N)`-normalized canonical quadratic energy of the side-`N`
periodic Freudenthal family. Stage 2 samples continuum fields into this. -/
def scaledCanonicalEnergy (u : Vertex N N N → ℝ) : ℝ :=
  stencilNormalization N *
    hessianQuadratic
      (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
        (canonicalPeriodicIncidenceConsistent N N N))
      (toPotential N u)

theorem scaledCanonicalEnergy_eq_scaled_stencil (hN : 2 < N)
    (u : Vertex N N N → ℝ) :
    scaledCanonicalEnergy N u =
      stencilNormalization N * freudenthalStencilEnergy N u := by
  unfold scaledCanonicalEnergy
  rw [hessianQuadratic_canonical_eq_freudenthalStencil N hN u]

/-! ## §4. The moment tensor `A₀ = Σ_d c_d · d dᵀ` -/

/-- Real coordinates of the seven displacement classes (0/1 entries),
as an explicit table. `dispReal_matches_dispBits` kernel-checks the table
against the canonical `dispBits` displacement bits. -/
def dispReal : Fin 7 → Fin 3 → ℝ
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => 1 | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1
  | 3, 0 => 1 | 3, 1 => 1 | 3, 2 => 0
  | 4, 0 => 1 | 4, 1 => 0 | 4, 2 => 1
  | 5, 0 => 0 | 5, 1 => 1 | 5, 2 => 1
  | 6, 0 => 1 | 6, 1 => 1 | 6, 2 => 1

/-- The `dispReal` table is exactly the indicator coordinates of the
canonical displacement bit table `dispBits` (no free data). -/
theorem dispReal_matches_dispBits (d : Fin 7) :
    dispReal d 0 = (if (dispBits d).1 then 1 else 0) ∧
      dispReal d 1 = (if (dispBits d).2.1 then 1 else 0) ∧
      dispReal d 2 = (if (dispBits d).2.2 then 1 else 0) := by
  fin_cases d <;>
    refine ⟨?_, ?_, ?_⟩ <;> norm_num [dispReal, dispBits]

/-- The stencil moment tensor `A₀ = Σ_{d ∈ D} c_d · d dᵀ` of the canonical
Freudenthal displacement classes with their Hessian dual weights. -/
def stencilMomentTensor : Fin 3 → Fin 3 → ℝ := fun i j =>
  ∑ d : Fin 7, stencilWeight d * dispReal d i * dispReal d j

/-- EXACT value of the moment tensor:
`A₀ = (1 + √2)·I + (√2 + √3)·J` with `J` the all-ones matrix. Every
diagonal entry is `1 + 2√2 + √3`; every off-diagonal entry is `√2 + √3`.
The entries are irrational (in `ℚ[√2,√3]`); this is the exact
kernel-checked value. -/
theorem stencilMomentTensor_eq (i j : Fin 3) :
    stencilMomentTensor i j =
      (if i = j then 1 + Real.sqrt 2 else 0) + (Real.sqrt 2 + Real.sqrt 3) := by
  fin_cases i <;> fin_cases j <;>
    · norm_num [stencilMomentTensor, Fin.sum_univ_seven, dispReal,
        stencilWeight, periodicDispSqEdge, Real.sqrt_one]
      try ring

theorem stencilMomentTensor_symm (i j : Fin 3) :
    stencilMomentTensor i j = stencilMomentTensor j i := by
  unfold stencilMomentTensor
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- Exact sum-of-squares decomposition of the moment-tensor quadratic form:
`vᵀ A₀ v = Σ_d c_d ⟨d, v⟩²`. This is the kernel-level PSD witness. -/
theorem stencilMomentTensor_quadratic_eq (v : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, stencilMomentTensor i j * v i * v j) =
      ∑ d : Fin 7,
        stencilWeight d * (∑ i : Fin 3, dispReal d i * v i) ^ (2 : ℕ) := by
  simp only [stencilMomentTensor, Fin.sum_univ_three, Fin.sum_univ_seven,
    dispReal]
  ring

/-- KERNEL-PROVED: the moment tensor `A₀` is positive semidefinite. -/
theorem stencilMomentTensor_psd (v : Fin 3 → ℝ) :
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, stencilMomentTensor i j * v i * v j := by
  rw [stencilMomentTensor_quadratic_eq]
  refine Finset.sum_nonneg fun d _ => ?_
  exact mul_nonneg (stencilWeight_nonneg d) (by positivity)

theorem sqrt_two_add_sqrt_three_pos : 0 < Real.sqrt 2 + Real.sqrt 3 := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  linarith

/-- KERNEL-PROVED: `A₀` is nonzero — every diagonal entry
`1 + 2√2 + √3` is strictly positive. -/
theorem stencilMomentTensor_diag_pos (i : Fin 3) :
    0 < stencilMomentTensor i i := by
  rw [stencilMomentTensor_eq]
  rw [if_pos rfl]
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  linarith

theorem stencilMomentTensor_ne_zero : stencilMomentTensor 0 0 ≠ 0 :=
  ne_of_gt (stencilMomentTensor_diag_pos 0)

/-- Off-diagonal entries of `A₀` are strictly positive (`√2 + √3`). -/
theorem stencilMomentTensor_offDiag_pos (i j : Fin 3) (hij : i ≠ j) :
    0 < stencilMomentTensor i j := by
  rw [stencilMomentTensor_eq, if_neg hij]
  simpa using sqrt_two_add_sqrt_three_pos

/-- FINDING (kernel-checked): the moment tensor is ANISOTROPIC. The
off-diagonal entry is `√2 + √3 > 0`, so `A₀ ≠ c·I` for every scalar `c`.
Isotropy is NOT claimed; the exact anisotropic value is
`stencilMomentTensor_eq`. -/
theorem stencilMomentTensor_not_isotropic (c : ℝ) :
    stencilMomentTensor ≠ fun i j => if i = j then c else 0 := by
  intro h
  have hne : (0 : Fin 3) ≠ 1 := by decide
  have h01 := congrFun (congrFun h 0) 1
  rw [if_neg hne] at h01
  exact absurd h01 (ne_of_gt (stencilMomentTensor_offDiag_pos 0 1 hne))

/-! ## §5. Status record (documentation, not mathematics) -/

/-- Status flags for the Freudenthal stencil preflight (documentation
record; the mathematics lives in the theorems above, not in these
booleans).

Honest scope: this stage-1 record certifies the general-N stencil identity
derived from the canonical Regge Hessian, the a-priori normalization
`ρ(N) = 1/N`, and the exact anisotropic PSD moment tensor
`A₀ = (1+√2)·I + (√2+√3)·J`. Together with stage 2 this remains a SCOPED
PARTIAL of the action-level continuum limit of the frozen quadratic energy
on the canonical Freudenthal family; the pillar-2 path-sum flag stays red
(flipping it requires the refinement-indexed measure-weighted sum over
inequivalent triangulation classes). -/
structure StencilPreflightStatus where
  /-- `freudenthal_stencil_identity`: general-N identity, all seven
  displacement classes, derived from `canonicalReggeHessian`. -/
  general_N_identity_derived : Bool
  /-- `stencilNormalization` declared a priori with dimensional
  justification; no post-hoc fitting. -/
  normalization_a_priori : Bool
  /-- `stencilMomentTensor_psd` + `stencilMomentTensor_diag_pos`. -/
  moment_tensor_psd_nonzero : Bool
  /-- `stencilMomentTensor_not_isotropic`: anisotropy is the finding;
  isotropy is NOT claimed. -/
  moment_tensor_anisotropic_finding : Bool

/-- The canonical status inhabitant (documentation record, not a proof
obligation). -/
def stencilPreflightStatus : StencilPreflightStatus where
  general_N_identity_derived := true
  normalization_a_priori := true
  moment_tensor_psd_nonzero := true
  moment_tensor_anisotropic_finding := true

end

end FreudenthalStencilPreflight
end Analysis
end Gravity
end IndisputableMonolith
