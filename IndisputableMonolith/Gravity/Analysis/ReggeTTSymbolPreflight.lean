import Mathlib
import IndisputableMonolith.Gravity.Analysis.FreudenthalStencilPreflight
import IndisputableMonolith.Gravity.PhysicalSixTetCubicDirichletInstance

/-!
# Regge TT symbol preflight: the true nonlinear action, its flat point, the
# frozen-model identification, and the TT Bloch symbol object

QG full-theory campaign, `ReggeTTContinuumSymbol` program, Stage 1 (unlocked
by critic sign-off on the C10 probe, receipt commit 1e38531ee2).

## Tier tags (binding, per-claim)

* THEOREM: everything proved in this file (kernel-checked here; no sorry, no
  admit, no new axioms, no native_decide, no `: True` shells).
* NUMERICAL EVIDENCE (never proof): the C10 provenance-gated numerics probe
  (`state/qg_full_theory/true_regge_tt_probe/`, commit f1d44266e5, critic
  sign-off with independent reproduction at 1e38531ee2) reports that the TT
  Bloch symbol of the true nonlinear Regge action on this lattice is
  ISOTROPIC in the continuum limit with value `K(0) = -(1/4)·I_TT` on all 14
  preregistered directions, and that `-1/4` is exactly the linearized
  Einstein-Hilbert TT coefficient in those conventions.  Nothing in this
  file proves that; the corresponding Lean statement is the named OPEN
  target `ReggeTTContinuumIsotropyTarget` below, and its status flag is
  `false`.
* OPEN: `ReggeTTContinuumIsotropyTarget` (existence and value of the
  continuum TT symbol).

## What this module defines (a, c)

* `trueReggeAction`: the TRUE nonlinear 3D Regge action on the canonical
  periodic Freudenthal torus as a function of an ARBITRARY edge
  squared-length field `ℓ : PeriodicEdge N N N → ℝ`:
  `S(ℓ) = Σ_e √(ℓ_e) · (2π − Σ_{incident tets} θ)`, with the dihedral
  angles computed by the existing Cayley-Menger machinery
  (`dihedralAngle3Sq`, i.e. `arccos` of the `cmCofactor3` ratio) on the
  local squared-edge tuples read off the field through the canonical
  edge-slot lookup `canonicalEdgeSlot?`.  The deficit machinery is REUSED,
  not re-derived: the per-slot angle is literally
  `DihedralDerivatives.dihedralAngle3Sq`, and at conformal fields the whole
  action is proved equal to the existing
  `ReggeActionConcrete.reggeAction` (see `reggeAction_conformal_eq`).
* `planeWaveEdgeField`, `ttSecondDifference`, `TTBlochSymbolIs`,
  `ReggeTTContinuumSymbolIs`: the TT Bloch symbol object.  For a
  commensurate momentum `k = 2π·m/N` (`m : Fin 3 → ℤ`, so `k` is
  commensurate on the side-`N` torus for every `N`) and a polarization
  matrix `E`, the perturbation family is the midpoint-phase plane wave of
  the C10 preregistration, `ℓ_e(t) = ℓ²_flat + t·(E·D_d·D_d)·cos(k·(x +
  D_d/2))`; `ttSecondDifference` is its per-unit-cell second-difference
  quadratic form `(2/N³)·(S(t) − 2S(0) + S(−t))/t²`;
  `TTBlochSymbolIs N E m H` states (via `Filter.Tendsto` on `𝓝[≠] 0`)
  that the amplitude second difference converges to `H`; and
  `ReggeTTContinuumSymbolIs E m Λ` states that the `|k|²`-normalized
  symbol values converge to `Λ` along the torus family `N = j + 3 → ∞`
  (fixed integer wave vector, so `|k_N| → 0` at fixed direction).  These
  are DEFINITIONS ONLY: no existence or value of any of these limits is
  claimed anywhere in this file.

## What this module proves (b, d) — all THEOREM

* Flat point (b): `deficitOfField_flatEdgeField` — at the flat edge
  assignment (`ℓ_e = ℓ²` of the displacement class) every deficit vanishes
  (reusing the certified periodic angle-sum chain
  `canonicalPeriodicDirectTypedEdgeAngleSumTarget_holds`, not re-proved);
  hence `trueReggeAction_flatEdgeField : S(flat) = 0` and
  `planeWaveActionProfile_zero : S(plane wave at t = 0) = 0`.
* Frozen-model identification (d), as kernel equations:
  - `reggeAction_conformal_eq`: the existing conformal-ansatz action
    `ReggeActionConcrete.reggeAction` is EXACTLY the true action evaluated
    on the conformal edge fields
    `ℓ_e = ℓ²_flat(e) · exp(ξ_u + ξ_v)` (`typedConformalEdgeField`).  This
    states precisely which restriction the frozen wave analyzed.
  - `frozen_identification` / `frozen_identification_stencil`: along that
    conformal family the true action decomposes as `S = (1/2)·Q_frozen + R`,
    where `Q_frozen` is the quadratic form of the frozen graph-Laplacian
    model `canonicalReggeHessian` and `R` is the remainder.  HONESTY NOTE:
    this decomposition is a DEFINITIONAL TAUTOLOGY and carries NO
    mathematical content on its own — `reggeActionRemainder` is DEFINED as
    `S − S(0) − (1/2)·Q`, so the equation holds for ANY quadratic form `Q`
    and does NOT pin the graph-Laplacian in any way.  It is here only to
    NAME the frozen postulate explicitly and to expose `R` as the object a
    later stage must expand.  The genuine (non-tautological) content of
    this file's frozen-model bridge lives in the two REAL equalities:
    (1) `reggeAction_conformal_eq` — the existing conformal-ansatz action
    equals the true action on conformal edge fields (a real identity of
    two independently defined expressions), and (2) the stage-1 Test G
    theorem `hessianQuadratic_canonical_eq_freudenthalStencil` — `Q_frozen`
    equals the anisotropic seven-class stencil energy with moment tensor
    `A₀ = (1+√2)I + (√2+√3)J`.  So the identification that was FROZEN is:
    (i) restrict the true action to vertex-conformal edge fields
    (`reggeAction_conformal_eq`, real), and (ii) POSTULATE the graph-
    Laplacian `canonicalReggeHessian` as its quadratic model (the postulate
    itself, not a theorem).  The TT plane-wave fields of the C10 probe are
    not of that conformal form, which is how the frozen anisotropy and the
    (numerically observed) true-TT isotropy coexist.
  - `reggeAction_zeroPotential_eq_zero`: flat normalization of the
    conformal action, obtained here as a corollary of the typed flat-point
    theorem (no side-length hypothesis needed).
* Symbol-object well-formedness and symmetry (d):
  `planeWaveEdgeField_zero_amplitude` (the family passes through flat),
  `ttSecondDifference_even` (evenness in the amplitude),
  `ttSecondDifference_neg_polarization` (invariance under `E ↦ −E`, the
  quadratic-form sign symmetry), `polEdgeCoeff_neg`.
* Non-vacuity of the OPEN target's hypothesis class:
  `axisTTPolarizationPlus_isTT` / `axisTTPolarizationCross_isTT` — the
  preregistered axis direction carries two explicit TT polarizations
  satisfying `IsTTPolarization` (symmetric, traceless, transverse,
  Frobenius-normalized), so `ReggeTTContinuumIsotropyTarget` does not
  quantify over an empty set.

## Re-scoping disclosure (binding)

Stage-1 scope was re-scoped DOWN in two places, disclosed here and in the
status flags:

1. First-order behavior of the action at the flat point (differentiability
   of the arccos-of-Cayley-Menger-ratio compositions along the plane-wave
   family) is NOT proved here.  The flat VALUE is proved
   (`trueReggeAction_flatEdgeField`); derivatives are not attempted.
2. The existence and value of the TT Bloch symbol limits are NOT claimed.
   `TTBlochSymbolIs`/`ReggeTTContinuumSymbolIs` are definitions;
   `ReggeTTContinuumIsotropyTarget` (value `-(1/4)` on TT polarizations)
   is a named OPEN target with status flag `false`.  The C10 numbers stay
   NUMERICAL EVIDENCE.

No `sorry`, no `admit`, no new axioms, no `native_decide` in this file.

## Inherited axiom footprint (disclosure)

`#print axioms` on the flat-point theorems and everything downstream of
them (`deficitOfField_flatEdgeField`, `trueReggeAction_flatEdgeField`,
`reggeAction_zeroPotential_eq_zero`, `frozen_identification`,
`frozen_identification_stencil`, `status_flags_grounded`) reports
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler,
Quot.sound]`.  The compiler-trust axioms `Lean.ofReduceBool` /
`Lean.trustCompiler` are NOT introduced here: they enter through the
inherited certified Freudenthal angle-sum chain
(`PhysicalSixTetCubicDirichletInstance.canonicalPeriodicDirectTypedEdgeAngleSumTarget_holds`
already carries exactly this footprint).  The purely algebraic theorems of
this file (`reggeAction_conformal_eq`, `ttSecondDifference_even`,
`ttSecondDifference_neg_polarization`, `axisTTPolarizationPlus_isTT`,
`axisTTPolarizationCross_isTT`) carry the standard footprint
`[propext, Classical.choice, Quot.sound]`.  Audited in
`scripts/qg7_axiom_audit.lean`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTSymbolPreflight

open Geometry.PeriodicFreudenthalTorus
open Geometry.ReggeActionConcrete
open Geometry.ReggeHessian3D
open Geometry.DihedralDerivatives
open PhysicalSixTetCubicDirichletInstance
open FreudenthalStencilPreflight

noncomputable section

variable (N : ℕ) [NeZero N]

/-! ## §1. The true Regge action on edge squared-length fields (a)

The action is a function of an arbitrary per-edge squared-length field on
the typed periodic Freudenthal torus.  The Lean deficit machinery is reused
verbatim: local squared-edge tuples are read off the field through the
canonical edge-slot tables, and each dihedral angle is
`DihedralDerivatives.dihedralAngle3Sq` (arccos of the Cayley-Menger
cofactor ratio `dihedralCos3Sq`). -/

/-- An edge squared-length field on the side-`N` periodic Freudenthal
torus: one real number (a squared length) per positive-displacement
periodic edge. -/
abbrev EdgeField := PeriodicEdge N N N → ℝ

/-- The flat background field: every edge carries the squared length of its
displacement class (`1,1,1,2,2,2,3`). -/
def flatEdgeField : EdgeField N := fun e => periodicDispSqEdge e.disp

/-- The six local squared-edge coordinates of the tetrahedron
`(cell, tet)`, read off an edge field through the canonical local-edge
tables. -/
def tetSqEdgesOfField (ℓ : EdgeField N) (cellTet : PeriodicTet N N N) :
    Geometry.CayleyMengerPolynomial.SqEdges :=
  fun f => ℓ (localEdgeOf cellTet.1 cellTet.2 f)

/-- Dihedral angle at local edge slot `f` of tetrahedron `(cell, tet)`
under an edge field: the existing Cayley-Menger `arccos` machinery applied
to the field's local squared-edge tuple. -/
def tetDihedralAngleOfField (ℓ : EdgeField N) (cellTet : PeriodicTet N N N)
    (f : Fin 6) : ℝ :=
  dihedralAngle3Sq (tetSqEdgesOfField N ℓ cellTet) f

/-- Contribution of the tetrahedron `(cell, tet)` to the angle sum around a
periodic edge, under an edge field.  Mirrors
`localDeficitAngleContribution` through the same `canonicalEdgeSlot?`
lookup. -/
def edgeAngleContributionOfField (ℓ : EdgeField N) (e : PeriodicEdge N N N)
    (cellTet : PeriodicTet N N N) : ℝ :=
  match canonicalEdgeSlot? e cellTet.1 cellTet.2 with
  | some f => tetDihedralAngleOfField N ℓ cellTet f
  | none => 0

/-- Regge deficit angle at a periodic edge under an edge field:
`2π` minus the incident dihedral-angle sum. -/
def deficitOfField (ℓ : EdgeField N) (e : PeriodicEdge N N N) : ℝ :=
  2 * Real.pi -
    ∑ cellTet : PeriodicTet N N N, edgeAngleContributionOfField N ℓ e cellTet

/-- THE TRUE NONLINEAR 3D REGGE ACTION on the side-`N` periodic Freudenthal
torus, as a function of the edge squared-length field:
`S(ℓ) = Σ_e √(ℓ_e) · deficit_e`.  This is the object whose TT Bloch symbol
the C10 probe measured. -/
def trueReggeAction (ℓ : EdgeField N) : ℝ :=
  ∑ e : PeriodicEdge N N N, Real.sqrt (ℓ e) * deficitOfField N ℓ e

/-! ## §2. The flat point (b) — THEOREM -/

/-- At the flat field, every tetrahedron sees exactly the canonical
one-cube Freudenthal squared-edge tuple. -/
theorem tetSqEdgesOfField_flat (cellTet : PeriodicTet N N N) :
    tetSqEdgesOfField N (flatEdgeField N) cellTet =
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges := by
  funext f
  simp only [tetSqEdgesOfField, flatEdgeField]
  exact (freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf
    cellTet.1 cellTet.2 f).symm

/-- At the flat field, the per-tetrahedron angle contribution is exactly
the certified typed-edge angle contribution of the periodic angle-sum
chain. -/
theorem edgeAngleContributionOfField_flat (e : PeriodicEdge N N N)
    (cellTet : PeriodicTet N N N) :
    edgeAngleContributionOfField N (flatEdgeField N) e cellTet =
      canonicalPeriodicTypedEdgeAngleContribution e cellTet := by
  simp only [edgeAngleContributionOfField,
    canonicalPeriodicTypedEdgeAngleContribution]
  cases h : canonicalEdgeSlot? e cellTet.1 cellTet.2 with
  | none => rfl
  | some f =>
      simp only [tetDihedralAngleOfField, tetSqEdgesOfField_flat,
        freudenthalLocalDihedralAngle]

/-- FLAT POINT, deficit form (THEOREM): at the flat edge assignment every
deficit angle vanishes.  Reuses the certified periodic angle-sum chain
(`canonicalPeriodicDirectTypedEdgeAngleSumTarget_holds`); the geometry is
not re-derived here. -/
theorem deficitOfField_flatEdgeField (e : PeriodicEdge N N N) :
    deficitOfField N (flatEdgeField N) e = 0 := by
  unfold deficitOfField
  have hsum :
      (∑ cellTet : PeriodicTet N N N,
        edgeAngleContributionOfField N (flatEdgeField N) e cellTet) =
        2 * Real.pi := by
    calc
      (∑ cellTet : PeriodicTet N N N,
          edgeAngleContributionOfField N (flatEdgeField N) e cellTet)
          = ∑ cellTet : PeriodicTet N N N,
              canonicalPeriodicTypedEdgeAngleContribution e cellTet :=
        Finset.sum_congr rfl fun cellTet _ =>
          edgeAngleContributionOfField_flat N e cellTet
      _ = 2 * Real.pi :=
        canonicalPeriodicDirectTypedEdgeAngleSumTarget_holds N N N e
  rw [hsum]
  ring

/-- FLAT POINT, action form (THEOREM): the true Regge action vanishes at
the flat edge assignment. -/
theorem trueReggeAction_flatEdgeField :
    trueReggeAction N (flatEdgeField N) = 0 := by
  unfold trueReggeAction
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [deficitOfField_flatEdgeField N e, mul_zero]

/-! ## §3. The frozen-model identification (d) — THEOREM

The frozen wave (Test G, `FreudenthalStencilPreflight` /
`FreudenthalEnergyLimit`) analyzed `ReggeActionConcrete.reggeAction`, the
vertex-conformal restriction of the true action, with the graph-Laplacian
`canonicalReggeHessian` POSTULATED as its quadratic model.  The next
theorems state that identification as kernel equations. -/

/-- The conformal edge field induced by a vertex potential `u`: edge `e`
carries `ℓ²_flat(e) · exp(u(e₊) + u(e₋))`.  This is EXACTLY the family of
edge fields the frozen wave analyzed (through
`ReggeActionConcrete.conformalLocalSqEdge`). -/
def typedConformalEdgeField (u : Vertex N N N → ℝ) : EdgeField N :=
  fun e =>
    periodicDispSqEdge e.disp *
      Real.exp (u e.endpoints.1 + u e.endpoints.2)

theorem periodicDispSqEdge_nonneg (d : Fin 7) : 0 ≤ periodicDispSqEdge d := by
  fin_cases d <;> norm_num [periodicDispSqEdge]

/-- Definitional transparency of the canonical triangulation's local
tetrahedron (proof is `rfl`). -/
theorem canonical_tet_eq (τ : Fin (canonicalPeriodicTriangulation N N N).nT) :
    (canonicalPeriodicTriangulation N N N).tet τ =
      Geometry.FreudenthalCubeTriangulation.freudenthalTet := rfl

/-- Definitional transparency of the canonical triangulation's tetrahedron
vertex map (proof is `rfl`). -/
theorem canonical_tetVerts_eq
    (τ : Fin (canonicalPeriodicTriangulation N N N).nT) (k : Fin 4) :
    (canonicalPeriodicTriangulation N N N).tetVerts τ k =
      (vertexFinEquiv N N N).symm
        (addVertexBits (tetFinEquiv N N N τ).1
          (Geometry.FreudenthalCubeTriangulation.tetVerts
            (tetFinEquiv N N N τ).2 k)) := rfl

/-- Definitional transparency of the canonical triangulation's
edge-in-tetrahedron lookup (proof is `rfl`). -/
theorem canonical_edgeInTet_eq
    (e : Fin (canonicalPeriodicTriangulation N N N).nE)
    (τ : Fin (canonicalPeriodicTriangulation N N N).nT) :
    (canonicalPeriodicTriangulation N N N).edgeInTet e τ =
      canonicalEdgeSlot? (edgeFinEquiv N N N e)
        (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2 := rfl

/-- The conformal local squared-edge tuple of the frozen wave equals the
typed conformal edge field read through the local-edge tables. -/
theorem conformalTetSqEdges_eq_typedField (u : Vertex N N N → ℝ)
    (τ : Fin (canonicalPeriodicTriangulation N N N).nT) :
    conformalTetSqEdges (canonicalPeriodicTriangulation N N N)
        (toPotential N u) τ =
      tetSqEdgesOfField N (typedConformalEdgeField N u)
        (tetFinEquiv N N N τ) := by
  funext f
  simp only [conformalTetSqEdges, conformalLocalSqEdge, tetSqEdgesOfField,
    typedConformalEdgeField]
  rw [canonical_tet_eq, canonical_tetVerts_eq, canonical_tetVerts_eq,
    toPotential_symm_apply, toPotential_symm_apply]
  rw [show Geometry.FreudenthalCubeTriangulation.freudenthalTet.sqEdge f =
      periodicDispSqEdge
        ((localEdgeOf (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2
          f).disp) from
    freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf
      (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2 f]
  rcases localEdgeOf_endpoints_match_tetVerts
      (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2 f with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · have harg :
        u (addVertexBits (tetFinEquiv N N N τ).1
            (Geometry.FreudenthalCubeTriangulation.tetVerts
              (tetFinEquiv N N N τ).2
              (Geometry.ReggeRigorousFoundation.edgeVertices f).1)) +
          u (addVertexBits (tetFinEquiv N N N τ).1
            (Geometry.FreudenthalCubeTriangulation.tetVerts
              (tetFinEquiv N N N τ).2
              (Geometry.ReggeRigorousFoundation.edgeVertices f).2)) =
        u ((localEdgeOf (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2
            f).endpoints.1) +
          u ((localEdgeOf (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2
            f).endpoints.2) := by
      rw [h1, h2, add_comm]
    rw [harg]

/-- The frozen wave's deficit angle at a conformal potential equals the
true-action deficit at the corresponding conformal edge field. -/
theorem deficitAngle_conformal_eq (u : Vertex N N N → ℝ)
    (e : Fin (canonicalPeriodicTriangulation N N N).nE) :
    deficitAngle (canonicalPeriodicTriangulation N N N) (toPotential N u) e =
      deficitOfField N (typedConformalEdgeField N u)
        (edgeFinEquiv N N N e) := by
  unfold deficitAngle deficitOfField
  congr 1
  refine Fintype.sum_equiv (tetFinEquiv N N N) _ _ fun τ => ?_
  simp only [localDeficitAngleContribution, edgeAngleContributionOfField]
  rw [canonical_edgeInTet_eq]
  cases h : canonicalEdgeSlot? (edgeFinEquiv N N N e)
      (tetFinEquiv N N N τ).1 (tetFinEquiv N N N τ).2 with
  | none => rfl
  | some f =>
      simp only [tetDihedralAngleUnderConformal, tetDihedralAngleOfField,
        dihedralAngle3Sq]
      rw [conformalTetSqEdges_eq_typedField]

/-- The frozen wave's conformal hinge measure equals the square root of the
conformal edge field. -/
theorem hingeMeasure_conformal_eq (u : Vertex N N N → ℝ)
    (e : Fin (canonicalPeriodicTriangulation N N N).nE) :
    hingeMeasureUnderConformal (canonicalPeriodicTriangulation N N N)
        (canonicalPeriodicIncidenceConsistent N N N) (toPotential N u) e =
      Real.sqrt (typedConformalEdgeField N u (edgeFinEquiv N N N e)) := by
  simp only [hingeMeasureUnderConformal, typedConformalEdgeField]
  rw [canonical_edgeVerts_eq N e, canonical_globalSqEdge_eq N e]
  rw [Real.sqrt_mul (periodicDispSqEdge_nonneg _), ← Real.exp_half,
    toPotential_symm_apply, toPotential_symm_apply]

/-- FROZEN-MODEL IDENTIFICATION, part 1 (THEOREM): the conformal-ansatz
Regge action analyzed by the frozen wave is EXACTLY the true nonlinear
Regge action evaluated on the conformal edge fields.  This is the kernel
equation stating which restriction of the true action the frozen model
lives on. -/
theorem reggeAction_conformal_eq (u : Vertex N N N → ℝ) :
    reggeAction (canonicalPeriodicTriangulation N N N)
        (canonicalPeriodicIncidenceConsistent N N N) (toPotential N u) =
      trueReggeAction N (typedConformalEdgeField N u) := by
  unfold reggeAction trueReggeAction
  refine Fintype.sum_equiv (edgeFinEquiv N N N) _ _ fun e => ?_
  rw [hingeMeasure_conformal_eq, deficitAngle_conformal_eq]

/-- The zero potential induces the flat edge field. -/
theorem typedConformalEdgeField_zero :
    typedConformalEdgeField N (fun _ => 0) = flatEdgeField N := by
  funext e
  simp only [typedConformalEdgeField, flatEdgeField, add_zero,
    Real.exp_zero, mul_one]

/-- Flat normalization of the conformal action, derived here from the typed
flat point (no side-length hypothesis needed). -/
theorem reggeAction_zeroPotential_eq_zero :
    reggeAction (canonicalPeriodicTriangulation N N N)
        (canonicalPeriodicIncidenceConsistent N N N)
        (zeroPotential (canonicalPeriodicTriangulation N N N)) = 0 := by
  have h : toPotential N (fun _ => 0) =
      zeroPotential (canonicalPeriodicTriangulation N N N) := rfl
  rw [← h, reggeAction_conformal_eq, typedConformalEdgeField_zero,
    trueReggeAction_flatEdgeField]

/-- FROZEN-MODEL IDENTIFICATION, part 2 (THEOREM, but DEFINITIONALLY TRUE):
along the conformal family the true action decomposes as
`S = (1/2)·Q_frozen + remainder`, where `Q_frozen` is the quadratic form of
the frozen graph-Laplacian `canonicalReggeHessian`.  CONTENT WARNING: this
equation is a tautology — `reggeActionRemainder` is DEFINED as
`S − S(0) − (1/2)·Q`, so it holds for any quadratic form and pins nothing.
It exists only to name the frozen postulate and expose the remainder as the
object a later stage must expand.  The real (non-tautological) content is
`reggeAction_conformal_eq` (a genuine equality of two independently defined
actions) composed with `hessianQuadratic_canonical_eq_freudenthalStencil`
(Test G).  The identification that was FROZEN is: restrict to conformal edge
fields (real theorem) and POSTULATE `canonicalReggeHessian` as the quadratic
model (a postulate, not proved). -/
theorem frozen_identification (u : Vertex N N N → ℝ) :
    trueReggeAction N (typedConformalEdgeField N u) =
      (1 / 2) *
          hessianQuadratic
            (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
              (canonicalPeriodicIncidenceConsistent N N N))
            (toPotential N u) +
        reggeActionRemainder (canonicalPeriodicTriangulation N N N)
          (canonicalPeriodicIncidenceConsistent N N N)
          (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
            (canonicalPeriodicIncidenceConsistent N N N))
          (toPotential N u) := by
  rw [← reggeAction_conformal_eq]
  rw [reggeAction_taylor_decomposition (canonicalPeriodicTriangulation N N N)
    (canonicalPeriodicIncidenceConsistent N N N)
    (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
      (canonicalPeriodicIncidenceConsistent N N N))
    (toPotential N u)]
  rw [reggeAction_zeroPotential_eq_zero]
  ring

/-- FROZEN-MODEL IDENTIFICATION, stencil form (THEOREM, `N > 2`): the
frozen quadratic term along the conformal family is the anisotropic
seven-class stencil energy of Test G (whose continuum moment tensor is
`A₀ = (1+√2)I + (√2+√3)J`, `stencilMomentTensor_eq`).  The (numerically
observed) isotropic TT physics lives OUTSIDE this conformal family; the
frozen anisotropy is a statement about this restriction plus this quadratic
model, which is how the two coexist. -/
theorem frozen_identification_stencil (hN : 2 < N) (u : Vertex N N N → ℝ) :
    trueReggeAction N (typedConformalEdgeField N u) =
      (1 / 2) * freudenthalStencilEnergy N u +
        reggeActionRemainder (canonicalPeriodicTriangulation N N N)
          (canonicalPeriodicIncidenceConsistent N N N)
          (canonicalReggeHessian (canonicalPeriodicTriangulation N N N)
            (canonicalPeriodicIncidenceConsistent N N N))
          (toPotential N u) := by
  rw [frozen_identification N u,
    hessianQuadratic_canonical_eq_freudenthalStencil N hN u]

/-! ## §4. The TT Bloch symbol object (c) — DEFINITIONS ONLY

Everything in this section is a definition; no limit existence or value is
claimed.  The perturbation family, the midpoint Bloch-phase convention, the
per-unit-cell normalization `(2/N³)`, and the `|k|⁻²` momentum
normalization mirror the C10 preregistration
(`state/qg_full_theory/true_regge_tt_probe/`, commit f1d44266e5). -/

/-- Real coordinates of a periodic vertex (its representative in
`[0,N)³`). -/
def vertCoord (x : Vertex N N N) : Fin 3 → ℝ
  | 0 => (x.1.val : ℝ)
  | 1 => (x.2.1.val : ℝ)
  | 2 => (x.2.2.val : ℝ)

/-- Edge-class coefficient of a polarization matrix:
`c_d = Σ_{ij} E_ij · D_d^i · D_d^j` (how a metric perturbation `E` loads
the squared length of displacement class `d`). -/
def polEdgeCoeff (E : Fin 3 → Fin 3 → ℝ) (d : Fin 7) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, E i j * dispReal d i * dispReal d j

/-- Commensurate momentum of an integer wave vector on the side-`N` torus:
`k = 2π·m/N`. -/
def commensurateMomentum (m : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun i => 2 * Real.pi * (m i : ℝ) / (N : ℝ)

/-- Midpoint Bloch phase of a periodic edge: `k · (x + D_d/2)` (the
preregistered midpoint convention of the C10 probe). -/
def edgeMidpointPhase (k : Fin 3 → ℝ) (e : PeriodicEdge N N N) : ℝ :=
  ∑ i : Fin 3, k i * (vertCoord N e.base i + dispReal e.disp i / 2)

/-- The plane-wave perturbation family at amplitude `t`:
`ℓ_e(t) = ℓ²_flat(e) + t · c_d · cos(k·(x + D_d/2))`. -/
def planeWaveEdgeField (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) (t : ℝ) :
    EdgeField N :=
  fun e =>
    periodicDispSqEdge e.disp +
      t * polEdgeCoeff E e.disp * Real.cos (edgeMidpointPhase N k e)

/-- The action along the plane-wave family, as a function of the
amplitude. -/
def planeWaveActionProfile (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (t : ℝ) : ℝ :=
  trueReggeAction N (planeWaveEdgeField N E k t)

/-- Per-unit-cell second-difference quadratic form of the true action along
the plane-wave family at amplitude `t`:
`(2/N³) · (S(t) − 2·S(0) + S(−t)) / t²`.  The `(2/N³)` normalization makes
this the per-unit-cell Bloch quadratic form in the C10 conventions. -/
def ttSecondDifference (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (2 / (N : ℝ) ^ (3 : ℕ)) *
    (planeWaveActionProfile N E k t - 2 * planeWaveActionProfile N E k 0 +
      planeWaveActionProfile N E k (-t)) / t ^ (2 : ℕ)

/-- The TT Bloch symbol VALUE PREDICATE at side `N`, polarization `E`, and
integer wave vector `m`: the amplitude second difference converges to `H`
as the amplitude tends to `0` (punctured-neighborhood limit).  DEFINITION
ONLY; existence is not claimed anywhere in this file. -/
def TTBlochSymbolIs (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) (H : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => ttSecondDifference N E (commensurateMomentum N m) t)
    (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds H)

/-- Squared norm of the commensurate momentum, `|2π·m/N|²`. -/
def momentumNormSq (m : Fin 3 → ℤ) : ℝ :=
  ∑ i : Fin 3, commensurateMomentum N m i ^ (2 : ℕ)

instance instNeZeroAddThree (j : ℕ) : NeZero (j + 3) := ⟨by omega⟩

/-- THE CONTINUUM TT SYMBOL VALUE PREDICATE (`ReggeTTContinuumSymbol`
program target object): `Λ` is the continuum TT Bloch symbol coefficient
for polarization `E` and integer wave vector `m` when there are per-torus
symbol values `H j` at sides `N = j + 3` (so `k_N = 2π·m/N → 0` at fixed
direction) whose `|k_N|²`-normalized values converge to `Λ`.  DEFINITION
ONLY: neither existence of the `H j` nor convergence is claimed in this
file; the C10 numerics supporting `Λ = -(1/4)` for TT polarizations remain
NUMERICAL EVIDENCE. -/
def ReggeTTContinuumSymbolIs (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (Λ : ℝ) : Prop :=
  ∃ H : ℕ → ℝ,
    (∀ j : ℕ, TTBlochSymbolIs (j + 3) E m (H j)) ∧
      Filter.Tendsto (fun j : ℕ => H j / momentumNormSq (j + 3) m)
        Filter.atTop (nhds Λ)

/-- TT polarization for the integer wave vector `m`: symmetric, traceless,
transverse to `m`, Frobenius-normalized. -/
def IsTTPolarization (m : Fin 3 → ℤ) (E : Fin 3 → Fin 3 → ℝ) : Prop :=
  (∀ i j : Fin 3, E i j = E j i) ∧
    (∑ i : Fin 3, E i i) = 0 ∧
    (∀ j : Fin 3, (∑ i : Fin 3, (m i : ℝ) * E i j) = 0) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, E i j * E i j) = 1

/-- The exact continuum coefficient reported by the C10 probe: `-(1/4)`,
which is the linearized Einstein-Hilbert TT coefficient of
`Σ ℓ·δ = (1/2)∫√g R` in these conventions.  The VALUE of this constant is
a definition; that the symbol ATTAINS it is the OPEN target below. -/
def reggeTTContinuumCoefficient : ℝ := -(1 / 4)

/-- **OPEN TARGET** (named, NOT proved, status flag `false`): for every
nonzero integer wave vector and every TT polarization, the continuum TT
Bloch symbol of the true Regge action exists and equals `-(1/4)` — i.e.
the symbol is isotropic with exactly the linearized Einstein-Hilbert TT
coefficient.  Supporting evidence is NUMERICAL ONLY (C10 probe, commit
f1d44266e5; critic sign-off 1e38531ee2: isotropy on all 14 preregistered
directions and exact `-1/4` identification).  Closing this Prop is the
`ReggeTTContinuumSymbol` program's kernel goal. -/
def ReggeTTContinuumIsotropyTarget : Prop :=
  ∀ (m : Fin 3 → ℤ) (E : Fin 3 → Fin 3 → ℝ),
    m ≠ 0 → IsTTPolarization m E →
      ReggeTTContinuumSymbolIs E m reggeTTContinuumCoefficient

/-! ## §5. Well-formedness and symmetry of the symbol object (d) — THEOREM -/

/-- At amplitude `0` the plane-wave family sits at the flat field. -/
theorem planeWaveEdgeField_zero_amplitude (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    planeWaveEdgeField N E k 0 = flatEdgeField N := by
  funext e
  simp only [planeWaveEdgeField, flatEdgeField, zero_mul, add_zero]

/-- The action profile vanishes at amplitude `0` (flat point of the
family). -/
theorem planeWaveActionProfile_zero (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    planeWaveActionProfile N E k 0 = 0 := by
  unfold planeWaveActionProfile
  rw [planeWaveEdgeField_zero_amplitude, trueReggeAction_flatEdgeField]

/-- The second-difference quadratic form is even in the amplitude. -/
theorem ttSecondDifference_even (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (t : ℝ) :
    ttSecondDifference N E k (-t) = ttSecondDifference N E k t := by
  unfold ttSecondDifference
  rw [neg_neg, neg_sq]
  ring

/-- Negating the polarization negates every edge-class coefficient. -/
theorem polEdgeCoeff_neg (E : Fin 3 → Fin 3 → ℝ) (d : Fin 7) :
    polEdgeCoeff (fun i j => -E i j) d = -polEdgeCoeff E d := by
  unfold polEdgeCoeff
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Negating the polarization is the same as negating the amplitude. -/
theorem planeWaveEdgeField_neg_polarization (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t : ℝ) :
    planeWaveEdgeField N (fun i j => -E i j) k t =
      planeWaveEdgeField N E k (-t) := by
  funext e
  simp only [planeWaveEdgeField]
  rw [polEdgeCoeff_neg]
  ring

/-- Sign symmetry of the symbol object (THEOREM): the second-difference
quadratic form is invariant under `E ↦ −E`, as a quadratic form must
be. -/
theorem ttSecondDifference_neg_polarization (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t : ℝ) :
    ttSecondDifference N (fun i j => -E i j) k t =
      ttSecondDifference N E k t := by
  unfold ttSecondDifference planeWaveActionProfile
  rw [planeWaveEdgeField_neg_polarization,
    planeWaveEdgeField_neg_polarization,
    planeWaveEdgeField_neg_polarization, neg_neg, neg_zero]
  ring

/-! ## §6. Non-vacuity of the TT constraint set — THEOREM

The OPEN target quantifies over `IsTTPolarization`; these witnesses prove
the constraint set is nonempty for the preregistered axis direction, so the
target is not vacuously closable. -/

/-- The axis integer wave vector `(1,0,0)`. -/
def axisWaveVector : Fin 3 → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0

/-- The `+`-polarization for the axis direction:
`diag(0, 1/√2, −1/√2)` (the C10 deterministic TT frame gives this pair up
to sign), as an explicit entry table. -/
def axisTTPolarizationPlus : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => 1 / Real.sqrt 2 | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => -(1 / Real.sqrt 2)

/-- The `×`-polarization for the axis direction: symmetric off-diagonal
block on the transverse plane with entries `1/√2`, as an explicit entry
table. -/
def axisTTPolarizationCross : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => 0 | 1, 2 => 1 / Real.sqrt 2
  | 2, 0 => 0 | 2, 1 => 1 / Real.sqrt 2 | 2, 2 => 0

theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem inv_sqrt_two_sq : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul, sqrt_two_mul_self]

/-- The `+`-witness is a TT polarization for the axis wave vector. -/
theorem axisTTPolarizationPlus_isTT :
    IsTTPolarization axisWaveVector axisTTPolarizationPlus := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [axisTTPolarizationPlus]
  · simp only [Fin.sum_univ_three, axisTTPolarizationPlus]
    ring
  · intro j
    fin_cases j <;>
      · simp only [Fin.sum_univ_three, axisTTPolarizationPlus,
          axisWaveVector]
        push_cast
        ring
  · simp only [Fin.sum_univ_three, axisTTPolarizationPlus]
    linear_combination 2 * inv_sqrt_two_sq

/-- The `×`-witness is a TT polarization for the axis wave vector. -/
theorem axisTTPolarizationCross_isTT :
    IsTTPolarization axisWaveVector axisTTPolarizationCross := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [axisTTPolarizationCross]
  · simp only [Fin.sum_univ_three, axisTTPolarizationCross]
    ring
  · intro j
    fin_cases j <;>
      · simp only [Fin.sum_univ_three, axisTTPolarizationCross,
          axisWaveVector]
        push_cast
        ring
  · simp only [Fin.sum_univ_three, axisTTPolarizationCross]
    linear_combination 2 * inv_sqrt_two_sq

/-- The axis wave vector is nonzero (so the witnesses instantiate the OPEN
target's hypotheses non-vacuously). -/
theorem axisWaveVector_ne_zero : axisWaveVector ≠ 0 := by
  intro h
  have h0 : axisWaveVector 0 = 0 := by rw [h]; rfl
  simp only [axisWaveVector] at h0
  exact one_ne_zero h0

/-! ## §7. Status flags (documentation record) -/

/-- Status flags for the Regge TT symbol preflight (PROTOCOL RECORD,
documentation only; the mathematics lives in the theorems, see
`status_flags_grounded`).

Honest scope: this stage-1 record certifies the true-action definition,
its kernel-checked flat point, the exact frozen-model identification along
the conformal family, the well-formedness/symmetry lemmas of the TT Bloch
symbol object, and the non-vacuity of the TT constraint set.  The
continuum symbol VALUE flag is `false`: `ReggeTTContinuumIsotropyTarget`
is OPEN, and the C10 isotropy/`-1/4` result is NUMERICAL EVIDENCE only. -/
structure ReggeTTSymbolPreflightStatus where
  /-- `deficitOfField_flatEdgeField`: all deficits vanish at flat. -/
  flat_deficit_zero : Bool
  /-- `trueReggeAction_flatEdgeField`: the true action vanishes at flat. -/
  flat_action_zero : Bool
  /-- Grounded in `reggeAction_conformal_eq` (the REAL content: the frozen
  conformal-ansatz action equals the true action on conformal fields), which
  is exactly what `status_flags_grounded` certifies for this flag.  The
  companion `frozen_identification(_stencil)` decomposition is a definitional
  tautology (see its docstring) and does NOT ground this flag. -/
  frozen_identification_proved : Bool
  /-- `ttSecondDifference_even` + `ttSecondDifference_neg_polarization` +
  `planeWaveActionProfile_zero`: symbol-object well-formedness. -/
  symbol_object_symmetries : Bool
  /-- `axisTTPolarizationPlus_isTT` + `axisTTPolarizationCross_isTT` +
  `axisWaveVector_ne_zero`: the TT constraint set is nonempty. -/
  tt_constraint_set_nonvacuous : Bool
  /-- `ReggeTTContinuumIsotropyTarget` is OPEN.  MUST stay `false` until a
  kernel proof of the continuum symbol value exists; the C10 numerics are
  NUMERICAL EVIDENCE and cannot flip this flag. -/
  continuum_symbol_value_proved : Bool

/-- The canonical status record.  Every `true` flag is grounded in its
kernel theorem by `status_flags_grounded`; the continuum-value flag is
`false` (OPEN). -/
def reggeTTSymbolPreflightStatus : ReggeTTSymbolPreflightStatus where
  flat_deficit_zero := true
  flat_action_zero := true
  frozen_identification_proved := true
  symbol_object_symmetries := true
  tt_constraint_set_nonvacuous := true
  continuum_symbol_value_proved := false

/-- The status flags are not bare Booleans: each `true` flag is tied to its
kernel theorem (here instantiated at `N = 3`, the smallest torus the
campaign uses; the theorems themselves hold for every `N`), and the OPEN
flag is pinned to `false`. -/
theorem status_flags_grounded :
    (reggeTTSymbolPreflightStatus.flat_deficit_zero = true ∧
      ∀ e : PeriodicEdge 3 3 3, deficitOfField 3 (flatEdgeField 3) e = 0) ∧
    (reggeTTSymbolPreflightStatus.flat_action_zero = true ∧
      trueReggeAction 3 (flatEdgeField 3) = 0) ∧
    (reggeTTSymbolPreflightStatus.frozen_identification_proved = true ∧
      ∀ u : Vertex 3 3 3 → ℝ,
        reggeAction (canonicalPeriodicTriangulation 3 3 3)
            (canonicalPeriodicIncidenceConsistent 3 3 3)
            (toPotential 3 u) =
          trueReggeAction 3 (typedConformalEdgeField 3 u)) ∧
    (reggeTTSymbolPreflightStatus.symbol_object_symmetries = true ∧
      ∀ (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) (t : ℝ),
        ttSecondDifference 3 E k (-t) = ttSecondDifference 3 E k t) ∧
    (reggeTTSymbolPreflightStatus.tt_constraint_set_nonvacuous = true ∧
      IsTTPolarization axisWaveVector axisTTPolarizationPlus) ∧
    reggeTTSymbolPreflightStatus.continuum_symbol_value_proved = false :=
  ⟨⟨rfl, deficitOfField_flatEdgeField 3⟩,
    ⟨rfl, trueReggeAction_flatEdgeField 3⟩,
    ⟨rfl, fun u => reggeAction_conformal_eq 3 u⟩,
    ⟨rfl, fun E k t => ttSecondDifference_even 3 E k t⟩,
    ⟨rfl, axisTTPolarizationPlus_isTT⟩,
    rfl⟩

end

end ReggeTTSymbolPreflight
end Analysis
end Gravity
end IndisputableMonolith
