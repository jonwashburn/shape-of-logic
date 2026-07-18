import IndisputableMonolith.Gravity.Analysis.ReggeTTSymbolPreflight

/-!
# Regge TT derivative gate: Stage-2 Gate-0 / Lane-A of `ReggeTTContinuumSymbol`

QG full-theory campaign, `ReggeTTContinuumSymbol` program, Stage 2
(Gate 0 + Lane A of the panel-locked two-lane protocol; Stage 1 is
`ReggeTTSymbolPreflight`).

## Tier tags (binding, per-claim)

* THEOREM: everything proved in this file (kernel-checked here; no sorry, no
  admit, no new axioms, no native_decide, no `: True` shells, no
  Nonempty-only shells).
* NUMERICAL EVIDENCE (never proof): the continuum TT symbol value `-(1/4)`
  remains exactly where Stage 1 left it — supported only by the C10
  provenance-gated numerics probe.  NOTHING in this file proves, or even
  approaches, the continuum value; `ReggeTTContinuumIsotropyTarget` stays
  OPEN with status flag `false` in Stage 1.
* OPEN: the continuum TT symbol existence and value; also second-derivative
  existence of the plane-wave action profile (stage 2a), which this file
  does NOT prove — Lane A here delivers only FIRST-derivative structure at
  the flat point of a single tetrahedron plus the flat-neighborhood
  nondegeneracy that stage 2a will need.

## What this module proves (all THEOREM)

* Gate 0a (`planeWaveActionProfile_eq_trueReggeAction`): the plane-wave
  action profile is BY DEFINITION the true nonlinear Regge action on the
  plane-wave edge field — kernel equation, no surrogate action anywhere.
* Gate 0b (`ttPolarization_frobeniusSq_eq_one`,
  `isTTPolarization_of_orthonormal_transverse_pair`,
  `exists_isTTPolarization`, `exists_isTTPolarization_of_ne_zero`): the
  Frobenius normalization is projected out of `IsTTPolarization` as a named
  lemma, and the TT constraint set is nonempty for EVERY integer wave
  vector (a fortiori every nonzero one), by an explicit Gram-Schmidt-style
  transverse frame with a planar/axial case split — not axis-only.
* Gate 0c (`flatAngleJacobian`, `flatSqrtEdgeDeriv`, `flatReggeStencilMoment`,
  `stencil_ordering_grounded`): the SHARED NAMED STENCIL both lanes must
  reference — the flat tuple `freudenthalTetSqEdges` (proved in Stage 1 to
  be exactly what every tetrahedron of the action sees at flat, re-exported
  here as `stencil_ordering_grounded`), the closed-form flat angle Jacobian
  `∂θ_f/∂a_k`, and the flat sqrt-edge derivatives `1/(2√a_f)`.
* Lane A1 (`flat_nondegeneracy_eventually`): an open neighborhood of the
  flat tuple (stated as a `∀ᶠ` in `nhds`) on which `cm3 > 0`, all six
  squared edges are positive, all diagonal cofactor products are positive,
  and every dihedral cosine lies strictly inside `(-1, 1)`.
* Lane A2 (`hasDerivAt_flatAngle_directional`,
  `hasDerivAt_flatWeightedAngleSum`): along every affine squared-edge
  direction `v` through the flat tuple, each dihedral angle is
  differentiable with directional derivative `∑_k v_k · J_{f,k}`, and the
  per-tetrahedron weighted angle sum `g(a) = ∑_f √a_f · θ_f(a)` is
  differentiable at flat with derivative `∑_f (v_f/(2√a_f)) · θ_f` — the
  `θ'`-terms cancel EXACTLY by the proved tetrahedral Schläfli identity
  (`flatAngleJacobian_schlaefli`), not by any numerical argument.
* Lane A3 (`flatArccosFactor_spec`, `flatAngleJacobian_cofactor_form`,
  `flatAngleJacobian_row0_norm`, `flatAngleJacobian_row0_eval`): every row
  of the flat angle Jacobian is pure cofactor algebra times an exactly
  evaluated arccos factor (√2, 1, 2/√3, 1, 1, √2 — zero arccos values
  anywhere), and the `f = 0` row is fully evaluated to exact rationals
  `(0, 0, 0, 0, -1/4, 1/2)`.

## What this module does NOT prove (binding scope disclosure)

* No second derivatives: stage 2a (second-derivative existence of the
  plane-wave profile) is NOT attempted here.
* No lattice sum: everything in Lane A is per-tetrahedron at the flat
  point; the assembly over the periodic torus is later-stage work.
* No symbol limits, no continuum value, no isotropy: `-(1/4)` remains
  NUMERICAL EVIDENCE (C10 probe) and `ReggeTTContinuumIsotropyTarget`
  remains OPEN.

## Inherited axiom footprint (disclosure)

This file never touches the certified periodic angle-sum chain, so nothing
here inherits `Lean.ofReduceBool` / `Lean.trustCompiler`.  Every theorem in
this file is pure algebra/analysis over the standard trio
`[propext, Classical.choice, Quot.sound]` (Gate 0a is a kernel `rfl` on the
Stage-1 definitions; the Schläfli input `tetraSchlaefliSixEdgeClosedForm`
and the bridge `schlaefli_summand_bridge_edge0` are pure-algebra theorems
with the standard footprint).

No `sorry`, no `admit`, no new axioms, no `native_decide` in this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTDerivativeGate

open Geometry.CayleyMengerPolynomial (SqEdges cm3)
open Geometry.CayleyMengerMatrix (cmCofactor3 cmCofactor3_contDiff)
open Geometry.DihedralCayleyMenger (dihedralCos3Sq dihedralDenom3 oppositeCMVertices)
open Geometry.DihedralDerivatives (dihedralAngle3Sq dihedralAngle3SqClosedFormDeriv)
open Geometry.FreudenthalCubeTriangulation (freudenthalTetSqEdges freudenthalTet
  cm3_freudenthalTetSqEdges)

noncomputable section

/-! ## §1. Gate 0a — the profile IS the true action (THEOREM, kernel `rfl`)

The C10 observable is the second difference of `planeWaveActionProfile`.
This theorem pins, as a kernel equation, that the profile is the TRUE
nonlinear Regge action `S(ℓ) = Σ_e √ℓ_e·(2π − Σθ)` evaluated on the
plane-wave edge field — there is no linearized or surrogate action anywhere
in the symbol object. -/

theorem planeWaveActionProfile_eq_trueReggeAction
    (N : ℕ) [NeZero N] (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) (t : ℝ) :
    ReggeTTSymbolPreflight.planeWaveActionProfile N E k t =
      ReggeTTSymbolPreflight.trueReggeAction N
        (ReggeTTSymbolPreflight.planeWaveEdgeField N E k t) := rfl

/-! ## §2. Gate 0b — TT audit and non-vacuity for every wave vector

`IsTTPolarization` bundles symmetry, tracelessness, transversality, and
Frobenius normalization.  The normalization is projected out as a named
lemma, and the constraint set is proved nonempty for EVERY integer wave
vector by an explicit orthonormal transverse frame (planar/axial case
split), strengthening the Stage-1 axis-only witnesses. -/

/-- The fourth `IsTTPolarization` conjunct as a named audit lemma: every TT
polarization has Frobenius norm square exactly `1`. -/
theorem ttPolarization_frobeniusSq_eq_one (m : Fin 3 → ℤ) (E : Fin 3 → Fin 3 → ℝ)
    (hE : ReggeTTSymbolPreflight.IsTTPolarization m E) :
    (∑ i : Fin 3, ∑ j : Fin 3, E i j * E i j) = 1 := hE.2.2.2

private theorem sum3_div_sq (x y z c : ℝ) (hc : 0 < c) (h : x ^ 2 + y ^ 2 + z ^ 2 = c) :
    x / Real.sqrt c * (x / Real.sqrt c) + y / Real.sqrt c * (y / Real.sqrt c) +
      z / Real.sqrt c * (z / Real.sqrt c) = 1 := by
  have hcs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, hcs,
    ← add_div, ← add_div,
    show x * x + y * y + z * z = c by linear_combination h]
  exact div_self (ne_of_gt hc)

private theorem sum3_div_orth (x y z x' y' z' c d : ℝ)
    (h : x * x' + y * y' + z * z' = 0) :
    x / c * (x' / d) + y / c * (y' / d) + z / c * (z' / d) = 0 := by
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
    ← add_div, ← add_div, h, zero_div]

private theorem sum3_dot_div (a b c x y z r : ℝ) (h : a * x + b * y + c * z = 0) :
    a * (x / r) + b * (y / r) + c * (z / r) = 0 := by
  rw [← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc,
    ← add_div, ← add_div, h, zero_div]

/-- TT polarization from an orthonormal transverse pair: if `u, v` are unit
vectors, mutually orthogonal, and both orthogonal to the (real cast of the)
integer wave vector `m`, then `E = (u⊗u − v⊗v)/√2` is a TT polarization for
`m`.  This is the generic Gram-Schmidt-style constructor behind the
non-vacuity theorem. -/
theorem isTTPolarization_of_orthonormal_transverse_pair
    (m : Fin 3 → ℤ) (u v : Fin 3 → ℝ)
    (hu : (∑ i : Fin 3, u i * u i) = 1)
    (hv : (∑ i : Fin 3, v i * v i) = 1)
    (huv : (∑ i : Fin 3, u i * v i) = 0)
    (hmu : (∑ i : Fin 3, (m i : ℝ) * u i) = 0)
    (hmv : (∑ i : Fin 3, (m i : ℝ) * v i) = 0) :
    ReggeTTSymbolPreflight.IsTTPolarization m
      (fun i j => (u i * u j - v i * v j) / Real.sqrt 2) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hhalf : ∀ x : ℝ,
      x / Real.sqrt 2 * (x / Real.sqrt 2) = x ^ 2 / 2 := by
    intro x
    rw [div_mul_div_comm, hs2]
    ring
  simp only [Fin.sum_univ_three] at hu hv huv hmu hmv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    dsimp only
    ring
  · simp only [Fin.sum_univ_three]
    linear_combination (1 / Real.sqrt 2) * hu - (1 / Real.sqrt 2) * hv
  · intro j
    simp only [Fin.sum_univ_three]
    linear_combination (u j / Real.sqrt 2) * hmu - (v j / Real.sqrt 2) * hmv
  · simp only [Fin.sum_univ_three, hhalf]
    linear_combination
      ((u 0 * u 0 + u 1 * u 1 + u 2 * u 2 + 1) / 2) * hu +
        ((v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + 1) / 2) * hv -
        (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) * huv

/-- First transverse unit vector for a wave vector with nonzero planar part
`(m₀, m₁)`: the normalized in-plane rotation `(−m₁, m₀, 0)/√(m₀²+m₁²)`. -/
def planarTransverse1 (m : Fin 3 → ℤ) : Fin 3 → ℝ
  | 0 => -(m 1 : ℝ) / Real.sqrt ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2)
  | 1 => (m 0 : ℝ) / Real.sqrt ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2)
  | 2 => 0 / Real.sqrt ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2)

/-- Second transverse unit vector: the normalized cross product
`m × (−m₁, m₀, 0) = (−m₀m₂, −m₁m₂, m₀²+m₁²)`, with norm
`√((m₀²+m₁²)·|m|²)`. -/
def planarTransverse2 (m : Fin 3 → ℤ) : Fin 3 → ℝ
  | 0 => -((m 0 : ℝ) * (m 2 : ℝ)) /
      Real.sqrt (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) *
        (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) + (m 2 : ℝ) ^ 2))
  | 1 => -((m 1 : ℝ) * (m 2 : ℝ)) /
      Real.sqrt (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) *
        (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) + (m 2 : ℝ) ^ 2))
  | 2 => ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) /
      Real.sqrt (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) *
        (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) + (m 2 : ℝ) ^ 2))

/-- Axial fallback frame (used when `m₀ = m₁ = 0`): the x-axis unit vector. -/
def axialTransverse1 : Fin 3 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

/-- Axial fallback frame (used when `m₀ = m₁ = 0`): the y-axis unit vector. -/
def axialTransverse2 : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0

/-- GATE 0b NON-VACUITY (THEOREM), general form: EVERY integer wave vector
(zero included) carries a TT polarization, built from an explicit
orthonormal transverse frame — planar rotation + cross product when
`(m₀, m₁) ≠ 0`, the axial `x/y` frame when `m₀ = m₁ = 0`.  No axis-only
weakening anywhere. -/
theorem exists_isTTPolarization (m : Fin 3 → ℤ) :
    ∃ E : Fin 3 → Fin 3 → ℝ, ReggeTTSymbolPreflight.IsTTPolarization m E := by
  by_cases h01 : (m 0 : ℝ) = 0 ∧ (m 1 : ℝ) = 0
  · refine ⟨_, isTTPolarization_of_orthonormal_transverse_pair m
      axialTransverse1 axialTransverse2 ?_ ?_ ?_ ?_ ?_⟩ <;>
      simp [axialTransverse1, axialTransverse2, Fin.sum_univ_three, h01.1, h01.2]
  · have h01' : (m 0 : ℝ) ≠ 0 ∨ (m 1 : ℝ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact h01 ⟨h.1, h.2⟩
    have hs : 0 < (m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 := by
      rcases h01' with h | h
      · have h0 : 0 < (m 0 : ℝ) ^ 2 := by positivity
        nlinarith [sq_nonneg ((m 1 : ℝ))]
      · have h1 : 0 < (m 1 : ℝ) ^ 2 := by positivity
        nlinarith [sq_nonneg ((m 0 : ℝ))]
    have hn : 0 < ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) + (m 2 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((m 2 : ℝ))]
    have hsn : 0 < ((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) *
        (((m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2) + (m 2 : ℝ) ^ 2) := mul_pos hs hn
    refine ⟨_, isTTPolarization_of_orthonormal_transverse_pair m
      (planarTransverse1 m) (planarTransverse2 m) ?_ ?_ ?_ ?_ ?_⟩
    · simp only [planarTransverse1, Fin.sum_univ_three]
      exact sum3_div_sq _ _ _ _ hs (by ring)
    · simp only [planarTransverse2, Fin.sum_univ_three]
      exact sum3_div_sq _ _ _ _ hsn (by ring)
    · simp only [planarTransverse1, planarTransverse2, Fin.sum_univ_three]
      exact sum3_div_orth _ _ _ _ _ _ _ _ (by ring)
    · simp only [planarTransverse1, Fin.sum_univ_three]
      exact sum3_dot_div _ _ _ _ _ _ _ (by ring)
    · simp only [planarTransverse2, Fin.sum_univ_three]
      exact sum3_dot_div _ _ _ _ _ _ _ (by ring)

/-- GATE 0b NON-VACUITY, panel-locked form: every NONZERO integer wave
vector carries a TT polarization. -/
theorem exists_isTTPolarization_of_ne_zero (m : Fin 3 → ℤ) (_hm : m ≠ 0) :
    ∃ E : Fin 3 → Fin 3 → ℝ, ReggeTTSymbolPreflight.IsTTPolarization m E :=
  exists_isTTPolarization m

/-! ## §3. Gate 0c — the SHARED NAMED STENCIL

Both lanes of the Stage-2 protocol must reference these objects BY NAME;
this structurally prevents transcription drift between the Lean lane and
the numerics lane.  The per-tet objects are: the flat squared-edge tuple
`freudenthalTetSqEdges = (1,2,3,1,2,1)` (in the action's actual local
six-edge ordering — Stage 1's `tetSqEdgesOfField_flat` proves every
tetrahedron of the true action sees exactly this tuple at flat, re-exported
below), the flat angle Jacobian `∂θ_f/∂a_k`, and the flat sqrt-edge
derivatives `1/(2√a_f)`. -/

/-- THE SHARED STENCIL JACOBIAN: closed-form derivative of the `f`-th local
dihedral angle with respect to the `k`-th local squared-edge coordinate,
evaluated at the flat Freudenthal tuple, in the action's local six-edge
ordering.  `flatAngleJacobian f k = ∂θ_f/∂a_k (freudenthalTetSqEdges)`. -/
def flatAngleJacobian (f k : Fin 6) : ℝ :=
  dihedralAngle3SqClosedFormDeriv freudenthalTetSqEdges f k

/-- THE SHARED STENCIL SQRT DERIVATIVES: `d√a/da` at the flat tuple,
`flatSqrtEdgeDeriv f = 1/(2√(a_f))` with `a = freudenthalTetSqEdges`. -/
def flatSqrtEdgeDeriv (f : Fin 6) : ℝ :=
  1 / (2 * Real.sqrt (freudenthalTetSqEdges f))

/-- The per-tetrahedron flat second-variation stencil data: flat tuple,
angle Jacobian, sqrt-edge derivatives.  Lane B's numerics script mirrors
exactly these three named objects. -/
structure FlatReggeStencil where
  /-- The flat local squared-edge tuple. -/
  sqEdges : SqEdges
  /-- The flat angle Jacobian `∂θ_f/∂a_k`. -/
  angleJacobian : Fin 6 → Fin 6 → ℝ
  /-- The flat sqrt-edge derivatives `1/(2√a_f)`. -/
  sqrtEdgeDeriv : Fin 6 → ℝ

/-- THE SHARED NAMED STENCIL (Gate 0c deliverable): the canonical per-tet
stencil moment object at the flat Freudenthal point. -/
def flatReggeStencilMoment : FlatReggeStencil where
  sqEdges := freudenthalTetSqEdges
  angleJacobian := flatAngleJacobian
  sqrtEdgeDeriv := flatSqrtEdgeDeriv

/-- Ordering grounding: at the flat edge field, every tetrahedron of the
TRUE action sees exactly the stencil's flat tuple (re-export of Stage 1's
`tetSqEdgesOfField_flat` in stencil vocabulary, so the stencil ordering and
the action's local ordering are kernel-identified). -/
theorem stencil_ordering_grounded (N : ℕ) [NeZero N]
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet N N N) :
    ReggeTTSymbolPreflight.tetSqEdgesOfField N
        (ReggeTTSymbolPreflight.flatEdgeField N) cellTet =
      flatReggeStencilMoment.sqEdges :=
  ReggeTTSymbolPreflight.tetSqEdgesOfField_flat N cellTet

/-- The stencil sqrt-edge derivative is the actual derivative of
`Real.sqrt` at the flat squared edge (the edges are positive, so `sqrt` is
differentiable there). -/
theorem hasDerivAt_sqrt_flatEdge (f : Fin 6) :
    HasDerivAt Real.sqrt (flatSqrtEdgeDeriv f) (freudenthalTetSqEdges f) :=
  Real.hasDerivAt_sqrt (ne_of_gt (freudenthalTet.sqEdge_pos f))

/-! ## §4. Exact flat cosine values and endpoint freedom

The six flat dihedral cosines are exactly `√2/2, 0, 1/2, 0, 0, √2/2`
(Stage-1 `freudenthalLocalDihedralCos_eq`), all strictly inside `(-1, 1)`.
These are the arccos endpoint-freedom facts every derivative below needs. -/

/-- Exact flat cosine at local edge slot `0`. -/
theorem flatCos₀ : dihedralCos3Sq freudenthalTetSqEdges 0 = Real.sqrt 2 / 2 :=
  PhysicalSixTetCubicDirichletInstance.freudenthalLocalDihedralCos_eq 0

/-- Exact flat cosine at local edge slot `1`. -/
theorem flatCos₁ : dihedralCos3Sq freudenthalTetSqEdges 1 = 0 :=
  PhysicalSixTetCubicDirichletInstance.freudenthalLocalDihedralCos_eq 1

/-- Exact flat cosine at local edge slot `2`. -/
theorem flatCos₂ : dihedralCos3Sq freudenthalTetSqEdges 2 = 1 / 2 :=
  PhysicalSixTetCubicDirichletInstance.freudenthalLocalDihedralCos_eq 2

/-- Exact flat cosine at local edge slot `3`. -/
theorem flatCos₃ : dihedralCos3Sq freudenthalTetSqEdges 3 = 0 :=
  PhysicalSixTetCubicDirichletInstance.freudenthalLocalDihedralCos_eq 3

/-- Exact flat cosine at local edge slot `4`. -/
theorem flatCos₄ : dihedralCos3Sq freudenthalTetSqEdges 4 = 0 :=
  PhysicalSixTetCubicDirichletInstance.freudenthalLocalDihedralCos_eq 4

/-- Exact flat cosine at local edge slot `5`. -/
theorem flatCos₅ : dihedralCos3Sq freudenthalTetSqEdges 5 = Real.sqrt 2 / 2 :=
  PhysicalSixTetCubicDirichletInstance.freudenthalLocalDihedralCos_eq 5

/-- Every flat cosine is one of the three exact values `√2/2, 0, 1/2`. -/
theorem flatCos_value_cases (f : Fin 6) :
    dihedralCos3Sq freudenthalTetSqEdges f = Real.sqrt 2 / 2 ∨
      dihedralCos3Sq freudenthalTetSqEdges f = 0 ∨
      dihedralCos3Sq freudenthalTetSqEdges f = 1 / 2 := by
  fin_cases f
  · exact Or.inl flatCos₀
  · exact Or.inr (Or.inl flatCos₁)
  · exact Or.inr (Or.inr flatCos₂)
  · exact Or.inr (Or.inl flatCos₃)
  · exact Or.inr (Or.inl flatCos₄)
  · exact Or.inl flatCos₅

/-- Every flat cosine lies strictly inside `(-1, 1)`. -/
theorem flatCos_bounds (f : Fin 6) :
    -1 < dihedralCos3Sq freudenthalTetSqEdges f ∧
      dihedralCos3Sq freudenthalTetSqEdges f < 1 := by
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases flatCos_value_cases f with h | h | h <;> rw [h] <;> constructor <;>
    nlinarith [sq_nonneg (Real.sqrt 2 - 2)]

/-- Arccos endpoint freedom at flat: no flat cosine equals `±1`. -/
theorem flatCos_ne_endpoints (f : Fin 6) :
    dihedralCos3Sq freudenthalTetSqEdges f ≠ -1 ∧
      dihedralCos3Sq freudenthalTetSqEdges f ≠ 1 :=
  ⟨ne_of_gt (flatCos_bounds f).1, ne_of_lt (flatCos_bounds f).2⟩

/-- All diagonal cofactor products are strictly positive at the flat tuple
(determinant-cofactor form, i.e. exactly the hypothesis shape of the
explicit derivative theorems). -/
theorem flat_cofactorProduct_pos (f : Fin 6) :
    0 < cmCofactor3 freudenthalTetSqEdges
          (oppositeCMVertices f).1 (oppositeCMVertices f).1 *
        cmCofactor3 freudenthalTetSqEdges
          (oppositeCMVertices f).2 (oppositeCMVertices f).2 := by
  have h := Geometry.CofactorDerivatives.dihedralCofactorProductPoly_pos_of_nonDegenerate
    freudenthalTet f
  simpa [Geometry.CofactorDerivatives.dihedralCofactorProductPoly,
    Geometry.CofactorPolynomial.cmCofactor3_eq_poly] using h

/-- The dihedral cosine denominator is nonzero at the flat tuple. -/
theorem flat_denom_ne_zero (f : Fin 6) :
    dihedralDenom3 freudenthalTetSqEdges f ≠ 0 := by
  rw [Geometry.CofactorDerivatives.dihedralDenom3_eq_poly]
  exact Geometry.CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate
    freudenthalTet f

/-! ## §5. Lane A1 — neighborhood nondegeneracy at the flat tuple (THEOREM)

There is an open neighborhood of `freudenthalTetSqEdges` in
`SqEdges = Fin 6 → ℝ` on which `cm3 > 0`, every squared edge is positive,
every diagonal cofactor product is positive, and every dihedral cosine is
strictly inside `(-1, 1)`.  Stated as a filter `∀ᶠ` at `nhds`; membership
of an actual open set follows from `Filter.eventually_iff_exists_open` /
`eventually_nhds_iff` if a set-level form is needed downstream.  Proof:
continuity of the polynomial/ratio maps plus the exact flat values
(`cm3 = 8`, cosines `√2/2, 0, 1/2`, integer cofactor products). -/

theorem flat_nondegeneracy_eventually :
    ∀ᶠ a in nhds freudenthalTetSqEdges,
      0 < cm3 a ∧
        ∀ f : Fin 6,
          0 < a f ∧
            0 < cmCofactor3 a
                  (oppositeCMVertices f).1 (oppositeCMVertices f).1 *
                cmCofactor3 a
                  (oppositeCMVertices f).2 (oppositeCMVertices f).2 ∧
            -1 < dihedralCos3Sq a f ∧ dihedralCos3Sq a f < 1 := by
  have hcm : ∀ᶠ a in nhds freudenthalTetSqEdges, 0 < cm3 a := by
    have hcont : ContinuousAt cm3 freudenthalTetSqEdges :=
      (Geometry.CayleyMengerPolynomial.cm3_contDiff (0 : ℕ∞)).continuous.continuousAt
    have hpos : (0 : ℝ) < cm3 freudenthalTetSqEdges := by
      rw [cm3_freudenthalTetSqEdges]; norm_num
    exact Filter.Tendsto.eventually hcont (eventually_gt_nhds hpos)
  have hf : ∀ f : Fin 6, ∀ᶠ a in nhds freudenthalTetSqEdges,
      0 < a f ∧
        0 < cmCofactor3 a
              (oppositeCMVertices f).1 (oppositeCMVertices f).1 *
            cmCofactor3 a
              (oppositeCMVertices f).2 (oppositeCMVertices f).2 ∧
        -1 < dihedralCos3Sq a f ∧ dihedralCos3Sq a f < 1 := by
    intro f
    have hedge : ∀ᶠ a in nhds freudenthalTetSqEdges, 0 < a f := by
      have hcont : ContinuousAt (fun a : SqEdges => a f) freudenthalTetSqEdges :=
        (continuous_apply f).continuousAt
      exact Filter.Tendsto.eventually hcont
        (eventually_gt_nhds (freudenthalTet.sqEdge_pos f))
    have hprod : ∀ᶠ a in nhds freudenthalTetSqEdges,
        0 < cmCofactor3 a
              (oppositeCMVertices f).1 (oppositeCMVertices f).1 *
            cmCofactor3 a
              (oppositeCMVertices f).2 (oppositeCMVertices f).2 := by
      have hcont : ContinuousAt (fun a : SqEdges =>
          cmCofactor3 a
              (oppositeCMVertices f).1 (oppositeCMVertices f).1 *
            cmCofactor3 a
              (oppositeCMVertices f).2 (oppositeCMVertices f).2)
          freudenthalTetSqEdges :=
        (((cmCofactor3_contDiff (0 : ℕ∞)
              (oppositeCMVertices f).1 (oppositeCMVertices f).1).continuous).mul
          ((cmCofactor3_contDiff (0 : ℕ∞)
              (oppositeCMVertices f).2 (oppositeCMVertices f).2).continuous)).continuousAt
      exact Filter.Tendsto.eventually hcont
        (eventually_gt_nhds (flat_cofactorProduct_pos f))
    have hcosCont : ContinuousAt (fun a : SqEdges => dihedralCos3Sq a f)
        freudenthalTetSqEdges :=
      Geometry.ReggeActionSmoothness.dihedralCos3Sq_continuousAt_of_den_ne_zero
        freudenthalTetSqEdges f (flat_denom_ne_zero f)
    have hlo : ∀ᶠ a in nhds freudenthalTetSqEdges, -1 < dihedralCos3Sq a f :=
      Filter.Tendsto.eventually hcosCont (eventually_gt_nhds (flatCos_bounds f).1)
    have hhi : ∀ᶠ a in nhds freudenthalTetSqEdges, dihedralCos3Sq a f < 1 :=
      Filter.Tendsto.eventually hcosCont (eventually_lt_nhds (flatCos_bounds f).2)
    exact hedge.and (hprod.and (hlo.and hhi))
  exact hcm.and (Filter.eventually_all.2 hf)

/-! ## §6. Lane A2 — the one-tet Schläfli spike (THEOREM)

For every direction `v : Fin 6 → ℝ`, the per-tetrahedron weighted angle sum
`g(a) = ∑_f √a_f · θ_f(a)` is differentiable at the flat tuple along the
affine path `a + t·v`, with derivative `∑_f (v_f/(2√a_f)) · θ_f(a)` — the
`√a_f · θ'_f` group cancels EXACTLY by the proved squared-edge tetrahedral
Schläfli identity.  This is the first-derivative vertical slice toward
stage 2a. -/

/-- The shared stencil Jacobian is exactly the squared-edge closed-form
dihedral derivative of the Schläfli module at the flat tetrahedron
(kernel `rfl`; this ties the Gate-0c stencil to the proved Schläfli
machinery with zero transcription). -/
theorem flatAngleJacobian_eq_dihedralClosedDerivSq (f k : Fin 6) :
    flatAngleJacobian f k =
      Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSq freudenthalTet f k := rfl

/-- SCHLÄFLI CANCELLATION AT FLAT (THEOREM): for every squared-edge
coordinate `k`, `∑_f √(a_f) · flatAngleJacobian f k = 0` at the flat tuple.
This is the proved six-edge closed-form tetrahedral Schläfli identity
(`tetraSchlaefliSixEdgeClosedForm`) instantiated at the Freudenthal
tetrahedron and written in stencil vocabulary. -/
theorem flatAngleJacobian_schlaefli (k : Fin 6) :
    (∑ f : Fin 6, Real.sqrt (freudenthalTetSqEdges f) * flatAngleJacobian f k) = 0 :=
  Geometry.SchlaefliTetrahedronProof.tetraSchlaefliSixEdgeClosedForm freudenthalTet k

/-- Directional derivative of one flat dihedral angle (THEOREM): along the
affine path `t ↦ a + t·v` through the flat tuple, the `f`-th dihedral angle
has derivative `∑_k v_k · flatAngleJacobian f k` at `t = 0`.  The
directional derivative is assembled from the six proved coordinate partial
derivatives through the `C¹` Fréchet derivative at the flat point. -/
theorem hasDerivAt_flatAngle_directional (v : Fin 6 → ℝ) (f : Fin 6) :
    HasDerivAt
      (fun t : ℝ =>
        dihedralAngle3Sq (fun j : Fin 6 => freudenthalTetSqEdges j + t * v j) f)
      (∑ k : Fin 6, v k * flatAngleJacobian f k) 0 := by
  have hC : ContDiffAt ℝ 1 (fun x : SqEdges => dihedralAngle3Sq x f)
      freudenthalTetSqEdges :=
    Geometry.ReggeActionFirstVariation.dihedralAngle3Sq_contDiffAt_nonDegenerate
      freudenthalTet f 1 (flatCos_ne_endpoints f)
  have hDiff : DifferentiableAt ℝ (fun x : SqEdges => dihedralAngle3Sq x f)
      freudenthalTetSqEdges :=
    hC.differentiableAt (by simp)
  have hF : HasFDerivAt (fun x : SqEdges => dihedralAngle3Sq x f)
      (fderiv ℝ (fun x : SqEdges => dihedralAngle3Sq x f) freudenthalTetSqEdges)
      freudenthalTetSqEdges :=
    hDiff.hasFDerivAt
  have hγ : HasDerivAt
      (fun t : ℝ => (fun j : Fin 6 => freudenthalTetSqEdges j + t * v j)) v 0 := by
    rw [hasDerivAt_pi]
    intro j
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (freudenthalTetSqEdges j)
  have hF' : HasFDerivAt (fun x : SqEdges => dihedralAngle3Sq x f)
      (fderiv ℝ (fun x : SqEdges => dihedralAngle3Sq x f) freudenthalTetSqEdges)
      (fun j : Fin 6 => freudenthalTetSqEdges j + (0 : ℝ) * v j) := by
    simpa using hF
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ))
    (f := fun t : ℝ => (fun j : Fin 6 => freudenthalTetSqEdges j + t * v j))
    hF' hγ
  have hvalue :
      (fderiv ℝ (fun x : SqEdges => dihedralAngle3Sq x f) freudenthalTetSqEdges) v =
        ∑ k : Fin 6, v k * flatAngleJacobian f k := by
    rw [Geometry.ReggeActionFirstVariation.continuousLinearMap_apply_eq_sum_single]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (fun z => v k * z)
      (Geometry.ReggeActionFirstVariation.fderiv_dihedralAngle3Sq_apply_single
        freudenthalTet f k (flatCos_ne_endpoints f))
  rw [hvalue] at hcomp
  simpa [Function.comp_def] using hcomp

/-- Directional derivative of one flat sqrt-edge factor (THEOREM): along
the same affine path, `√((a + t·v)_f)` has derivative `v_f/(2√a_f)` at
`t = 0`. -/
theorem hasDerivAt_flatSqrtEdge_directional (v : Fin 6 → ℝ) (f : Fin 6) :
    HasDerivAt (fun t : ℝ => Real.sqrt (freudenthalTetSqEdges f + t * v f))
      (v f / (2 * Real.sqrt (freudenthalTetSqEdges f))) 0 := by
  have hpos : 0 < freudenthalTetSqEdges f := freudenthalTet.sqEdge_pos f
  have hinner : HasDerivAt (fun t : ℝ => freudenthalTetSqEdges f + t * v f) (v f) 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v f)).const_add (freudenthalTetSqEdges f)
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (freudenthalTetSqEdges f)))
      (freudenthalTetSqEdges f + (0 : ℝ) * v f) := by
    simpa using Real.hasDerivAt_sqrt (ne_of_gt hpos)
  have hcomp : HasDerivAt (fun t : ℝ => Real.sqrt (freudenthalTetSqEdges f + t * v f))
      (1 / (2 * Real.sqrt (freudenthalTetSqEdges f)) * v f) 0 :=
    hsq.comp (0 : ℝ) hinner
  have hval : v f / (2 * Real.sqrt (freudenthalTetSqEdges f)) =
      1 / (2 * Real.sqrt (freudenthalTetSqEdges f)) * v f := by ring
  rw [hval]
  exact hcomp

/-- LANE A2, THE ONE-TET SCHLÄFLI SPIKE (THEOREM): along every affine
squared-edge direction `v` through the flat Freudenthal tuple, the
per-tetrahedron weighted angle sum `∑_f √a_f · θ_f(a)` is differentiable at
flat with derivative `∑_f (v_f/(2√a_f)) · θ_f(flat)`.  The product rule
produces `∑_f [(√)'·θ + √·θ']`; the entire `θ'` group
`∑_k v_k (∑_f √a_f · ∂θ_f/∂a_k)` vanishes term-by-term by the PROVED
tetrahedral Schläfli identity (`flatAngleJacobian_schlaefli`).  Only the
sqrt-derivative group survives — exactly the structure the second-variation
stage needs. -/
theorem hasDerivAt_flatWeightedAngleSum (v : Fin 6 → ℝ) :
    HasDerivAt
      (fun t : ℝ => ∑ f : Fin 6,
        Real.sqrt (freudenthalTetSqEdges f + t * v f) *
          dihedralAngle3Sq (fun j : Fin 6 => freudenthalTetSqEdges j + t * v j) f)
      (∑ f : Fin 6,
        v f / (2 * Real.sqrt (freudenthalTetSqEdges f)) *
          dihedralAngle3Sq freudenthalTetSqEdges f) 0 := by
  have hterm : ∀ f : Fin 6, HasDerivAt
      (fun t : ℝ =>
        Real.sqrt (freudenthalTetSqEdges f + t * v f) *
          dihedralAngle3Sq (fun j : Fin 6 => freudenthalTetSqEdges j + t * v j) f)
      (v f / (2 * Real.sqrt (freudenthalTetSqEdges f)) *
          dihedralAngle3Sq freudenthalTetSqEdges f +
        Real.sqrt (freudenthalTetSqEdges f) *
          (∑ k : Fin 6, v k * flatAngleJacobian f k)) 0 := by
    intro f
    have h := (hasDerivAt_flatSqrtEdge_directional v f).mul
      (hasDerivAt_flatAngle_directional v f)
    simpa using h
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (A := fun f t =>
      Real.sqrt (freudenthalTetSqEdges f + t * v f) *
        dihedralAngle3Sq (fun j : Fin 6 => freudenthalTetSqEdges j + t * v j) f)
    (A' := fun f =>
      v f / (2 * Real.sqrt (freudenthalTetSqEdges f)) *
          dihedralAngle3Sq freudenthalTetSqEdges f +
        Real.sqrt (freudenthalTetSqEdges f) *
          (∑ k : Fin 6, v k * flatAngleJacobian f k))
    (x := 0) (fun f _ => hterm f)
  have hcancel : (∑ f : Fin 6, Real.sqrt (freudenthalTetSqEdges f) *
      (∑ k : Fin 6, v k * flatAngleJacobian f k)) = 0 := by
    calc
      (∑ f : Fin 6, Real.sqrt (freudenthalTetSqEdges f) *
          (∑ k : Fin 6, v k * flatAngleJacobian f k))
          = ∑ k : Fin 6, v k *
              (∑ f : Fin 6, Real.sqrt (freudenthalTetSqEdges f) *
                flatAngleJacobian f k) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun f _ => ?_
            ring
      _ = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [flatAngleJacobian_schlaefli k]
            ring
  have hfinal :
      (∑ f : Fin 6,
        (v f / (2 * Real.sqrt (freudenthalTetSqEdges f)) *
            dihedralAngle3Sq freudenthalTetSqEdges f +
          Real.sqrt (freudenthalTetSqEdges f) *
            (∑ k : Fin 6, v k * flatAngleJacobian f k))) =
      ∑ f : Fin 6,
        v f / (2 * Real.sqrt (freudenthalTetSqEdges f)) *
          dihedralAngle3Sq freudenthalTetSqEdges f := by
    rw [Finset.sum_add_distrib, hcancel, add_zero]
  rw [hfinal] at hsum
  exact hsum

/-! ## §7. Lane A3 — the flat Jacobian rows as pure cofactor algebra

Every row of `flatAngleJacobian` is `-(arccos factor) × (closed-form
cofactor cosine derivative)`, with the arccos factor evaluated to exact
radicals (`√2, 1, 2/√3, 1, 1, √2`) — ZERO arccos values remain.  The
`f = 0` row is then fully evaluated to exact rationals through the proved
Schläfli radical bridge (the row is `(1/4)·(rationalized summand)` at flat,
and the rationalized summand is radical-free cofactor algebra). -/

/-- The exact arccos chain-rule factors `1/√(1-c_f²)` at the flat point:
`√2, 1, 2/√3, 1, 1, √2`. -/
def flatArccosFactor : Fin 6 → ℝ
  | 0 => Real.sqrt 2
  | 1 => 1
  | 2 => 2 / Real.sqrt 3
  | 3 => 1
  | 4 => 1
  | 5 => Real.sqrt 2

private theorem inv_sqrt_half : 1 / Real.sqrt (1 - (Real.sqrt 2 / 2) ^ 2) = Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [show (1 : ℝ) - (Real.sqrt 2 / 2) ^ 2 = 1 / 2 by rw [div_pow, h2]; norm_num]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.sqrt_inv, one_div, inv_inv]

private theorem inv_sqrt_three_quarters :
    1 / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) = 2 / Real.sqrt 3 := by
  rw [show (1 : ℝ) - (1 / 2 : ℝ) ^ 2 = 3 / 4 by norm_num]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3) 4]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [one_div_div]

private theorem arccosFactor₀ :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges 0 ^ 2) = Real.sqrt 2 := by
  rw [flatCos₀]; exact inv_sqrt_half

private theorem arccosFactor₁ :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges 1 ^ 2) = 1 := by
  rw [flatCos₁]; norm_num

private theorem arccosFactor₂ :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges 2 ^ 2) = 2 / Real.sqrt 3 := by
  rw [flatCos₂]; exact inv_sqrt_three_quarters

private theorem arccosFactor₃ :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges 3 ^ 2) = 1 := by
  rw [flatCos₃]; norm_num

private theorem arccosFactor₄ :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges 4 ^ 2) = 1 := by
  rw [flatCos₄]; norm_num

private theorem arccosFactor₅ :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges 5 ^ 2) = Real.sqrt 2 := by
  rw [flatCos₅]; exact inv_sqrt_half

/-- LANE A3 ARCCOS FACTOR EVALUATION (THEOREM): at the flat point the
arccos chain-rule multiplier `1/√(1-c_f²)` equals the exact radical table
`flatArccosFactor` — `c = √2/2` gives `√2`, `c = 0` gives `1`, `c = 1/2`
gives `2/√3`. -/
theorem flatArccosFactor_spec (f : Fin 6) :
    1 / Real.sqrt (1 - dihedralCos3Sq freudenthalTetSqEdges f ^ 2) =
      flatArccosFactor f := by
  fin_cases f
  · exact arccosFactor₀
  · exact arccosFactor₁
  · exact arccosFactor₂
  · exact arccosFactor₃
  · exact arccosFactor₄
  · exact arccosFactor₅

/-- LANE A3 ROW NORMALIZATION (THEOREM): every entry of the flat angle
Jacobian is pure cofactor algebra times the exactly evaluated arccos
factor — `flatAngleJacobian f k = -(factor_f) · (closed-form cofactor
cosine derivative at flat)`, with NO arccos value anywhere on the right. -/
theorem flatAngleJacobian_cofactor_form (f k : Fin 6) :
    flatAngleJacobian f k =
      -(flatArccosFactor f) *
        Geometry.CofactorDerivatives.dihedralCos3SqClosedFormDeriv
          freudenthalTetSqEdges f k := by
  unfold flatAngleJacobian
  rw [Geometry.DihedralDerivatives.dihedralAngle3SqClosedFormDeriv_def,
    ← flatArccosFactor_spec f]

/-- The `f = 0` Jacobian row through the proved Schläfli radical bridge: at
the flat tuple (`√a₀ = 1`, `√(2·cm3) = 4`) the row is `(1/4)` times the
RADICAL-FREE rationalized Schläfli summand.  This is the exact convention
manifest Lane B mirrors: the row is pure rational cofactor algebra. -/
theorem flatAngleJacobian_row0_norm (k : Fin 6) :
    flatAngleJacobian 0 k =
      (1 / 4 : ℝ) *
        Geometry.SchlaefliTetrahedronProof.schlaefliPolySummandNorm
          freudenthalTetSqEdges 0 k := by
  have hb := Geometry.SchlaefliTetrahedronProof.schlaefli_summand_bridge_edge0
    freudenthalTet k
  have h1 : Real.sqrt (freudenthalTet.sqEdge 0) = 1 := by
    rw [show freudenthalTet.sqEdge 0 = 1 from rfl, Real.sqrt_one]
  have h4 : Real.sqrt (2 * cm3 freudenthalTet.sqEdge) = 4 := by
    have hcm : cm3 freudenthalTet.sqEdge = 8 := cm3_freudenthalTetSqEdges
    rw [hcm, show (2 : ℝ) * 8 = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [h1, one_mul, h4] at hb
  have hkey : flatAngleJacobian 0 k =
      Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSqPoly freudenthalTet 0 k := by
    rw [flatAngleJacobian_eq_dihedralClosedDerivSq]
    exact Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSq_eq_poly
      freudenthalTet 0 k
  rw [hkey, hb]
  rfl

/-- The exact `f = 0` Jacobian row values at the flat tuple. -/
def flatAngleJacobianRow0 : Fin 6 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => -(1 / 4)
  | 5 => 1 / 2

/-- LANE A3 ROW `f = 0` FULL EVALUATION (THEOREM): the flat angle Jacobian
row `f = 0` is exactly `(0, 0, 0, 0, -1/4, 1/2)` — exact rationals, no
radicals survive (the arccos factor `√2` cancels against the `1/√32`
cofactor denominator through the Schläfli radical bridge). -/
theorem flatAngleJacobian_row0_eval (k : Fin 6) :
    flatAngleJacobian 0 k = flatAngleJacobianRow0 k := by
  rw [flatAngleJacobian_row0_norm k]
  fin_cases k <;>
    norm_num [flatAngleJacobianRow0,
      Geometry.SchlaefliTetrahedronProof.schlaefliPolySummandNorm,
      Geometry.CofactorPolynomial.cmCofactor3Poly,
      Geometry.CofactorPolynomial.cmCofactorPartial,
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges]

end

end ReggeTTDerivativeGate
end Analysis
end Gravity
end IndisputableMonolith
