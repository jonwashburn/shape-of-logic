import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import IndisputableMonolith.Constants
import IndisputableMonolith.Geometry.Schlaefli
import IndisputableMonolith.Foundation.SimplicialLedger.ContinuumBridge
import IndisputableMonolith.Foundation.SimplicialLedger.EdgeLengthFromPsi

/-!
# Weak-Field Conformal Reduction of the Regge Action

This module proves the algebraic core of the reduction Jon is moving into
Regge's notation in the gravity paper:

  (a) Regge action            S = (1/κ) · Σ_h A_h · δ_h
  (b) Conformal edge ansatz   ℓ_{ij} = ℓ_0 · exp((ξ_i + ξ_j)/2)
  (c) Weak-field expansion    expand to second order in ξ
  (d) Reduction               S^(2) = (1/κ) · Σ_⟨i,j⟩ ½ · (ξ_i − ξ_j)² · A_{ij}

Piran–Williams (1986) handle a more general perturbation that does not
single out the conformal mode. The reduction here picks the conformal
sector and proves the finite-dimensional algebra that turns a symmetric
zero-row-sum second-variation matrix into the Dirichlet form on
differences `(ξ_i − ξ_j)²`. The remaining geometric task is to compute
the Regge second-variation coefficients from Cayley–Menger/dihedral
formulas (or an equivalent Piran–Williams specialization) and verify the
row-sum condition for the chosen lattice.

## Layering

The module is split into three independent algebraic claims plus one
geometric hypothesis package:

§1. *Conformal expansion (algebraic, fully proven).*
    `ℓ_{ij}² / ℓ_0² = 1 + (ξ_i + ξ_j) + ½(ξ_i + ξ_j)² + remainder`
    with the remainder named exactly as `exp(t) - 1 - t - t²/2`.

§2. *Graph-Laplacian decomposition (algebraic, fully proven).*
    For any symmetric matrix `M` on `Fin n × Fin n` with zero row sums,
    `Σ_{i,j} M_{ij} ξ_i ξ_j = −½ Σ_{i,j} M_{ij} (ξ_i − ξ_j)²`.
    This is the structural lemma that turns "Regge bilinear form" into
    "Dirichlet form".

§3. *Second-order Regge action coefficients (geometric input).*
    We package the first-order area and deficit responses in a
    `WeakFieldReggeData` structure and state the Schläfli/flat-mode
    row-sum condition those coefficients must satisfy. This file does not
    compute those coefficients from Cayley–Menger data.

§4. *The reduction (composition).*
    Combining §2 with the row-sum property, the packaged second-order
    conformal Regge functional equals the discrete Dirichlet energy with
    weights `A_{ij} = -M_{ij}`.

Zero `sorry`, zero new `axiom`. The file is a conditional theorem: once
the geometric coefficients and Schläfli row-sum are supplied, the
Dirichlet reduction is formal.

## References

- Regge, T. (1961). *General relativity without coordinates.* Nuovo
  Cim. 19, 558–571.
- Piran, T. & Williams, R. M. (1986). *Three-plus-one formulation of
  Regge calculus.* Phys. Rev. D 33, 1622–1633.
- Roček, M. & Williams, R. M. (1981). *Quantum Regge calculus.* Phys.
  Lett. B 104, 31–37. (linearized Regge action on a regular lattice)
- Schläfli, L. (1858). *On the multiple integral ∫^n dx dy ··· dz.*
- Hartle, J. B. & Sorkin, R. (1981). *Boundary terms in the action for
  the Regge calculus.* Gen. Rel. Grav. 13, 541–549.
-/

namespace IndisputableMonolith
namespace Gravity
namespace WeakFieldConformalRegge

open Constants Real Geometry.Schlaefli Geometry.DihedralAngle
open Foundation.SimplicialLedger.ContinuumBridge
open Foundation.SimplicialLedger.EdgeLengthFromPsi

noncomputable section

/-! ## §1. Conformal edge-length expansion

The exact identity `ℓ_{ij}² = ℓ_0² · exp(ξ_i + ξ_j)` factors out the
conformal field. We expose two clean forms:

* `conformal_length_sq_exact`: the exact form (no expansion, no error).
* `conformal_length_sq_taylor2`: the second-order Taylor decomposition
  with an explicit remainder `R(ξ_i + ξ_j)`.

Both are fully proven from the algebra of `Real.exp`. -/

/-- The exact identity:
    `ℓ_{ij}(ξ)² = ℓ_0² · exp(ξ_i + ξ_j)`. -/
theorem conformal_length_sq_exact
    {n : ℕ} (a : ℝ) (ha : 0 < a) (ε : LogPotential n) (i j : Fin n) :
    (conformal_edge_length_field a ha ε).length i j ^ 2
      = a ^ 2 * Real.exp (ε i + ε j) := by
  unfold conformal_edge_length_field
  simp only
  have hexp : Real.exp ((ε i + ε j) / 2) ^ 2
              = Real.exp (ε i + ε j) := by
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  rw [mul_pow, hexp]

/-- The Taylor expansion of `exp(t) − 1 − t − t²/2` is the third-order
    remainder. We do *not* prove a quantitative bound here (Mathlib's
    `Real.exp_taylor_lt` route is heavy); we just expose the algebraic
    decomposition with the remainder named explicitly. -/
def conformal_remainder (t : ℝ) : ℝ := Real.exp t - 1 - t - t ^ 2 / 2

/-- The second-order conformal expansion. This is *exact* with the
    remainder explicitly named: it is just the rearrangement of
    `exp(t) = 1 + t + t²/2 + R(t)`. -/
theorem conformal_length_sq_taylor2
    {n : ℕ} (a : ℝ) (ha : 0 < a) (ε : LogPotential n) (i j : Fin n) :
    (conformal_edge_length_field a ha ε).length i j ^ 2 / a ^ 2
      = 1 + (ε i + ε j) + (ε i + ε j) ^ 2 / 2
        + conformal_remainder (ε i + ε j) := by
  have ha2 : (a : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
  rw [conformal_length_sq_exact a ha ε i j]
  unfold conformal_remainder
  field_simp
  ring

/-- At the flat vacuum `ξ ≡ 0`, the conformal remainder vanishes. -/
theorem conformal_remainder_zero : conformal_remainder 0 = 0 := by
  unfold conformal_remainder
  simp

/-- The first- and second-order coefficients of `ℓ_{ij}² / ℓ_0²` in `ξ`.

    First order:  `δ¹(ℓ²/ℓ_0²) = ξ_i + ξ_j`.
    Second order: `δ²(ℓ²/ℓ_0²) = (ξ_i + ξ_j)² / 2`.

    These are the building blocks for §3. -/
def edgeSqFirstOrder {n : ℕ} (ε : LogPotential n) (i j : Fin n) : ℝ :=
  ε i + ε j

def edgeSqSecondOrder {n : ℕ} (ε : LogPotential n) (i j : Fin n) : ℝ :=
  (ε i + ε j) ^ 2 / 2

/-- The conformal expansion writes `ℓ²/ℓ_0² − 1 − δ¹ − δ²` as the
    remainder. This is a tautology after `conformal_length_sq_taylor2`
    but it is the form that downstream "second-order action" reductions
    need. -/
theorem conformal_length_sq_decomposition
    {n : ℕ} (a : ℝ) (ha : 0 < a) (ε : LogPotential n) (i j : Fin n) :
    (conformal_edge_length_field a ha ε).length i j ^ 2 / a ^ 2
      = 1 + edgeSqFirstOrder ε i j + edgeSqSecondOrder ε i j
        + conformal_remainder (ε i + ε j) := by
  unfold edgeSqFirstOrder edgeSqSecondOrder
  exact conformal_length_sq_taylor2 a ha ε i j

/-! ## §2. Graph-Laplacian decomposition

The pure-algebraic identity that drives the reduction. If `M_{ij}` is
symmetric with zero row sums, then `ξ ↦ Σ_{i,j} M_{ij} ξ_i ξ_j` is the
discrete Dirichlet energy `−½ Σ_{i,j} M_{ij} (ξ_i − ξ_j)²`.

This is the discrete analog of `∫ φ Δφ = −∫ |∇φ|²` (integration by parts
on a closed manifold) and is what makes a "Regge bilinear form on edges"
manifestly the same as a "Dirichlet form on vertices". -/

/-- The Dirichlet form generated by a symmetric matrix `M` and a vertex
    function `ξ`: `D[ξ; M] = ½ Σ_{i,j} M_{ij} (ξ_i − ξ_j)²`. -/
def dirichletForm {n : ℕ} (M : Fin n → Fin n → ℝ) (ε : LogPotential n) : ℝ :=
  (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, M i j * (ε i - ε j) ^ 2

/-- The bilinear form: `Q[ξ; M] = Σ_{i,j} M_{ij} ξ_i ξ_j`. -/
def quadraticForm {n : ℕ} (M : Fin n → Fin n → ℝ) (ε : LogPotential n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, M i j * ε i * ε j

/-- Helper: pulling a constant out of a sum (right-multiplication form). -/
private lemma sum_const_mul_right {n : ℕ} (f : Fin n → ℝ) (c : ℝ) :
    ∑ j : Fin n, f j * c = (∑ j : Fin n, f j) * c := by
  rw [← Finset.sum_mul]

/-- Helper: pulling a constant out of an inner sum at `j` (when the inner
    factor depends only on `i`). -/
private lemma inner_sum_const {n : ℕ} (M : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, M i j * g i = (∑ j : Fin n, M i j) * g i :=
  sum_const_mul_right (fun j => M i j) (g i)

/-- **GRAPH-LAPLACIAN DECOMPOSITION.**
    For symmetric `M` with zero row sums,
    `Q[ξ; M] = −D[ξ; M]`.

    This is the algebraic core of the weak-field reduction. -/
theorem dirichlet_eq_neg_quadratic
    {n : ℕ} (M : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, M i j = M j i)
    (hrow : ∀ i, ∑ j : Fin n, M i j = 0)
    (ε : LogPotential n) :
    quadraticForm M ε = - dirichletForm M ε := by
  unfold quadraticForm dirichletForm
  -- Expand `(ε i − ε j)² = ε i² − 2 ε i ε j + ε j²` and sum.
  have hkey : ∀ i j, M i j * (ε i - ε j) ^ 2
              = M i j * (ε i) ^ 2 - 2 * (M i j * ε i * ε j)
                + M i j * (ε j) ^ 2 := by
    intro i j; ring
  -- Sum the identity term-by-term.
  have hsum : ∑ i : Fin n, ∑ j : Fin n, M i j * (ε i - ε j) ^ 2
              = (∑ i : Fin n, ∑ j : Fin n, M i j * (ε i) ^ 2)
                - 2 * (∑ i : Fin n, ∑ j : Fin n, M i j * ε i * ε j)
                + (∑ i : Fin n, ∑ j : Fin n, M i j * (ε j) ^ 2) := by
    have h1 : ∀ i, ∑ j : Fin n, M i j * (ε i - ε j) ^ 2
              = ∑ j : Fin n, (M i j * (ε i) ^ 2 - 2 * (M i j * ε i * ε j)
                              + M i j * (ε j) ^ 2) := by
      intro i; exact Finset.sum_congr rfl (fun j _ => hkey i j)
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hpull : ∀ i, ∑ j : Fin n, 2 * (M i j * ε i * ε j)
                  = 2 * ∑ j : Fin n, M i j * ε i * ε j := by
      intro i
      exact (Finset.mul_sum _ _ _).symm
    simp only [hpull, ← Finset.mul_sum]
  -- Use the row-sum condition on the `ε i² · M i j` and `ε j² · M i j` pieces.
  have hi2 : ∑ i : Fin n, ∑ j : Fin n, M i j * (ε i) ^ 2 = 0 := by
    have hpull : ∀ i, ∑ j : Fin n, M i j * (ε i) ^ 2
                  = (∑ j : Fin n, M i j) * (ε i) ^ 2 := fun i =>
      sum_const_mul_right (fun j => M i j) ((ε i) ^ 2)
    simp only [hpull, hrow, zero_mul, Finset.sum_const_zero]
  have hj2 : ∑ i : Fin n, ∑ j : Fin n, M i j * (ε j) ^ 2 = 0 := by
    -- Swap order, then `hrow` (transposed via symmetry).
    rw [Finset.sum_comm]
    have hpull : ∀ j, ∑ i : Fin n, M i j * (ε j) ^ 2
                  = (∑ i : Fin n, M i j) * (ε j) ^ 2 := fun j =>
      sum_const_mul_right (fun i => M i j) ((ε j) ^ 2)
    have hrow' : ∀ j, ∑ i : Fin n, M i j = 0 := by
      intro j
      have heq : ∑ i : Fin n, M i j = ∑ i : Fin n, M j i :=
        Finset.sum_congr rfl (fun i _ => hsymm i j)
      rw [heq]; exact hrow j
    simp only [hpull, hrow', zero_mul, Finset.sum_const_zero]
  -- Plug back in.
  rw [hsum, hi2, hj2]
  ring

/-- **CONSEQUENCE.** When `M` is symmetric with zero row sums, the
    Dirichlet form is the natural positive expression of the bilinear:
    `D[ξ; M] = − Q[ξ; M]`. -/
theorem dirichlet_form_eq_neg_quadratic
    {n : ℕ} (M : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, M i j = M j i)
    (hrow : ∀ i, ∑ j : Fin n, M i j = 0)
    (ε : LogPotential n) :
    dirichletForm M ε = - quadraticForm M ε := by
  have h := dirichlet_eq_neg_quadratic M hsymm hrow ε
  linarith

/-! ## §3. Second-order Regge action under Schläfli

We package the geometric coefficients (linearizations of `A_h` and
`δ_h` in the conformal field `ξ`) as a structure, then prove that the
second-order Regge action takes the bilinear form
  `S^(2)[ξ] = Σ_h A_h^(1)[ξ] · δ_h^(1)[ξ]`
which combined with the conformal flat-mode invariance and §2 gives
the Dirichlet reduction.

The structure isolates *exactly* the geometric data the paper relies
on, separate from the algebra of §1 and §2. -/

/-- The first-order linearization data of a flat-background Regge
    configuration under conformal vertex perturbations.

    Fields:
    * `dArea i j`     — coefficient of `(ξ_i + ξ_j)/2` in `A_h^(1)` for
                        the hinge attached to edge `⟨i,j⟩`. (Background
                        data: linear response of the hinge area to a
                        unit change in edge length.)
    * `dDeficit i j`  — coefficient of `(ξ_i + ξ_j)/2` in `δ_h^(1)` for
                        the same hinge. (Background data: linear
                        response of the deficit angle.)

    The data is symmetric in `i, j` and lives on a finite vertex set
    `Fin n`. -/
structure WeakFieldReggeData (n : ℕ) where
  dArea : Fin n → Fin n → ℝ
  dDeficit : Fin n → Fin n → ℝ
  dArea_symm : ∀ i j, dArea i j = dArea j i
  dDeficit_symm : ∀ i j, dDeficit i j = dDeficit j i

/-- The bilinear coefficient matrix induced by the linearization data:
    `M_{ij} = dArea_{ij} · dDeficit_{ij}` (the entry-wise product
    that appears in `S^(2) = Σ A^(1) δ^(1)` after the conformal
    expansion).

    This is symmetric because both factors are symmetric. -/
def bilinearCoefficient {n : ℕ} (W : WeakFieldReggeData n)
    (i j : Fin n) : ℝ :=
  W.dArea i j * W.dDeficit i j

theorem bilinearCoefficient_symm {n : ℕ} (W : WeakFieldReggeData n)
    (i j : Fin n) :
    bilinearCoefficient W i j = bilinearCoefficient W j i := by
  unfold bilinearCoefficient
  rw [W.dArea_symm i j, W.dDeficit_symm i j]

/-- The *Schläfli-derived row-sum vanishing* property. On a flat
    background, the deficit-angle linearization satisfies Schläfli's
    identity, which forces the bilinear-coefficient matrix to have
    zero row sums when contracted with the conformal mode.

    Concretely: for each vertex `i`,
    `Σ_j dArea_{ij} · dDeficit_{ij} = 0`.

    This is the geometric content of "uniform `ξ ≡ c` produces no
    curvature change" combined with Schläfli's identity. -/
def SchlaefliRowSum {n : ℕ} (W : WeakFieldReggeData n) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, bilinearCoefficient W i j = 0

/-- The second-order Regge action functional in the conformal mode.
    Plugging the conformal expansion of `ℓ²` into the linearized Regge
    action and collecting the order-`ξ²` terms gives this bilinear:

        S^(2)[ξ] = (1/4) · Σ_{i,j} (ξ_i + ξ_j)² · M_{ij}
                = (1/4) · Σ_{i,j} (ξ_i² + 2 ξ_i ξ_j + ξ_j²) · M_{ij}.

    The factor `1/4` comes from the `(ξ_i + ξ_j)/2` factors entering
    twice (once from `A_h^(1)`, once from `δ_h^(1)`).

    With the Schläfli row-sum property, the `ξ_i² + ξ_j²` parts
    vanish on summation and the `2 ξ_i ξ_j` part rearranges via §2 into
    the Dirichlet form on differences. -/
def secondOrderReggeAction {n : ℕ} (W : WeakFieldReggeData n)
    (ε : LogPotential n) : ℝ :=
  (1 / 4) * ∑ i : Fin n, ∑ j : Fin n,
    bilinearCoefficient W i j * (ε i + ε j) ^ 2

/-! ## §4. The reduction theorem

The composition of §1 (conformal expansion), §2 (graph-Laplacian
decomposition), and §3 (Schläfli-anchored second-order form) yields:

  `S^(2)[ξ] = (1/2) · Σ_⟨i,j⟩ A_{ij} · (ξ_i − ξ_j)²`

with `A_{ij} = − bilinearCoefficient W i j` (the sign comes from
`Q = − D` in §2).

This is the Lean form of equation (d) in Jon's note. -/

/-- The "edge area" weights `A_{ij}` derived from the linearization
    data. Defined as `−M_{ij} = − dArea · dDeficit`; the sign comes
    from §2 (`Q = − D`). On standard regular lattices these are
    non-negative. -/
def edgeArea {n : ℕ} (W : WeakFieldReggeData n) (i j : Fin n) : ℝ :=
  - bilinearCoefficient W i j

theorem edgeArea_symm {n : ℕ} (W : WeakFieldReggeData n) (i j : Fin n) :
    edgeArea W i j = edgeArea W j i := by
  unfold edgeArea
  rw [bilinearCoefficient_symm]

/-- **Missing component-level comparison target.**

Philip's question about `M_{ij}` versus `area(f_{ij})` is exactly this datum.
For a genuine Regge triangulation, one must compute the second-variation
coefficient matrix `M = bilinearCoefficient W` from the Cayley-Menger /
dihedral-angle formulas and show that, off diagonal, it is the negative of
the geometric area/face weight matrix used by the J-cost Dirichlet form.

This structure does **not** assert that the computation has been done.  It
names the theorem-shaped target:

* `geometricArea i j` is the intended `area(f_ij)` / hinge-dual weight;
* `offDiag_component_match` says `M_ij = -geometricArea_ij` for `i ≠ j`;
* `schlaefli_row_sum` supplies the diagonal/row-sum closure.

Once an actual component computation produces this structure for a concrete
mesh, the general weak-field reduction below turns it into the Dirichlet
energy with those geometric weights. -/
structure ReggeComponentComparison {n : ℕ} (W : WeakFieldReggeData n) where
  geometricArea : Fin n → Fin n → ℝ
  geometricArea_symm : ∀ i j, geometricArea i j = geometricArea j i
  geometricArea_nonneg : ∀ i j, 0 ≤ geometricArea i j
  offDiag_component_match :
    ∀ i j, i ≠ j → bilinearCoefficient W i j = - geometricArea i j
  schlaefli_row_sum : SchlaefliRowSum W

/-- The Dirichlet form on the negated coefficient matrix is the negation
    of the Dirichlet form on the original. Pure algebra: each summand
    `(- M i j) * (ε i - ε j)² = - (M i j * (ε i - ε j)²)`. -/
theorem dirichletForm_neg
    {n : ℕ} (M : Fin n → Fin n → ℝ) (ε : LogPotential n) :
    dirichletForm (fun i j => - M i j) ε = - dirichletForm M ε := by
  unfold dirichletForm
  have h1 : ∀ i j, (- M i j) * (ε i - ε j) ^ 2
              = - (M i j * (ε i - ε j) ^ 2) := by
    intro i j; ring
  have hinner : ∀ i, ∑ j : Fin n, (- M i j) * (ε i - ε j) ^ 2
              = - ∑ j : Fin n, M i j * (ε i - ε j) ^ 2 := by
    intro i
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => h1 i j)
  rw [show (fun i => ∑ j, (- M i j) * (ε i - ε j) ^ 2)
        = (fun i => - ∑ j, M i j * (ε i - ε j) ^ 2) from funext hinner]
  rw [Finset.sum_neg_distrib]; ring

/-- The Dirichlet form on `edgeArea W` is the negation of the Dirichlet
    form on `bilinearCoefficient W`. Direct from `dirichletForm_neg`
    plus the definition `edgeArea = − bilinearCoefficient`. -/
theorem dirichletForm_edgeArea
    {n : ℕ} (W : WeakFieldReggeData n) (ε : LogPotential n) :
    dirichletForm (edgeArea W) ε
      = - dirichletForm (bilinearCoefficient W) ε := by
  have h := dirichletForm_neg (bilinearCoefficient W) ε
  -- `(fun i j => - bilinearCoefficient W i j)` is definitionally `edgeArea W`.
  exact h

/-- **WEAK-FIELD CONFORMAL REDUCTION (the main theorem).**

    Under the Schläfli row-sum hypothesis (§3) on the linearization
    data `W`, the second-order Regge action equals the discrete
    Dirichlet energy on the conformal mode `ε`, with edge weights
    `A_{ij} = − dArea_{ij} · dDeficit_{ij}`:

        secondOrderReggeAction W ε
            = (1/2) · Σ_{i,j} ½ · (ε i − ε j)² · A_{ij}
            = ½ · dirichletForm A ε.

    Multiplying through by `1/κ` recovers Jon's equation (d):

        S^(2)/κ = (1/κ) · Σ_⟨i,j⟩ ½ · (ξ_i − ξ_j)² · A_{ij}.

    Proof:
    1. Expand `(ξ_i + ξ_j)² = ξ_i² + 2 ξ_i ξ_j + ξ_j²`.
    2. The `ξ_i²` and `ξ_j²` pieces collapse via Schläfli row-sum.
    3. The `2 ξ_i ξ_j` piece is `quadraticForm M ε = − dirichletForm M ε`
       by `dirichlet_eq_neg_quadratic` (§2).
    4. `dirichletForm (edgeArea W) ε = − dirichletForm M ε`
       by `dirichletForm_edgeArea`.
    Combining: LHS = `(1/4)·(0 + 2·(−D) + 0) = −D/2 = (1/2)·(−D)
                  = (1/2) · dirichletForm (edgeArea W) ε = RHS`. -/
theorem weak_field_conformal_reduction
    {n : ℕ} (W : WeakFieldReggeData n)
    (hSchl : SchlaefliRowSum W)
    (ε : LogPotential n) :
    secondOrderReggeAction W ε
      = (1 / 2) * dirichletForm (edgeArea W) ε := by
  -- Abbreviations.
  set M : Fin n → Fin n → ℝ := bilinearCoefficient W with hM_def
  -- Step 1: expand the square.
  have hexp : ∀ i j, M i j * (ε i + ε j) ^ 2
              = M i j * (ε i) ^ 2
                + 2 * (M i j * ε i * ε j)
                + M i j * (ε j) ^ 2 := by
    intro i j; ring
  -- Sum over i, j.
  have hsum : ∑ i : Fin n, ∑ j : Fin n, M i j * (ε i + ε j) ^ 2
              = (∑ i : Fin n, ∑ j : Fin n, M i j * (ε i) ^ 2)
                + 2 * (∑ i : Fin n, ∑ j : Fin n, M i j * ε i * ε j)
                + (∑ i : Fin n, ∑ j : Fin n, M i j * (ε j) ^ 2) := by
    have h1 : ∀ i, ∑ j : Fin n, M i j * (ε i + ε j) ^ 2
              = ∑ j : Fin n, (M i j * (ε i) ^ 2
                              + 2 * (M i j * ε i * ε j)
                              + M i j * (ε j) ^ 2) := fun i =>
      Finset.sum_congr rfl (fun j _ => hexp i j)
    simp only [h1, Finset.sum_add_distrib]
    have hpull : ∀ i, ∑ j : Fin n, 2 * (M i j * ε i * ε j)
                  = 2 * ∑ j : Fin n, M i j * ε i * ε j := fun i =>
      (Finset.mul_sum _ _ _).symm
    simp only [hpull, ← Finset.mul_sum]
  -- Step 2: the (ε i)² and (ε j)² pieces vanish under Schläfli row-sum.
  have hSchl_M : ∀ i : Fin n, ∑ j : Fin n, M i j = 0 := hSchl
  have hi2 : ∑ i : Fin n, ∑ j : Fin n, M i j * (ε i) ^ 2 = 0 := by
    have hpull : ∀ i, ∑ j : Fin n, M i j * (ε i) ^ 2
                  = (∑ j : Fin n, M i j) * (ε i) ^ 2 := fun i =>
      sum_const_mul_right (fun j => M i j) ((ε i) ^ 2)
    simp only [hpull, hSchl_M, zero_mul, Finset.sum_const_zero]
  have hSchl_col : ∀ j : Fin n, ∑ i : Fin n, M i j = 0 := by
    intro j
    have heq : ∑ i : Fin n, M i j = ∑ i : Fin n, M j i :=
      Finset.sum_congr rfl (fun i _ => bilinearCoefficient_symm W i j)
    rw [heq]; exact hSchl_M j
  have hj2 : ∑ i : Fin n, ∑ j : Fin n, M i j * (ε j) ^ 2 = 0 := by
    rw [Finset.sum_comm]
    have hpull : ∀ j, ∑ i : Fin n, M i j * (ε j) ^ 2
                  = (∑ i : Fin n, M i j) * (ε j) ^ 2 := fun j =>
      sum_const_mul_right (fun i => M i j) ((ε j) ^ 2)
    simp only [hpull, hSchl_col, zero_mul, Finset.sum_const_zero]
  -- Step 3: rewrite the cross term via §2.
  have hQ : quadraticForm M ε = - dirichletForm M ε :=
    dirichlet_eq_neg_quadratic M (bilinearCoefficient_symm W) hSchl ε
  -- Step 4: rewrite the goal RHS via `dirichletForm_edgeArea`.
  rw [dirichletForm_edgeArea W ε]
  -- Now expand the LHS.
  unfold secondOrderReggeAction
  rw [show (∑ i : Fin n, ∑ j : Fin n, bilinearCoefficient W i j * (ε i + ε j) ^ 2)
        = (∑ i : Fin n, ∑ j : Fin n, M i j * (ε i + ε j) ^ 2) from rfl]
  rw [hsum, hi2, hj2]
  -- Goal: `(1/4) * (0 + 2 * Σ Σ M i j * ε i * ε j + 0) = (1/2) * (- D)`.
  unfold quadraticForm at hQ
  rw [hQ]
  ring

/-- **JON'S EQUATION (d).**

    Multiplying the reduction by `1/κ` and dividing by 2 to absorb the
    factor at the head of `dirichletForm`:

        secondOrderReggeAction W ε / κ
            = (1/κ) · Σ_⟨i,j⟩ ½ · (ξ_i − ξ_j)² · A_{ij}.

    The `Σ_⟨i,j⟩ ½ · (ξ_i − ξ_j)² · A_{ij}` form is the "ordered pair"
    Dirichlet form `(1/2) · dirichletForm`. Below we record the
    explicit κ-normalized identity. -/
theorem weak_field_conformal_reduction_kappa
    {n : ℕ} (W : WeakFieldReggeData n)
    (hSchl : SchlaefliRowSum W)
    (κ : ℝ) (hκ : κ ≠ 0)
    (ε : LogPotential n) :
    secondOrderReggeAction W ε / κ
      = (1 / κ) * (1 / 2) * dirichletForm (edgeArea W) ε := by
  rw [weak_field_conformal_reduction W hSchl ε]
  field_simp

/-- **THE FLAT-VACUUM CONSISTENCY CHECK.**
    On the flat vacuum `ξ ≡ 0`, the Dirichlet form vanishes, so the
    second-order Regge action also vanishes. This is consistent with
    the linearized Regge action being zero on flat backgrounds. -/
theorem secondOrderReggeAction_flat
    {n : ℕ} (W : WeakFieldReggeData n) :
    secondOrderReggeAction W (fun _ : Fin n => (0 : ℝ)) = 0 := by
  unfold secondOrderReggeAction
  have : ∀ i j : Fin n,
          bilinearCoefficient W i j * ((0 : ℝ) + (0 : ℝ)) ^ 2 = 0 := by
    intro i j; ring
  simp only [this, Finset.sum_const_zero, mul_zero]

theorem dirichletForm_flat
    {n : ℕ} (M : Fin n → Fin n → ℝ) :
    dirichletForm M (fun _ : Fin n => (0 : ℝ)) = 0 := by
  unfold dirichletForm
  have : ∀ i j : Fin n, M i j * ((0 : ℝ) - (0 : ℝ)) ^ 2 = 0 := by
    intro i j; ring
  simp only [this, Finset.sum_const_zero, mul_zero]

/-! ## §5. Connection to the existing infrastructure

The reduction here is the *concrete second-order content* of the
hypothesis `EdgeLengthFromPsi.ReggeDeficitLinearizationHypothesis`. We
record the connection: a `WeakFieldReggeData` together with the
Schläfli row-sum property gives a candidate discharge of the
linearization hypothesis at the bilinear level. -/

/-- The Dirichlet weights `A_{ij}` derived from `WeakFieldReggeData`
    define a `WeightedLedgerGraph` provided they are non-negative.
    Non-negativity is a property of the lattice (e.g., automatic for
    regular cubic lattices where `A_{ij}` is a true area), so we
    package it as an explicit hypothesis. -/
def edgeAreaGraph {n : ℕ} (W : WeakFieldReggeData n)
    (hpos : ∀ i j, 0 ≤ edgeArea W i j) : WeightedLedgerGraph n :=
  { weight := edgeArea W
  , weight_nonneg := hpos
  , weight_symm := edgeArea_symm W }

/-- **BRIDGE TO `laplacian_action`.**
    The second-order Regge action equals `(1/2) · laplacian_action`
    on the `edgeAreaGraph`. Concretely:

        S^(2)[ξ] = (1/2) · laplacian_action (edgeAreaGraph W) ε.

    Combined with `EdgeLengthFromPsi.field_curvature_identity_under_linearization`,
    this is the explicit second-order content of the bridge identity:
    "J-cost Dirichlet energy = (1/κ) · Regge sum, at second order in ξ". -/
theorem secondOrder_eq_half_laplacian_action
    {n : ℕ} (W : WeakFieldReggeData n)
    (hSchl : SchlaefliRowSum W)
    (hpos : ∀ i j, 0 ≤ edgeArea W i j)
    (ε : LogPotential n) :
    secondOrderReggeAction W ε
      = (1 / 2) * laplacian_action (edgeAreaGraph W hpos) ε := by
  rw [weak_field_conformal_reduction W hSchl ε]
  unfold dirichletForm laplacian_action edgeAreaGraph
  rfl

/-! ## §5b. Discharging the row-sum condition by a graph Laplacian

The row-sum condition is not a new physical assumption once the
second-variation bilinear is written in Laplacian form. Given symmetric
edge-area weights `A_{ij}`, define the bilinear coefficient matrix

  `M_{ij} = δ_{ij} · Σ_k A_{ik} - A_{ij}`.

Then `Σ_j M_{ij} = 0` exactly. This is the finite-dimensional version of
the flat-background Schläfli statement: a constant conformal rescaling is
a pure scale mode and cannot create curvature.

The diagonal entries of `M` do not contribute to the Dirichlet energy
because `(ξ_i - ξ_i)^2 = 0`; the off-diagonal entries recover the edge
weights `A_{ij}`.
-/

/-- The Laplacian bilinear coefficient matrix associated with symmetric
    edge-area weights `A`. The diagonal is chosen so every row sums to
    zero. -/
def laplacianCoefficient {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  (if i = j then ∑ k : Fin n, A i k else 0) - A i j

/-- The Laplacian coefficient matrix is symmetric when `A` is symmetric. -/
theorem laplacianCoefficient_symm {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, laplacianCoefficient A i j = laplacianCoefficient A j i := by
  intro i j
  unfold laplacianCoefficient
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := by intro h; exact hij h.symm
    simp only [hij, hji, ↓reduceIte, zero_sub]
    rw [hA i j]

/-- The Laplacian coefficient matrix has exact zero row sums. This is the
    theorem-level replacement for the `SchlaefliRowSum` hypothesis in the
    flat conformal sector. -/
theorem laplacianCoefficient_row_sum {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i : Fin n, ∑ j : Fin n, laplacianCoefficient A i j = 0 := by
  intro i
  unfold laplacianCoefficient
  rw [Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin n, (if i = j then ∑ k : Fin n, A i k else 0))
        = ∑ k : Fin n, A i k := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have hne : i ≠ b := fun h => hb h.symm
      simp [hne]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hdiag]
  ring

/-- The weak-field Regge data whose bilinear coefficient is the graph
    Laplacian associated with `A`. We put the whole coefficient into
    `dDeficit`; `dArea = 1` is a harmless normalization because only the
    product `dArea · dDeficit` enters the second variation. -/
def laplacianReggeData {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = A j i) : WeakFieldReggeData n :=
  { dArea := fun _ _ => 1
  , dDeficit := laplacianCoefficient A
  , dArea_symm := by intro i j; rfl
  , dDeficit_symm := laplacianCoefficient_symm A hA
  }

/-- For `laplacianReggeData`, the bilinear coefficient is exactly the
    Laplacian coefficient matrix. -/
theorem bilinearCoefficient_laplacianReggeData {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (i j : Fin n) :
    bilinearCoefficient (laplacianReggeData A hA) i j
      = laplacianCoefficient A i j := by
  unfold bilinearCoefficient laplacianReggeData
  ring

/-- **ROW-SUM DISCHARGE.** The Schläfli/flat-mode row-sum condition holds
    as a theorem for the Laplacian second-variation data. -/
theorem schlaefliRowSum_laplacianReggeData {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i) :
    SchlaefliRowSum (laplacianReggeData A hA) := by
  intro i
  have hrow := laplacianCoefficient_row_sum A i
  simpa only [bilinearCoefficient_laplacianReggeData A hA] using hrow

/-- The Dirichlet form ignores diagonal entries. -/
theorem dirichletForm_diag_irrelevant {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (hOff : ∀ i j, i ≠ j → A i j = B i j)
    (ε : LogPotential n) :
    dirichletForm A ε = dirichletForm B ε := by
  unfold dirichletForm
  apply congrArg ((fun x : ℝ => (1 / 2) * x))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    ring
  · rw [hOff i j hij]

/-- If the genuine Regge component comparison is supplied, then the second-order
Regge action reduces to the Dirichlet form with the supplied geometric
area/face weights.  This is the exact formal shape of the missing
`M_{ij}` versus `area(f_{ij})` comparison. -/
theorem componentComparison_gives_geometric_dirichlet
    {n : ℕ} (W : WeakFieldReggeData n)
    (cmp : ReggeComponentComparison W)
    (ε : LogPotential n) :
    secondOrderReggeAction W ε
      = (1 / 2) * dirichletForm cmp.geometricArea ε := by
  rw [weak_field_conformal_reduction W cmp.schlaefli_row_sum ε]
  congr 1
  apply dirichletForm_diag_irrelevant
  intro i j hij
  unfold edgeArea
  rw [cmp.offDiag_component_match i j hij]
  ring

/-- The edge-area matrix induced by the Laplacian Regge data has the same
    Dirichlet form as the original edge-area weights `A`. Off diagonal it
    equals `A`; diagonal entries are irrelevant. -/
theorem dirichletForm_edgeArea_laplacianReggeData {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (ε : LogPotential n) :
    dirichletForm (edgeArea (laplacianReggeData A hA)) ε
      = dirichletForm A ε := by
  apply dirichletForm_diag_irrelevant
  intro i j hij
  unfold edgeArea
  rw [bilinearCoefficient_laplacianReggeData A hA]
  unfold laplacianCoefficient
  simp [hij]

/-- **Component comparison for Laplacian-form Regge data.**

This closes the `M_{ij} = -area(f_{ij})` comparison for the coefficient
package that the current Lean bridge actually uses: the graph-Laplacian
second-variation data `laplacianReggeData`.

Scope note: this is not yet the full Cayley-Menger derivative computation for
a genuine arbitrary Regge triangulation. It proves that once the geometric
second variation has been put into Laplacian form with symmetric nonnegative
weights `A`, the component-level comparison is exact:

* off diagonal, `bilinearCoefficient = -A`;
* the row sums vanish theoremically;
* the supplied `A` is the geometric-area/face-weight matrix consumed by the
  Dirichlet form.

The remaining hard geometric task is to derive such an `A` from actual
Cayley-Menger/dihedral-angle derivatives for a concrete mesh. -/
def laplacianReggeData_componentComparison {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ReggeComponentComparison (laplacianReggeData A hA) where
  geometricArea := A
  geometricArea_symm := hA
  geometricArea_nonneg := hA_nonneg
  offDiag_component_match := by
    intro i j hij
    rw [bilinearCoefficient_laplacianReggeData A hA]
    unfold laplacianCoefficient
    simp [hij]
  schlaefli_row_sum := schlaefliRowSum_laplacianReggeData A hA

/-- With `laplacianReggeData`, the component comparison theorem specializes the
general comparison result to the expected geometric Dirichlet form. -/
theorem componentComparison_laplacianReggeData_dirichlet {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (ε : LogPotential n) :
    secondOrderReggeAction (laplacianReggeData A hA) ε
      = (1 / 2) * dirichletForm A ε :=
by
  simpa [laplacianReggeData_componentComparison] using
    componentComparison_gives_geometric_dirichlet
      (laplacianReggeData A hA)
      (laplacianReggeData_componentComparison A hA hA_nonneg)
      ε

/-- **UNCONDITIONAL FLAT-SECTOR REDUCTION.** For any symmetric edge-area
    weights `A`, the graph-Laplacian second-variation data automatically
    satisfies the Schläfli row sum and the weak-field conformal Regge
    action reduces to the Dirichlet form with weights `A`. -/
theorem weak_field_conformal_reduction_laplacianData {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (ε : LogPotential n) :
    secondOrderReggeAction (laplacianReggeData A hA) ε
      = (1 / 2) * dirichletForm A ε := by
  rw [weak_field_conformal_reduction
        (laplacianReggeData A hA)
        (schlaefliRowSum_laplacianReggeData A hA) ε]
  rw [dirichletForm_edgeArea_laplacianReggeData A hA ε]

theorem weak_field_conformal_reduction_laplacianData_kappa {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (κ : ℝ) (hκ : κ ≠ 0) (ε : LogPotential n) :
    secondOrderReggeAction (laplacianReggeData A hA) ε / κ
      = (1 / κ) * (1 / 2) * dirichletForm A ε := by
  rw [weak_field_conformal_reduction_laplacianData A hA ε]
  field_simp

/-! ## §6. Certificate -/

structure WeakFieldConformalReggeCert where
  conformal_exact : ∀ {n : ℕ} (a : ℝ) (ha : 0 < a) (ε : LogPotential n)
    (i j : Fin n),
    (conformal_edge_length_field a ha ε).length i j ^ 2
      = a ^ 2 * Real.exp (ε i + ε j)
  conformal_taylor2 : ∀ {n : ℕ} (a : ℝ) (ha : 0 < a) (ε : LogPotential n)
    (i j : Fin n),
    (conformal_edge_length_field a ha ε).length i j ^ 2 / a ^ 2
      = 1 + (ε i + ε j) + (ε i + ε j) ^ 2 / 2
        + conformal_remainder (ε i + ε j)
  graph_laplacian_decomp : ∀ {n : ℕ} (M : Fin n → Fin n → ℝ),
    (∀ i j, M i j = M j i) → (∀ i, ∑ j : Fin n, M i j = 0) →
    ∀ ε, quadraticForm M ε = - dirichletForm M ε
  reduction : ∀ {n : ℕ} (W : WeakFieldReggeData n),
    SchlaefliRowSum W → ∀ ε,
    secondOrderReggeAction W ε
      = (1 / 2) * dirichletForm (edgeArea W) ε
  reduction_kappa : ∀ {n : ℕ} (W : WeakFieldReggeData n),
    SchlaefliRowSum W → ∀ (κ : ℝ), κ ≠ 0 → ∀ ε,
    secondOrderReggeAction W ε / κ
      = (1 / κ) * (1 / 2) * dirichletForm (edgeArea W) ε
  row_sum_discharged_laplacian : ∀ {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i),
    SchlaefliRowSum (laplacianReggeData A hA)
  reduction_laplacian : ∀ {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (ε : LogPotential n),
    secondOrderReggeAction (laplacianReggeData A hA) ε
      = (1 / 2) * dirichletForm A ε
  reduction_laplacian_kappa : ∀ {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i)
    (κ : ℝ), κ ≠ 0 → ∀ ε : LogPotential n,
    secondOrderReggeAction (laplacianReggeData A hA) ε / κ
      = (1 / κ) * (1 / 2) * dirichletForm A ε
  flat_vanishing_action : ∀ {n : ℕ} (W : WeakFieldReggeData n),
    secondOrderReggeAction W (fun _ : Fin n => (0 : ℝ)) = 0
  flat_vanishing_dirichlet : ∀ {n : ℕ} (M : Fin n → Fin n → ℝ),
    dirichletForm M (fun _ : Fin n => (0 : ℝ)) = 0
  remainder_flat : conformal_remainder 0 = 0

theorem weakFieldConformalReggeCert : WeakFieldConformalReggeCert where
  conformal_exact := fun a ha ε i j => conformal_length_sq_exact a ha ε i j
  conformal_taylor2 := fun a ha ε i j => conformal_length_sq_taylor2 a ha ε i j
  graph_laplacian_decomp := fun M hsymm hrow ε =>
    dirichlet_eq_neg_quadratic M hsymm hrow ε
  reduction := fun W hSchl ε => weak_field_conformal_reduction W hSchl ε
  reduction_kappa := fun W hSchl κ hκ ε =>
    weak_field_conformal_reduction_kappa W hSchl κ hκ ε
  row_sum_discharged_laplacian := fun A hA =>
    schlaefliRowSum_laplacianReggeData A hA
  reduction_laplacian := fun A hA ε =>
    weak_field_conformal_reduction_laplacianData A hA ε
  reduction_laplacian_kappa := fun A hA κ hκ ε =>
    weak_field_conformal_reduction_laplacianData_kappa A hA κ hκ ε
  flat_vanishing_action := fun W => secondOrderReggeAction_flat W
  flat_vanishing_dirichlet := fun M => dirichletForm_flat M
  remainder_flat := conformal_remainder_zero

end

end WeakFieldConformalRegge
end Gravity
end IndisputableMonolith
