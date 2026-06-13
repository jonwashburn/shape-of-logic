import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Explicit Cayley-Menger Polynomial for a Tetrahedron (n = 3)

This module begins the rigorous program to close Philip's deeper concern:
the genuine Regge second-variation coefficient matrix `M_ij` computed from
Cayley-Menger / dihedral-angle derivatives must be compared component by
component to `area(f_ij)`.

## Strategy

The classical Cayley-Menger determinant for a tetrahedron is a fixed
polynomial of degree 3 in the six squared edge lengths.  We define it
directly as that polynomial and verify it matches the classical 5x5
determinant on the regular and standard right-angle tetrahedron test
points.  Smoothness in the squared edge lengths then follows by direct
construction from `ContDiff` combinators.

## Edge convention

We index the six edges of a tetrahedron with vertices `0, 1, 2, 3` by
`Fin 6`:

  edge 0 = (0,1),  squared length `α := a 0`
  edge 1 = (0,2),  squared length `β := a 1`
  edge 2 = (0,3),  squared length `γ := a 2`
  edge 3 = (1,2),  squared length `λ := a 3`
  edge 4 = (1,3),  squared length `μ := a 4`
  edge 5 = (2,3),  squared length `ν := a 5`

Opposite-edge pairs are `(0,5)`, `(1,4)`, `(2,3)`.

## Verified polynomial form

```
CM_3(a) = 2 · [ α·ν·(β+γ+λ+μ−α−ν)
              + β·μ·(α+γ+λ+ν−β−μ)
              + γ·λ·(α+β+μ+ν−γ−λ)
              − α·β·λ − α·γ·μ − β·γ·ν − λ·μ·ν ]
```

The classical Cayley relation is `288 · V² = CM_3(a)` for genuine
Euclidean tetrahedra, verified below on two test points.

This polynomial is the workhorse for all later derivative and
component-comparison theorems.
-/

namespace IndisputableMonolith
namespace Geometry
namespace CayleyMengerPolynomial

noncomputable section

/-- Squared edge lengths of a tetrahedron, indexed by `Fin 6`. -/
abbrev SqEdges : Type := Fin 6 → ℝ

/-- The explicit Cayley-Menger polynomial in the six squared edge lengths. -/
def cm3 (a : SqEdges) : ℝ :=
  2 * ( a 0 * a 5 * (a 1 + a 2 + a 3 + a 4 - a 0 - a 5)
      + a 1 * a 4 * (a 0 + a 2 + a 3 + a 5 - a 1 - a 4)
      + a 2 * a 3 * (a 0 + a 1 + a 4 + a 5 - a 2 - a 3)
      - a 0 * a 1 * a 3
      - a 0 * a 2 * a 4
      - a 1 * a 2 * a 5
      - a 3 * a 4 * a 5 )

/-! ## §1. Test points: numerical verification of `288 V² = cm3` -/

/-- Edge data for the unit regular tetrahedron (all squared lengths = 1). -/
def regularUnitSqEdges : SqEdges := fun _ => 1

/-- The Cayley-Menger value of the unit regular tetrahedron is 4.
Classical: `V_unit_regular = √2 / 12`, so `288 V² = 288 / 72 = 4`. -/
theorem cm3_regular_unit : cm3 regularUnitSqEdges = 4 := by
  unfold cm3 regularUnitSqEdges
  norm_num

/-- Edge data for the right-angle unit tetrahedron with three orthogonal
unit edges from a single vertex. -/
def rightAngleUnitSqEdges : SqEdges :=
  fun e =>
    match e with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 1
    | ⟨3, _⟩ => 2
    | ⟨4, _⟩ => 2
    | ⟨5, _⟩ => 2
    | ⟨n+6, h⟩ => absurd h (by omega)

/-- The Cayley-Menger value of the right-angle unit tetrahedron is 8.
Classical: `V = 1/6`, so `288 V² = 288/36 = 8`. -/
theorem cm3_rightAngle_unit : cm3 rightAngleUnitSqEdges = 8 := by
  unfold cm3 rightAngleUnitSqEdges
  norm_num

/-! ## §2. Smoothness of the Cayley-Menger polynomial

We prove `ContDiff ℝ n cm3` for any natural smoothness order `n`.  This
covers all derivative needs (Hessian, Schläfli, etc.).
-/

/-- Each coordinate projection `a ↦ a i` from `(Fin 6 → ℝ)` to `ℝ` is
smooth at any natural order `n`. -/
private theorem contDiff_eval (n : ℕ∞) (i : Fin 6) :
    ContDiff ℝ n (fun a : SqEdges => a i) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) i).contDiff

/-- The Cayley-Menger polynomial is `Cⁿ` for any natural order `n`.
Built explicitly from `ContDiff.add`, `ContDiff.sub`, `ContDiff.mul`. -/
theorem cm3_contDiff (n : ℕ∞) : ContDiff ℝ n cm3 := by
  have h0 := contDiff_eval n 0
  have h1 := contDiff_eval n 1
  have h2 := contDiff_eval n 2
  have h3 := contDiff_eval n 3
  have h4 := contDiff_eval n 4
  have h5 := contDiff_eval n 5
  have hconst : ContDiff ℝ n (fun _ : SqEdges => (2 : ℝ)) := contDiff_const
  -- Build linear combinations.
  have s1 : ContDiff ℝ n (fun a : SqEdges => a 1 + a 2 + a 3 + a 4 - a 0 - a 5) :=
    ContDiff.sub (ContDiff.sub
      (ContDiff.add (ContDiff.add (ContDiff.add h1 h2) h3) h4) h0) h5
  have s2 : ContDiff ℝ n (fun a : SqEdges => a 0 + a 2 + a 3 + a 5 - a 1 - a 4) :=
    ContDiff.sub (ContDiff.sub
      (ContDiff.add (ContDiff.add (ContDiff.add h0 h2) h3) h5) h1) h4
  have s3 : ContDiff ℝ n (fun a : SqEdges => a 0 + a 1 + a 4 + a 5 - a 2 - a 3) :=
    ContDiff.sub (ContDiff.sub
      (ContDiff.add (ContDiff.add (ContDiff.add h0 h1) h4) h5) h2) h3
  -- Three "balanced" cubic terms.
  have c1 : ContDiff ℝ n (fun a : SqEdges =>
      a 0 * a 5 * (a 1 + a 2 + a 3 + a 4 - a 0 - a 5)) :=
    ContDiff.mul (ContDiff.mul h0 h5) s1
  have c2 : ContDiff ℝ n (fun a : SqEdges =>
      a 1 * a 4 * (a 0 + a 2 + a 3 + a 5 - a 1 - a 4)) :=
    ContDiff.mul (ContDiff.mul h1 h4) s2
  have c3 : ContDiff ℝ n (fun a : SqEdges =>
      a 2 * a 3 * (a 0 + a 1 + a 4 + a 5 - a 2 - a 3)) :=
    ContDiff.mul (ContDiff.mul h2 h3) s3
  -- Four monomial cubic terms.
  have nA : ContDiff ℝ n (fun a : SqEdges => a 0 * a 1 * a 3) :=
    ContDiff.mul (ContDiff.mul h0 h1) h3
  have nB : ContDiff ℝ n (fun a : SqEdges => a 0 * a 2 * a 4) :=
    ContDiff.mul (ContDiff.mul h0 h2) h4
  have nC : ContDiff ℝ n (fun a : SqEdges => a 1 * a 2 * a 5) :=
    ContDiff.mul (ContDiff.mul h1 h2) h5
  have nD : ContDiff ℝ n (fun a : SqEdges => a 3 * a 4 * a 5) :=
    ContDiff.mul (ContDiff.mul h3 h4) h5
  have inner : ContDiff ℝ n (fun a : SqEdges =>
        a 0 * a 5 * (a 1 + a 2 + a 3 + a 4 - a 0 - a 5)
      + a 1 * a 4 * (a 0 + a 2 + a 3 + a 5 - a 1 - a 4)
      + a 2 * a 3 * (a 0 + a 1 + a 4 + a 5 - a 2 - a 3)
      - a 0 * a 1 * a 3
      - a 0 * a 2 * a 4
      - a 1 * a 2 * a 5
      - a 3 * a 4 * a 5 ) :=
    ContDiff.sub (ContDiff.sub (ContDiff.sub (ContDiff.sub
      (ContDiff.add (ContDiff.add c1 c2) c3) nA) nB) nC) nD
  show ContDiff ℝ n cm3
  unfold cm3
  exact ContDiff.mul hconst inner

/-- An immediate corollary: `cm3` is continuous. -/
theorem cm3_continuous : Continuous cm3 :=
  (cm3_contDiff 0).continuous

/-! ## §3. Polynomial behavior under uniform scaling

If all squared edge lengths are scaled by `s`, the CM polynomial scales by
`s³`.  Classical: `V → s^{3/2} V`, hence `V² → s³ V²`, hence
`CM = 288 V² → s³ · CM`.  This is a useful structural sanity check. -/

theorem cm3_scaling (a : SqEdges) (s : ℝ) :
    cm3 (fun e => s * a e) = s ^ 3 * cm3 a := by
  unfold cm3
  ring

/-- A trivial but useful corollary: the regular CM value at common
squared-length `s` equals `s³ · 4`. -/
theorem cm3_constSq (s : ℝ) : cm3 (fun _ => s) = 4 * s ^ 3 := by
  have h := cm3_scaling regularUnitSqEdges s
  have h1 : cm3 regularUnitSqEdges = 4 := cm3_regular_unit
  have h2 : (fun e : Fin 6 => s * regularUnitSqEdges e) = (fun _ : Fin 6 => s) := by
    funext e
    unfold regularUnitSqEdges
    ring
  have h3 : cm3 (fun _ : Fin 6 => s) = s ^ 3 * cm3 regularUnitSqEdges := by
    rw [← h2]; exact h
  rw [h3, h1]
  ring

end

end CayleyMengerPolynomial
end Geometry
end IndisputableMonolith
