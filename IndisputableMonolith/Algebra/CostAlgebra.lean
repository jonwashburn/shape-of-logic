/-
Copyright (c) 2026 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Cost.FunctionalEquationAczel

/-!
# Cost Algebra — The Foundational Algebraic Object of Recognition Science

This module formalizes the **cost algebra**: the algebraic structure arising from
the J-cost function J(x) = ½(x + x⁻¹) − 1 and its Recognition Composition Law.

## The Primitive

The Recognition Composition Law (RCL) is:
  J(xy) + J(x/y) = 2·J(x)·J(y) + 2·J(x) + 2·J(y)

This is the **one primitive** from which all of Recognition Science flows.

## Algebraic Structure

The cost algebra has several layers:

1. **Multiplicative monoid** (ℝ₊, ·, 1) with J as a pseudometric
2. **The RCL as a 2-cocycle condition** — it is a compatibility law
   for how costs compose under multiplication
3. **Log-coordinate ring** — under t = ln(x), J becomes cosh(t) − 1,
   and the RCL becomes the standard d'Alembert equation
4. **Reciprocal involution** — x ↦ 1/x is an algebra automorphism

## Key Results (Proved)

- `RCL_holds` : J satisfies the Recognition Composition Law
- `J_reciprocal_auto` : J(x) = J(1/x) (involution invariance)
- `J_multiplicative_identity` : J(1) = 0 (identity has zero cost)
- `costCompose_assoc_defect` : the raw cost-composition associator is `2 * (a - c)`
- `defectDist_quasi_triangle_local` : local quasi-triangle bound for bounded ratios
- `ShiftedCarrier` : the shifted operation `A • B = 2AB` is a commutative monoid on `[1/2, ∞)`

## Connection to Full Theory

CostAlgebra is Level 1 of Recognition Algebra:
  RCL → J unique (T5) → φ forced (T6) → 8-tick (T7) → D=3 (T8) → all physics

Lean module: `IndisputableMonolith.Algebra.CostAlgebra`
-/

namespace IndisputableMonolith
namespace Algebra
namespace CostAlgebra

open Real IndisputableMonolith.Cost
open IndisputableMonolith.Cost.FunctionalEquation

/-! ## §1. The J-Cost Function as Algebraic Primitive -/

/-- The J-cost function: the unique cost satisfying the Recognition Composition Law.
    J(x) = ½(x + x⁻¹) − 1 -/
noncomputable def J (x : ℝ) : ℝ := Jcost x

/-- **Normalization**: The multiplicative identity has zero cost. -/
theorem J_at_one : J 1 = 0 := Jcost_unit0

/-- **Reciprocal symmetry**: Cost is invariant under inversion.
    This is the algebraic encoding of "double-entry": every ratio x
    and its reciprocal 1/x carry the same cost. -/
theorem J_reciprocal (x : ℝ) (hx : 0 < x) : J x = J x⁻¹ :=
  Jcost_symm hx

/-- **Non-negativity**: All costs are non-negative on ℝ₊. -/
theorem J_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ J x :=
  Jcost_nonneg hx

/-- **Defect characterization**: J(x) = (x − 1)²/(2x) for x ≠ 0. -/
theorem J_defect_form (x : ℝ) (hx : x ≠ 0) : J x = (x - 1) ^ 2 / (2 * x) :=
  Jcost_eq_sq hx

/-! ## §2. The Recognition Composition Law (RCL) -/

/-- The **Recognition Composition Law**: the ONE primitive of Recognition Science.

    J(xy) + J(x/y) = 2·J(x)·J(y) + 2·J(x) + 2·J(y)

    In the log-coordinate form (t = ln x, u = ln y), this becomes:
    G(t+u) + G(t−u) = 2·G(t)·G(u) + 2·(G(t) + G(u))

    which is a calibrated multiplicative form of the d'Alembert functional equation. -/
def SatisfiesRCL (F : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    F (x * y) + F (x / y) = 2 * F x * F y + 2 * F x + 2 * F y

/-- **THEOREM: J satisfies the RCL.**
    This is the foundational identity — everything else follows. -/
theorem RCL_holds : SatisfiesRCL J := by
  intro x y hx hy
  unfold J Jcost
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hxy_div0 : x / y ≠ 0 := div_ne_zero hx0 hy0
  field_simp [hx0, hy0, hxy0, hxy_div0]
  ring

/-! ## §3. Cost Composition as Algebraic Operation -/

/-- **Cost-composition**: The binary operation on costs induced by the RCL.
    Given two "cost levels" a = J(x) and b = J(y), the composed cost is:
    a ★ b = 2ab + 2a + 2b = 2(a+1)(b+1) − 2

    This captures how costs combine under multiplication of ratios. -/
noncomputable def costCompose (a b : ℝ) : ℝ := 2 * a * b + 2 * a + 2 * b

/-- Notation for cost composition -/
infixl:70 " ★ " => costCompose

/-- **THEOREM: Cost composition is commutative.** -/
theorem costCompose_comm (a b : ℝ) : a ★ b = b ★ a := by
  unfold costCompose; ring

/-- **THEOREM: Associator defect for raw RCL composition.**
    The unnormalized RCL form is not strictly associative; the defect is `2*(a-c)`. -/
theorem costCompose_assoc_defect (a b c : ℝ) :
    (a ★ b) ★ c = a ★ (b ★ c) + 2 * (a - c) := by
  unfold costCompose
  ring_nf

/-- The raw `★`-operation is flexible. -/
theorem costCompose_flexible (a b : ℝ) : (a ★ b) ★ a = a ★ (b ★ a) := by
  simpa using (costCompose_assoc_defect a b a)

/-- **THEOREM: Left-zero evaluation for raw RCL composition.** -/
theorem costCompose_zero_left (a : ℝ) : (0 : ℝ) ★ a = 2 * a := by
  unfold costCompose
  ring_nf

theorem costCompose_zero_right (a : ℝ) : a ★ (0 : ℝ) = 2 * a := by
  unfold costCompose
  ring_nf

/-- **THEOREM: Cost composition preserves non-negativity.**
    If a ≥ 0 and b ≥ 0, then a ★ b ≥ 0. -/
theorem costCompose_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a ★ b := by
  unfold costCompose
  have h1 : 0 ≤ 2 * a * b := by positivity
  have h2 : 0 ≤ 2 * a := by linarith
  have h3 : 0 ≤ 2 * b := by linarith
  linarith

/-- **The factored form**: a ★ b = 2(a+1)(b+1) − 2.
    This reveals the monoid structure: if we set A = a+1, B = b+1,
    then A ★' B = 2AB − 2, and (A ★' B) + 1 = 2AB − 1. -/
theorem costCompose_factored (a b : ℝ) :
    a ★ b = 2 * (a + 1) * (b + 1) - 2 := by
  unfold costCompose; ring

/-- The nonnegative `★`-magma has no identity element. -/
theorem costCompose_no_identity :
    ¬ ∃ e : ℝ, 0 ≤ e ∧ ∀ a : ℝ, 0 ≤ a → e ★ a = a := by
  intro h
  rcases h with ⟨e, he_nonneg, he⟩
  have h0 : e ★ 0 = 0 := he 0 le_rfl
  rw [costCompose_zero_right] at h0
  have he0 : e = 0 := by
    linarith
  have h1 : (0 : ℝ) ★ 1 = 1 := by
    simpa [he0] using he 1 (by positivity)
  rw [costCompose_zero_left] at h1
  norm_num at h1

/-- Third-power associativity: the triple `★`-power is unambiguous. -/
theorem costCompose_power_assoc (a : ℝ) : (a ★ a) ★ a = a ★ (a ★ a) := by
  simpa using (costCompose_flexible a a)

/-- Four copies already witness failure of full power-associativity. -/
theorem costCompose_fourfold_power_counterexample :
    (((1 : ℝ) ★ 1) ★ 1) ★ 1 ≠ ((1 : ℝ) ★ 1) ★ ((1 : ℝ) ★ 1) := by
  norm_num [costCompose]

/-! ## §4. The Shifted Monoid: H = J + 1 -/

/-- The shifted cost: H(x) = J(x) + 1 = ½(x + x⁻¹).
    Under H, the RCL becomes the standard d'Alembert equation:
    H(xy) + H(x/y) = 2·H(x)·H(y) -/
noncomputable def H (x : ℝ) : ℝ := J x + 1

/-- H at identity equals 1. -/
theorem H_at_one : H 1 = 1 := by
  unfold H; rw [J_at_one]; ring

/-- **THEOREM: H satisfies the standard d'Alembert equation.**
    H(xy) + H(x/y) = 2·H(x)·H(y)

    This is the canonical form of the multiplicative d'Alembert
    functional equation, whose unique continuous solution is cosh. -/
theorem H_dAlembert (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    H (x * y) + H (x / y) = 2 * H x * H y := by
  unfold H J
  have rcl := RCL_holds x y hx hy
  have hsum :
      Jcost (x * y) + Jcost (x / y) + 2 =
        2 * Jcost x * Jcost y + 2 * Jcost x + 2 * Jcost y + 2 := by
    have h' := congrArg (fun z : ℝ => z + 2) rcl
    simpa [add_assoc, add_left_comm, add_comm] using h'
  have hmul :
      2 * (Jcost x + 1) * (Jcost y + 1) =
        2 * Jcost x * Jcost y + 2 * Jcost x + 2 * Jcost y + 2 := by
    ring
  calc
    Jcost (x * y) + 1 + (Jcost (x / y) + 1)
        = Jcost (x * y) + Jcost (x / y) + 2 := by ring
    _ = 2 * Jcost x * Jcost y + 2 * Jcost x + 2 * Jcost y + 2 := hsum
    _ = 2 * (Jcost x + 1) * (Jcost y + 1) := hmul.symm

/-! ## §4a. The Shifted Monoid on `[1/2, ∞)` -/

/-- The carrier of the shifted monoid from Theorem 2.7:
    real values bounded below by `1/2`. -/
abbrev ShiftedCarrier := {A : ℝ // (1 / 2 : ℝ) ≤ A}

/-- The shifted operation `A • B = 2AB` on `[1/2, ∞)`. -/
def shiftedCompose (A B : ShiftedCarrier) : ShiftedCarrier := by
  refine ⟨2 * A.1 * B.1, ?_⟩
  nlinarith [A.2, B.2]

instance : Mul ShiftedCarrier := ⟨shiftedCompose⟩

/-- The identity element `1/2` for the shifted monoid. -/
noncomputable def shiftedUnit : ShiftedCarrier := ⟨1 / 2, le_rfl⟩

noncomputable instance : One ShiftedCarrier := ⟨shiftedUnit⟩

@[simp] theorem shiftedUnit_val : (shiftedUnit : ℝ) = 1 / 2 := rfl

@[simp] theorem shiftedCompose_val (A B : ShiftedCarrier) :
    ((A * B : ShiftedCarrier) : ℝ) = 2 * A.1 * B.1 := rfl

noncomputable instance : CommMonoid ShiftedCarrier where
  mul := (· * ·)
  mul_assoc A B C := by
    apply Subtype.ext
    change 2 * (2 * A.1 * B.1) * C.1 = 2 * A.1 * (2 * B.1 * C.1)
    ring
  one := 1
  one_mul A := by
    apply Subtype.ext
    change 2 * (1 / 2 : ℝ) * A.1 = A.1
    ring
  mul_one A := by
    apply Subtype.ext
    change 2 * A.1 * (1 / 2 : ℝ) = A.1
    ring
  mul_comm A B := by
    apply Subtype.ext
    change 2 * A.1 * B.1 = 2 * B.1 * A.1
    ring

/-- `H(x)` lands in `[1, ∞)` on positive reals, hence in `[1/2, ∞)` as well. -/
theorem H_ge_one (x : ℝ) (hx : 0 < x) : 1 ≤ H x := by
  unfold H
  have hJ : 0 ≤ J x := J_nonneg x hx
  linarith

/-- A positive input determines a canonical shifted-monoid element. -/
noncomputable def shiftedOfH (x : ℝ) (hx : 0 < x) : ShiftedCarrier :=
  ⟨H x, by
    have hHx : 1 ≤ H x := H_ge_one x hx
    linarith⟩

/-- The narrower `[1, ∞)` range supporting the actual values of `H`. -/
abbrev ShiftedHValue := {A : ℝ // 1 ≤ A}

/-- The shifted operation is closed on the `H`-value range `[1, ∞)`. -/
def shiftedComposeH (A B : ShiftedHValue) : ShiftedHValue := by
  refine ⟨2 * A.1 * B.1, ?_⟩
  nlinarith [A.2, B.2]

instance : Mul ShiftedHValue := ⟨shiftedComposeH⟩

@[simp] theorem shiftedComposeH_val (A B : ShiftedHValue) :
    ((A * B : ShiftedHValue) : ℝ) = 2 * A.1 * B.1 := rfl

instance : CommSemigroup ShiftedHValue where
  mul := (· * ·)
  mul_assoc A B C := by
    apply Subtype.ext
    change 2 * (2 * A.1 * B.1) * C.1 = 2 * A.1 * (2 * B.1 * C.1)
    ring
  mul_comm A B := by
    apply Subtype.ext
    change 2 * A.1 * B.1 = 2 * B.1 * A.1
    ring

/-- The `H`-value of a positive real belongs to the closed range `[1, ∞)`. -/
noncomputable def shiftedHValueOf (x : ℝ) (hx : 0 < x) : ShiftedHValue :=
  ⟨H x, H_ge_one x hx⟩

/-! ## §5. The Defect Pseudometric -/

/-- **Defect distance**: d(x,y) = J(x/y) measures the "cost of deviation"
    between two positive reals.

    Properties:
    - d(x,x) = 0 (identity)
    - d(x,y) = d(y,x) (symmetry, from J reciprocity)
    - d(x,y) ≥ 0 (non-negativity) -/
noncomputable def defectDist (x y : ℝ) : ℝ := J (x / y)

/-- **PROVED: Defect distance is zero at identity.** -/
theorem defectDist_self (x : ℝ) (hx : 0 < x) : defectDist x x = 0 := by
  unfold defectDist
  rw [div_self (ne_of_gt hx)]
  exact J_at_one

/-- **PROVED: Defect distance is symmetric.** -/
theorem defectDist_symm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    defectDist x y = defectDist y x := by
  unfold defectDist
  have h : x / y > 0 := div_pos hx hy
  rw [J_reciprocal (x / y) h]
  congr 1
  field_simp

/-- **PROVED: Defect distance is non-negative.** -/
theorem defectDist_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ defectDist x y :=
  J_nonneg (x / y) (div_pos hx hy)

/-! ## §5a. Quasi-Triangle Bounds for the Defect Distance -/

/-- On the symmetric interval `[1 / M, M]`, the canonical cost is bounded by
    its endpoint value `J(M)`. -/
theorem J_le_J_of_inv_le_le {r M : ℝ} (hM : 1 ≤ M) (hr : 0 < r)
    (hr_lower : 1 / M ≤ r) (hr_upper : r ≤ M) :
    J r ≤ J M := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM
  have hfactor :
      M + M⁻¹ - (r + r⁻¹) = ((M - r) * (M * r - 1)) / (M * r) := by
    field_simp [hMpos.ne', hr.ne']
    ring
  have hMr_ge_one : 1 ≤ M * r := by
    have hmul := mul_le_mul_of_nonneg_left hr_lower (le_of_lt hMpos)
    simpa [one_div, hMpos.ne'] using hmul
  have hnum_nonneg : 0 ≤ (M - r) * (M * r - 1) := by
    have h1 : 0 ≤ M - r := sub_nonneg.mpr hr_upper
    have h2 : 0 ≤ M * r - 1 := by linarith
    exact mul_nonneg h1 h2
  have hden_pos : 0 < M * r := mul_pos hMpos hr
  have hsum_le : r + r⁻¹ ≤ M + M⁻¹ := by
    have hdiff_nonneg : 0 ≤ M + M⁻¹ - (r + r⁻¹) := by
      rw [hfactor]
      exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
    linarith
  unfold J Jcost
  linarith

/-- Ratio-bounded pairs have defect at most `J(M)`. -/
theorem defectDist_le_J_of_ratio_bounds {M x y : ℝ} (hM : 1 ≤ M)
    (hx : 0 < x) (hy : 0 < y)
    (hxy_lower : 1 / M ≤ x / y) (hxy_upper : x / y ≤ M) :
    defectDist x y ≤ J M := by
  unfold defectDist
  exact J_le_J_of_inv_le_le hM (div_pos hx hy) hxy_lower hxy_upper

/-- The local quasi-triangle constant from Proposition 2.6. -/
theorem quasiTriangleConstant_eq (M : ℝ) :
    2 + J M = (M + 2 + M⁻¹) / 2 := by
  unfold J Jcost
  ring

/-- Proposition 2.6, local form: on bounded edge-ratios, the defect distance
    satisfies the quasi-triangle bound with the paper's constant `K_M`. -/
theorem defectDist_quasi_triangle_local {M x y z : ℝ} (hM : 1 ≤ M)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy_lower : 1 / M ≤ x / y) (hxy_upper : x / y ≤ M)
    (hyz_lower : 1 / M ≤ y / z) (hyz_upper : y / z ≤ M) :
    defectDist x z ≤ ((M + 2 + M⁻¹) / 2) * (defectDist x y + defectDist y z) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM
  have hxy_pos : 0 < x / y := div_pos hx hy
  have hyz_pos : 0 < y / z := div_pos hy hz
  have hratio : (x / y) * (y / z) = x / z := by
    field_simp [hy.ne', hz.ne']
  have hsub :
      J ((x / y) * (y / z)) ≤
        2 * J (x / y) + 2 * J (y / z) + 2 * J (x / y) * J (y / z) := by
    simpa [J] using (Jcost_submult (x := x / y) (y := y / z) hxy_pos hyz_pos)
  have hsub' :
      defectDist x z ≤
        2 * defectDist x y + 2 * defectDist y z + 2 * defectDist x y * defectDist y z := by
    unfold defectDist
    simpa [hratio] using hsub
  have hxy_bound : defectDist x y ≤ J M :=
    defectDist_le_J_of_ratio_bounds hM hx hy hxy_lower hxy_upper
  have hyz_bound : defectDist y z ≤ J M :=
    defectDist_le_J_of_ratio_bounds hM hy hz hyz_lower hyz_upper
  have hxy_nonneg : 0 ≤ defectDist x y := defectDist_nonneg x y hx hy
  have hyz_nonneg : 0 ≤ defectDist y z := defectDist_nonneg y z hy hz
  have hM_nonneg : 0 ≤ J M := J_nonneg M hMpos
  have hcross :
      2 * defectDist x y * defectDist y z ≤ J M * (defectDist x y + defectDist y z) := by
    have hleft :
        defectDist x y * defectDist y z ≤ J M * defectDist y z := by
      exact mul_le_mul_of_nonneg_right hxy_bound hyz_nonneg
    have hright :
        defectDist x y * defectDist y z ≤ defectDist x y * J M := by
      exact mul_le_mul_of_nonneg_left hyz_bound hxy_nonneg
    have hsum :
        defectDist x y * defectDist y z + defectDist x y * defectDist y z ≤
          J M * defectDist y z + defectDist x y * J M := by
      exact add_le_add hleft hright
    nlinarith [hsum]
  calc
    defectDist x z
        ≤ 2 * defectDist x y + 2 * defectDist y z + 2 * defectDist x y * defectDist y z := hsub'
    _ ≤ 2 * defectDist x y + 2 * defectDist y z + J M * (defectDist x y + defectDist y z) := by
          nlinarith [hcross]
    _ = (2 + J M) * (defectDist x y + defectDist y z) := by ring
    _ = ((M + 2 + M⁻¹) / 2) * (defectDist x y + defectDist y z) := by
          rw [quasiTriangleConstant_eq]

/-- Proposition 2.6, global form: no finite quasi-triangle constant works on
    all positive triples. -/
theorem defectDist_no_global_quasi_triangle :
    ¬ ∃ K : ℝ, 1 < K ∧
      ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
        defectDist x z ≤ K * (defectDist x y + defectDist y z) := by
  intro h
  rcases h with ⟨K, hK, htriangle⟩
  let r : ℝ := 2 * K
  have hKpos : 0 < K := lt_trans (by norm_num : (0 : ℝ) < 1) hK
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr_sq : 0 < r ^ 2 := by positivity
  have hineq := htriangle 1 r (r ^ 2) (by positivity) hr hr_sq
  have hd1 : defectDist 1 r = J r := by
    unfold defectDist
    simpa [one_div] using (J_reciprocal r hr).symm
  have hd2 : defectDist r (r ^ 2) = J r := by
    unfold defectDist
    have hr0 : r ≠ 0 := hr.ne'
    have hdiv : r / r ^ 2 = r⁻¹ := by
      rw [pow_two, div_eq_mul_inv]
      field_simp [hr0]
    rw [hdiv]
    exact (J_reciprocal r hr).symm
  have hd3 : defectDist 1 (r ^ 2) = J (r ^ 2) := by
    unfold defectDist
    simpa [one_div] using (J_reciprocal (r ^ 2) hr_sq).symm
  have hRCL := RCL_holds r r hr hr
  have hr_div : r / r = 1 := by field_simp [hr.ne']
  rw [hr_div, J_at_one] at hRCL
  have hJsq : J (r ^ 2) = 2 * J r * J r + 4 * J r := by
    have hpow : r * r = r ^ 2 := by ring
    rw [hpow] at hRCL
    nlinarith
  have hineq' : 2 * J r * J r + 4 * J r ≤ K * (2 * J r) := by
    calc
      2 * J r * J r + 4 * J r = defectDist 1 (r ^ 2) := by rw [hd3, hJsq]
      _ ≤ K * (defectDist 1 r + defectDist r (r ^ 2)) := hineq
      _ = K * (2 * J r) := by rw [hd1, hd2]; ring
  have hJr_nonneg : 0 ≤ J r := J_nonneg r hr
  have hJr_ne : J r ≠ 0 := by
    intro hzero
    have hr_one : r = 1 := (Jcost_eq_zero_iff r hr).mp (by simpa [J] using hzero)
    have : (1 : ℝ) < r := by
      dsimp [r]
      linarith
    linarith
  have hJr_pos : 0 < J r := lt_of_le_of_ne hJr_nonneg (Ne.symm hJr_ne)
  have hupper : J r + 2 ≤ K := by
    nlinarith [hineq', hJr_pos]
  have hJr_eval : J r = K - 1 + 1 / (4 * K) := by
    dsimp [r]
    unfold J Jcost
    field_simp [hKpos.ne']
    ring
  have hfrac_pos : 0 < 1 / (4 * K) := by positivity
  have hlower : K < J r + 2 := by
    nlinarith [hJr_eval, hfrac_pos]
  linarith

/-! ## §5b. Left-Cancellation for Raw Cost Composition -/

/-- Subtracting two raw cost-compositions factors through the positive
    coefficient `2a + 2`. -/
theorem costCompose_sub_left (a b₁ b₂ : ℝ) :
    a ★ b₁ - a ★ b₂ = (2 * a + 2) * (b₁ - b₂) := by
  unfold costCompose
  ring

/-- Equation (2.6): left-cancellation holds on the nonnegative cost range. -/
theorem costCompose_left_cancel {a b₁ b₂ : ℝ} (ha : 0 ≤ a)
    (h : a ★ b₁ = a ★ b₂) : b₁ = b₂ := by
  have hsub : a ★ b₁ - a ★ b₂ = 0 := sub_eq_zero.mpr h
  rw [costCompose_sub_left] at hsub
  have hcoeff : 2 * a + 2 ≠ 0 := by
    linarith
  have hdiff : b₁ - b₂ = 0 := by
    rcases mul_eq_zero.mp hsub with hzero | hzero
    · exact False.elim (hcoeff hzero)
    · exact hzero
  linarith

/-- Right-cancellation follows from commutativity of `★`. -/
theorem costCompose_right_cancel {a₁ a₂ b : ℝ} (hb : 0 ≤ b)
    (h : a₁ ★ b = a₂ ★ b) : a₁ = a₂ := by
  rw [costCompose_comm a₁ b, costCompose_comm a₂ b] at h
  exact costCompose_left_cancel hb h

/-! ## §5b. Recognition Cost Systems and Window Aggregation -/

/-- The ambient domain of recognition cost systems: positive reals. -/
def PositiveDomain : Set ℝ := Set.Ioi 0

/-- A recognition cost system packages a ratio cost, a conservation
    functional, and a finite window length. -/
structure RecognitionCostSystem (n : ℕ) where
  cost : ℝ → ℝ
  rcl : SatisfiesRCL cost
  sigma : (Fin n → ℝ) → ℝ
  W : ℕ
  W_pos : 0 < W

/-- The canonical conservation functional from Definition 2.7:
    sum of logarithms on positive coordinates. -/
noncomputable def canonicalSigma {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (x i)

/-- The canonical recognition cost system `(ℝ₊, J, σ, W)`. -/
noncomputable def canonicalRecognitionCostSystem (n W : ℕ) (hW : 0 < W) :
    RecognitionCostSystem n where
  cost := J
  rcl := RCL_holds
  sigma := canonicalSigma
  W := W
  W_pos := hW

/-- The canonical recognition cost system uses the positive reals as state space. -/
theorem canonicalRecognitionCostSystem_domain :
    PositiveDomain = Set.Ioi 0 := rfl

/-- The canonical recognition cost system inherits balance. -/
theorem canonicalRecognitionCostSystem_cost_one {n W : ℕ} (hW : 0 < W) :
    (canonicalRecognitionCostSystem n W hW).cost 1 = 0 :=
  J_at_one

/-- The canonical recognition cost system inherits reciprocal symmetry. -/
theorem canonicalRecognitionCostSystem_cost_inv {n W : ℕ} (hW : 0 < W)
    {x : ℝ} (hx : 0 < x) :
    (canonicalRecognitionCostSystem n W hW).cost x =
      (canonicalRecognitionCostSystem n W hW).cost x⁻¹ :=
  J_reciprocal x hx

/-- The one-step shift on sequences. -/
def seqShift {α : Type*} (y : ℕ → α) : ℕ → α := fun n => y (n + 1)

/-- The `W`-block window-sum operator from Proposition 2.8. -/
def windowSums {α : Type*} [AddCommMonoid α] (W : ℕ) (y : ℕ → α) : ℕ → α :=
  fun k => Finset.sum (Finset.range W) (fun j => y (W * k + j))

/-- Shifting the input sequence by one full window shifts the windowed output
    by one index. -/
theorem windowSums_shift_equivariant {α : Type*} [AddCommMonoid α]
    (W : ℕ) (y : ℕ → α) :
    windowSums W (fun n => y (n + W)) = seqShift (windowSums W y) := by
  funext k
  unfold windowSums seqShift
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Nat.mul_add, Nat.mul_one]
  ac_rfl

/-! ## §6. The Cost Algebra Structure -/

/-- **The Cost Algebra**: a structure packaging the complete algebraic data.

    This is the fundamental algebraic object of Recognition Science:
    - Carrier: ℝ₊ (positive reals)
    - Binary operation: multiplication (inherited from ℝ)
    - Cost function: J satisfying RCL
    - Identity: 1 with J(1) = 0
    - Involution: x ↦ 1/x preserving J

    From this single structure, all of RS is derived. -/
structure CostAlgebraData where
  /-- The cost function -/
  cost : ℝ → ℝ
  /-- Satisfies the Recognition Composition Law -/
  rcl : SatisfiesRCL cost
  /-- Normalization: cost at identity is zero -/
  normalized : cost 1 = 0
  /-- Reciprocal symmetry -/
  symmetric : ∀ x : ℝ, 0 < x → cost x = cost x⁻¹
  /-- Non-negativity on ℝ₊ -/
  nonneg : ∀ x : ℝ, 0 < x → 0 ≤ cost x

/-- **THEOREM: J provides the canonical CostAlgebraData.** -/
noncomputable def canonicalCostAlgebra : CostAlgebraData where
  cost := J
  rcl := RCL_holds
  normalized := J_at_one
  symmetric := J_reciprocal
  nonneg := J_nonneg

/-- **THEOREM: The canonical cost algebra is unique.**
    Any CostAlgebraData with the same axioms + calibration J''(1)=1
    must have cost = J. (This is T5 in the forcing chain.) -/
theorem cost_algebra_unique (C : CostAlgebraData)
    (hCalib : deriv (deriv (fun t => C.cost (Real.exp t))) 0 = 1)
    (hCont : ContinuousOn C.cost (Set.Ioi 0))
    (hSmooth : dAlembert_continuous_implies_smooth_hypothesis (IndisputableMonolith.Cost.FunctionalEquation.H C.cost))
    (hODE : dAlembert_to_ODE_hypothesis (IndisputableMonolith.Cost.FunctionalEquation.H C.cost))
    (hContReg : ode_regularity_continuous_hypothesis (IndisputableMonolith.Cost.FunctionalEquation.H C.cost))
    (hDiffReg : ode_regularity_differentiable_hypothesis (IndisputableMonolith.Cost.FunctionalEquation.H C.cost))
    (hBoot : ode_linear_regularity_bootstrap_hypothesis (IndisputableMonolith.Cost.FunctionalEquation.H C.cost)) :
    ∀ x : ℝ, 0 < x → C.cost x = J x := by
  have hRecip : IsReciprocalCost C.cost := by
    intro x hx
    simpa using C.symmetric x hx
  have hNorm : IsNormalized C.cost := by
    simpa [IsNormalized] using C.normalized
  have hComp : SatisfiesCompositionLaw C.cost := by
    intro x y hx hy
    exact C.rcl x y hx hy
  have hCal : IsCalibrated C.cost := by
    simpa [IsCalibrated, G] using hCalib
  intro x hx
  simpa [J] using
    (law_of_logic_forces_jcost_with_regularization C.cost hRecip hNorm hComp hCal hCont
      hSmooth hODE hContReg hDiffReg hBoot x hx)

/-- **THEOREM (T5, clean form): The canonical cost algebra is unique, via Aczél's theorem.**

    This is the same result as `cost_algebra_unique` but with no regularity hypothesis
    parameters. The single Aczél axiom (`aczel_dAlembert_smooth`) is used internally
    by `law_of_logic_forces_jcost_aczel`. -/
theorem cost_algebra_unique_aczel (C : CostAlgebraData)
    (hCalib : deriv (deriv (fun t => C.cost (Real.exp t))) 0 = 1)
    (hCont : ContinuousOn C.cost (Set.Ioi 0)) :
    ∀ x : ℝ, 0 < x → C.cost x = J x := by
  have hRecip : IsReciprocalCost C.cost := fun x hx => by simpa using C.symmetric x hx
  have hNorm : IsNormalized C.cost := by simpa [IsNormalized] using C.normalized
  have hComp : SatisfiesCompositionLaw C.cost := fun x y hx hy => C.rcl x y hx hy
  have hCal : IsCalibrated C.cost := by simpa [IsCalibrated, G] using hCalib
  intro x hx
  simpa [J] using law_of_logic_forces_jcost_aczel C.cost hRecip hNorm hComp hCal hCont x hx

/-! ## §7. Morphisms of Cost Algebras -/

/-- A **morphism of cost algebras** is a multiplicative map that preserves cost. -/
structure CostMorphism (C₁ C₂ : CostAlgebraData) where
  /-- The underlying map on ℝ₊ -/
  map : ℝ → ℝ
  /-- Preserves positivity -/
  pos : ∀ x, 0 < x → 0 < map x
  /-- Multiplicative: f(xy) = f(x)·f(y) -/
  multiplicative : ∀ x y, 0 < x → 0 < y → map (x * y) = map x * map y
  /-- Preserves cost: C₂.cost(f(x)) = C₁.cost(x) -/
  preserves_cost : ∀ x, 0 < x → C₂.cost (map x) = C₁.cost x

/-- **THEOREM: The identity is a cost morphism.** -/
def CostMorphism.id (C : CostAlgebraData) : CostMorphism C C where
  map := fun x => x
  pos := fun _ h => h
  multiplicative := fun _ _ _ _ => rfl
  preserves_cost := fun _ _ => rfl

/-- **THEOREM: Cost morphisms compose.** -/
def CostMorphism.comp {C₁ C₂ C₃ : CostAlgebraData}
    (g : CostMorphism C₂ C₃) (f : CostMorphism C₁ C₂) : CostMorphism C₁ C₃ where
  map := g.map ∘ f.map
  pos := fun x hx => g.pos _ (f.pos x hx)
  multiplicative := fun x y hx hy => by
    simp [Function.comp]
    rw [f.multiplicative x y hx hy, g.multiplicative _ _ (f.pos x hx) (f.pos y hy)]
  preserves_cost := fun x hx => by
    simp [Function.comp]
    rw [g.preserves_cost _ (f.pos x hx), f.preserves_cost x hx]

/-! ## §8. The Automorphism Group -/

/-- The **reciprocal automorphism**: x ↦ 1/x.
    This is the fundamental symmetry of the cost algebra. -/
noncomputable def reciprocalAuto : ℝ → ℝ := fun x => x⁻¹

/-- **PROVED: The reciprocal map is an involution.** -/
theorem reciprocal_involution (x : ℝ) :
    reciprocalAuto (reciprocalAuto x) = x := by
  unfold reciprocalAuto
  exact inv_inv x

/-- **PROVED: The reciprocal map preserves J-cost.** -/
theorem reciprocal_preserves_cost (x : ℝ) (hx : 0 < x) :
    J (reciprocalAuto x) = J x := by
  unfold reciprocalAuto
  exact (J_reciprocal x hx).symm

/-- Exact level-set classification for `J` on positive reals:
    equal cost means equal ratio or reciprocal ratio. -/
theorem J_eq_iff_eq_or_inv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    J y = J x ↔ y = x ∨ y = x⁻¹ := by
  constructor
  · intro h
    unfold J Jcost at h
    have hfrac : y + y⁻¹ = x + x⁻¹ := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hy0 : y ≠ 0 := ne_of_gt hy
    field_simp [hx0, hy0] at hfrac
    have hfactor : (y - x) * (x * y - 1) = 0 := by
      calc
        (y - x) * (x * y - 1) = x * y ^ 2 + x - (x ^ 2 * y + y) := by ring
        _ = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with hxy | hxy
    · left
      linarith
    · right
      have hxy1 : x * y = 1 := by linarith
      calc
        y = (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx0, one_mul]
        _ = x⁻¹ * (x * y) := by ring
        _ = x⁻¹ := by rw [hxy1, mul_one]
  · intro h
    rcases h with rfl | h
    · rfl
    · simpa [h] using (J_reciprocal x hx).symm

/-- The genuine positive domain of the canonical cost algebra. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- Multiplication on positive reals. -/
def posMul (x y : PosReal) : PosReal :=
  ⟨x.1 * y.1, mul_pos x.2 y.2⟩

/-- Inversion on positive reals. -/
noncomputable def posInv (x : PosReal) : PosReal :=
  ⟨x.1⁻¹, inv_pos.mpr x.2⟩

/-- Distinguished positive constants used to close the automorphism proof. -/
def posOne : PosReal := ⟨1, by norm_num⟩
def posTwo : PosReal := ⟨2, by norm_num⟩
noncomputable def posHalf : PosReal := ⟨(1 / 2 : ℝ), by norm_num⟩

@[simp] theorem posInv_inv (x : PosReal) : posInv (posInv x) = x := by
  apply Subtype.ext
  simp [posInv]

@[simp] theorem posInv_one : posInv posOne = posOne := by
  apply Subtype.ext
  simp [posInv, posOne]

@[simp] theorem posInv_two : posInv posTwo = posHalf := by
  apply Subtype.ext
  norm_num [posInv, posTwo, posHalf]

@[simp] theorem posInv_half : posInv posHalf = posTwo := by
  apply Subtype.ext
  norm_num [posInv, posTwo, posHalf]

/-- The honest automorphism type of the canonical cost algebra on `ℝ_{>0}`. -/
def JAut : Type :=
  { f : PosReal → PosReal //
      (∀ x y : PosReal, f (posMul x y) = posMul (f x) (f y)) ∧
      (∀ x : PosReal, J (f x).1 = J x.1) }

namespace JAut

instance : CoeFun JAut (fun _ => PosReal → PosReal) := ⟨fun f => f.1⟩

/-- Multiplicativity of a `J`-automorphism. -/
theorem multiplicative (f : JAut) (x y : PosReal) :
    f (posMul x y) = posMul (f x) (f y) :=
  f.2.1 x y

/-- Cost preservation of a `J`-automorphism. -/
theorem preserves_cost (f : JAut) (x : PosReal) :
    J (f x).1 = J x.1 :=
  f.2.2 x

@[ext] theorem ext {f g : JAut} (h : ∀ x : PosReal, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

/-- The identity automorphism. -/
def id : JAut :=
  ⟨fun x => x, by
    constructor
    · intro _ _
      rfl
    · intro _
      rfl⟩

/-- The reciprocal automorphism. -/
noncomputable def reciprocal : JAut :=
  ⟨posInv, by
    constructor
    · intro x y
      apply Subtype.ext
      simp [posMul, posInv, mul_comm]
    · intro x
      simpa [posInv] using (J_reciprocal x.1 x.2).symm⟩

/-- Composition of `J`-automorphisms. -/
def comp (g f : JAut) : JAut :=
  ⟨fun x => g (f x), by
    constructor
    · intro x y
      change g (f (posMul x y)) = posMul (g (f x)) (g (f y))
      rw [f.multiplicative x y, g.multiplicative (f x) (f y)]
    · intro x
      rw [g.preserves_cost (f x), f.preserves_cost x]⟩

@[simp] theorem comp_apply (g f : JAut) (x : PosReal) : comp g f x = g (f x) := rfl

@[simp] theorem comp_id (f : JAut) : comp id f = f := by
  apply JAut.ext
  intro x
  rfl

@[simp] theorem id_comp (f : JAut) : comp f id = f := by
  apply JAut.ext
  intro x
  rfl

@[simp] theorem reciprocal_comp_reciprocal : comp reciprocal reciprocal = id := by
  apply JAut.ext
  intro x
  simp [comp, reciprocal, id]

/-- Pointwise, a `J`-automorphism can only choose the identity branch or the
    reciprocal branch. -/
theorem eq_self_or_inv (f : JAut) (x : PosReal) :
    f x = x ∨ f x = posInv x := by
  have hJ : J (f x).1 = J x.1 := f.preserves_cost x
  rcases (J_eq_iff_eq_or_inv x.2 (f x).2).mp hJ with h | h
  · left
    exact Subtype.ext h
  · right
    exact Subtype.ext h

/-- If `2 * x⁻¹ = 2 * x`, positivity forces `x = 1`. -/
theorem two_mul_inv_eq_two_mul_iff (x : PosReal) :
    posMul posTwo (posInv x) = posMul posTwo x ↔ x = posOne := by
  constructor
  · intro h
    apply Subtype.ext
    have hval : (2 : ℝ) * (x : ℝ)⁻¹ = 2 * (x : ℝ) := congrArg Subtype.val h
    have hx0 : (x : ℝ) ≠ 0 := ne_of_gt x.2
    field_simp [hx0] at hval
    have hsq : (x : ℝ) ^ 2 = 1 := by linarith
    have hx1 : (x : ℝ) = 1 := by nlinarith [x.2, hsq]
    simpa [posOne] using hx1
  · intro h
    subst x
    simp [posMul, posInv, posOne, posTwo]

/-- The mixed equation `2 * x⁻¹ = (2x)⁻¹` is impossible on `ℝ_{>0}`. -/
theorem two_mul_inv_ne_inv_two_mul (x : PosReal) :
    posMul posTwo (posInv x) ≠ posInv (posMul posTwo x) := by
  intro h
  have hval : (2 : ℝ) * (x : ℝ)⁻¹ = ((2 : ℝ) * (x : ℝ))⁻¹ := congrArg Subtype.val h
  have hx0 : (x : ℝ) ≠ 0 := ne_of_gt x.2
  field_simp [hx0] at hval
  norm_num at hval

/-- Any automorphism that fixes `2` is the identity everywhere. -/
theorem eq_id_of_map_two_eq_two (f : JAut) (h2 : f posTwo = posTwo) : f = id := by
  apply JAut.ext
  intro x
  rcases eq_self_or_inv f x with hfx | hfx
  · exact hfx
  · have hmul : f (posMul posTwo x) = posMul posTwo (posInv x) := by
      calc
        f (posMul posTwo x) = posMul (f posTwo) (f x) := f.multiplicative posTwo x
        _ = posMul posTwo (posInv x) := by rw [h2, hfx]
    rcases eq_self_or_inv f (posMul posTwo x) with htx | htx
    · have hx1 : x = posOne := (two_mul_inv_eq_two_mul_iff x).mp (hmul.symm.trans htx)
      subst x
      simpa [id] using hfx
    · exact False.elim ((two_mul_inv_ne_inv_two_mul x) (hmul.symm.trans htx))

/-- The reciprocal automorphism is genuinely nontrivial. -/
theorem reciprocal_ne_id : reciprocal ≠ id := by
  intro h
  have htwo : reciprocal posTwo = id posTwo := congrArg (fun f : JAut => f posTwo) h
  have hval : ((reciprocal posTwo : PosReal) : ℝ) = ((id posTwo : PosReal) : ℝ) :=
    congrArg Subtype.val htwo
  norm_num [reciprocal, id, posInv, posTwo] at hval

/-- Exact classification: every `J`-automorphism is either identity or reciprocal. -/
theorem eq_id_or_reciprocal (f : JAut) : f = id ∨ f = reciprocal := by
  rcases eq_self_or_inv f posTwo with h2 | h2
  · left
    exact eq_id_of_map_two_eq_two f h2
  · right
    have hcomp : comp reciprocal f = id := by
      apply eq_id_of_map_two_eq_two
      calc
        comp reciprocal f posTwo = reciprocal (f posTwo) := rfl
        _ = reciprocal (posInv posTwo) := by rw [h2]
        _ = posTwo := by simp [reciprocal]
    apply JAut.ext
    intro x
    have hx : comp reciprocal f x = id x := congrArg (fun g : JAut => g x) hcomp
    have hx' : posInv (posInv (f x)) = posInv x := congrArg posInv hx
    simpa [comp, reciprocal, id] using hx'

/-- A two-point coding of `Aut(J)`. -/
noncomputable def equivFinTwo : JAut ≃ Fin 2 := by
  classical
  refine
    { toFun := fun f => if f = id then 0 else 1
      invFun := fun i => if i = 0 then id else reciprocal
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    rcases eq_id_or_reciprocal f with h | h
    · simp [h]
    · simp [h, reciprocal_ne_id]
  · intro i
    fin_cases i <;> simp [reciprocal_ne_id]

/-- **Closed automorphism theorem**: `Aut(J)` is exactly `ℤ/2ℤ`. -/
noncomputable def equivZModTwo : JAut ≃ ZMod 2 :=
  equivFinTwo.trans (ZMod.finEquiv 2).toEquiv

end JAut

/-- Paper-facing closed automorphism theorem:
    the only continuous multiplicative bijections on `ℝ_{>0}` preserving `J`
    are the identity and reciprocal maps. The continuity and bijectivity
    assumptions are stronger than needed; the proof uses the sharper `JAut`
    classification above. -/
theorem continuous_bijective_preserves_J_eq_id_or_inv
    {f : PosReal → PosReal} (_hCont : Continuous f) (_hBij : Function.Bijective f)
    (hmul : ∀ x y : PosReal, f (posMul x y) = posMul (f x) (f y))
    (hJ : ∀ x : PosReal, J (f x).1 = J x.1) :
    f = (fun x => x) ∨ f = posInv := by
  let g : JAut := ⟨f, ⟨hmul, hJ⟩⟩
  rcases JAut.eq_id_or_reciprocal g with hg | hg
  · left
    funext x
    have hx : g x = JAut.id x := by
      simpa using congrArg (fun h : JAut => h x) hg
    simpa [g, JAut.id] using hx
  · right
    funext x
    have hx : g x = JAut.reciprocal x := by
      simpa using congrArg (fun h : JAut => h x) hg
    simpa [g, JAut.reciprocal] using hx

/-! ## §9. Summary Certificate -/

/-- **COST ALGEBRA CERTIFICATE**

    The cost algebra packages the foundational algebraic structure:
    1. J satisfies RCL (the ONE primitive) ✓
    2. J(1) = 0 (normalization) ✓
    3. J(x) = J(1/x) (reciprocal symmetry) ✓
    4. J(x) ≥ 0 on ℝ₊ (non-negativity) ✓
    5. Raw cost composition is commutative with explicit associator defect ✓
    6. Left-cancellation holds on the nonnegative cost range ✓
    7. The shifted operation `A • B = 2AB` is a commutative monoid on `[1/2,∞)` ✓
    8. H = J+1 satisfies d'Alembert equation ✓
    9. Uniqueness (T5): J is the UNIQUE solution ✓ (modulo regularity)
    10. Reciprocal automorphism is an involution ✓ -/
theorem cost_algebra_certificate :
    -- RCL holds
    SatisfiesRCL J ∧
    -- Normalization
    J 1 = 0 ∧
    -- Associator defect is controlled explicitly
    (∀ a b c : ℝ, (a ★ b) ★ c = a ★ (b ★ c) + 2 * (a - c)) ∧
    -- Left-cancellation on the nonnegative range
    (∀ a b₁ b₂ : ℝ, 0 ≤ a → a ★ b₁ = a ★ b₂ → b₁ = b₂) ∧
    -- H satisfies d'Alembert
    (∀ x y : ℝ, 0 < x → 0 < y → H (x*y) + H (x/y) = 2 * H x * H y) :=
  ⟨RCL_holds, J_at_one, costCompose_assoc_defect,
    fun _ _ _ ha h => costCompose_left_cancel ha h, H_dAlembert⟩

end CostAlgebra
end Algebra
end IndisputableMonolith
