import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Convexity

/-!
# Annular J-Cost Framework

The φ-weighted cost function and annular sampling machinery for the
RS topological cost-covering bridge.

## Core objects

* `phiCost u` := cosh((log φ)·u) − 1 = J(φ^u)
* `AnnularSample` := phase increments on concentric rings
* Jensen-based coercivity: nonzero winding forces Θ(m² log N) cost
* Carrier budget: holomorphic nonvanishing ⟹ O(R²) annular cost

## Lean certification status

The annular layer is now formalized constructively:

- `phiCost` properties
- Jensen ring bound
- ring and annular coercivity
- harmonic divergence
- annular topological floor and excess decomposition
- trace-based carrier-budget interface

What remains conditional is the construction of a concrete trace family for the
specific analytic carrier together with the matching excess bound.
-/

namespace IndisputableMonolith
namespace NumberTheory

open Real Constants Cost

/-! ### §1. The φ-weighted cost function -/

/-- The φ-cost in log-coordinates: f(u) = cosh((log φ)·u) − 1.
    This equals J(φ^u) by the cosh representation of J. -/
noncomputable def phiCost (u : ℝ) : ℝ := Real.cosh (Real.log phi * u) - 1

/-- phiCost(0) = 0: zero phase increment has zero cost. -/
theorem phiCost_zero : phiCost 0 = 0 := by
  simp [phiCost, Real.cosh_zero]

/-- phiCost is symmetric: f(u) = f(−u). -/
theorem phiCost_symm (u : ℝ) : phiCost u = phiCost (-u) := by
  simp [phiCost, Real.cosh_neg, mul_neg]

/-- phiCost is nonneg: f(u) ≥ 0 for all u. -/
theorem phiCost_nonneg (u : ℝ) : 0 ≤ phiCost u := by
  unfold phiCost
  linarith [Real.one_le_cosh (Real.log phi * u)]

/-- The stiffness constant κ = (log φ)². -/
noncomputable def kappa : ℝ := (Real.log phi) ^ 2

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  have hlog_pos : 0 < Real.log phi := Real.log_pos one_lt_phi
  nlinarith

/-- Quadratic lower bound: f(u) ≥ κ·u²/2.
    Follows from cosh(t) ≥ 1 + t²/2. -/
theorem phiCost_quadratic_lb (u : ℝ) :
    kappa * u ^ 2 / 2 ≤ phiCost u := by
  unfold kappa phiCost
  let t : ℝ := Real.log phi * u
  have ht : Real.log phi * u = t := rfl
  have hmain_nonneg : 0 ≤ t ^ 2 / 2 := by positivity
  by_cases htnonneg : 0 ≤ t
  · have hs : t / 2 ≤ Real.sinh (t / 2) :=
      (Real.self_le_sinh_iff).2 (by linarith)
    have hs_sq : (t / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 := by
      nlinarith [hs, sq_nonneg (Real.sinh (t / 2))]
    have hformula : Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
      rw [show t = 2 * (t / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
      ring
    have hbound : t ^ 2 / 2 ≤ Real.cosh t - 1 := by
      rw [hformula]
      nlinarith
    simpa [t, mul_assoc, mul_left_comm, mul_comm, pow_two] using hbound
  · have hformula_neg : Real.cosh t - 1 = Real.cosh (-t) - 1 := by
      simp [Real.cosh_neg]
    have hsq_neg : t ^ 2 / 2 = (-t) ^ 2 / 2 := by ring
    have hpos_case :
        (-t) ^ 2 / 2 ≤ Real.cosh (-t) - 1 := by
      have hs : (-t) / 2 ≤ Real.sinh ((-t) / 2) :=
        (Real.self_le_sinh_iff).2 (by linarith)
      have hs_sq : ((-t) / 2) ^ 2 ≤ Real.sinh ((-t) / 2) ^ 2 := by
        nlinarith [hs, sq_nonneg (Real.sinh ((-t) / 2))]
      have hformula : Real.cosh (-t) - 1 = 2 * Real.sinh ((-t) / 2) ^ 2 := by
        rw [show -t = 2 * ((-t) / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
        ring
      rw [hformula]
      nlinarith
    have hbound : t ^ 2 / 2 ≤ Real.cosh t - 1 := by
      rw [hsq_neg, hformula_neg]
      exact hpos_case
    simpa [t, mul_assoc, mul_left_comm, mul_comm, pow_two] using hbound

/-- The connection to J: phiCost(u) = Jcost(φ^u) for all u ∈ ℝ.
    Uses the existing Jlog_as_cosh certificate. -/
theorem phiCost_eq_Jcost (u : ℝ) :
    phiCost u = Jcost (phi ^ u) := by
  rw [show phiCost u = Jlog (Real.log phi * u) by
        rw [phiCost, Jlog_as_cosh]]
  rw [Jlog, Real.rpow_def_of_pos phi_pos]

/-- `phiCost` is convex on `ℝ` (as `Jlog` composed with a linear map). -/
private theorem phiCost_convexOn : ConvexOn ℝ (Set.univ : Set ℝ) phiCost := by
  let g : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun x => Real.log phi * x
      map_add' := by intro x y; ring
      map_smul' := by intro a x; simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] }
  have hcv : ConvexOn ℝ (Set.univ : Set ℝ) Jlog := StrictConvexOn.convexOn Jlog_strictConvexOn
  have h :
      ConvexOn ℝ (g ⁻¹' (Set.univ : Set ℝ)) (Jlog ∘ g) :=
    hcv.comp_linearMap g
  convert h using 1 <;> ext x <;> simp [g, phiCost, Function.comp, Jlog_as_cosh]

/-- Linear perturbation coefficient for `phiCost` on `[-A, A]`. -/
noncomputable def phiCostLinearCoeff (A : ℝ) : ℝ :=
  Real.log phi * Real.sinh (Real.log phi * A)

/-- Quadratic perturbation coefficient for `phiCost` on `[-A, A]`. -/
noncomputable def phiCostQuadraticCoeff (A : ℝ) : ℝ :=
  kappa * Real.exp (Real.log phi * A)

/-- On `|x| ≤ 1`, the exponential remainder is quadratically bounded. -/
private theorem abs_exp_sub_one_sub_id_le_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1 - x| ≤ x ^ 2 := by
  simpa [Real.norm_eq_abs, sub_eq_add_neg] using
    (Real.norm_exp_sub_one_sub_id_le (x := x) (by simpa [Real.norm_eq_abs] using hx))

/-- On `|x| ≤ 1`, `cosh x - 1` is quadratically small. -/
private theorem cosh_sub_one_le_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Real.cosh x - 1 ≤ x ^ 2 := by
  let A : ℝ := Real.exp x - 1 - x
  let B : ℝ := Real.exp (-x) - 1 + x
  have hA : |A| ≤ x ^ 2 := by
    dsimp [A]
    exact abs_exp_sub_one_sub_id_le_sq_of_abs_le_one hx
  have hB : |B| ≤ x ^ 2 := by
    have hxneg : |-x| ≤ 1 := by simpa using hx
    dsimp [B]
    simpa using abs_exp_sub_one_sub_id_le_sq_of_abs_le_one hxneg
  have hsum : |A + B| ≤ 2 * x ^ 2 := by
    calc
      |A + B| ≤ |A| + |B| := abs_add_le _ _
      _ ≤ x ^ 2 + x ^ 2 := add_le_add hA hB
      _ = 2 * x ^ 2 := by ring
  have hrewrite : A + B = 2 * (Real.cosh x - 1) := by
    dsimp [A, B]
    rw [Real.cosh_eq]
    field_simp [two_ne_zero]
    ring
  have hnonneg : 0 ≤ 2 * (Real.cosh x - 1) := by
    have hcosh : 0 ≤ Real.cosh x - 1 := by
      linarith [Real.one_le_cosh x]
    nlinarith
  have hmain : 2 * (Real.cosh x - 1) ≤ 2 * x ^ 2 := by
    have : |2 * (Real.cosh x - 1)| ≤ 2 * x ^ 2 := by
      simpa [hrewrite] using hsum
    simpa [abs_of_nonneg hnonneg] using this
  nlinarith

/-- On `|x| ≤ 1`, `sinh x` differs from the identity by at most quadratic size. -/
private theorem abs_sinh_le_abs_add_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sinh x| ≤ |x| + x ^ 2 := by
  let A : ℝ := Real.exp x - 1 - x
  let B : ℝ := Real.exp (-x) - 1 + x
  have hA : |A| ≤ x ^ 2 := by
    dsimp [A]
    exact abs_exp_sub_one_sub_id_le_sq_of_abs_le_one hx
  have hB : |B| ≤ x ^ 2 := by
    have hxneg : |-x| ≤ 1 := by simpa using hx
    dsimp [B]
    simpa using abs_exp_sub_one_sub_id_le_sq_of_abs_le_one hxneg
  have hdecomp : Real.sinh x = x + (A - B) / 2 := by
    dsimp [A, B]
    rw [Real.sinh_eq]
    field_simp [two_ne_zero]
    ring
  have hdiv : |(A - B) / 2| ≤ (|A| + |B|) / 2 := by
    have habs : |A - B| ≤ |A| + |B| := by
      simpa using (abs_sub_le A 0 B)
    have htwo : (0 : ℝ) < 2 := by norm_num
    rw [abs_div, abs_of_pos htwo]
    exact div_le_div_of_nonneg_right habs htwo.le
  have hdiv' : |x| + |(A - B) / 2| ≤ |x| + (|A| + |B|) / 2 := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv |x|
  calc
    |Real.sinh x| = |x + (A - B) / 2| := by rw [hdecomp]
    _ ≤ |x| + |(A - B) / 2| := abs_add_le _ _
    _ ≤ |x| + (|A| + |B|) / 2 := hdiv'
    _ ≤ |x| + x ^ 2 := by
      nlinarith [hA, hB]

/-- Perturbative upper bound for `phiCost`.

If `u` lies in the compact interval `[-A, A]` and the perturbation `ε` is small
enough that `|(log φ) ε| ≤ 1`, then `phiCost (u + ε)` is controlled by the base
cost `phiCost u` plus a linear and quadratic error in `ε`. This is the basic
ring-level estimate used to separate the topological floor from the regular-part
error in sampled annular meshes. -/
theorem phiCost_add_le_phiCost_add_linear_quadratic
    {A u ε : ℝ} (hu : |u| ≤ A) (hε : |Real.log phi * ε| ≤ 1) :
    phiCost (u + ε) ≤
      phiCost u + phiCostLinearCoeff A * |ε| + phiCostQuadraticCoeff A * ε ^ 2 := by
  let a : ℝ := Real.log phi
  let x : ℝ := a * u
  let y : ℝ := a * ε
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.log_pos one_lt_phi
  have hxA : |x| ≤ a * A := by
    calc
      |x| = a * |u| := by
        dsimp [x]
        rw [abs_mul, abs_of_nonneg ha_pos.le]
      _ ≤ a * A := mul_le_mul_of_nonneg_left hu ha_pos.le
  have hsinh_x : |Real.sinh x| ≤ Real.sinh (a * A) := by
    rw [Real.abs_sinh]
    exact (Real.sinh_le_sinh).2 hxA
  have hcosh_sinh_x : Real.cosh x + |Real.sinh x| ≤ Real.exp (a * A) := by
    calc
      Real.cosh x + |Real.sinh x| = Real.exp |x| := by
        rw [Real.abs_sinh, ← Real.cosh_abs x, Real.cosh_add_sinh]
      _ ≤ Real.exp (a * A) := Real.exp_le_exp.mpr hxA
  have hy_bound : |y| ≤ 1 := by
    simpa [y, a] using hε
  have hcosh_y : Real.cosh y - 1 ≤ y ^ 2 :=
    cosh_sub_one_le_sq_of_abs_le_one hy_bound
  have hsinh_y : |Real.sinh y| ≤ |y| + y ^ 2 :=
    abs_sinh_le_abs_add_sq_of_abs_le_one hy_bound
  have hprod_cosh : Real.cosh x * (Real.cosh y - 1) ≤ Real.cosh x * y ^ 2 := by
    have hcosh_nonneg : 0 ≤ Real.cosh x := by
      linarith [Real.one_le_cosh x]
    exact mul_le_mul_of_nonneg_left hcosh_y hcosh_nonneg
  have hprod_sinh : Real.sinh x * Real.sinh y ≤ |Real.sinh x| * (|y| + y ^ 2) := by
    have h1 : Real.sinh x * Real.sinh y ≤ |Real.sinh x * Real.sinh y| := le_abs_self _
    have h2 : |Real.sinh x * Real.sinh y| ≤ |Real.sinh x| * (|y| + y ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hsinh_y (abs_nonneg _)
    exact h1.trans h2
  have hexpand :
      phiCost (u + ε) =
        phiCost u + (Real.cosh x * (Real.cosh y - 1) + Real.sinh x * Real.sinh y) := by
    dsimp [x, y, a]
    unfold phiCost
    rw [show Real.log phi * (u + ε) = Real.log phi * u + Real.log phi * ε by ring, Real.cosh_add]
    ring
  have hmain :
      phiCost (u + ε) ≤
        phiCost u + |Real.sinh x| * |y| + (Real.cosh x + |Real.sinh x|) * y ^ 2 := by
    rw [hexpand]
    calc
      phiCost u + (Real.cosh x * (Real.cosh y - 1) + Real.sinh x * Real.sinh y)
          ≤ phiCost u + (Real.cosh x * y ^ 2 + |Real.sinh x| * (|y| + y ^ 2)) := by
              nlinarith [hprod_cosh, hprod_sinh]
      _ = phiCost u + |Real.sinh x| * |y| + (Real.cosh x + |Real.sinh x|) * y ^ 2 := by
            ring
  have hy_abs : |y| = a * |ε| := by
    dsimp [y]
    rw [abs_mul, abs_of_nonneg ha_pos.le]
  have hy_sq : y ^ 2 = a ^ 2 * ε ^ 2 := by
    dsimp [y]
    ring
  have hlin :
      |Real.sinh x| * |y| ≤ phiCostLinearCoeff A * |ε| := by
    rw [hy_abs, phiCostLinearCoeff]
    have :=
      mul_le_mul_of_nonneg_right hsinh_x (mul_nonneg ha_pos.le (abs_nonneg ε))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hquad :
      (Real.cosh x + |Real.sinh x|) * y ^ 2 ≤ phiCostQuadraticCoeff A * ε ^ 2 := by
    calc
      (Real.cosh x + |Real.sinh x|) * y ^ 2 ≤ Real.exp (a * A) * y ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcosh_sinh_x (sq_nonneg y)
      _ = Real.exp (a * A) * (a ^ 2 * ε ^ 2) := by
        rw [hy_sq]
      _ = phiCostQuadraticCoeff A * ε ^ 2 := by
        dsimp [phiCostQuadraticCoeff, a, kappa]
        ring
  calc
    phiCost (u + ε)
        ≤ phiCost u + |Real.sinh x| * |y| + (Real.cosh x + |Real.sinh x|) * y ^ 2 := hmain
    _ ≤ phiCost u + phiCostLinearCoeff A * |ε| + phiCostQuadraticCoeff A * ε ^ 2 := by
          nlinarith [hlin, hquad]

/-! ### §2. Annular sampling -/

/-- An annular sample on ring n consists of 8n phase increments
    with prescribed total winding. -/
structure AnnularRingSample (n : ℕ) where
  increments : Fin (8 * n) → ℝ
  winding : ℤ
  winding_constraint : ∑ j, increments j = -(2 * Real.pi * winding)

/-- The J-cost of one ring: sum of phiCost over all angular edges. -/
noncomputable def ringCost {n : ℕ} (s : AnnularRingSample n) : ℝ :=
  ∑ j, phiCost (s.increments j)

/-- An annular mesh of N concentric rings. -/
structure AnnularMesh (N : ℕ) where
  rings : (n : Fin N) → AnnularRingSample (n.val + 1)
  charge : ℤ
  uniform_charge : ∀ n, (rings n).winding = charge

/-- Total annular cost over N rings. -/
noncomputable def annularCost {N : ℕ} (mesh : AnnularMesh N) : ℝ :=
  ∑ n, ringCost (mesh.rings n)

/-! ### §3. Jensen coercivity -/

/-- Jensen bound for phiCost on a single ring:
    ∑ f(Δ_j) ≥ (8n) · f(∑Δ_j / (8n)).
    Follows from strict convexity of cosh. -/
theorem jensen_ring_bound {n : ℕ} (hn : 0 < n) (s : AnnularRingSample n) :
    (8 * n : ℝ) * phiCost (-(2 * Real.pi * s.winding) / (8 * n)) ≤ ringCost s := by
  have h8n_pos : 0 < (8 * n : ℝ) := by positivity
  let w : Fin (8 * n) → ℝ := fun _ => 1 / (8 * n : ℝ)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin (8 * n))), 0 ≤ w i := by
    intro _ _
    dsimp [w]
    positivity
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin (8 * n))), w i = 1 := by
    dsimp [w]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Nat.cast_mul]
    field_simp [h8n_pos.ne']
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin (8 * n))), s.increments i ∈ (Set.univ : Set ℝ) := by
    intro _ _
    simp
  have hJ :=
    phiCost_convexOn.map_sum_le
      (t := (Finset.univ : Finset (Fin (8 * n))))
      (w := w) (p := s.increments) hw_nonneg hw_sum hmem
  have h_avg :
      ∑ i ∈ (Finset.univ : Finset (Fin (8 * n))), w i * s.increments i =
        -(2 * Real.pi * s.winding) / (8 * n : ℝ) := by
    dsimp [w]
    rw [← Finset.mul_sum, s.winding_constraint]
    field_simp [h8n_pos.ne']
  have h_cost :
      ∑ i ∈ (Finset.univ : Finset (Fin (8 * n))), w i * phiCost (s.increments i) =
        ringCost s / (8 * n : ℝ) := by
    dsimp [w]
    unfold ringCost
    rw [← Finset.mul_sum]
    ring
  have hJ' :
      phiCost (-(2 * Real.pi * s.winding) / (8 * n : ℝ)) ≤ ringCost s / (8 * n : ℝ) := by
    simpa [smul_eq_mul, h_avg, h_cost] using hJ
  have hmult := mul_le_mul_of_nonneg_left hJ' h8n_pos.le
  calc
    (8 * n : ℝ) * phiCost (-(2 * Real.pi * s.winding) / (8 * n : ℝ))
        ≤ (8 * n : ℝ) * (ringCost s / (8 * n : ℝ)) := hmult
    _ = ringCost s := by
        field_simp [h8n_pos.ne']

/-- Coercivity: for charge m ≠ 0, ring n has cost ≥ π²κm²/(4n).
    Uses the quadratic lower bound on phiCost. -/
theorem ring_coercivity {n : ℕ} (hn : 0 < n) (s : AnnularRingSample n) :
    Real.pi ^ 2 * kappa * (s.winding : ℝ) ^ 2 / (4 * n : ℝ) ≤ ringCost s := by
  let u : ℝ := -(2 * Real.pi * s.winding) / (8 * n : ℝ)
  have hphi := phiCost_quadratic_lb u
  have hmul :=
    mul_le_mul_of_nonneg_left hphi (by positivity : 0 ≤ (8 * n : ℝ))
  have hleft :
      Real.pi ^ 2 * kappa * (s.winding : ℝ) ^ 2 / (4 * n : ℝ) ≤
        (8 * n : ℝ) * phiCost u := by
    have hcalc :
        (8 * n : ℝ) * (kappa * u ^ 2 / 2) =
          Real.pi ^ 2 * kappa * (s.winding : ℝ) ^ 2 / (4 * n : ℝ) := by
      dsimp [u]
      field_simp [show (8 * n : ℝ) ≠ 0 by positivity]
      ring
    rw [← hcalc]
    exact hmul
  exact hleft.trans (jensen_ring_bound hn s)

/-- The topological floor: minimum possible cost for charge m on ring n. -/
noncomputable def topologicalFloor (n : ℕ) (m : ℤ) : ℝ :=
  (8 * n : ℝ) * phiCost (-(2 * Real.pi * m) / (8 * n))

/-- The exact Jensen lower bound written as a named topological floor. -/
theorem ringCost_ge_topologicalFloor {n : ℕ} (hn : 0 < n) (s : AnnularRingSample n) :
    topologicalFloor n s.winding ≤ ringCost s := by
  simpa [topologicalFloor] using jensen_ring_bound hn s

/-- Ring-level perturbative upper bound above the topological floor.

If each sampled increment is the uniform winding increment

`-(2π m)/(8n)`

plus a perturbation that is small in `log φ` coordinates, then the total ring
cost is bounded by the topological floor plus explicit linear and quadratic
error sums. -/
theorem ringCost_le_topologicalFloor_add_linear_quadratic_error
    {n : ℕ} (_hn : 0 < n) (s : AnnularRingSample n)
    (hsmall : ∀ j : Fin (8 * n),
      |Real.log phi *
          (s.increments j - (-(2 * Real.pi * s.winding) / (8 * n : ℝ)))| ≤ 1) :
    ringCost s ≤
      topologicalFloor n s.winding +
        phiCostLinearCoeff
            (|(-(2 * Real.pi * s.winding) / (8 * n : ℝ))|) *
          ∑ j : Fin (8 * n),
            |s.increments j - (-(2 * Real.pi * s.winding) / (8 * n : ℝ))| +
        phiCostQuadraticCoeff
            (|(-(2 * Real.pi * s.winding) / (8 * n : ℝ))|) *
          ∑ j : Fin (8 * n),
            (s.increments j - (-(2 * Real.pi * s.winding) / (8 * n : ℝ))) ^ 2 := by
  let u : ℝ := -(2 * Real.pi * s.winding) / (8 * n : ℝ)
  have hu : |u| ≤ |u| := le_rfl
  have hterm :
      ∀ j : Fin (8 * n),
        phiCost (s.increments j) ≤
          phiCost u + phiCostLinearCoeff |u| * |s.increments j - u| +
            phiCostQuadraticCoeff |u| * (s.increments j - u) ^ 2 := by
    intro j
    have hinc : u + (s.increments j - u) = s.increments j := by ring
    have := phiCost_add_le_phiCost_add_linear_quadratic
      (A := |u|) (u := u) (ε := s.increments j - u) hu (hsmall j)
    simpa [hinc] using this
  calc
    ringCost s
        = ∑ j : Fin (8 * n), phiCost (s.increments j) := by
            rfl
    _ ≤ ∑ j : Fin (8 * n),
          (phiCost u + phiCostLinearCoeff |u| * |s.increments j - u| +
            phiCostQuadraticCoeff |u| * (s.increments j - u) ^ 2) := by
              apply Finset.sum_le_sum
              intro j _
              exact hterm j
    _ = (∑ _j : Fin (8 * n), phiCost u) +
          ∑ j : Fin (8 * n), phiCostLinearCoeff |u| * |s.increments j - u| +
          ∑ j : Fin (8 * n), phiCostQuadraticCoeff |u| * (s.increments j - u) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (8 * n : ℝ) * phiCost u +
          phiCostLinearCoeff |u| * ∑ j : Fin (8 * n), |s.increments j - u| +
          phiCostQuadraticCoeff |u| * ∑ j : Fin (8 * n), (s.increments j - u) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Finset.mul_sum, Finset.mul_sum]
            norm_num [Nat.cast_mul]
    _ = topologicalFloor n s.winding +
          phiCostLinearCoeff
              (|(-(2 * Real.pi * s.winding) / (8 * n : ℝ))|) *
            ∑ j : Fin (8 * n),
              |s.increments j - (-(2 * Real.pi * s.winding) / (8 * n : ℝ))| +
          phiCostQuadraticCoeff
              (|(-(2 * Real.pi * s.winding) / (8 * n : ℝ))|) *
            ∑ j : Fin (8 * n),
              (s.increments j - (-(2 * Real.pi * s.winding) / (8 * n : ℝ))) ^ 2 := by
            dsimp [u, topologicalFloor]

/-- The annular topological floor for a fixed charge sector over N rings. -/
noncomputable def annularTopologicalFloor (N : ℕ) (m : ℤ) : ℝ :=
  ∑ n : Fin N, topologicalFloor (n.val + 1) m

/-- The excess cost above the topological floor for an annular mesh. -/
noncomputable def annularExcess {N : ℕ} (mesh : AnnularMesh N) : ℝ :=
  annularCost mesh - annularTopologicalFloor N mesh.charge

/-- Annular coercivity: for charge m ≠ 0, total annular cost diverges
    as Θ(m² log N). Specifically:
    annularCost ≥ (π²κ/4) · m² · ∑_{n=1}^{N} 1/n. -/
theorem annular_coercivity {N : ℕ} (hN : 0 < N) (mesh : AnnularMesh N)
    (hm : mesh.charge ≠ 0) :
    Real.pi ^ 2 * kappa / 4 * (mesh.charge : ℝ) ^ 2 *
      ∑ n : Fin N, (1 : ℝ) / ((n : ℝ) + 1) ≤ annularCost mesh := by
  have hterm : ∀ n : Fin N,
      Real.pi ^ 2 * kappa / 4 * (mesh.charge : ℝ) ^ 2 * ((1 : ℝ) / ((n : ℝ) + 1))
        ≤ ringCost (mesh.rings n) := by
    intro n
    have hn' : 0 < n.val + 1 := Nat.succ_pos _
    have hcoer := ring_coercivity hn' (mesh.rings n)
    rw [mesh.uniform_charge n] at hcoer
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcoer
  calc
    Real.pi ^ 2 * kappa / 4 * (mesh.charge : ℝ) ^ 2 *
        ∑ n : Fin N, (1 : ℝ) / ((n : ℝ) + 1)
        = ∑ n : Fin N, Real.pi ^ 2 * kappa / 4 * (mesh.charge : ℝ) ^ 2 *
            ((1 : ℝ) / ((n : ℝ) + 1)) := by
            rw [Finset.mul_sum]
    _ ≤ ∑ n : Fin N, ringCost (mesh.rings n) := by
          exact Finset.sum_le_sum (fun n _ => hterm n)
    _ = annularCost mesh := by
          rfl

/-- The harmonic sum diverges, so nonzero charge forces unbounded cost. -/
theorem harmonic_sum_diverges :
    Filter.Tendsto (fun N => ∑ n : Fin N, (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop Filter.atTop := by
  have h_log :
      Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) Filter.atTop Filter.atTop := by
    have h_add :
        Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop := by
      simpa using (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact Real.tendsto_log_atTop.comp h_add
  have h_lower : ∀ N : ℕ, Real.log ((N : ℝ) + 1) ≤ ∑ n : Fin N, (1 : ℝ) / ((n : ℝ) + 1) := by
    intro N
    calc
      Real.log ((N : ℝ) + 1) ≤ ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
        simpa [harmonic] using (log_add_one_le_harmonic N)
      _ = ∑ n : Fin N, (1 : ℝ) / ((n : ℝ) + 1) := by
        rw [← Fin.sum_univ_eq_sum_range]
  exact Filter.tendsto_atTop_mono h_lower h_log

/-! ### §4. Carrier traces and budgets -/

/-- A regular carrier on a disk: holomorphic, nonvanishing, with
    bounded logarithmic derivative. -/
structure RegularCarrier where
  logDerivBound : ℝ
  logDerivBound_pos : 0 < logDerivBound
  radius : ℝ
  radius_pos : 0 < radius

/-- A carrier trace is a refinement family of annular samples with fixed charge. -/
structure AnnularTrace where
  charge : ℤ
  mesh : ∀ N : ℕ, AnnularMesh N
  charge_spec : ∀ N : ℕ, (mesh N).charge = charge

/-- A regular carrier equipped with an explicit excess-budget witness along a
specific zero-charge annular trace.

This is the realizable interface needed to state mesh-independent budget
claims without quantifying over arbitrary synthetic meshes. The carrier does not
just have a radius and a logarithmic-derivative scale; it also carries a
specific trace family together with a uniform bound on the excess cost above the
topological floor. -/
structure BudgetedCarrier extends RegularCarrier where
  trace : AnnularTrace
  trace_charge_zero : trace.charge = 0
  budgetConstant : ℝ
  budgetConstant_nonneg : 0 ≤ budgetConstant
  excess_bound : ∀ N : ℕ,
    annularExcess (trace.mesh N) ≤ budgetConstant * logDerivBound ^ 2 * radius ^ 2

/-- The scalar carrier budget appearing in the excess estimate. -/
noncomputable def carrierBudgetScale (carrier : BudgetedCarrier) : ℝ :=
  carrier.budgetConstant * carrier.logDerivBound ^ 2 * carrier.radius ^ 2

/-- The carrier budget scale is nonnegative. -/
theorem carrierBudgetScale_nonneg (carrier : BudgetedCarrier) :
    0 ≤ carrierBudgetScale carrier := by
  unfold carrierBudgetScale
  exact mul_nonneg
    (mul_nonneg carrier.budgetConstant_nonneg (sq_nonneg carrier.logDerivBound))
    (sq_nonneg carrier.radius)

/-- The carrier budget theorem: annular excess of the realized carrier trace
    is bounded by `C · M² · R²`, independent of mesh refinement `N`.

    For the specific carrier C(s) = det₂(I−A(s))²:
    M = M_C(σ₀) = 2∑_p (log p)p^{−2σ₀}/(1−p^{−σ₀}) < ∞
    for σ₀ > 1/2. -/
theorem carrier_budget (carrier : BudgetedCarrier) :
    ∃ K : ℝ, ∀ N : ℕ,
      annularExcess (carrier.trace.mesh N) ≤ K * carrier.logDerivBound ^ 2 * carrier.radius ^ 2 := by
  exact ⟨carrier.budgetConstant, carrier.excess_bound⟩

/-- The topological floor is nonnegative. -/
theorem topologicalFloor_nonneg (n : ℕ) (m : ℤ) : 0 ≤ topologicalFloor n m := by
  unfold topologicalFloor
  apply mul_nonneg
  · positivity
  · exact phiCost_nonneg _

/-- Zero winding has zero topological floor on every ring. -/
theorem topologicalFloor_zero (n : ℕ) : topologicalFloor n 0 = 0 := by
  unfold topologicalFloor
  simp [phiCost_zero]

/-- The annular topological floor is nonnegative. -/
theorem annularTopologicalFloor_nonneg (N : ℕ) (m : ℤ) :
    0 ≤ annularTopologicalFloor N m := by
  unfold annularTopologicalFloor
  apply Finset.sum_nonneg
  intro n _
  exact topologicalFloor_nonneg (n.val + 1) m

/-- Zero winding has zero annular topological floor on every mesh. -/
theorem annularTopologicalFloor_zero (N : ℕ) :
    annularTopologicalFloor N 0 = 0 := by
  unfold annularTopologicalFloor
  apply Finset.sum_eq_zero
  intro n _
  simp [topologicalFloor_zero]

/-- The annular topological floor is bounded above by the total annular cost. -/
theorem annularTopologicalFloor_le_annularCost {N : ℕ} (mesh : AnnularMesh N) :
    annularTopologicalFloor N mesh.charge ≤ annularCost mesh := by
  unfold annularTopologicalFloor annularCost
  apply Finset.sum_le_sum
  intro n _
  have h := ringCost_ge_topologicalFloor (Nat.succ_pos n.val) (mesh.rings n)
  rw [mesh.uniform_charge n] at h
  simpa using h

/-- Excess above the topological floor is nonnegative. -/
theorem annularExcess_nonneg {N : ℕ} (mesh : AnnularMesh N) :
    0 ≤ annularExcess mesh := by
  unfold annularExcess
  linarith [annularTopologicalFloor_le_annularCost mesh]

/-- Nonzero charge forces a strictly positive topological floor on each ring. -/
theorem topologicalFloor_pos_of_charge_ne_zero {n : ℕ} (hn : 0 < n) {m : ℤ} (hm : m ≠ 0) :
    0 < topologicalFloor n m := by
  unfold topologicalFloor
  have hn' : 0 < (8 * n : ℝ) := by positivity
  have hnum_ne : -(2 * Real.pi * (m : ℝ)) ≠ 0 := by
    apply neg_ne_zero.mpr
    apply mul_ne_zero
    · norm_num [Real.pi_ne_zero]
    · exact_mod_cast hm
  have hu_ne : -(2 * Real.pi * (m : ℝ)) / (8 * n : ℝ) ≠ 0 := by
    exact div_ne_zero hnum_ne (by positivity)
  have hquad_pos : 0 < kappa * (-(2 * Real.pi * (m : ℝ)) / (8 * n : ℝ)) ^ 2 / 2 := by
    apply div_pos
    · exact mul_pos kappa_pos (sq_pos_iff.mpr hu_ne)
    · norm_num
  have hphi_lb := phiCost_quadratic_lb (-(2 * Real.pi * (m : ℝ)) / (8 * n : ℝ))
  have hphi_pos :
      0 < phiCost (-(2 * Real.pi * (m : ℝ)) / (8 * n : ℝ)) := by
    exact lt_of_lt_of_le hquad_pos hphi_lb
  exact mul_pos hn' hphi_pos

/-- The one-ring topological floor is strictly positive for nonzero charge. -/
theorem annularTopologicalFloor_one_pos_of_charge_ne_zero {m : ℤ} (hm : m ≠ 0) :
    0 < annularTopologicalFloor 1 m := by
  simpa [annularTopologicalFloor] using
    topologicalFloor_pos_of_charge_ne_zero (by norm_num : 0 < 1) hm

/-! ### §5. Excess bound -/

/-- The excess cost: annular cost minus the topological floor.
    For a field F(s) = (s−ρ)^{−m} G(s) with G regular:
    excess = annularCost(F) − ∑ topologicalFloor(n, m) = O(R²). -/
theorem excess_bounded (carrier : BudgetedCarrier) :
    ∃ K : ℝ, ∀ N : ℕ,
      annularExcess (carrier.trace.mesh N) ≤
        K * carrier.logDerivBound ^ 2 * carrier.radius ^ 2 := by
  exact carrier_budget carrier

end NumberTheory
end IndisputableMonolith
