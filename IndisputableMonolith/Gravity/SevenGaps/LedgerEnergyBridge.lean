import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Gravity.RecognitionLedger

/-!
# Seven Gaps, Lane 1b: the corrected ledger-to-geometry bridge

## Status: THEOREM for every proved statement below (0 sorry, 0 RS-internal
axiom; `decide` is used ONLY for `Fin 3`/`Fin 4` literal disequalities in
the two witness-evaluation lemmas, no `native_decide` anywhere); MODEL and
OPEN items are listed in `LedgerEnergyBridgeStatus` at the end.

`SevenGaps.LedgerBridgeNoGo` proves that the previously assumed bridge form
(ledger deficit = raw SIGNED geometric hinge deficit) is unsatisfiable on
two-sided weak-field classes: ledger deficits are nonnegative and even in
the deformation parameter, while the signed Regge deficit response is odd.
This module builds the corrected bridge to the honest target: the
nonnegative curvature-QUADRATIC geometric energy, discrete Isaacson-type
form Σ_h A_h · δ_h².

**Definitional separation of the two sides (with an honest limit).**
* The geometric side `quadraticCurvatureEnergy` is defined purely from
  hinge data (areas and deficits); no ledger object appears in its
  definition.
* The ledger side `coboundaryStrainLedger` and its `totalCost` are defined
  purely from the substrate potential and the J-cost; no hinge or geometric
  object appears in theirs.
The matching theorem `coboundary_totalCost_quadratic_matching` links the two
definitionally separate sides. HONEST LIMIT: in the canonical bridge
INSTANCE (`canonicalQuadraticEnergyBridge`) the hinge data is instantiated
FROM the ledger's own potential (deficits = potential differences, areas =
1/2 on ordered pairs), so the instance certifies shape-compatibility of the
two functionals, not yet a match against independently derived Regge
geometry; that comparison is the OPEN Hessian-symbol flag below.

**Scoped class (honest scoping).** The J-ratio cost of a strain field
`s : Λ → Λ → ℝ` forms a `RecognitionLedger` when `s` is a COBOUNDARY
(`s i j = f i - f j` for a cell potential `f`). For coboundary strains the
ratios satisfy the cocycle property exp(s i j)·exp(s j k) = exp(s i k), and
RCL subadditivity follows from the d'Alembert identity
J(xy) + J(x/y) = R(J(x), J(y)) with J(x/y) ≥ 0
(`rclGate_Jcost_eq`, `Cost.dalembert_identity`). For GENERAL antisymmetric
strains the RCL gate can FAIL: `general_antisymmetric_strain_can_violate_rcl`
exhibits an antisymmetric strain on three cells violating the gate. The
construction is therefore scoped to coboundary strains, and this scoping is
itself a theorem-backed necessity, not a convenience.

**Explicit constants.** The per-strain expansion is
t²/2 ≤ J(exp t) = cosh t − 1 ≤ (t²/2)·cosh t (all t), whence for |t| ≤ 1:
|J(exp t) − t²/2| ≤ (t⁴/4)·cosh 1 ≤ t⁴/2 (using cosh 1 < 2). The summed
matching bound is |totalCost − (ε²/2)·S₂| ≤ (ε⁴/2)·S₄ with
S₂ = Σ_{i,j} (f₀ i − f₀ j)², S₄ = Σ_{i,j} (f₀ i − f₀ j)⁴, under the explicit
hypothesis |ε·(f₀ i − f₀ j)| ≤ 1 for all i, j. Note S₂, S₄ run over ORDERED
pairs, so each unordered pair is counted twice.

**Shear-visibility gate.** The pure-shear rectangle pattern (horizontal
strain h, vertical strain −h: the traceless two-sided class of the no-go)
is realized as a coboundary strain by the potential (0, −h, 0, −h), and its
ledger energy is strictly positive for every h ≠ 0
(`rectangleShear_ledgerEnergy_pos`), as is its quadratic hinge energy
(`rectangleShear_quadraticEnergy_pos`). Pure shear carries nonzero ledger
energy: the corrected bridge sees exactly the sector on which the
conformal-average ansatz was blind.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

/-! ## §1. The geometric side: discrete quadratic curvature energy

Defined purely from hinge data. No ledger objects appear. -/

/-- **Discrete quadratic (Isaacson-type) curvature energy.** For hinge data
consisting of areas `A : H → ℝ` and deficit angles `δ : H → ℝ`, the energy
is Σ_h A_h · δ_h². This is the discrete form of the nonnegative
curvature-quadratic energy density; it is EVEN in δ, matching the parity
and sign of the ledger side. Purely geometric: no ledger objects. -/
noncomputable def quadraticCurvatureEnergy {H : Type*} [Fintype H]
    (A δ : H → ℝ) : ℝ :=
  ∑ h, A h * δ h ^ 2

/-- **THEOREM.** The quadratic curvature energy is nonnegative for
nonnegative areas (any deficit signs). -/
theorem quadraticCurvatureEnergy_nonneg {H : Type*} [Fintype H]
    {A : H → ℝ} (hA : ∀ h, 0 ≤ A h) (δ : H → ℝ) :
    0 ≤ quadraticCurvatureEnergy A δ := by
  unfold quadraticCurvatureEnergy
  exact Finset.sum_nonneg fun h _ => mul_nonneg (hA h) (sq_nonneg _)

/-- **THEOREM.** The quadratic curvature energy is strictly positive as
soon as one hinge has positive area and nonzero deficit. -/
theorem quadraticCurvatureEnergy_pos {H : Type*} [Fintype H]
    {A δ : H → ℝ} (hA : ∀ h, 0 ≤ A h) (h₀ : H)
    (hA₀ : 0 < A h₀) (hδ₀ : δ h₀ ≠ 0) :
    0 < quadraticCurvatureEnergy A δ := by
  have hsq : 0 < δ h₀ ^ 2 :=
    (sq_nonneg (δ h₀)).lt_of_ne (Ne.symm (pow_ne_zero 2 hδ₀))
  have hterm : 0 < A h₀ * δ h₀ ^ 2 := mul_pos hA₀ hsq
  have hle : A h₀ * δ h₀ ^ 2 ≤ quadraticCurvatureEnergy A δ :=
    Finset.single_le_sum (fun h _ => mul_nonneg (hA h) (sq_nonneg _))
      (Finset.mem_univ h₀)
  linarith

/-! ## §2. Per-strain expansion lemmas (THEOREM tier)

J(exp t) = cosh t − 1. The two-sided quadratic bounds and the quartic
remainder bound, with explicit constants. -/

/-- **THEOREM.** sinh t ≤ t·cosh t for t ≥ 0, by termwise comparison of the
power series: t^(2n+1)/(2n+1)! ≤ t^(2n+1)/(2n)!. -/
theorem sinh_le_self_mul_cosh {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t * Real.cosh t := by
  refine hasSum_le (fun n => ?_) (Real.hasSum_sinh t)
    ((Real.hasSum_cosh t).mul_left t)
  have hfact_le : ((2 * n).factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n ≤ 2 * n + 1)
  have hfact_pos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * n)
  have hpow : (0 : ℝ) ≤ t ^ (2 * n + 1) := pow_nonneg ht _
  calc t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
      ≤ t ^ (2 * n + 1) / ((2 * n).factorial : ℝ) :=
        div_le_div_of_nonneg_left hpow hfact_pos hfact_le
    _ = t * (t ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
        rw [pow_succ]; ring

/-- **THEOREM.** |sinh t| ≤ |t|·cosh t for all t. -/
theorem abs_sinh_le_abs_mul_cosh (t : ℝ) :
    |Real.sinh t| ≤ |t| * Real.cosh t := by
  rw [Real.abs_sinh, ← Real.cosh_abs]
  exact sinh_le_self_mul_cosh (abs_nonneg t)

/-- **THEOREM (two-sided quadratic upper bound).**
cosh t − 1 ≤ (t²/2)·cosh t for ALL t. Combined with
`Cost.cosh_quadratic_lower_bound` (t²/2 ≤ cosh t − 1) this brackets the
ledger cell cost between two quadratic forms. -/
theorem cosh_sub_one_le_half_sq_mul_cosh (t : ℝ) :
    Real.cosh t - 1 ≤ t ^ 2 / 2 * Real.cosh t := by
  have hkey := Cost.cosh_minus_one_eq t
  have hs := abs_sinh_le_abs_mul_cosh (t / 2)
  have h1 : |Real.sinh (t / 2)| ^ 2 ≤ (|t / 2| * Real.cosh (t / 2)) ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg _) hs
    simpa [pow_two] using this
  have h2 : Real.sinh (t / 2) ^ 2 ≤ (t / 2) ^ 2 * Real.cosh (t / 2) ^ 2 := by
    rw [sq_abs] at h1
    rw [mul_pow, sq_abs] at h1
    exact h1
  have hC : Real.cosh (t / 2) ^ 2 ≤ Real.cosh t := by
    have h2m := Real.cosh_two_mul (t / 2)
    have harg : (2 : ℝ) * (t / 2) = t := by ring
    rw [harg] at h2m
    have hpyth := Real.cosh_sq_sub_sinh_sq (t / 2)
    nlinarith [sq_nonneg (Real.cosh (t / 2) - 1), Real.one_le_cosh (t / 2)]
  have hS_le : Real.sinh (t / 2) ^ 2 ≤ (t / 2) ^ 2 * Real.cosh t :=
    le_trans h2 (mul_le_mul_of_nonneg_left hC (sq_nonneg _))
  nlinarith [hkey, hS_le]

/-- **THEOREM.** The quadratic remainder of the ledger cell cost is
nonnegative: 0 ≤ cosh t − 1 − t²/2. -/
theorem cosh_remainder_nonneg (t : ℝ) : 0 ≤ Real.cosh t - 1 - t ^ 2 / 2 := by
  have h := Cost.cosh_quadratic_lower_bound t
  linarith

/-- **THEOREM (explicit quartic remainder).**
cosh t − 1 − t²/2 ≤ (t⁴/4)·cosh t for ALL t, by iterating the quadratic
upper bound: cosh t − 1 − t²/2 ≤ (t²/2)(cosh t − 1) ≤ (t⁴/4)·cosh t. -/
theorem cosh_remainder_le (t : ℝ) :
    Real.cosh t - 1 - t ^ 2 / 2 ≤ t ^ 4 / 4 * Real.cosh t := by
  have h1 := cosh_sub_one_le_half_sq_mul_cosh t
  have h3 : t ^ 2 / 2 * (Real.cosh t - 1)
      ≤ t ^ 2 / 2 * (t ^ 2 / 2 * Real.cosh t) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [h1, h3]

/-- **THEOREM.** cosh 1 < 2 (explicit numeric bound for the remainder
constant), from exp 1 < 2.7182818286 and exp(−1)·exp(1) = 1. -/
theorem cosh_one_lt_two : Real.cosh 1 < 2 := by
  have he : (2 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num [Real.exp_zero]
  have hpos : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
  rw [Real.cosh_eq]
  nlinarith [hprod, he, hpos, hlt]

/-- **THEOREM (per-strain quadratic expansion, explicit constant 1/2).**
For |t| ≤ 1: |J(exp t) − t²/2| ≤ t⁴/2. The constant comes from
(1/4)·cosh 1 ≤ 1/2 via `cosh_one_lt_two`. -/
theorem Jcost_exp_sub_half_sq_abs_le (t : ℝ) (ht : |t| ≤ 1) :
    |Cost.Jcost (Real.exp t) - t ^ 2 / 2| ≤ t ^ 4 / 2 := by
  rw [Cost.Jcost_exp_cosh]
  have h0 := cosh_remainder_nonneg t
  have h1 := cosh_remainder_le t
  have hcosh : Real.cosh t ≤ 2 := by
    have hmono : Real.cosh t ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh]
      simpa using ht
    linarith [cosh_one_lt_two]
  rw [abs_of_nonneg h0]
  have h2 : t ^ 4 / 4 * Real.cosh t ≤ t ^ 4 / 4 * 2 :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  linarith

/-! ## §3. The ledger side: the coboundary-strain J-ledger

Defined purely from the substrate potential and the J-cost. No hinge or
geometric object appears. -/

/-- A strain field is a coboundary if it is the difference field of a cell
potential: s i j = f i − f j. Coboundary strains are automatically
antisymmetric and satisfy the ratio cocycle property. -/
def IsCoboundary {Λ : Type*} (s : Λ → Λ → ℝ) : Prop :=
  ∃ f : Λ → ℝ, ∀ i j, s i j = f i - f j

/-- Coboundary strains are antisymmetric. -/
theorem IsCoboundary.antisymm {Λ : Type*} {s : Λ → Λ → ℝ}
    (hs : IsCoboundary s) : ∀ i j, s i j = - s j i := by
  obtain ⟨f, hf⟩ := hs
  intro i j
  rw [hf i j, hf j i]
  ring

/-- **THEOREM (the panel's key identity).** The RCL gate evaluated on two
J-costs is EXACTLY the J-cost of the product ratio plus the J-cost of the
quotient ratio: R(J(x), J(y)) = J(xy) + J(x/y) for x, y > 0. Since
J(x/y) ≥ 0, the gate inequality J(xy) ≤ R(J(x), J(y)) follows with
identified slack J(x/y). Pure algebra from `Cost.dalembert_identity`. -/
theorem rclGate_Jcost_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    RecognitionLedger.rclGate (Cost.Jcost x) (Cost.Jcost y)
      = Cost.Jcost (x * y) + Cost.Jcost (x / y) := by
  have h := Cost.dalembert_identity hx hy
  unfold RecognitionLedger.rclGate
  linarith

/-- **THEOREM (the corrected ledger construction, coboundary scope).**
The J-ratio costs of a coboundary strain field form a genuine
`RecognitionLedger`: cost i j = J(exp(f i − f j)).
* symmetry from J(x) = J(1/x) (`Cost.Jcost_symm`),
* diagonal zero from J(1) = 0,
* nonnegativity from J ≥ 0 on positives,
* RCL subadditivity from the cocycle property
  exp(f i − f j)·exp(f j − f k) = exp(f i − f k) plus J-submultiplicativity
  (`Cost.Jcost_submult` in the proof; equivalently the d'Alembert identity
  `rclGate_Jcost_eq` with J(x/y) ≥ 0).
Scoped to coboundary strains: for general antisymmetric strains the gate
can fail (`general_antisymmetric_strain_can_violate_rcl`). -/
noncomputable def coboundaryStrainLedger {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] (f : Λ → ℝ) :
    RecognitionLedger.RecognitionLedger Λ where
  cost i j := Cost.Jcost (Real.exp (f i - f j))
  symmetric := by
    intro i j
    show Cost.Jcost (Real.exp (f i - f j)) = Cost.Jcost (Real.exp (f j - f i))
    have h : Real.exp (f j - f i) = (Real.exp (f i - f j))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [h]
    exact Cost.Jcost_symm (Real.exp_pos _)
  diagonal_zero := by
    intro i
    show Cost.Jcost (Real.exp (f i - f i)) = 0
    rw [sub_self, Real.exp_zero, Cost.Jcost_unit0]
  nonneg := fun i j => Cost.Jcost_nonneg (Real.exp_pos _)
  rcl_subadditive := by
    intro i j k
    show Cost.Jcost (Real.exp (f i - f k))
      ≤ RecognitionLedger.rclGate (Cost.Jcost (Real.exp (f i - f j)))
          (Cost.Jcost (Real.exp (f j - f k)))
    have hcomp : Real.exp (f i - f k)
        = Real.exp (f i - f j) * Real.exp (f j - f k) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsub := Cost.Jcost_submult (Real.exp_pos (f i - f j))
      (Real.exp_pos (f j - f k))
    rw [hcomp]
    unfold RecognitionLedger.rclGate
    linarith

/-- The gate-violating antisymmetric strain on three cells: strain 1 from
cell 0 to cell 2 but zero strain on both legs through cell 1. Antisymmetric
by construction; NOT a coboundary (a coboundary would force
s 0 2 = s 0 1 + s 1 2 = 0). -/
noncomputable def gateViolatingStrain : Fin 3 → Fin 3 → ℝ := fun i j =>
  (if i = 0 ∧ j = 2 then (1 : ℝ) else 0)
    - (if j = 0 ∧ i = 2 then (1 : ℝ) else 0)

/-- **THEOREM.** The gate-violating strain is antisymmetric. -/
theorem gateViolatingStrain_antisymm :
    ∀ i j, gateViolatingStrain i j = - gateViolatingStrain j i := by
  intro i j
  unfold gateViolatingStrain
  ring

/-- **THEOREM.** Values of the gate-violating strain on the relevant pairs.
(Uses `decide` only for `Fin 3` literal disequalities.) -/
theorem gateViolatingStrain_vals :
    gateViolatingStrain 0 2 = 1 ∧ gateViolatingStrain 0 1 = 0 ∧
      gateViolatingStrain 1 2 = 0 := by
  have h20 : ¬((2 : Fin 3) = 0) := by decide
  have h02 : ¬((0 : Fin 3) = 2) := by decide
  have h12 : ¬((1 : Fin 3) = 2) := by decide
  have h10 : ¬((1 : Fin 3) = 0) := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    · unfold gateViolatingStrain
      norm_num [h20, h02, h12, h10]

/-- **THEOREM (honest scoping witness).** A general ANTISYMMETRIC strain
field need not yield an RCL-subadditive cost: on three cells, the
antisymmetric strain with s 0 2 = 1 but s 0 1 = s 1 2 = 0 gives
J(exp(s 0 2)) > 0 = R(J(exp(s 0 1)), J(exp(s 1 2))). This is why
`coboundaryStrainLedger` is scoped to coboundary strains: the scoping is
forced, not chosen. -/
theorem general_antisymmetric_strain_can_violate_rcl :
    ∃ s : Fin 3 → Fin 3 → ℝ, (∀ i j, s i j = - s j i) ∧
      ¬ (Cost.Jcost (Real.exp (s 0 2)) ≤
          RecognitionLedger.rclGate (Cost.Jcost (Real.exp (s 0 1)))
            (Cost.Jcost (Real.exp (s 1 2)))) := by
  refine ⟨gateViolatingStrain, gateViolatingStrain_antisymm, ?_⟩
  obtain ⟨h02, h01, h12⟩ := gateViolatingStrain_vals
  rw [h02, h01, h12, Real.exp_zero, Cost.Jcost_unit0]
  have hgate : RecognitionLedger.rclGate 0 0 = 0 := by
    unfold RecognitionLedger.rclGate
    ring
  rw [hgate]
  have hone : (1 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpos : 0 < Cost.Jcost (Real.exp 1) :=
    Cost.Jcost_pos_of_ne_one _ (Real.exp_pos 1) (ne_of_gt hone)
  linarith

/-! ## §4. The matching theorem (the corrected bridge) -/

/-- **THEOREM (quadratic matching, explicit constants).** For the
one-parameter coboundary strain family ε·f₀ with all scaled strains in
[−1, 1], the total ledger cost matches the quadratic strain energy
(ε²/2)·S₂ to fourth order with explicit remainder constant 1/2:

  |totalCost(ε·f₀) − (ε²/2)·Σ_{i,j}(f₀ i − f₀ j)²|
      ≤ (ε⁴/2)·Σ_{i,j}(f₀ i − f₀ j)⁴.

Sums run over ORDERED pairs (each unordered pair counted twice). The
hypothesis |ε·(f₀ i − f₀ j)| ≤ 1 is the explicit small-strain premise; no
hidden assumptions. -/
theorem coboundary_totalCost_quadratic_matching {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] (f₀ : Λ → ℝ) (ε : ℝ)
    (hsmall : ∀ i j, |ε * (f₀ i - f₀ j)| ≤ 1) :
    |RecognitionLedger.totalCost
        (coboundaryStrainLedger (fun i => ε * f₀ i))
      - ε ^ 2 / 2 * ∑ i, ∑ j, (f₀ i - f₀ j) ^ 2|
      ≤ ε ^ 4 / 2 * ∑ i, ∑ j, (f₀ i - f₀ j) ^ 4 := by
  classical
  have hcost : ∀ i j : Λ,
      (coboundaryStrainLedger (fun i => ε * f₀ i)).cost i j
        = Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j))) := by
    intro i j
    show Cost.Jcost (Real.exp (ε * f₀ i - ε * f₀ j)) = _
    have harg : ε * f₀ i - ε * f₀ j = ε * (f₀ i - f₀ j) := by ring
    rw [harg]
  have hexpand : RecognitionLedger.totalCost
      (coboundaryStrainLedger (fun i => ε * f₀ i))
      = ∑ i, ∑ j, Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j))) := by
    unfold RecognitionLedger.totalCost
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hcost i j
  have hquad : ε ^ 2 / 2 * ∑ i, ∑ j, (f₀ i - f₀ j) ^ 2
      = ∑ i, ∑ j, (ε * (f₀ i - f₀ j)) ^ 2 / 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hquart : ε ^ 4 / 2 * ∑ i, ∑ j, (f₀ i - f₀ j) ^ 4
      = ∑ i, ∑ j, (ε * (f₀ i - f₀ j)) ^ 4 / 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexpand, hquad, hquart]
  have hcombine : ∑ i, ∑ j, Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j)))
      - ∑ i, ∑ j, (ε * (f₀ i - f₀ j)) ^ 2 / 2
      = ∑ i, ∑ j, (Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j)))
          - (ε * (f₀ i - f₀ j)) ^ 2 / 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_sub_distrib _ _).symm
  rw [hcombine]
  calc |∑ i, ∑ j, (Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j)))
          - (ε * (f₀ i - f₀ j)) ^ 2 / 2)|
      ≤ ∑ i, |∑ j, (Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j)))
          - (ε * (f₀ i - f₀ j)) ^ 2 / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |Cost.Jcost (Real.exp (ε * (f₀ i - f₀ j)))
          - (ε * (f₀ i - f₀ j)) ^ 2 / 2| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (ε * (f₀ i - f₀ j)) ^ 4 / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have h := Jcost_exp_sub_half_sq_abs_le (ε * (f₀ i - f₀ j))
            (hsmall i j)
          linarith

/-! ## §5. The corrected bridge structure and its canonical instance -/

/-- Uniform hinge areas for the ordered-pair hinge set Λ × Λ: each ordered
pair carries area 1/2, so that summing over ordered pairs matches the
per-unordered-pair weight 1. Purely geometric bookkeeping. -/
noncomputable def strainHingeAreas (Λ : Type*) : Λ × Λ → ℝ := fun _ => 1 / 2

/-- Hinge deficits induced by a cell potential: the hinge (i, j) carries
deficit f i − f j. This is hinge DATA (a signed deficit assignment); it is
consumed quadratically by `quadraticCurvatureEnergy`, so its sign is
invisible to the energy, exactly as the parity no-go requires. -/
noncomputable def strainHingeDeficits {Λ : Type*} (f : Λ → ℝ) :
    Λ × Λ → ℝ := fun p => f p.1 - f p.2

/-- **THEOREM.** The quadratic curvature energy of the strain hinge data is
half the ordered-pair sum of squared potential differences. -/
theorem quadraticCurvatureEnergy_strainHinges {Λ : Type*} [Fintype Λ]
    (f₀ : Λ → ℝ) :
    quadraticCurvatureEnergy (strainHingeAreas Λ) (strainHingeDeficits f₀)
      = (∑ i, ∑ j, (f₀ i - f₀ j) ^ 2) / 2 := by
  unfold quadraticCurvatureEnergy strainHingeAreas strainHingeDeficits
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (1 : ℝ) / 2 * (f₀ i - f₀ j) ^ 2 = (f₀ i - f₀ j) ^ 2 / 2
  ring

/-- **The corrected bridge (deliverable B).** From a coboundary strain
configuration (base potential f₀, deformation parameter ε, explicit
small-strain hypothesis) to quadratic hinge energy data (areas, deficits),
with the PROVED two-sided matching bound as a field: the total ledger cost
of the scaled strain equals ε² times the quadratic hinge energy up to the
explicit quartic remainder (ε⁴/2)·S₄. There are NO assumed fields: every
Prop field of the canonical instance `canonicalQuadraticEnergyBridge` is
discharged by a kernel-checked proof. Contrast with the refuted
`LedgerToHingeBridge.bridge_assumed`. -/
structure LedgerToQuadraticEnergyBridge
    (Λ : Type*) [Fintype Λ] [DecidableEq Λ] where
  /-- The base cell potential f₀ (strain generator). -/
  basePotential : Λ → ℝ
  /-- The deformation parameter ε. -/
  eps : ℝ
  /-- Explicit small-strain premise: every scaled strain lies in [−1, 1]. -/
  small_strain : ∀ i j, |eps * (basePotential i - basePotential j)| ≤ 1
  /-- Hinge areas (geometric side). -/
  hingeArea : Λ × Λ → ℝ
  /-- Areas are nonnegative. -/
  hingeArea_nonneg : ∀ p, 0 ≤ hingeArea p
  /-- Hinge deficits (geometric side). -/
  hingeDeficit : Λ × Λ → ℝ
  /-- PROVED two-sided matching (both bounds, via absolute value): ledger
  energy = ε²·(quadratic hinge energy) + O(ε⁴) with explicit constant. -/
  matching : |RecognitionLedger.totalCost
      (coboundaryStrainLedger (fun i => eps * basePotential i))
    - eps ^ 2 * quadraticCurvatureEnergy hingeArea hingeDeficit|
    ≤ eps ^ 4 / 2 *
        ∑ i, ∑ j, (basePotential i - basePotential j) ^ 4

/-- **THEOREM (canonical instance).** Every coboundary strain configuration
with small scaled strains yields a `LedgerToQuadraticEnergyBridge`: hinge
areas 1/2 on ordered pairs, hinge deficits f₀ i − f₀ j, matching proved by
`coboundary_totalCost_quadratic_matching`. No assumed fields. -/
noncomputable def canonicalQuadraticEnergyBridge {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] (f₀ : Λ → ℝ) (ε : ℝ)
    (hsmall : ∀ i j, |ε * (f₀ i - f₀ j)| ≤ 1) :
    LedgerToQuadraticEnergyBridge Λ where
  basePotential := f₀
  eps := ε
  small_strain := hsmall
  hingeArea := strainHingeAreas Λ
  hingeArea_nonneg := fun _ => by
    unfold strainHingeAreas
    norm_num
  hingeDeficit := strainHingeDeficits f₀
  matching := by
    rw [quadraticCurvatureEnergy_strainHinges f₀]
    have harg : ε ^ 2 * ((∑ i, ∑ j, (f₀ i - f₀ j) ^ 2) / 2)
        = ε ^ 2 / 2 * ∑ i, ∑ j, (f₀ i - f₀ j) ^ 2 := by ring
    rw [harg]
    exact coboundary_totalCost_quadratic_matching f₀ ε hsmall

/-! ## §6. The shear-visibility gate (nonflat witness) -/

/-- The rectangle pure-shear potential: cells 0 and 2 at potential 0, cells
1 and 3 at potential −h. The induced coboundary strains carry strain h on
the two horizontal edges (0→1, 2→3) and −h on the two vertical edges
(1→2, 3→0): the traceless rectangle shear pattern (horizontal strain h,
vertical strain v = −h, h ≠ v for h ≠ 0). This is the rectangle shear mode
of `TensorShearSector` re-expressed as antisymmetric pair strains; as an
edge pattern with h ≠ v it has NO vertex-conformal (averaging) realization,
but as a difference field it IS a coboundary, so the corrected ledger
bridge applies to it. -/
noncomputable def rectangleShearPotential (h : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 1 ∨ i = 3 then -h else 0

/-- **THEOREM.** The rectangle shear potential realizes the pure-shear
strain pattern: horizontal strains h, vertical strains −h.
(Uses `decide` only for `Fin 4` literal disequalities.) -/
theorem rectangleShearPotential_strains (h : ℝ) :
    rectangleShearPotential h 0 - rectangleShearPotential h 1 = h ∧
    rectangleShearPotential h 2 - rectangleShearPotential h 3 = h ∧
    rectangleShearPotential h 1 - rectangleShearPotential h 2 = -h ∧
    rectangleShearPotential h 3 - rectangleShearPotential h 0 = -h := by
  have h01 : ¬((0 : Fin 4) = 1) := by decide
  have h03 : ¬((0 : Fin 4) = 3) := by decide
  have h21 : ¬((2 : Fin 4) = 1) := by decide
  have h23 : ¬((2 : Fin 4) = 3) := by decide
  have h13 : ¬((1 : Fin 4) = 3) := by decide
  have h31 : ¬((3 : Fin 4) = 1) := by decide
  unfold rectangleShearPotential
  norm_num [h01, h03, h21, h23, h13, h31]

/-- **THEOREM (shear-visibility gate).** The pure-shear rectangle strain
carries strictly positive ledger energy for every h ≠ 0. Shear is VISIBLE
to the corrected J-ledger bridge: the cell cost on the horizontal edge is
J(exp h) = cosh h − 1 > 0, and all cell costs are nonnegative. This is
exactly the transverse-traceless sector on which the conformal-average
ansatz was proved blind
(`Gravity.conformal_ansatz_cannot_recover_gravitational_waves`). -/
theorem rectangleShear_ledgerEnergy_pos (h : ℝ) (hh : h ≠ 0) :
    0 < RecognitionLedger.totalCost
      (coboundaryStrainLedger (rectangleShearPotential h)) := by
  classical
  unfold RecognitionLedger.totalCost
  have hval : rectangleShearPotential h 0 - rectangleShearPotential h 1
      = h := (rectangleShearPotential_strains h).1
  have hterm :
      0 < (coboundaryStrainLedger (rectangleShearPotential h)).cost 0 1 := by
    show 0 < Cost.Jcost (Real.exp
      (rectangleShearPotential h 0 - rectangleShearPotential h 1))
    rw [hval, Cost.Jcost_exp_cosh]
    have hcosh : 1 < Real.cosh h := Real.one_lt_cosh.mpr hh
    linarith
  have hinner :
      0 < ∑ j, (coboundaryStrainLedger (rectangleShearPotential h)).cost 0 j := by
    have hle := Finset.single_le_sum
      (f := fun j => (coboundaryStrainLedger (rectangleShearPotential h)).cost 0 j)
      (fun j _ => (coboundaryStrainLedger (rectangleShearPotential h)).nonneg 0 j)
      (Finset.mem_univ 1)
    linarith
  have houter := Finset.single_le_sum
    (f := fun i => ∑ j, (coboundaryStrainLedger (rectangleShearPotential h)).cost i j)
    (fun i _ => Finset.sum_nonneg fun j _ =>
      (coboundaryStrainLedger (rectangleShearPotential h)).nonneg i j)
    (Finset.mem_univ 0)
  exact lt_of_lt_of_le hinner houter

/-- **THEOREM.** The geometric side sees the same shear: the quadratic
hinge energy of the rectangle shear data is strictly positive for h ≠ 0. -/
theorem rectangleShear_quadraticEnergy_pos (h : ℝ) (hh : h ≠ 0) :
    0 < quadraticCurvatureEnergy (strainHingeAreas (Fin 4))
      (strainHingeDeficits (rectangleShearPotential h)) := by
  refine quadraticCurvatureEnergy_pos
    (fun p => by unfold strainHingeAreas; norm_num)
    ((0 : Fin 4), (1 : Fin 4))
    (by unfold strainHingeAreas; norm_num) ?_
  show rectangleShearPotential h 0 - rectangleShearPotential h 1 ≠ 0
  rw [(rectangleShearPotential_strains h).1]
  exact hh

/-- **THEOREM (canonical shear bridge witness).** Under the explicit
small-strain premise (every scaled pair strain in [−1, 1]; the pair strains
of the rectangle shear potential are 0 and ±h, so |ε·h| ≤ 1 suffices), the
pure-shear rectangle configuration instantiates the corrected bridge. -/
noncomputable def rectangleShearBridge (h ε : ℝ)
    (hsmall : ∀ i j : Fin 4, |ε * (rectangleShearPotential h i
      - rectangleShearPotential h j)| ≤ 1) :
    LedgerToQuadraticEnergyBridge (Fin 4) :=
  canonicalQuadraticEnergyBridge (rectangleShearPotential h) ε hsmall

/-! ## §7. Status: honest tier accounting -/

/-- Status flags for the corrected ledger-energy bridge, by honesty tier.

**THEOREM** (kernel-checked, this module):
* the per-strain expansion t²/2 ≤ J(exp t) = cosh t − 1 ≤ (t²/2)·cosh t
  and the quartic remainder |J(exp t) − t²/2| ≤ t⁴/2 on |t| ≤ 1
  (`cosh_sub_one_le_half_sq_mul_cosh`, `Jcost_exp_sub_half_sq_abs_le`);
* the coboundary-strain J-ledger is a `RecognitionLedger`
  (`coboundaryStrainLedger`), with the gate identity
  R(J(x), J(y)) = J(xy) + J(x/y) (`rclGate_Jcost_eq`) and the failure of
  the gate for general antisymmetric strain
  (`general_antisymmetric_strain_can_violate_rcl`);
* the quadratic matching |totalCost − (ε²/2)S₂| ≤ (ε⁴/2)S₄
  (`coboundary_totalCost_quadratic_matching`) and the canonical bridge
  instance (`canonicalQuadraticEnergyBridge`);
* the shear-visibility gate: pure rectangle shear carries strictly
  positive ledger AND quadratic hinge energy
  (`rectangleShear_ledgerEnergy_pos`, `rectangleShear_quadraticEnergy_pos`).

**MODEL** (definitional identification, not derived here): reading
Σ_h A_h · δ_h² (`quadraticCurvatureEnergy`) as the discrete Isaacson-type
transverse-traceless energy, i.e. as the continuum partner of the ledger
energy. The parity and sign structure force a curvature-QUADRATIC target
(that much is THEOREM, from the no-go); WHICH quadratic functional is the
Regge/Isaacson one is the modeling identification.

**OPEN**: the full Hessian-symbol comparison of the ledger quadratic form
against the frozen Regge quadratic functional on the periodic Freudenthal
mesh; the tensor multichannel escalation beyond the single coboundary
channel. -/
structure LedgerEnergyBridgeStatus where
  /-- THEOREM tier: two-sided quadratic expansion with explicit constants. -/
  jcost_expansion_theorem : Bool
  /-- THEOREM tier: coboundary-strain J-costs form a RecognitionLedger. -/
  coboundary_ledger_instance_theorem : Bool
  /-- THEOREM tier: RCL gate can fail for general antisymmetric strain
  (the scoping to coboundary strains is forced). -/
  general_antisymmetric_gate_failure_theorem : Bool
  /-- THEOREM tier: quadratic matching with explicit quartic remainder. -/
  quadratic_matching_theorem : Bool
  /-- THEOREM tier: pure shear carries strictly positive ledger energy. -/
  shear_visibility_theorem : Bool
  /-- MODEL tier: identifying Σ A_h δ_h² as the Isaacson-type continuum
  partner (definitional identification, not a derivation). -/
  isaacson_identification_model : Bool
  /-- OPEN: Hessian-symbol comparison against the frozen Regge quadratic
  functional on the periodic Freudenthal mesh. -/
  hessian_symbol_comparison_open : Bool
  /-- OPEN: tensor multichannel escalation. -/
  tensor_multichannel_open : Bool

/-- The canonical status record. -/
def ledgerEnergyBridgeStatus : LedgerEnergyBridgeStatus where
  jcost_expansion_theorem := true
  coboundary_ledger_instance_theorem := true
  general_antisymmetric_gate_failure_theorem := true
  quadratic_matching_theorem := true
  shear_visibility_theorem := true
  isaacson_identification_model := true
  hessian_symbol_comparison_open := true
  tensor_multichannel_open := true

/-- **Status flags theorem (rfl-forced).** -/
theorem ledgerEnergyBridgeStatus_flags :
    ledgerEnergyBridgeStatus.jcost_expansion_theorem = true ∧
    ledgerEnergyBridgeStatus.coboundary_ledger_instance_theorem = true ∧
    ledgerEnergyBridgeStatus.general_antisymmetric_gate_failure_theorem
      = true ∧
    ledgerEnergyBridgeStatus.quadratic_matching_theorem = true ∧
    ledgerEnergyBridgeStatus.shear_visibility_theorem = true ∧
    ledgerEnergyBridgeStatus.isaacson_identification_model = true ∧
    ledgerEnergyBridgeStatus.hessian_symbol_comparison_open = true ∧
    ledgerEnergyBridgeStatus.tensor_multichannel_open = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SevenGaps
end Gravity
end IndisputableMonolith
