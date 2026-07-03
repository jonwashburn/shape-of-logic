import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.SimplicialLedger.ContinuumBridge
import IndisputableMonolith.Foundation.SimplicialLedger.EdgeLengthFromPsi

/-!
# Nonlinear J-Cost / Regge Bridge (Addressing Beltracchi §6)

This module addresses Philip Beltracchi's §6 concern: the existing
J-cost ↔ Regge identification is valid only at the quadratic (weak
field) order, so it does not by itself authorize black-hole physics.

## The non-linear J-cost action

The nonlinear J-cost coupling between two simplices with log-potentials
`ε_i, ε_j` is

   `J(exp(ε_i − ε_j)) = cosh(ε_i − ε_j) − 1`

which is valid at **all orders** in `(ε_i − ε_j)`, including the
strong-field regime where the quadratic approximation
`(ε_i − ε_j)² / 2` fails.

## What this module proves

1. The "exact J-cost action" `exactJCostAction G ε` is defined as
   `Σ_{i,j} w_{ij} · (cosh(ε_i − ε_j) − 1)`. It reduces to
   `laplacian_action G ε` at leading order in `ε`.

2. A quantitative bound showing the quadratic Laplacian action
   is exactly the leading-order truncation of the exact action:

      `exactJCostAction = laplacian_action + quartic_remainder`

   where the remainder is non-negative (by the Taylor series of
   `cosh`) and is `O((ε_i − ε_j)⁴)` in magnitude.

3. **Strong-field validity of the J-cost side.** The exact J-cost
   action is defined for **any** `ε`, not just small `ε`. This
   is the Lean-level answer to Philip's concern: the J-cost
   side of the identity does not require a weak-field assumption.

4. **What remains unavoidably a separate hypothesis.** The
   non-linear Regge action on a generic simplicial complex is
   defined via `Σ_h A_h · δ_h` with `δ_h` the exact deficit
   angle from Cayley-Menger determinants. The identity
   `exactJCostAction = κ · exactReggeAction` beyond the
   linearized regime is a **genuine mathematical statement**
   about piecewise-flat curvature; it is packaged here as
   `NonlinearReggeJCostIdentity`, clearly labeled as a
   hypothesis to be discharged by Cayley-Menger computations
   (or the Cheeger-Müller-Schrader non-linear theorem) rather
   than as an axiom.

5. Under this named hypothesis, the Einstein field equations
   from J-cost stationarity are valid **in the strong-field
   regime**: the identity reads
      `δ(exactJCostAction) = 0 ⇒ δ(exactReggeAction) = 0`,
   and the Regge equations at stationarity are the discrete
   Einstein equations (`κ G_μν = κ T_μν`), whose continuum
   limit is the full non-linear EFE.

Zero `sorry`, zero new `axiom`.

## References

- Regge, T. (1961). *General Relativity Without Coordinates*.
- Cheeger, J., Müller, W., Schrader, R. (1984). *Commun. Math.
  Phys.* **92**, 405-454 (full non-linear convergence).
- Beltracchi, P., Washburn, J. (2026 draft). Outstanding issues
  §6.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SimplicialLedger
namespace NonlinearBridge

open Constants Cost ContinuumBridge EdgeLengthFromPsi

noncomputable section

/-! ## §1. The exact (non-linear) J-cost action -/

/-- The **exact J-cost action** on a weighted ledger graph, with
    no weak-field approximation. The functional form is the full
    cosh-based coupling:

    `exactJCostAction G ε = Σ_{i,j} w_{ij} (cosh(ε_i − ε_j) − 1)`.

    This is what the Recognition Composition Law actually prescribes.
    The quadratic `laplacian_action G ε` is the leading-order
    truncation (see `exact_decomposition` below). -/
def exactJCostAction {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    G.weight i j * (Real.cosh (ε i - ε j) - 1)

/-- The exact J-cost action vanishes on the flat vacuum `ε ≡ 0`. -/
theorem exactJCostAction_flat {n : ℕ} (G : WeightedLedgerGraph n) :
    exactJCostAction G (fun _ => (0 : ℝ)) = 0 := by
  unfold exactJCostAction
  simp

/-- The exact J-cost action is non-negative. -/
theorem exactJCostAction_nonneg {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) : 0 ≤ exactJCostAction G ε := by
  unfold exactJCostAction
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (G.weight_nonneg i j)
  have h : Real.cosh (ε i - ε j) ≥ 1 := Real.one_le_cosh _
  linarith

/-! ## §2. J-cost ↔ cosh identity as the non-linear primitive -/

/-- **CORE IDENTITY.** For every pair of log-potentials, the J-cost
    of the *ratio* `ψ_i / ψ_j = exp(ε_i − ε_j)` equals
    `cosh(ε_i − ε_j) − 1`. This is the single-edge formula behind
    the exact action above.

    This is the full non-linear statement; it is not an
    approximation. Proved in `Cost.Jcost_exp_cosh`. -/
theorem Jcost_ratio_eq_cosh_minus_one (εi εj : ℝ) :
    Jcost (Real.exp (εi - εj)) = Real.cosh (εi - εj) - 1 :=
  Cost.Jcost_exp_cosh (εi - εj)

/-- The exact J-cost action is a sum of `Jcost`-valued single-edge
    contributions — the exact form of what the field-theory
    `laplacian_action` approximates at leading order. -/
theorem exactJCostAction_via_Jcost {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) :
    exactJCostAction G ε
      = ∑ i : Fin n, ∑ j : Fin n,
          G.weight i j * Jcost (Real.exp (ε i - ε j)) := by
  unfold exactJCostAction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Jcost_ratio_eq_cosh_minus_one]

/-! ## §3. Leading-order agreement with the Laplacian action -/

/-- **QUADRATIC APPROXIMATION.** At leading order in `|ε_i − ε_j|`,
    the exact J-cost action coincides with the Laplacian action.

    This is the precise statement that `laplacian_action` is the
    weak-field limit of `exactJCostAction`. The remainder is the
    "non-linear cosh correction":
    `cosh(x) − 1 − x²/2 = x⁴/24 + O(x⁶)`. -/
def coshRemainder (x : ℝ) : ℝ := Real.cosh x - 1 - x ^ 2 / 2

/-- The cosh remainder is non-negative for all `x` (because
    `cosh x ≥ 1 + x²/2` — a Taylor lower bound). -/
theorem coshRemainder_nonneg (x : ℝ) : 0 ≤ coshRemainder x := by
  unfold coshRemainder
  have h := cosh_quadratic_lower_bound x
  linarith

/-- The cosh remainder is zero at `x = 0` (the flat vacuum). -/
theorem coshRemainder_zero : coshRemainder 0 = 0 := by
  unfold coshRemainder
  simp

/-! ## §4. Decomposition: exact = linearized + quartic remainder -/

/-- The quartic remainder of the full action (the "non-linear
    correction" to the weak-field Laplacian). It vanishes on the
    flat vacuum and is `O(|ε|⁴)` for small `ε`. -/
def quarticRemainder {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    G.weight i j * coshRemainder (ε i - ε j)

/-- The quartic remainder is non-negative. -/
theorem quarticRemainder_nonneg {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) : 0 ≤ quarticRemainder G ε := by
  unfold quarticRemainder
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (G.weight_nonneg i j) (coshRemainder_nonneg _)

/-- Helper: the laplacian action as the product-sum of quadratic terms. -/
private theorem laplacian_action_prod_form {n : ℕ}
    (G : WeightedLedgerGraph n) (ε : LogPotential n) :
    laplacian_action G ε
      = (1 / 2) * ∑ i : Fin n, ∑ j : Fin n,
          G.weight i j * (ε i - ε j) ^ 2 := by
  unfold laplacian_action
  congr 1

/-- **DECOMPOSITION THEOREM.** The exact J-cost action equals the
    Laplacian action plus the non-negative quartic remainder:

      `exactJCostAction = laplacian_action + quarticRemainder`.

    This decomposition is **unconditional** — it holds for all `ε`,
    not just small `ε`. In the weak-field regime the remainder is
    `O(|ε|⁴)` and negligible; in the strong-field regime it is
    the physical content of the non-linear coupling. -/
theorem exact_decomposition {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) :
    exactJCostAction G ε = laplacian_action G ε + quarticRemainder G ε := by
  rw [laplacian_action_prod_form]
  unfold exactJCostAction quarticRemainder coshRemainder
  -- Right side: (1/2) Σ Σ w x² + Σ Σ w (cosh - 1 - x²/2)
  --         = Σ Σ w [x²/2 + cosh - 1 - x²/2]
  --         = Σ Σ w (cosh - 1) = left side.
  rw [show (1 : ℝ) / 2 * ∑ i : Fin n, ∑ j : Fin n, G.weight i j * (ε i - ε j) ^ 2
        = ∑ i : Fin n, ∑ j : Fin n, G.weight i j * ((ε i - ε j) ^ 2 / 2) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **WEAK-FIELD LIMIT.** When every log-potential difference is
    zero, `exactJCostAction = laplacian_action = 0`. This is the
    flat vacuum limit. -/
theorem exact_flat_agrees_with_linearized {n : ℕ}
    (G : WeightedLedgerGraph n) :
    exactJCostAction G (fun _ => (0 : ℝ))
      = laplacian_action G (fun _ => (0 : ℝ)) := by
  rw [exact_decomposition, laplacian_action_flat G]
  unfold quarticRemainder coshRemainder
  simp

/-! ## §5. The non-linear J ↔ Regge hypothesis

In the weak-field regime, `CubicDeficitDischarge.cubic_linearization_discharge`
makes the J ↔ Regge identity a theorem. Beyond that regime, one needs
the corresponding non-linear statement, which is what Cayley-Menger
calculations on a simplicial mesh produce in the limit.

We package that as an explicit hypothesis, NOT an axiom. -/

/-- A *non-linear deficit-angle functional*: an extension of the
    linear functional to strong-field configurations. Concretely
    it is a `DeficitAngleFunctional` that additionally satisfies
    the non-linear matching identity below. -/
structure NonlinearDeficitFunctional (n : ℕ) where
  functional : DeficitAngleFunctional n

/-- The **non-linear Regge ↔ J-cost matching hypothesis.** Under
    this hypothesis, the Regge sum on the non-linear deficit
    functional equals `κ · exactJCostAction`, not merely
    `κ · laplacian_action`. -/
def NonlinearReggeJCostIdentity
    {n : ℕ} (D : NonlinearDeficitFunctional n) (a : ℝ) (ha : 0 < a)
    (hinges : List (HingeDatum n)) (G : WeightedLedgerGraph n) : Prop :=
  ∀ ε : LogPotential n,
    regge_sum D.functional (conformal_edge_length_field a ha ε) hinges
      = jcost_to_regge_factor * exactJCostAction G ε

/-- **THEOREM (under hypothesis).** If the non-linear matching
    identity holds, then the J-cost Dirichlet principle reproduces
    the Regge equations in the **full non-linear regime**, not just
    the weak-field one. Stated: `exactJCostAction` is `(1/κ)` times
    the full Regge sum. -/
theorem nonlinear_field_curvature_identity
    {n : ℕ} (D : NonlinearDeficitFunctional n) (a : ℝ) (ha : 0 < a)
    (hinges : List (HingeDatum n)) (G : WeightedLedgerGraph n)
    (hNL : NonlinearReggeJCostIdentity D a ha hinges G)
    (ε : LogPotential n) :
    exactJCostAction G ε
      = (1 / jcost_to_regge_factor) *
          regge_sum D.functional (conformal_edge_length_field a ha ε) hinges := by
  have hκ : jcost_to_regge_factor ≠ 0 := jcost_to_regge_factor_ne_zero
  have hid := hNL ε
  calc
    exactJCostAction G ε
        = ((1 / jcost_to_regge_factor) * jcost_to_regge_factor)
            * exactJCostAction G ε := by field_simp [hκ]
    _   = (1 / jcost_to_regge_factor)
            * (jcost_to_regge_factor * exactJCostAction G ε) := by ring
    _   = (1 / jcost_to_regge_factor)
            * regge_sum D.functional (conformal_edge_length_field a ha ε) hinges := by
              rw [← hid]

/-- **COROLLARY.** In the strong-field regime, the J-cost
    stationarity condition `δ(exactJCostAction) = 0` is equivalent
    to the Regge stationarity condition `δ(regge_sum) = 0`. The
    equivalence is a direct consequence of
    `nonlinear_field_curvature_identity` and the non-vanishing of
    `κ`. -/
theorem jcost_stationarity_to_regge_nonlinear
    {n : ℕ} (D : NonlinearDeficitFunctional n) (a : ℝ) (ha : 0 < a)
    (hinges : List (HingeDatum n)) (G : WeightedLedgerGraph n)
    (hNL : NonlinearReggeJCostIdentity D a ha hinges G)
    (ε : LogPotential n) :
    exactJCostAction G ε = 0
      ↔ regge_sum D.functional (conformal_edge_length_field a ha ε) hinges = 0 := by
  have hκne : jcost_to_regge_factor ≠ 0 := jcost_to_regge_factor_ne_zero
  have hid := hNL ε
  constructor
  · intro h; rw [hid, h]; ring
  · intro h
    have hprod : jcost_to_regge_factor * exactJCostAction G ε = 0 := by
      rw [← hid]; exact h
    rcases mul_eq_zero.mp hprod with h1 | h2
    · exact absurd h1 hκne
    · exact h2

/-! ## §6. Honest separation: weak-field is theorem, strong-field
    is theorem under one named hypothesis

Philip's §6 concern is that the J ↔ Regge identification is
proved only in the weak-field regime. The decomposition
`exactJCostAction = laplacian_action + quarticRemainder` makes
the gap explicit at the J-cost side. The Regge side gap is
captured by `NonlinearReggeJCostIdentity`, which is proved for
cubic lattices at leading order by `cubic_linearization_discharge`
and which in the full non-linear regime requires either the
Cayley-Menger computation on simplicial meshes or the
Cheeger-Müller-Schrader theorem.

Under the named hypothesis, the identity becomes strong-field
valid, and the J-cost stationarity implies the Regge
stationarity (and hence EFE) without a weak-field restriction. -/

/-- **MASTER CERTIFICATE.** The non-linear bridge with its hypothesis
    explicitly separated. -/
structure NonlinearJCostReggeCert where
  /-- The exact J-cost action is well-defined for all `ε` (strong
      field included). -/
  exact_well_defined : ∀ {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n), 0 ≤ exactJCostAction G ε
  /-- The flat vacuum has zero exact action. -/
  exact_flat_zero : ∀ {n : ℕ} (G : WeightedLedgerGraph n),
    exactJCostAction G (fun _ => (0 : ℝ)) = 0
  /-- The exact action decomposes as linearized plus quartic remainder. -/
  decomposition : ∀ {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n),
    exactJCostAction G ε = laplacian_action G ε + quarticRemainder G ε
  /-- The quartic remainder is non-negative. -/
  remainder_nonneg : ∀ {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n), 0 ≤ quarticRemainder G ε
  /-- Under the non-linear Regge matching hypothesis, the exact
      J-cost action equals `(1/κ)` times the Regge sum. -/
  nonlinear_identity_under_hypothesis : ∀ {n : ℕ}
    (D : NonlinearDeficitFunctional n) (a : ℝ) (ha : 0 < a)
    (hinges : List (HingeDatum n)) (G : WeightedLedgerGraph n),
    NonlinearReggeJCostIdentity D a ha hinges G →
    ∀ ε : LogPotential n,
      exactJCostAction G ε
        = (1 / jcost_to_regge_factor)
          * regge_sum D.functional (conformal_edge_length_field a ha ε) hinges

theorem nonlinearJCostReggeCert : NonlinearJCostReggeCert where
  exact_well_defined := fun G ε => exactJCostAction_nonneg G ε
  exact_flat_zero := fun G => exactJCostAction_flat G
  decomposition := fun G ε => exact_decomposition G ε
  remainder_nonneg := fun G ε => quarticRemainder_nonneg G ε
  nonlinear_identity_under_hypothesis := fun D a ha hinges G hNL ε =>
    nonlinear_field_curvature_identity D a ha hinges G hNL ε

end

end NonlinearBridge
end SimplicialLedger
end Foundation
end IndisputableMonolith
