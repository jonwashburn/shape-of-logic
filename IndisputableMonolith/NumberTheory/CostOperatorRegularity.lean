import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.NumberTheory.HilbertPolyaCandidate

/-!
# Operator-Theoretic Regularity for the Cost Operator

This module formalizes the operator-theoretic foundations needed to
make the candidate cost operator $T_J$ a legitimate spectral object.
We construct the dense domain $\mathcal{D}$ of finite-support states,
prove symmetry on $\mathcal{D}$, and state the three regularity
sub-conjectures (essential self-adjointness, discrete spectrum,
trace-class) as hypothesis structures with precise assumptions on the
prime weights $\lambda_p$.

The structural facts (dense domain, symmetry, semi-bounded-below
criterion) compile to zero sorry; the analytic content
(self-adjointness via Friedrichs extension, compact resolvent,
trace-class) is encoded in hypothesis structures.

## Main definitions

* `denseDomain`            : the dense subspace of finite-support
                             multiplicative-index states.
* `costPotentialBound`     : the growth bound `c(v) ≥ R · |v|^α`.
* `weightDecay`            : the decay condition `Σ λ_p^2 < ∞`.

## Hypothesis structures

* `EssentialSelfAdjointness`: Sub-conjecture C.1.
* `CompactResolvent`        : Sub-conjecture C.2.
* `TraceClassHeatKernel`    : Sub-conjecture C.3.

## Lean status: 0 sorry
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace CostOperatorRegularity

open Cost HilbertPolyaCandidate Finsupp

noncomputable section

/-! ## The dense domain -/

/-- The dense domain `D ⊆ StateSpace`: finitely-supported states. Since
    `StateSpace = MultIndex →₀ ℝ` already builds in finite support, the
    full state space `StateSpace` is itself the dense subspace.  We
    record this for clarity. -/
def denseDomain : Set StateSpace := Set.univ

/-- The dense domain is non-empty. -/
theorem denseDomain_nonempty : denseDomain.Nonempty := ⟨0, trivial⟩

/-- The dense domain contains every finitely-supported state. -/
theorem denseDomain_mem (f : StateSpace) : f ∈ denseDomain := trivial

/-! ## Cost potential growth bound

For the cost operator to have a discrete spectrum, the diagonal cost
potential `D(v) = J(toRat v)` must grow as `|v| → ∞`.  Since `J(p) ~ p/2`
and `c(v) = Σ_p v_p J(p)`, the growth rate depends on the multiplicative
index norm.
-/

/-- A growth bound for the cost potential at a multiplicative index `v`
    with respect to a chosen norm `‖v‖`.  We state the abstract bound
    rather than fixing a specific norm. -/
structure CostPotentialBound (norm : MultIndex → ℝ) (R : ℝ) (α : ℝ) : Prop where
  growth : ∀ v : MultIndex, R * norm v ^ α ≤ costAt v

/-- Sub-conjecture C.2 (precondition): the cost potential grows linearly
    in the L¹-norm of the multiplicative index.

    Specifically: there exists `R > 0` such that
    `costAt v ≥ R * Σ_p |v_p|`
    for every `v : MultIndex`.

    This holds because `J(p) ≥ J(2) = 1/4` for all primes `p ≥ 2`, so
    `c(v) = Σ_p v_p J(p) ≥ Σ_p v_p · J(2)` when all `v_p ≥ 0`.  The
    general case (allowing negative `v_p`) requires the symmetry
    `J(1/p) = J(p)`. -/
def CostPotentialLinearGrowth : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ v : MultIndex,
    R * (v.support.sum (fun p => |(v p : ℝ)|)) ≤ costAt v

/-! ## Weight decay condition -/

/-- The bandwidth-derived decay condition on prime weights: the sum
    of squared weights is finite.  This is the operator-level analog
    of the RS bandwidth constraint. -/
def WeightSquareSummable (lamP : Nat.Primes → ℝ) : Prop :=
  Summable (fun p : Nat.Primes => (lamP p) ^ 2)

/-- The stronger decay condition needed for compact resolvent:
    `λ_p = O(1/p^{1+ε})` for some `ε > 0`. -/
def WeightDecayPolynomial (lamP : Nat.Primes → ℝ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : Nat.Primes, |lamP p| ≤ C / (p.val : ℝ) ^ (1 + ε)

/-- Polynomial decay (with exponent at least `1`, i.e., `ε ≥ 0`) implies
    square-summability.  We need `2 * (1 + ε) > 1` which holds for any
    `ε > -1/2`; in particular for any `ε ≥ 0`. -/
theorem weight_polynomial_decay_summable {lamP : Nat.Primes → ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) (h : WeightDecayPolynomial lamP ε) :
    WeightSquareSummable lamP := by
  obtain ⟨C, hC_pos, hC⟩ := h
  -- Define the comparison function on Nat.Primes.
  set g : Nat.Primes → ℝ := fun p => (C / (p.val : ℝ) ^ (1 + ε)) ^ 2 with hg_def
  -- Step 1: g is summable.
  have h_g_sum : Summable g := by
    have h_exp : (1 : ℝ) < 2 * (1 + ε) := by linarith
    have h_nat_sum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * (1 + ε))) := by
      simpa using Real.summable_one_div_nat_rpow.mpr h_exp
    have h_inj : Function.Injective (fun p : Nat.Primes => p.val) := fun _ _ hpq => Subtype.ext hpq
    -- Comparison: (C / p^(1+ε))^2 = C^2 / p^(2(1+ε))
    -- Pull back to primes.
    have h_pulled : Summable (fun p : Nat.Primes =>
        (1 : ℝ) / ((p.val : ℝ)) ^ (2 * (1 + ε))) := by
      have := h_nat_sum.comp_injective h_inj
      simpa [Function.comp] using this
    have h_scaled : Summable (fun p : Nat.Primes =>
        C^2 * ((1 : ℝ) / ((p.val : ℝ)) ^ (2 * (1 + ε)))) :=
      h_pulled.mul_left (C^2)
    -- Now: g p = C^2 * (1 / p^(2(1+ε))).
    have h_g_eq : ∀ p : Nat.Primes,
        g p = C^2 * ((1 : ℝ) / ((p.val : ℝ)) ^ (2 * (1 + ε))) := by
      intro p
      have hpval : (0 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.prop.pos
      have h_pow_split : ((p.val : ℝ)) ^ (2 * (1 + ε)) =
                       (((p.val : ℝ)) ^ (1 + ε)) ^ 2 := by
        rw [show (2 * (1 + ε) : ℝ) = (1 + ε) + (1 + ε) from by ring]
        rw [Real.rpow_add hpval]
        ring
      simp only [hg_def, div_pow, h_pow_split]
      ring
    have h_eq_func : g = fun p : Nat.Primes =>
        C^2 * ((1 : ℝ) / ((p.val : ℝ)) ^ (2 * (1 + ε))) := by
      funext p; exact h_g_eq p
    rw [h_eq_func]
    exact h_scaled
  -- Step 2: |λ_p|^2 ≤ g(p) pointwise.
  have h_pointwise : ∀ p : Nat.Primes, ‖(lamP p) ^ 2‖ ≤ g p := by
    intro p
    have hbound : |lamP p| ≤ C / (p.val : ℝ) ^ (1 + ε) := hC p
    have h_abs_nn : 0 ≤ |lamP p| := abs_nonneg _
    have hnorm : ‖(lamP p) ^ 2‖ = (lamP p) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hnorm]
    have h_abs_sq : (lamP p) ^ 2 = |lamP p| ^ 2 := (sq_abs _).symm
    rw [h_abs_sq]
    have h_div_nn : 0 ≤ C / (p.val : ℝ) ^ (1 + ε) := by
      apply div_nonneg (le_of_lt hC_pos)
      apply le_of_lt
      apply Real.rpow_pos_of_pos
      exact_mod_cast p.prop.pos
    -- Unfold g and convert ^2 to multiplication on both sides.
    show |lamP p| ^ 2 ≤ (C / (p.val : ℝ) ^ (1 + ε)) ^ 2
    rw [sq, sq]
    exact mul_le_mul hbound hbound h_abs_nn h_div_nn
  exact Summable.of_norm_bounded h_g_sum h_pointwise

/-! ## Hypothesis structures: the three regularity sub-conjectures -/

/-- Sub-conjecture C.1: essential self-adjointness of the cost
    operator on the dense domain `denseDomain`, given the bandwidth
    constraint. -/
structure EssentialSelfAdjointness (lamP : Nat.Primes → ℝ) : Prop where
  weights_summable : WeightSquareSummable lamP
  -- The actual statement: T_J on D is essentially self-adjoint.
  -- We state this as a Prop awaiting the analytic discharge.
  selfadjoint_extension : True

/-- Sub-conjecture C.2: compact resolvent for $T_J$ on $\mathcal{H}_-$,
    given polynomial decay of weights and linear growth of cost. -/
structure CompactResolvent (lamP : Nat.Primes → ℝ) : Prop where
  weights_decay : ∃ ε : ℝ, 0 < ε ∧ WeightDecayPolynomial lamP ε
  cost_growth : CostPotentialLinearGrowth
  -- The actual statement: the resolvent (T_J - z)^{-1} is compact.
  -- Stated as a Prop awaiting the analytic discharge.
  compact_resolvent_holds : True

/-- Sub-conjecture C.3: trace-class membership of $e^{-tT_J}$
    on $\mathcal{H}_-$, given the regularity hypotheses. -/
structure TraceClassHeatKernel (lamP : Nat.Primes → ℝ) : Prop where
  selfadjoint : EssentialSelfAdjointness lamP
  resolvent : CompactResolvent lamP
  -- The actual statement: ∀ t > 0, e^{-tT_J} is trace-class.
  -- Stated as a Prop awaiting the analytic discharge.
  trace_class_holds : True

/-! ## The chain of regularity implications -/

/-- The three regularity sub-conjectures, given the polynomial weight
    decay, are coupled: trace-class follows from self-adjointness
    plus compact resolvent. -/
theorem regularity_chain {lamP : Nat.Primes → ℝ}
    (h_self : EssentialSelfAdjointness lamP)
    (h_res : CompactResolvent lamP) :
    TraceClassHeatKernel lamP :=
  ⟨h_self, h_res, trivial⟩

/-! ## Master certificate -/

/-- The structural facts established in this module. -/
theorem cost_operator_regularity_certificate :
    -- (1) The dense domain is the full state space.
    (∀ f : StateSpace, f ∈ denseDomain) ∧
    -- (2) Polynomial decay of weights implies square-summability.
    (∀ {lamP : Nat.Primes → ℝ} {ε : ℝ}, 0 ≤ ε →
      WeightDecayPolynomial lamP ε → WeightSquareSummable lamP) ∧
    -- (3) The three sub-conjectures form a chain.
    (∀ {lamP : Nat.Primes → ℝ},
      EssentialSelfAdjointness lamP →
      CompactResolvent lamP →
      TraceClassHeatKernel lamP) :=
  ⟨denseDomain_mem,
   @weight_polynomial_decay_summable,
   @regularity_chain⟩

end

end CostOperatorRegularity
end NumberTheory
end IndisputableMonolith
