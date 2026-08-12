import Mathlib

/-!
# Gap 2 / C11 / A36: the anomaly is the loop-count residual

Track D lane C11 measures the anomaly fraction `q(c) = ‖r(h)‖²_μ / ‖h‖²_μ` of
the incidence history `h = 2·n_proper` against the count span `{nV, nE, nT}`
over the iso-class ensemble with `μ = 1/|Aut|` (frozen A30/A33/A34/A35
receipts, tilt 2).  The C11 fork was whether `q(c)` tends to zero or to a
small positive limit.  This module proves the algebraic heart of the answer:

  **h = 2·nE − 2·n_loop pointwise, and nE lies in the count span, so the
  residual of h is exactly −2 times the residual of the loop count.**
  THE ANOMALY IS THE LOOP-COUNT RESIDUAL.

Consequences proved here, in an arbitrary real inner-product space:

* `resid_history_eq_neg_two_resid_loop`: the residual identity itself;
* `norm_sq_resid_history`: `‖r(h)‖² = 4·‖r(n_loop)‖²`;
* `norm_sq_resid_le`: contraction, `‖r(n_loop)‖² ≤ ‖n_loop‖²` (Pythagoras);
* `anomaly_fraction_eq`: with `n_proper := nE − n_loop`,
  `q = ‖r(n_loop)‖² / ‖n_proper‖²`;
* `anomaly_fraction_le`: the moment bound `q ≤ ‖n_loop‖² / ‖n_proper‖²`.

## Verified identity (MEASURED)

The identity was verified per class against the four frozen receipts at caps
1..6 by `QG/attack_full_theory_20260729/a36_anomaly_mechanism.py` (receipt
`scripts/qg/out/anomaly_mechanism_20260731.json`): zero mismatches at every
class of every cap, including cap 6's 157,920 classes, with the recomputed
`q(c)` string-equal to the frozen `q_sequence` values.  This file is the
receipt-free proof of why the identity must hold.

## The asymptotic theorem (DERIVED-UNFORMALIZED, paper proof in A36)

The census product form (orbit-stabilizer for `S_nV × S_nE`, verified per
`(nV, nE, n_loop)` cell at caps 1..6) makes the μ-law of `(nV, nE, n_loop, nT)`
explicit: conditional on `(n, k)`, `n_loop ~ Binomial(k, 1/n)`, `nT` free.
The saddle of the weights `n^(2k)/(n!·k!)` sits at `k = c` (saturated) and
`n*` solving `n* log n* = 2c` (interior for `c ≥ 8`), giving
`E_μ[n_loop²] = O((log c)²)` while `E_μ[n_proper²] ~ c²`, hence

  `q(c) ≤ E_μ[n_loop²] / E_μ[n_proper²] = O((log c)² / c²) → 0`,

with the sharp rate `q(c) = (log c)/(2c²)·(1 + o(1))`.  The closed form
(validated string-equal to the frozen `q` at caps 2..6) gives the exact
advance prediction `q(7) = 187550654661536444414913801027847000271640931 /
6506666184691079714323445427739711317065991705 ≈ 0.028824` for the planned
cap-7 enumeration.  The asymptotic statement is about the concrete enumerated
ensemble and lives on paper in
`QG/attack_full_theory_20260729/A36_AnomalyMechanism_20260731.html`; the
kernel-checked content of this module is the mechanism identity and the
bound, which are the load-bearing algebra of that proof.
-/

open scoped RealInnerProductSpace

namespace Gap2AnomalyAsymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The count span `{nV, nE, nT}` as a submodule of the ambient space of
class functions (vertex count, edge count, tet count). -/
noncomputable def countSpan (nv ne nt : E) : Submodule ℝ E :=
  Submodule.span ℝ {nv, ne, nt}

instance (nv ne nt : E) : FiniteDimensional ℝ (countSpan nv ne nt) := by
  rw [countSpan]
  exact FiniteDimensional.span_of_finite ℝ (Set.toFinite _)

instance (nv ne nt : E) : CompleteSpace (countSpan nv ne nt) :=
  FiniteDimensional.complete ℝ _

/-- The residual of a class function `x` against the count span: `x` minus
its orthogonal projection onto the span of the three count observables. -/
noncomputable def resid (nv ne nt x : E) : E :=
  x - (countSpan nv ne nt).starProjection x

/-- **The mechanism identity.**  Since `h = 2·nE − 2·n_loop` pointwise and
`nE` lies in the count span, the residual of `h` against the count span is
exactly `−2` times the residual of the loop count.  Verified per class
against the frozen C11 receipts at caps 1..6; proved here from linearity
alone. -/
theorem resid_history_eq_neg_two_resid_loop (nv ne nt nl h : E)
    (hh : h = (2 : ℝ) • ne - (2 : ℝ) • nl) :
    resid nv ne nt h = (-2 : ℝ) • resid nv ne nt nl := by
  have hne_mem : ne ∈ countSpan nv ne nt := by
    unfold countSpan
    exact Submodule.subset_span (by simp)
  have hne : (countSpan nv ne nt).starProjection ne = ne := by
    rw [Submodule.starProjection_eq_self_iff]
    exact hne_mem
  have hproj : (countSpan nv ne nt).starProjection h =
      (2 : ℝ) • ne - (2 : ℝ) • (countSpan nv ne nt).starProjection nl := by
    rw [hh, map_sub, map_smul, map_smul, hne]
  unfold resid
  rw [hproj, hh]
  module

/-- Norm form of the identity: `‖r(h)‖² = 4·‖r(n_loop)‖²`. -/
theorem norm_sq_resid_history (nv ne nt nl h : E)
    (hh : h = (2 : ℝ) • ne - (2 : ℝ) • nl) :
    ‖resid nv ne nt h‖ ^ 2 = 4 * ‖resid nv ne nt nl‖ ^ 2 := by
  have hnorm : ‖(-2 : ℝ)‖ = 2 := by norm_num
  rw [resid_history_eq_neg_two_resid_loop nv ne nt nl h hh, norm_smul, hnorm]
  ring

/-- Contraction: projection only shrinks the loop count,
`‖r(n_loop)‖² ≤ ‖n_loop‖²`, by Pythagoras. -/
theorem norm_sq_resid_le (nv ne nt nl : E) :
    ‖resid nv ne nt nl‖ ^ 2 ≤ ‖nl‖ ^ 2 := by
  unfold resid
  have hdecomp : nl = (countSpan nv ne nt).starProjection nl +
      (nl - (countSpan nv ne nt).starProjection nl) := by abel
  have horth := Submodule.inner_right_of_mem_orthogonal
      ((countSpan nv ne nt).starProjection_apply_mem nl)
      (Submodule.sub_starProjection_mem_orthogonal nl)
  conv_rhs => rw [hdecomp]
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real horth]
  exact le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The anomaly fraction as a loop-moment ratio: with `n_proper = nE − n_loop`,
`q = ‖r(h)‖²/‖h‖²` equals `‖r(n_loop)‖²/‖n_proper‖²`. -/
theorem anomaly_fraction_eq (nv ne nt nl np h : E) (hnp : np = ne - nl)
    (hh : h = (2 : ℝ) • np) :
    ‖resid nv ne nt h‖ ^ 2 / ‖h‖ ^ 2 =
      ‖resid nv ne nt nl‖ ^ 2 / ‖np‖ ^ 2 := by
  have hh' : h = (2 : ℝ) • ne - (2 : ℝ) • nl := by
    rw [hh, hnp]
    module
  rw [norm_sq_resid_history nv ne nt nl h hh']
  have hnorm : ‖(2 : ℝ)‖ = 2 := by norm_num
  have h2 : ‖h‖ ^ 2 = 4 * ‖np‖ ^ 2 := by
    rw [hh, norm_smul, hnorm]
    ring
  rw [h2]
  exact mul_div_mul_left _ _ (by norm_num)

/-- **The moment bound.**  The anomaly fraction is bounded by the raw loop
second moment over the proper-edge second moment:
`q ≤ ‖n_loop‖²/‖n_proper‖²`.  This is the inequality that closes the C11
fork on paper: the product-form census gives `E_μ[n_loop²] = O((log c)²)`
and `E_μ[n_proper²] ~ c²`, hence `q(c) → 0`. -/
theorem anomaly_fraction_le (nv ne nt nl np h : E) (hnp : np = ne - nl)
    (hh : h = (2 : ℝ) • np) (hnz : np ≠ 0) :
    ‖resid nv ne nt h‖ ^ 2 / ‖h‖ ^ 2 ≤ ‖nl‖ ^ 2 / ‖np‖ ^ 2 := by
  rw [anomaly_fraction_eq nv ne nt nl np h hnp hh]
  have hpos : 0 < ‖np‖ ^ 2 := pow_pos (norm_pos_iff.mpr hnz) 2
  rw [div_le_div_iff_of_pos_right hpos]
  exact norm_sq_resid_le nv ne nt nl

#print axioms resid_history_eq_neg_two_resid_loop
#print axioms norm_sq_resid_history
#print axioms norm_sq_resid_le
#print axioms anomaly_fraction_eq
#print axioms anomaly_fraction_le

end Gap2AnomalyAsymptotics
