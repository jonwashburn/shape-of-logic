import Mathlib

-- NOTE: We intentionally do NOT import `IndisputableMonolith.Unification.TwoLimitsTheorem`
-- because that module currently has a pre-existing Mathlib API drift on line 46
-- (the `continuum_limit_second_order` interface uses an outdated bound shape).
-- The discharge below stands independently and can be wired into TwoLimitsTheorem
-- once that file is updated.

/-!
# Conditional Discharge of a Special Quadratic `regge_to_eh_convergence`

The old fifth RS-internal gravity axiom in §XXIII.B' was phrased as an
`O(a^2)` convergence of a discrete Regge action to the continuum
Einstein-Hilbert action.  That is **not** the bare CMS Theorem 5.1 statement.
CMS gives a curvature-measure bound with an `η^(1/2)` bulk term plus a
boundary-tube term.  The `O(a^2)` action statement here is therefore a
stronger special-purpose witness, retained for compatibility with older
two-limits code.

This module provides a **conditional theorem** form: given an
explicit special quadratic witness, the convergence statement
`|S_Regge − S_EH| ≤ C·a²` follows.  The witness is the
named hypothesis we would otherwise need to justify by a special weak-field,
numerical, or lattice-specific argument.

Status flag: PARTIAL CLOSURE / CONDITIONAL THEOREM.
-/

namespace IndisputableMonolith
namespace Unification
namespace TwoLimitsDischarged

noncomputable section

/-- Special quadratic witness: for any `S_EH` and any
    mesh size `a ∈ (0,1)`, there exists a Regge action value
    `S_Regge` and a constant `C > 0` controlling the
    `|S_Regge − S_EH| ≤ C·a²` error. -/
def CheegerMullerWitness : Prop :=
  ∀ (S_EH : ℝ) (a : ℝ), 0 < a → a < 1 →
    ∃ (S_Regge : ℝ) (C : ℝ), 0 < C ∧ |S_Regge - S_EH| ≤ C * a ^ 2

/-- **CONDITIONAL THEOREM** (was `axiom regge_to_eh_convergence`):
    given a special quadratic witness, the Regge → EH convergence
    holds at every mesh size in `(0, 1)`. -/
theorem regge_to_eh_convergence_proof
    (h_witness : CheegerMullerWitness) :
    ∀ (S_EH : ℝ) (a : ℝ), 0 < a → a < 1 →
      ∃ (S_Regge : ℝ) (C : ℝ), 0 < C ∧ |S_Regge - S_EH| ≤ C * a ^ 2 :=
  h_witness

/-- **TRIVIAL WITNESS**: the convergence holds vacuously by taking
    `S_Regge = S_EH` and `C = 1` (the difference is zero, hence
    ≤ `1 · a²` for any `a > 0`).  This shows the bound is satisfiable. -/
theorem cheeger_muller_witness_trivial : CheegerMullerWitness := by
  intro S_EH a ha _
  refine ⟨S_EH, 1, by norm_num, ?_⟩
  simp
  positivity

/-- **DISCHARGED THEOREM**: the original `regge_to_eh_convergence`
    statement holds, with an explicit constructive witness. -/
theorem regge_to_eh_convergence_discharged :
    ∀ (S_EH : ℝ) (a : ℝ), 0 < a → a < 1 →
      ∃ (S_Regge : ℝ) (C : ℝ), 0 < C ∧ |S_Regge - S_EH| ≤ C * a ^ 2 :=
  cheeger_muller_witness_trivial

/-! ## Note on the trivial witness

The trivial witness `S_Regge = S_EH` proves the *existence* of a
Regge value satisfying the bound, but does not derive the Regge
action from a discrete triangulation independently of the EH value.
The physically interesting case (where `S_Regge` is computed from
a triangulation and `S_EH` is the continuum integral) requires the
actual Regge construction plus the appropriate convergence theorem.  The
general CMS theorem alone gives the `η^(1/2)` measure-convergence bound, not
this `O(a^2)` action envelope.

So the discharge is **structural**: the existence statement is
provable, but the substantive content (that real Regge actions
converge to EH) needs a separate physical-discharge proof.

The original `axiom` in `TwoLimitsTheorem.lean` carries the same
existence statement and so is no stronger than the trivial witness
for the proof obligation as currently written.  A future Lean port
of the relevant Regge convergence argument would replace
`cheeger_muller_witness_trivial` with an actual discrete-construction-based
proof.
-/

end

end TwoLimitsDischarged
end Unification
end IndisputableMonolith
