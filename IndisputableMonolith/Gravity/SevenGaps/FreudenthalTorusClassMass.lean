import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.PathSumProbes
import IndisputableMonolith.Gravity.SevenGaps.ClassPushforward

/-!
# Seven Gaps, Crux-2 consistency gate: torus class mass, labeled vs class

## Protocol: QUOTIENT_BOOKKEEPING (panel-locked).

## WORDING REPAIR (recorded per the panel's C6 trap)

The originally-worded gate ("the class summand of the canonical torus in
the pushforward form is suppressed as N⁻³") is ILL-POSED as stated,
because the pushforward class mass is `|fiber| · (1/|Aut|)`
(`PathSum.classMass_eq_fiberCard_mul_mu`) and the labeled fiber
cardinality GROWS with the class size.  The panel's own kill list forbids
the absolute N⁻³ / N⁻⁶ suppression claim for the PUSHFORWARD mass.  This
module implements the honest split, keeping the two objects separated in
the type system:

**THEOREM (proved below, 0 sorry, 0 new axioms) — the LABELED object:**
* `mu_torusClassMember_le`: EVERY labeled member `K` of the torus class
  (`⟦K⟧ = ⟦T_N⟧`) has symmetry-factor mass `μ(K) ≤ 1/N³` (the per-`1/|Aut|`
  statement, derived from `mu_congr` + `mu_freudenthal_le_inv_cube`).
* `norm_freudenthal_labeledSummand_le`: the single-labeled-representative
  summand `‖μ(K) · z‖ ≤ 1/N³` for any unit-modulus `z` and any labeled
  member `K` of the torus class (the class-API restatement of
  `unnormalized_torus_weight_suppressed`).
* `tendsto_mu_freudenthal_zero` and `tendsto_labeledSummand_zero`: the
  labeled-representative summand sequence
  `fun N => μ(T_{N+1}) · z_N` (any unit-modulus `z_N`) tends to `0`.

**THEOREM — the CLASS object (with the honest fiber factor):**
* `torus_classMass_eq_fiberCard_mul_mu`: the pushforward class mass of the
  torus class equals `|fiber| · μ(T_N)`.
* `torus_classMass_le_fiberCard_div_cube`:
  `classMass(⟦T_N⟧) ≤ |fiber| / N³`.  The fiber cardinality is NOT
  bounded here (it grows with the labeled class), so this does NOT give
  an absolute N⁻³ suppression of the pushforward mass.

**FORBIDDEN (not claimed anywhere in this module):**
* "classMass(⟦T_N⟧) ≤ 1/N³" — FALSE in general; the killed absolute
  pushforward-suppression claim.  Reason: `|fiber|` grows.
* Any convergence / continuum-limit / dominance claim about `Z`.

**OPEN (flags stay RED; nothing here changes them):**
* `Z_RS_continuum_limit` : RED.
* `substrate_measure_derived` : RED.
* `gap1_bridge_derived` : RED.

## Proof notes
* Zero `sorry`, zero `admit`, zero new axioms, zero `decide` /
  `native_decide` in this module.
* The tendsto statements are about the LABELED representative sequence
  only, exactly as the honest gate requires.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace FreudenthalTorusClassMass

open PathSumMeasure
open PathSumProbes
open PathSum
open FiniteQuotient

/-! ## §1. The LABELED object: per-representative `1/|Aut|` suppression -/

/-- **THEOREM (labeled, per-`1/|Aut|`).**  Every labeled member of the
torus class carries symmetry-factor mass at most `N⁻³`: μ is a class
function (`mu_congr`), and the translation embedding gives
`μ(T_N) ≤ 1/N³`.  This is a statement about EACH labeled representative,
not about the pushforward class mass. -/
theorem mu_torusClassMember_le (N : ℕ) [NeZero N]
    (K : BoundedComplex (7 * N ^ 3))
    (hK : Quotient.mk (relabelSetoid (7 * N ^ 3)) K =
      Quotient.mk (relabelSetoid (7 * N ^ 3)) (freudenthalBoundedComplex N)) :
    mu K ≤ 1 / ((N : ℝ) ^ 3) := by
  rw [mu_congr (equivalent_of_mk_eq hK)]
  exact mu_freudenthal_le_inv_cube N

/-- **THEOREM (labeled summand bound; class-API restatement of
`unnormalized_torus_weight_suppressed`).**  For any labeled member `K` of
the torus class and any unit-modulus value `z`, the single labeled
summand `μ(K)·z` has modulus at most `N⁻³`.  LABELED / CLASS DISTINCTION:
this bounds ONE labeled summand; the pushforward CLASS mass is
`|fiber|·μ` and is NOT bounded by `N⁻³` here. -/
theorem norm_freudenthal_labeledSummand_le (N : ℕ) [NeZero N]
    (K : BoundedComplex (7 * N ^ 3))
    (hK : Quotient.mk (relabelSetoid (7 * N ^ 3)) K =
      Quotient.mk (relabelSetoid (7 * N ^ 3)) (freudenthalBoundedComplex N))
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(mu K : ℂ) * z‖ ≤ 1 / ((N : ℝ) ^ 3) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mu_pos K)]
  calc mu K * ‖z‖
      ≤ mu K * 1 := mul_le_mul_of_nonneg_left hz (le_of_lt (mu_pos K))
    _ = mu K := mul_one _
    _ ≤ 1 / ((N : ℝ) ^ 3) := mu_torusClassMember_le N K hK

/-! ## §2. The CLASS object: the honest fiber factor -/

/-- **THEOREM (class mass, identity form).**  The pushforward class mass
of the torus class is the labeled fiber cardinality times the symmetry
factor of the canonical torus:
`classMass(⟦T_N⟧) = |fiber(⟦T_N⟧)| · μ(T_N)`. -/
theorem torus_classMass_eq_fiberCard_mul_mu (N : ℕ) [NeZero N] :
    classMass (Quotient.mk (relabelSetoid (7 * N ^ 3))
        (freudenthalBoundedComplex N)) =
      (fiberCard (relabelSetoid (7 * N ^ 3))
          (Quotient.mk (relabelSetoid (7 * N ^ 3))
            (freudenthalBoundedComplex N)) : ℝ) *
        mu (freudenthalBoundedComplex N) := by
  rw [classMass_eq_fiberCard_mul_mu]
  congr 1
  exact mu_congr (equivalent_of_mk_eq (Quotient.out_eq _))

/-- **THEOREM (the honest class-mass bound).**
`classMass(⟦T_N⟧) ≤ |fiber(⟦T_N⟧)| / N³`.  The fiber cardinality is NOT
bounded here; in particular this does NOT yield the (killed) absolute
`N⁻³` suppression of the pushforward mass. -/
theorem torus_classMass_le_fiberCard_div_cube (N : ℕ) [NeZero N] :
    classMass (Quotient.mk (relabelSetoid (7 * N ^ 3))
        (freudenthalBoundedComplex N)) ≤
      (fiberCard (relabelSetoid (7 * N ^ 3))
          (Quotient.mk (relabelSetoid (7 * N ^ 3))
            (freudenthalBoundedComplex N)) : ℝ) / ((N : ℝ) ^ 3) := by
  rw [torus_classMass_eq_fiberCard_mul_mu, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (mu_freudenthal_le_inv_cube N)
    (Nat.cast_nonneg _)

/-! ## §3. Tendsto-zero for the LABELED representative sequence -/

/-- The dominating sequence `1/(n+1)³` is below `1/(n+1)`. -/
theorem one_div_cube_le_one_div (n : ℕ) :
    1 / (((n : ℝ) + 1) ^ 3) ≤ 1 / ((n : ℝ) + 1) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := lt_of_lt_of_le one_pos h1
  exact one_div_le_one_div_of_le hpos (le_self_pow₀ h1 (by norm_num))

/-- **THEOREM (labeled tendsto, measure form).**  The symmetry-factor mass
of the canonical torus LABELED representative tends to zero:
`μ(T_{N+1}) → 0`.  (Squeeze between `0` and `1/(N+1)³ ≤ 1/(N+1)`.) -/
theorem tendsto_mu_freudenthal_zero :
    Filter.Tendsto (fun n : ℕ => mu (freudenthalBoundedComplex (n + 1)))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun n => le_of_lt (mu_pos _)) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  calc mu (freudenthalBoundedComplex (n + 1))
      ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 3) := mu_freudenthal_le_inv_cube (n + 1)
    _ = 1 / (((n : ℝ) + 1) ^ 3) := by rw [Nat.cast_add, Nat.cast_one]
    _ ≤ 1 / ((n : ℝ) + 1) := one_div_cube_le_one_div n

/-- **THEOREM (labeled tendsto, summand form; the honest T4 gate).**  The
labeled-representative summand sequence `μ(T_{N+1}) · z_N`, for ANY
sequence of unit-modulus values (e.g. `unitaryWeight` values of any
action), tends to `0`.  LABELED / CLASS DISTINCTION: this is the labeled
representative sequence; NO claim is made about the pushforward CLASS
mass sequence `|fiber|·μ`, whose fiber factor grows. -/
theorem tendsto_labeledSummand_zero (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ => (mu (freudenthalBoundedComplex (n + 1)) : ℂ) * z n)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_mu_freudenthal_zero
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mu_pos _)]
  exact mul_le_of_le_one_right (le_of_lt (mu_pos _)) (hz n)

/-! ## §4. Status ledger (rfl-forced; RED flags stay RED) -/

/-- Status record for the torus class-mass consistency gate.  No `True`
shells; every flag is forced by `rfl` below. -/
structure TorusClassMassStatus where
  labeled_member_mass_bounded : Bool
  labeled_summand_bounded : Bool
  labeled_summand_tendsto_zero : Bool
  classMass_identity_proved : Bool
  classMass_fiberCard_bound_proved : Bool
  /-- FALSE (killed claim, wording repair recorded in the header): the
  pushforward class mass is NOT absolutely `N⁻³`-suppressed; the labeled
  fiber cardinality grows. -/
  pushforward_classMass_absolutely_suppressed : Bool
  /-- RED. -/
  Z_RS_continuum_limit : Bool
  /-- RED. -/
  substrate_measure_derived : Bool
  /-- RED. -/
  gap1_bridge_derived : Bool

/-- The consistency-gate status after this module. -/
def torusClassMassStatus : TorusClassMassStatus where
  labeled_member_mass_bounded := true
  labeled_summand_bounded := true
  labeled_summand_tendsto_zero := true
  classMass_identity_proved := true
  classMass_fiberCard_bound_proved := true
  pushforward_classMass_absolutely_suppressed := false
  Z_RS_continuum_limit := false
  substrate_measure_derived := false
  gap1_bridge_derived := false

theorem torusClassMassStatus_flags :
    torusClassMassStatus.labeled_member_mass_bounded = true ∧
    torusClassMassStatus.labeled_summand_bounded = true ∧
    torusClassMassStatus.labeled_summand_tendsto_zero = true ∧
    torusClassMassStatus.classMass_identity_proved = true ∧
    torusClassMassStatus.classMass_fiberCard_bound_proved = true ∧
    torusClassMassStatus.pushforward_classMass_absolutely_suppressed = false ∧
    torusClassMassStatus.Z_RS_continuum_limit = false ∧
    torusClassMassStatus.substrate_measure_derived = false ∧
    torusClassMassStatus.gap1_bridge_derived = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FreudenthalTorusClassMass
end SevenGaps
end Gravity
end IndisputableMonolith
