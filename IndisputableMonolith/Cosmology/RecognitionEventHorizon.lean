import Mathlib
import IndisputableMonolith.Constants

/-!
# Cosmology: the recognition event horizon `8 φ²` (Phase 9 freeze-out)

## Status: THEOREM (0 sorry, 0 RS-internal axiom).

This module formalizes the finite recognition horizon that drives the Phase-9
accelerated-expansion freeze-out in
`scripts/cosmogenesis/freeze_out_dynamics.py`.

## The forced setup (no tuned Hubble rate, no coupling)

A recognition signal travels one comoving cell per tick at unit scale. The
cadence is eight ticks per recognition epoch (T-7), so a signal covers eight
comoving cells per epoch at unit scale. The forced self-similar dilation
expands the comoving scale by `φ` per epoch (T-6), so the comoving distance a
signal covers in epoch `m` is divided by `φ^m`:

  `perEpochReach m = 8 / φ^m = 8 (1/φ)^m`.

The cumulative comoving reach after infinitely many epochs is the geometric
series `∑ 8 (1/φ)^m`. Because the dilation ratio `1/φ` is strictly below one,
this series converges to a finite limit, the de Sitter recognition event
horizon:

  `∑_{m ≥ 0} 8 (1/φ)^m = 8 φ² = 8 (φ + 1) ≈ 20.944` comoving cells.

The two ingredients are the cadence `8` (T-7) and the dilation sum `φ²`
(T-6, via `φ² = φ + 1`). There is no fitted constant.

## What this forces physically

The partial reach after any finite number of epochs is strictly below `8 φ²`
and increases monotonically toward it. So a comoving separation at or beyond
`8 φ²` is never crossed by a recognition signal. Structure on those scales can
never be brought into causal contact, so it can never be homogenized: it
freezes at its primordial amplitude. Structure below the horizon is eventually
crossed and homogenizes. That is the RS `Ω_Λ` freeze-out.

## Relation to `VacuumHorizonForcing`

`VacuumHorizonForcing` selects the *past-directed particle horizon* for the
*vacuum-energy ledger cost*, and there the de Sitter event horizon is excluded
because that calculation must not depend on future expansion. This module is a
different object: the *future-directed* reach of a signal launched now, which
is exactly a de Sitter event horizon. The two are consistent, not in tension:
the ledger ground-state cost uses the past cone, the forward freeze-out of
structure uses the future cone.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RecognitionEventHorizon

open scoped BigOperators

/-- Local alias for the golden ratio, following the per-module convention. -/
noncomputable abbrev φ : ℝ := Constants.phi

lemma phi_pos : 0 < φ := Constants.phi_pos
lemma one_lt_phi : 1 < φ := Constants.one_lt_phi
lemma phi_sq_eq : φ ^ 2 = φ + 1 := Constants.phi_sq_eq

/-! ## §1. The dilation ratio `1/φ` -/

lemma phi_inv_pos : 0 < 1 / φ := one_div_pos.mpr phi_pos

lemma phi_inv_nonneg : (0 : ℝ) ≤ 1 / φ := le_of_lt phi_inv_pos

lemma phi_inv_lt_one : 1 / φ < 1 := by
  rw [div_lt_one phi_pos]; exact one_lt_phi

/-! ## §2. Per-epoch reach, cumulative reach, the horizon -/

/-- The comoving distance a recognition signal covers in epoch `m`: the cadence
`8` (T-7) divided by the forced dilation `φ^m` (T-6). -/
noncomputable def perEpochReach (m : ℕ) : ℝ := 8 * (1 / φ) ^ m

/-- The de Sitter recognition event horizon forced by φ-dilation: `8 φ²`. -/
noncomputable def recognitionEventHorizon : ℝ := 8 * φ ^ 2

/-- The cumulative comoving reach after `n` epochs: the partial sum of
per-epoch reaches. -/
noncomputable def cumulativeReach (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, perEpochReach m

lemma perEpochReach_pos (k : ℕ) : 0 < perEpochReach k := by
  unfold perEpochReach
  exact mul_pos (by norm_num) (pow_pos phi_inv_pos k)

lemma perEpochReach_summable : Summable perEpochReach :=
  (summable_geometric_of_lt_one phi_inv_nonneg phi_inv_lt_one).mul_left 8

/-! ## §3. The geometric sum: `∑ (1/φ)^m = φ²` -/

/-- The closed-form geometric sum of the dilation ratio. With ratio `1/φ < 1`,
`∑_{m ≥ 0} (1/φ)^m = (1 - 1/φ)⁻¹`, and `(1 - 1/φ)⁻¹ = φ²` follows from the
self-similar identity `φ² = φ + 1`. -/
theorem tsum_phi_inv_pow : ∑' m : ℕ, (1 / φ) ^ m = φ ^ 2 := by
  rw [tsum_geometric_of_lt_one phi_inv_nonneg phi_inv_lt_one]
  -- Goal: (1 - 1/φ)⁻¹ = φ ^ 2
  have hφ : φ ≠ 0 := ne_of_gt phi_pos
  have hkey : (1 - 1 / φ) * φ ^ 2 = 1 := by
    have e1 : (1 - 1 / φ) * φ ^ 2 = φ ^ 2 - φ := by
      field_simp
    rw [e1, phi_sq_eq]; ring
  exact inv_eq_of_mul_eq_one_right hkey

/-! ## §4. The total reach equals the horizon -/

/-- **THEOREM.** The total cumulative reach over all epochs equals the forced
event horizon `8 φ²`. A recognition signal can only ever traverse a finite
comoving distance, even given infinitely many epochs. -/
theorem tsum_perEpochReach :
    ∑' m : ℕ, perEpochReach m = recognitionEventHorizon := by
  unfold perEpochReach recognitionEventHorizon
  rw [tsum_mul_left, tsum_phi_inv_pow]

/-- The horizon in closed form, purely from `φ² = φ + 1`. Numerically
`8 (φ + 1) ≈ 20.944` comoving cells, matching the numeric simulation. -/
theorem recognitionEventHorizon_eq : recognitionEventHorizon = 8 * (φ + 1) := by
  unfold recognitionEventHorizon; rw [phi_sq_eq]

/-! ## §5. The partial reach never reaches the horizon -/

/-- **THEOREM.** After any finite number of epochs the cumulative reach is
strictly below the horizon. A comoving separation at or beyond `8 φ²` is
therefore never crossed by a recognition signal, so super-horizon structure can
never be homogenized: it freezes at its primordial amplitude. -/
theorem cumulativeReach_lt_horizon (n : ℕ) :
    cumulativeReach n < recognitionEventHorizon := by
  have hsum := perEpochReach_summable
  have hsplit := Summable.sum_add_tsum_nat_add n hsum
  have htail_summable : Summable (fun i => perEpochReach (i + n)) :=
    (summable_nat_add_iff n).2 hsum
  have htail_pos : 0 < ∑' i, perEpochReach (i + n) :=
    htail_summable.tsum_pos (fun i => le_of_lt (perEpochReach_pos _)) 0
      (perEpochReach_pos _)
  have key :
      cumulativeReach n + ∑' i, perEpochReach (i + n) = recognitionEventHorizon := by
    have h := hsplit
    rw [tsum_perEpochReach] at h
    simpa [cumulativeReach] using h
  linarith [htail_pos, key]

/-- **THEOREM.** The cumulative reach increases strictly with each epoch:
each epoch adds a strictly positive per-epoch reach, so the reach climbs
monotonically toward (but never attains) the horizon. -/
theorem cumulativeReach_strictMono : StrictMono cumulativeReach := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hstep : cumulativeReach (n + 1) = cumulativeReach n + perEpochReach n := by
    simp [cumulativeReach, Finset.sum_range_succ]
  rw [hstep]; linarith [perEpochReach_pos n]

/-! ## §6. The dyadic freeze rung: the horizon sits between `2^4` and `2^5` -/

/-- The horizon strictly exceeds the dyadic rung `2^4 = 16`: `16 < 8 φ²`, equivalently
`2 < φ²`, equivalently `1 < φ`. So a self-similar (dyadic) structure at scale `2^4 = 16` is
sub-horizon and is homogenized. -/
theorem two_pow_four_lt_horizon : (2 : ℝ) ^ 4 < recognitionEventHorizon := by
  have h16 : (2 : ℝ) ^ 4 = 16 := by norm_num
  rw [recognitionEventHorizon_eq, h16]
  linarith [one_lt_phi]

/-- The horizon is strictly below the dyadic rung `2^5 = 32`: `8 φ² < 32`, equivalently
`φ² < 4`, equivalently `φ < 3` (in fact `φ ≤ 5/3`). So a self-similar (dyadic) structure at
scale `2^5 = 32` is super-horizon and freezes at its primordial amplitude. -/
theorem horizon_lt_two_pow_five : recognitionEventHorizon < (2 : ℝ) ^ 5 := by
  have h32 : (2 : ℝ) ^ 5 = 32 := by norm_num
  rw [recognitionEventHorizon_eq, h32]
  nlinarith [phi_sq_eq, sq_nonneg (φ - 2)]

/-- **THEOREM.** The recognition event horizon `8 φ²` sits strictly between the dyadic rungs
`2^4 = 16` and `2^5 = 32`. So a self-similar (dyadic) structure freezes exactly at and above
the scale `2^5 = 32` and homogenizes at and below `2^4 = 16`: the freeze break is forced to
the fifth dyadic rung, with no fitted scale. This is the arithmetic anchor of the Phase-16
freeze-out scale selection (`scripts/cosmogenesis/foam_freeze_out.py`). -/
theorem recognitionEventHorizon_between_dyadic_rungs :
    (2 : ℝ) ^ 4 < recognitionEventHorizon ∧ recognitionEventHorizon < (2 : ℝ) ^ 5 :=
  ⟨two_pow_four_lt_horizon, horizon_lt_two_pow_five⟩

/-- The forced dyadic freeze rung: the least exponent `k` with `2^k` above the horizon. -/
def dyadicFreezeRung : ℕ := 5

/-- **THEOREM.** `dyadicFreezeRung = 5` is the least power-of-two rung strictly above the
recognition horizon: `2^5 > 8 φ²`, while every smaller rung `2^k` (`k < 5`) is strictly below
it. So the freeze-out selects exactly the dyadic scales at or above `2^5 = 32`. -/
theorem dyadicFreezeRung_is_least :
    recognitionEventHorizon < (2 : ℝ) ^ dyadicFreezeRung ∧
    ∀ k : ℕ, k < dyadicFreezeRung → (2 : ℝ) ^ k < recognitionEventHorizon := by
  refine ⟨horizon_lt_two_pow_five, ?_⟩
  intro k hk
  simp only [dyadicFreezeRung] at hk
  have hk4 : k ≤ 4 := by omega
  have hnat : (2 : ℕ) ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
  have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := by exact_mod_cast hnat
  exact lt_of_le_of_lt hmono two_pow_four_lt_horizon

/-! ## §7. One-statement master theorem -/

/-- **RECOGNITION EVENT HORIZON, ONE STATEMENT.** The forced φ-dilation (one
φ-rung per eight-tick epoch, T-6 and T-7) gives a finite de Sitter recognition
horizon equal to `8 φ² = 8 (φ + 1)`; the cumulative reach converges to it from
strictly below and increases monotonically, so any comoving separation at or
beyond `8 φ²` is never crossed. This is the law-derived freeze-out mechanism:
no tuned Hubble rate and no fitted coupling enter. -/
theorem recognition_event_horizon_one_statement :
    (∑' m : ℕ, perEpochReach m = recognitionEventHorizon) ∧
    recognitionEventHorizon = 8 * (φ + 1) ∧
    (∀ n : ℕ, cumulativeReach n < recognitionEventHorizon) ∧
    StrictMono cumulativeReach :=
  ⟨tsum_perEpochReach, recognitionEventHorizon_eq, cumulativeReach_lt_horizon,
    cumulativeReach_strictMono⟩

/-! ## §8. Real-space reachability dichotomy (Phase 17) -/

/-- **THEOREM.** The real-space freeze-out dichotomy. A comoving separation `r` is eventually
crossed by a recognition signal launched at the σ = 0 seed iff it lies strictly below the
horizon: for every `r < 8 φ²` there is a finite epoch whose cumulative reach exceeds `r` (so
structure at radius `r` is eventually homogenized), while for every `r ≥ 8 φ²` no finite epoch
ever reaches `r` (so structure at radius `r` freezes at its primordial amplitude). This is the
real-space form of the Phase-9 horizon and the law-derived statement behind the inner
homogenized ball / outer frozen foam split in
`scripts/cosmogenesis/foam_real_space_freeze_out.py`: the freeze surface is the comoving sphere
of radius `8 φ²`, which by §6 sits strictly between the dyadic shells `2^4 = 16` and
`2^5 = 32`. -/
theorem reach_dichotomy :
    (∀ r : ℝ, r < recognitionEventHorizon → ∃ n : ℕ, r < cumulativeReach n) ∧
    (∀ r : ℝ, recognitionEventHorizon ≤ r → ∀ n : ℕ, cumulativeReach n < r) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    have hsum : HasSum perEpochReach recognitionEventHorizon := by
      have h := perEpochReach_summable.hasSum
      rwa [tsum_perEpochReach] at h
    have hT : Filter.Tendsto cumulativeReach Filter.atTop (nhds recognitionEventHorizon) := by
      simpa [cumulativeReach] using hsum.tendsto_sum_nat
    have hev : ∀ᶠ n in Filter.atTop, r < cumulativeReach n :=
      hT.eventually (eventually_gt_nhds hr)
    exact hev.exists
  · intro r hr n
    exact lt_of_lt_of_le (cumulativeReach_lt_horizon n) hr

end RecognitionEventHorizon
end Cosmology
end IndisputableMonolith
