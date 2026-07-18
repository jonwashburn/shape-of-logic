import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.HingeStationarityCore
import IndisputableMonolith.Gravity.SevenGaps.RecognitionRatioBridge

/-!
# Seven Gaps: stationarity-to-bridge closure (the bridge inhabited by derivation)

## Status: THEOREM for every named statement in this file (0 sorry, 0 admit,
0 new axiom, no `native_decide`; `decide` is used only for `Fin 2` literal
disequalities, as in `RecognitionRatioBridge`). MODEL for the deficit-source
coupling inside `sourcedAction`, exactly as flagged in
`HingeStationarityCore`; that constitutive premise is inherited here and
named MODEL everywhere it appears.

This module closes the loop left OPEN by `RecognitionRatioBridge` (its
`derivation_from_stationarity_open` flag): it builds a CONSTRUCTOR,
`recognitionRatioBridge_ofStationarity`, that takes the constitutive
deficit-source action data (hinge-wise coupling and deficit, channel count,
mesh scale, and a structural source-domination bound) and PROVES the
`ratio_relation` field from the stationarity theorems of
`HingeStationarityCore`. The bridge structure is thereby INHABITED BY
DERIVATION: `xRatio` is DEFINED as the exponential of the total strain of
the unique global minimizer of the sourced action
(`sourcedMinimizer` / `sourced_unique_minimizer`), and the cubic remainder
clause is DERIVED from `sourced_ratio_cubic_error` (constant 1/6). No
hypothesis of the constructor is the ratio relation or anything equivalent
to it; the audit is in the constructor's docstring.

LOCKED promotion language (verbatim, per the campaign): the bridge is
"derived from an explicit deficit-source constitutive action plus
J-stationarity", never "from the bare RecognitionLedger". The J-cost
identification inside that phrase is the kernel equation
`sourcedAction_eq_jcost_sum`; the deficit-source coupling is the disclosed
constitutive MODEL premise, and the kernel-checked kill records of
`HingeStationarityCore` (`closedCycle_coboundary_sum_eq_zero`,
`budget_implies_ratio_without_stationarity`) prove the bare-ledger route
is dead/circular. Accordingly the status flag
`derivation_from_bare_ledger` below is `false` and STAYS false.

## Contents

* **T1** `stationaryRatio_cubic`: the sourced stationary log-ratio obeys the
  bridge-shaped cubic bound |log x* - c| <= (n/6) * h^3 whenever the total
  source strength c = kappa*delta is dominated by the mesh, |c| <= n*h. The
  h-dependence is explicit: the mesh enters ONLY through the domination
  hypothesis; the analysis is `sourced_ratio_cubic_error`, reused, not
  re-derived. (The curvature-scaled variant |delta(h)| <= C_K h^2, giving
  the sharper O(h^6)-content constant, is already
  `sourced_ratio_isAdmissible` in `HingeStationarityCore` and is consumed
  below, not restated.)
* **T2** the nontrivial admissible family. Panel deviation, recorded
  honestly: the panel's literal family delta_m = 1/(m+1),
  h_m = |kappa|/(n(m+1)) has delta LINEAR in h (kappa*delta/n = h up to
  sign), and the codebase's `RecognitionRatioFamily.IsAdmissible` predicate
  hard-codes the curvature conjunct |delta(h)| <= C_K h^2, which a linear
  family violates for every constant as h -> 0. That incompatibility is
  itself kernel-checked here (`linear_deficit_family_not_isAdmissible`, a
  kill record for the literal form). The correctly-typed analogue in this
  framework is the QUADRATIC-deficit family delta(h) = (n/kappa) h^2 (so
  kappa*delta/n = h^2), `quadraticSourceFamily`: it is genuinely nontrivial
  (`quadraticSourceFamily_deficit_ne_zero`,
  `quadraticSourceFamily_logRatio_pos`) and satisfies `IsAdmissible` with
  UNIFORM constants C_K = n/|kappa|, C_R = n*h0^3/6, constants outside h
  (`quadraticSourceFamily_isAdmissible`, via `sourced_ratio_isAdmissible`).
  So the derivation covers a genuine h -> 0 family, not a single point.
* **T3** `recognitionRatioBridge_ofStationarity`: the headline constructor.
  Hypotheses: channel count n >= 1, mesh scale h > 0, and the structural
  source-domination bound |kappa sigma * delta sigma| <= n*h at every
  hinge. NOT hypotheses: the ratio relation, the value of xRatio, or any
  bound on log xRatio. Fields: xRatio sigma := exp(n * arsinh(kappa sigma *
  delta sigma / n)) (the exponential of the minimizer's total strain,
  `ofStationarity_log_xRatio_eq_minimizer_strain` +
  `ofStationarity_minimizer_grounding`); remBound := n/6, the explicit
  constant inherited from the 1/6 of `sourced_ratio_cubic_error`;
  ratio_relation := proved, by `stationaryRatio_cubic`.
* **T4** non-vacuity: `concreteStationarityBridge`, the constructor
  instantiated at n = 4, kappa = 1, mesh h = 1/8 (the panel's h_m at m = 1)
  on two hinges with SIGNED deficits +1/16 and -1/16 (the quadratic-family
  magnitude (n/kappa) h^2 = 1/16 at that mesh, with the sign split of
  `ratioBridge_admits_negative_deficit`); every side condition is
  discharged by `norm_num`/`decide`. The instance has a strictly negative
  deficit at hinge 1 and correspondingly signed log ratios
  (`concreteStationarityBridge_nonvacuous`,
  `concreteStationarityBridge_logRatio_signed`), so nothing is vacuous.
* **T5** status flags: `constitutive_stationarity_bridge_closed := true`,
  grounded in the constructor plus the T2 family theorem;
  `derivation_from_bare_ledger := false`, which STAYS false (the coupling
  is the disclosed constitutive MODEL premise; the bare-ledger route is
  killed in `HingeStationarityCore`). NOTE: this module flips NO flag in
  `FullTheoryLedger`; whether and how the campaign ledger records this
  closure is the conductor's decision, not this module's.

## Honest tiers

* **THEOREM**: `stationaryRatio_cubic`, `stationaryLogRatio_total_strain`,
  `recognitionRatioBridge_ofStationarity` (the constructor itself: its
  `ratio_relation` field carries a kernel-checked proof term),
  `ofStationarity_xRatio_def`, `ofStationarity_log_xRatio`,
  `ofStationarity_log_xRatio_eq_minimizer_strain`,
  `ofStationarity_minimizer_grounding`, `ofStationarity_log_xRatio_pos`,
  `ofStationarity_log_xRatio_neg`, `linear_deficit_family_not_isAdmissible`,
  `quadraticSourceFamily_isAdmissible`,
  `quadraticSourceFamily_deficit_ne_zero`,
  `quadraticSourceFamily_logRatio_pos`,
  `quadraticSourceFamily_source_dominated`,
  `concreteStationarityBridge_nonvacuous`,
  `concreteStationarityBridge_logRatio_signed`.
* **MODEL**: the deficit-source coupling -(kappa*delta/n) * sum_i t_i inside
  `sourcedAction` (inherited from `HingeStationarityCore`). Every bridge
  produced by the constructor is therefore derived from an explicit
  deficit-source constitutive action plus J-stationarity, never from the
  bare RecognitionLedger.

## Remaining gap (recorded, not hidden)

The h -> 0 family content is carried by
`RecognitionRatioFamily.IsAdmissible` (uniform constants over (0, h0)),
closed here for the quadratic-deficit family. A mesh-INDEXED tower of
bridge STRUCTURES (one `RecognitionRatioBridge` per h with a shared
remainder constant, i.e. lane 2's full asymptotic object) is not built in
this file; the constructor applies at each fixed mesh and the family
theorem supplies the uniform constants, but the packaging of the tower is
left to lane 2.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

/-! ## §1. T1: the stationary log-ratio in bridge-shaped form -/

/-- **THEOREM.** The total strain of the unique sourced minimizer
(`sourcedMinimizer`, t_i = arsinh(c/n)) is n * arsinh(c/n): the quantity
whose exponential the constructor uses as xRatio. This is the kernel link
between "xRatio is defined from the minimizer" and the closed-form
expression the cubic bound is stated about. -/
theorem stationaryLogRatio_total_strain (n : ℕ) (c : ℝ) :
    ∑ i, sourcedMinimizer n c i = (n : ℝ) * Real.arsinh (c / n) := by
  simp only [sourcedMinimizer]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **THEOREM (T1, the bridge-shaped cubic bound).** If the total source
strength c = kappa*delta is dominated by the mesh, |c| <= n*h, then the
sourced stationary log-ratio log x* = n * arsinh(c/n) (the log of the
exponential of the minimizer's total strain) matches c up to the
bridge-shaped cubic remainder:

  |log x* - c| <= (n/6) * h^3.

The h-dependence is EXPLICIT: h enters only through the domination
hypothesis, and the constant n/6 is inherited from the 1/6 of
`sourced_ratio_cubic_error` via |c|^3/(6 n^2) <= (n h)^3/(6 n^2)
= (n/6) h^3. The analysis is reused from `HingeStationarityCore`, not
re-derived. (No 0 <= h hypothesis is taken: it is implied by the
domination hypothesis, since 0 <= |c| <= n*h and n >= 1.) -/
theorem stationaryRatio_cubic (n : ℕ) (hn : 1 ≤ n) (c h : ℝ)
    (hdom : |c| ≤ (n : ℝ) * h) :
    |Real.log (Real.exp ((n : ℝ) * Real.arsinh (c / n))) - c|
      ≤ (n : ℝ) / 6 * h ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  rw [Real.log_exp]
  have hcube : |c| ^ 3 ≤ ((n : ℝ) * h) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg c) hdom 3
  have hden : (0 : ℝ) ≤ (6 * (n : ℝ) ^ 2)⁻¹ := by positivity
  calc |(n : ℝ) * Real.arsinh (c / n) - c|
      ≤ |c| ^ 3 / (6 * (n : ℝ) ^ 2) := sourced_ratio_cubic_error n hn c
    _ ≤ ((n : ℝ) * h) ^ 3 / (6 * (n : ℝ) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hcube hden
    _ = (n : ℝ) / 6 * h ^ 3 := by
        field_simp

/-! ## §2. T3: the constructor (the bridge inhabited by derivation) -/

/-- **THEOREM-tier constructor (T3, the headline).** Builds a
`RecognitionRatioBridge` from the constitutive deficit-source action data,
PROVING the `ratio_relation` field from J-stationarity.

Hypothesis audit (every hypothesis is structural; NONE is the ratio
relation or equivalent to it):
* `hn : 1 ≤ n` — at least one recognition channel (positivity side
  condition of `sourced_ratio_cubic_error`).
* `hh : 0 < h` — positive mesh scale (the structure's own
  `meshScale_pos` field).
* `hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ n * h` — source domination: the
  total source strength at each hinge is bounded by the mesh budget n*h.
  This bounds the INPUT data (coupling times deficit); it says nothing
  about xRatio, log xRatio, or the remainder, so it cannot smuggle the
  conclusion.

Fields produced BY DERIVATION:
* `xRatio σ := exp(n * arsinh(kappa σ * geomDeficit σ / n))` — DEFINED as
  the exponential of the total strain of the unique global minimizer of
  the sourced action `sourcedAction n (kappa σ * geomDeficit σ)`
  (`sourcedMinimizer`; uniqueness and global minimality are
  `sourced_unique_minimizer`, re-exported for this bridge as
  `ofStationarity_minimizer_grounding`).
* `remBound := n / 6` — the explicit constant inherited from the 1/6 of
  `sourced_ratio_cubic_error`.
* `ratio_relation` — PROVED, by `stationaryRatio_cubic`; not passed in.

MODEL disclosure: the sourced action's coupling term is the explicit
deficit-source constitutive choice of `HingeStationarityCore`. Every
bridge this constructor produces is derived from an explicit
deficit-source constitutive action plus J-stationarity, never from the
bare RecognitionLedger. -/
noncomputable def recognitionRatioBridge_ofStationarity {H : Type*}
    (n : ℕ) (hn : 1 ≤ n) (kappa geomDeficit : H → ℝ) (h : ℝ) (hh : 0 < h)
    (hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ (n : ℝ) * h) :
    RecognitionRatioBridge H where
  xRatio := fun σ =>
    Real.exp ((n : ℝ) * Real.arsinh (kappa σ * geomDeficit σ / n))
  xRatio_pos := fun _ => Real.exp_pos _
  kappa := kappa
  geometricDeficit := geomDeficit
  meshScale := h
  meshScale_pos := hh
  remBound := (n : ℝ) / 6
  remBound_nonneg := by positivity
  ratio_relation := fun σ =>
    stationaryRatio_cubic n hn (kappa σ * geomDeficit σ) h (hdom σ)

/-- **THEOREM (definitional transparency of the constructor's ratio).**
xRatio is the exponential of n * arsinh(kappa*delta/n); recorded as an
equation so downstream proofs need not unfold the constructor. -/
theorem ofStationarity_xRatio_def {H : Type*}
    (n : ℕ) (hn : 1 ≤ n) (kappa geomDeficit : H → ℝ) (h : ℝ) (hh : 0 < h)
    (hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ (n : ℝ) * h) (σ : H) :
    (recognitionRatioBridge_ofStationarity n hn kappa geomDeficit h hh
        hdom).xRatio σ
      = Real.exp ((n : ℝ)
          * Real.arsinh (kappa σ * geomDeficit σ / n)) := rfl

/-- **THEOREM.** The log of the constructed ratio is exactly
n * arsinh(kappa*delta/n): the constructed bridge's log ratio is the
closed-form stationary value, with NO remainder at this level (the cubic
remainder lives between this value and kappa*delta). -/
theorem ofStationarity_log_xRatio {H : Type*}
    (n : ℕ) (hn : 1 ≤ n) (kappa geomDeficit : H → ℝ) (h : ℝ) (hh : 0 < h)
    (hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ (n : ℝ) * h) (σ : H) :
    Real.log ((recognitionRatioBridge_ofStationarity n hn kappa geomDeficit
        h hh hdom).xRatio σ)
      = (n : ℝ) * Real.arsinh (kappa σ * geomDeficit σ / n) := by
  rw [ofStationarity_xRatio_def, Real.log_exp]

/-- **THEOREM (the derivation receipt).** The log of the constructed ratio
IS the total strain of the sourced minimizer with source
c = kappa σ * delta σ: this is the sense in which xRatio is defined FROM
the stationary point of the constitutive action, not posited. -/
theorem ofStationarity_log_xRatio_eq_minimizer_strain {H : Type*}
    (n : ℕ) (hn : 1 ≤ n) (kappa geomDeficit : H → ℝ) (h : ℝ) (hh : 0 < h)
    (hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ (n : ℝ) * h) (σ : H) :
    Real.log ((recognitionRatioBridge_ofStationarity n hn kappa geomDeficit
        h hh hdom).xRatio σ)
      = ∑ i, sourcedMinimizer n (kappa σ * geomDeficit σ) i := by
  rw [ofStationarity_log_xRatio n hn kappa geomDeficit h hh hdom σ]
  exact (stationaryLogRatio_total_strain n (kappa σ * geomDeficit σ)).symm

/-- **THEOREM (stationarity grounding, re-export of
`sourced_unique_minimizer` for the constructed bridge).** The
configuration whose total strain the constructed bridge exponentiates is
the GLOBAL minimizer of the sourced action at each hinge, and it is the
UNIQUE minimizer. So the bridge's ratio field is pinned by J-stationarity
of the constitutive action: no other configuration could have produced
it. -/
theorem ofStationarity_minimizer_grounding {H : Type*}
    (n : ℕ) (kappa geomDeficit : H → ℝ) (σ : H) (t : Fin n → ℝ) :
    sourcedAction n (kappa σ * geomDeficit σ)
        (sourcedMinimizer n (kappa σ * geomDeficit σ))
      ≤ sourcedAction n (kappa σ * geomDeficit σ) t ∧
      (sourcedAction n (kappa σ * geomDeficit σ) t
          = sourcedAction n (kappa σ * geomDeficit σ)
              (sourcedMinimizer n (kappa σ * geomDeficit σ)) →
        t = sourcedMinimizer n (kappa σ * geomDeficit σ)) :=
  sourced_unique_minimizer n (kappa σ * geomDeficit σ) t

/-- **THEOREM (signed ratio, positive branch).** Where the source
kappa σ * delta σ is positive, the constructed bridge's log ratio is
strictly positive: the derivation transports the SIGN of the deficit into
log x, exactly the signed information the ledger-deficit no-gos cannot
carry (`ratioBridge_separates_deficit_observables`). -/
theorem ofStationarity_log_xRatio_pos {H : Type*}
    (n : ℕ) (hn : 1 ≤ n) (kappa geomDeficit : H → ℝ) (h : ℝ) (hh : 0 < h)
    (hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ (n : ℝ) * h) (σ : H)
    (hpos : 0 < kappa σ * geomDeficit σ) :
    0 < Real.log ((recognitionRatioBridge_ofStationarity n hn kappa
        geomDeficit h hh hdom).xRatio σ) := by
  rw [ofStationarity_log_xRatio n hn kappa geomDeficit h hh hdom σ]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos hn0 (Real.arsinh_pos_iff.mpr (div_pos hpos hn0))

/-- **THEOREM (signed ratio, negative branch).** Where the source is
negative, the constructed log ratio is strictly negative. -/
theorem ofStationarity_log_xRatio_neg {H : Type*}
    (n : ℕ) (hn : 1 ≤ n) (kappa geomDeficit : H → ℝ) (h : ℝ) (hh : 0 < h)
    (hdom : ∀ σ, |kappa σ * geomDeficit σ| ≤ (n : ℝ) * h) (σ : H)
    (hneg : kappa σ * geomDeficit σ < 0) :
    Real.log ((recognitionRatioBridge_ofStationarity n hn kappa geomDeficit
        h hh hdom).xRatio σ) < 0 := by
  rw [ofStationarity_log_xRatio n hn kappa geomDeficit h hh hdom σ]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_neg_of_pos_of_neg hn0
    (Real.arsinh_neg_iff.mpr (div_neg_of_neg_of_pos hneg hn0))

/-! ## §3. T2: the nontrivial uniform small-h family

Panel deviation, kernel-checked: the panel's literal family
delta_m = 1/(m+1), h_m = |kappa|/(n(m+1)) has delta LINEAR in the mesh
(kappa*delta/n = h up to sign). The codebase's admissibility predicate
`RecognitionRatioFamily.IsAdmissible` hard-codes the curvature conjunct
|delta(h)| <= C_K h^2, which a linear-deficit family violates for EVERY
choice of constants once h is small enough. §3 first records that
incompatibility as a kill record, then closes T2 with the correctly-typed
analogue: the quadratic-deficit family delta(h) = (n/kappa) h^2, whose
source satisfies kappa*delta(h)/n = h^2. -/

/-- **THEOREM (kill record for the panel's literal linear family).** For
every n >= 1, kappa ≠ 0, h0 > 0 and EVERY pair of constants (C_K, C_R),
the linear-deficit sourced family delta(h) = (n/kappa) * h (the
mesh-indexed form of the panel's delta_m = 1/(m+1), h_m = |kappa|/(n(m+1)),
which has kappa*delta/n = h) is NOT admissible: the curvature conjunct
|delta(h)| <= C_K h^2 of `RecognitionRatioFamily.IsAdmissible` fails at
small h because a linear deficit cannot be dominated by h^2 uniformly.
This is why T2 is closed with the quadratic-deficit family below; the
deviation from the panel's literal spec is forced by the predicate's
curvature conjunct, and this theorem is the receipt. -/
theorem linear_deficit_family_not_isAdmissible (n : ℕ) (hn : 1 ≤ n)
    (h₀ kappa C_K C_R : ℝ) (hh₀ : 0 < h₀) (hκ : kappa ≠ 0) :
    ¬ (sourcedRatioFamily n kappa
        (fun h => (n : ℝ) / kappa * h)).IsAdmissible h₀ kappa C_K C_R := by
  intro hadm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < |kappa| := abs_pos.mpr hκ
  set M := max C_K 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hden : 0 < |kappa| * (M + 1) := by positivity
  set h := min (h₀ / 2) ((n : ℝ) / (|kappa| * (M + 1))) with hdef
  have hhpos : 0 < h := lt_min (by linarith) (div_pos hn0 hden)
  have hhlt : h < h₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨hcurv, _⟩ := hadm h ⟨hhpos, hhlt⟩
  have hcurv' : (n : ℝ) / |kappa| * h ≤ C_K * h ^ 2 := by
    have hc : |(n : ℝ) / kappa * h| ≤ C_K * h ^ 2 := hcurv
    rw [abs_mul, abs_div, abs_of_pos hn0, abs_of_pos hhpos] at hc
    exact hc
  have hCM : C_K * h ^ 2 ≤ M * h ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg h)
  have e1 : (n : ℝ) * h ≤ |kappa| * M * h ^ 2 := by
    calc (n : ℝ) * h = |kappa| * ((n : ℝ) / |kappa| * h) := by
          field_simp
      _ ≤ |kappa| * (M * h ^ 2) :=
          mul_le_mul_of_nonneg_left (le_trans hcurv' hCM) hk.le
      _ = |kappa| * M * h ^ 2 := by ring
  have e2 : h * (|kappa| * (M + 1)) ≤ (n : ℝ) := by
    have hmin : h ≤ (n : ℝ) / (|kappa| * (M + 1)) := by
      rw [hdef]
      exact min_le_right _ _
    exact (le_div_iff₀ hden).mp hmin
  have e3 : h * (|kappa| * (M + 1)) * (M * h) ≤ (n : ℝ) * (M * h) :=
    mul_le_mul_of_nonneg_right e2 (mul_nonneg hM0 hhpos.le)
  have e4 : (n : ℝ) * h * (M + 1) ≤ |kappa| * M * h ^ 2 * (M + 1) :=
    mul_le_mul_of_nonneg_right e1 (by linarith)
  have hnh : 0 < (n : ℝ) * h := mul_pos hn0 hhpos
  nlinarith [e3, e4, hnh]

/-- The quadratic-deficit sourced family (the correctly-typed T2 witness):
delta(h) = (n/kappa) * h^2, so the per-channel source is
kappa * delta(h) / n = h^2 and the ratio is the sourced stationary value
x(h) = exp(n * arsinh(h^2)). Nontrivial for kappa ≠ 0, h ≠ 0
(`quadraticSourceFamily_deficit_ne_zero`,
`quadraticSourceFamily_logRatio_pos`). -/
noncomputable def quadraticSourceFamily (n : ℕ) (kappa : ℝ) :
    RecognitionRatioFamily :=
  sourcedRatioFamily n kappa (fun h => (n : ℝ) / kappa * h ^ 2)

/-- **THEOREM (T2, uniform admissibility of the quadratic family).** For
kappa ≠ 0 the quadratic-deficit family is admissible on (0, h0) with the
UNIFORM constants C_K = n/|kappa| and C_R = n * h0^3 / 6: both constants
sit OUTSIDE the mesh scale, per the admissibility predicate, so the
derivation covers a genuine h -> 0 family, not a single point. Proof:
`sourced_ratio_isAdmissible` (reused, not re-derived) with the curvature
bound an exact equality |delta(h)| = (n/|kappa|) h^2, followed by the
constant simplification |kappa|^3 (n/|kappa|)^3 h0^3/(6 n^2)
= n h0^3/6. (As in `sourced_ratio_isAdmissible`: for h0 <= 0 the predicate
is vacuously true; the statement carries content exactly when 0 < h0.) -/
theorem quadraticSourceFamily_isAdmissible (n : ℕ) (hn : 1 ≤ n)
    (h₀ kappa : ℝ) (hκ : kappa ≠ 0) :
    (quadraticSourceFamily n kappa).IsAdmissible h₀ kappa
      ((n : ℝ) / |kappa|) ((n : ℝ) * h₀ ^ 3 / 6) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hκ' : |kappa| ≠ 0 := abs_ne_zero.mpr hκ
  have hδ : ∀ h ∈ Set.Ioo (0 : ℝ) h₀,
      |(n : ℝ) / kappa * h ^ 2| ≤ (n : ℝ) / |kappa| * h ^ 2 := by
    intro h _
    rw [abs_mul, abs_div, abs_of_pos hn0, abs_of_nonneg (sq_nonneg h)]
  have hbase := sourced_ratio_isAdmissible n hn h₀ kappa
    ((n : ℝ) / |kappa|) (fun h => (n : ℝ) / kappa * h ^ 2) hδ
  have hconst : |kappa| ^ 3 * ((n : ℝ) / |kappa|) ^ 3 * h₀ ^ 3
      / (6 * (n : ℝ) ^ 2) = (n : ℝ) * h₀ ^ 3 / 6 := by
    field_simp
  rw [← hconst]
  exact hbase

/-- **THEOREM (nontriviality of the family: nonzero deficit).** For
kappa ≠ 0 and every nonzero mesh h, the quadratic family's deficit is
nonzero: the admissibility above is about a genuinely sourced family, not
the trivial delta = 0 one. -/
theorem quadraticSourceFamily_deficit_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (kappa h : ℝ) (hκ : kappa ≠ 0) (hh : h ≠ 0) :
    (quadraticSourceFamily n kappa).deficit h ≠ 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show (n : ℝ) / kappa * h ^ 2 ≠ 0
  exact mul_ne_zero (div_ne_zero (ne_of_gt hn0) hκ) (pow_ne_zero 2 hh)

/-- **THEOREM (nontriviality of the family: nonzero log ratio).** For
kappa ≠ 0 and every nonzero mesh h, the family's stationary log ratio
log x(h) = n * arsinh(h^2) is strictly positive: the bridge relation the
admissibility certifies is a relation between genuinely nonzero
quantities. -/
theorem quadraticSourceFamily_logRatio_pos (n : ℕ) (hn : 1 ≤ n)
    (kappa h : ℝ) (hκ : kappa ≠ 0) (hh : h ≠ 0) :
    0 < Real.log ((quadraticSourceFamily n kappa).ratio h) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  show 0 < Real.log (Real.exp
    ((n : ℝ) * Real.arsinh (kappa * ((n : ℝ) / kappa * h ^ 2) / n)))
  rw [Real.log_exp]
  have harg : kappa * ((n : ℝ) / kappa * h ^ 2) / n = h ^ 2 := by
    field_simp
  rw [harg]
  have hh2 : 0 < h ^ 2 :=
    lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh))
  exact mul_pos hn0 (Real.arsinh_pos_iff.mpr hh2)

/-- **THEOREM (family members feed the constructor).** For every mesh
0 < h <= 1 the quadratic family's source obeys the constructor's
domination side condition |kappa * delta(h)| <= n*h (since
|kappa * delta(h)| = n h^2 <= n h). So each family member is directly a
`recognitionRatioBridge_ofStationarity` input: the uniform-family
admissibility (T2) and the bridge-by-derivation construction (T3) cover
the same objects. -/
theorem quadraticSourceFamily_source_dominated (n : ℕ) (hn : 1 ≤ n)
    (kappa h : ℝ) (hκ : kappa ≠ 0) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    |kappa * (quadraticSourceFamily n kappa).deficit h| ≤ (n : ℝ) * h := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show |kappa * ((n : ℝ) / kappa * h ^ 2)| ≤ (n : ℝ) * h
  have heq : kappa * ((n : ℝ) / kappa * h ^ 2) = (n : ℝ) * h ^ 2 := by
    field_simp
  rw [heq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * h ^ 2)]
  have hsq : h ^ 2 ≤ h := by nlinarith [hh0, hh1]
  exact mul_le_mul_of_nonneg_left hsq hn0.le

/-! ## §4. T4: the concrete non-vacuity instance

The constructor instantiated at fully concrete data: n = 4 channels,
kappa = 1, mesh h = 1/8 (the panel's h_m = |kappa|/(n(m+1)) at m = 1), on
two hinges carrying SIGNED deficits +1/16 and -1/16. The magnitude 1/16 is
the quadratic family's deficit (n/kappa) h^2 = 4 * (1/8)^2 at that mesh;
the sign split is the two-hinge pattern of
`ratioBridge_admits_negative_deficit`, so the instance exhibits exactly
the signed-deficit non-vacuity the bridge modules expect. All side
conditions are discharged by `norm_num` (plus `decide` for the Fin 2
literal disequality). -/

/-- **THEOREM (concrete source domination).** |1 * (±1/16)| = 1/16
<= 4 * (1/8) = 1/2: the constructor's only substantive side condition,
checked by `norm_num` at the concrete data. -/
theorem concreteBridge_hdom : ∀ σ : Fin 2,
    |(1 : ℝ) * (if σ = 0 then (1 : ℝ) / 16 else -(1 / 16))|
      ≤ ((4 : ℕ) : ℝ) * (1 / 8) := by
  intro σ
  by_cases hσ : σ = 0
  · rw [if_pos hσ, one_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    norm_num
  · rw [if_neg hσ, one_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    norm_num

/-- **The concrete bridge instance (T4).** The constructor at n = 4,
kappa = 1, h = 1/8, deficits +1/16 and -1/16 on two hinges: an actual
`RecognitionRatioBridge (Fin 2)` inhabited BY DERIVATION, with every
hypothesis discharged numerically. Its ratio_relation field is the proof
produced by `stationaryRatio_cubic`; nothing was assumed. -/
noncomputable def concreteStationarityBridge : RecognitionRatioBridge (Fin 2) :=
  recognitionRatioBridge_ofStationarity 4 (by norm_num)
    (fun _ => 1) (fun σ => if σ = 0 then (1 : ℝ) / 16 else -(1 / 16))
    (1 / 8) (by norm_num) concreteBridge_hdom

/-- **THEOREM (T4 non-vacuity record).** The concrete instance has: the
prescribed signed deficits (+1/16 at hinge 0, -1/16 at hinge 1), a
STRICTLY NEGATIVE deficit at hinge 1 (the signed-deficit non-vacuity of
`ratioBridge_admits_negative_deficit`), mesh 1/8, unit coupling, and the
derived remainder constant remBound = 4/6 = 2/3 inherited from the cubic
error lemma. (Uses `decide` only for the Fin 2 literal disequality
1 ≠ 0, as in `RecognitionRatioBridge`.) -/
theorem concreteStationarityBridge_nonvacuous :
    concreteStationarityBridge.geometricDeficit 0 = 1 / 16 ∧
    concreteStationarityBridge.geometricDeficit 1 = -(1 / 16) ∧
    concreteStationarityBridge.geometricDeficit 1 < 0 ∧
    concreteStationarityBridge.meshScale = 1 / 8 ∧
    concreteStationarityBridge.remBound = 2 / 3 ∧
    (∀ σ, concreteStationarityBridge.kappa σ = 1) := by
  have h0 : concreteStationarityBridge.geometricDeficit 0 = 1 / 16 := by
    show (if (0 : Fin 2) = 0 then (1 : ℝ) / 16 else -(1 / 16)) = 1 / 16
    rw [if_pos rfl]
  have h1 : concreteStationarityBridge.geometricDeficit 1 = -(1 / 16) := by
    show (if (1 : Fin 2) = 0 then (1 : ℝ) / 16 else -(1 / 16)) = -(1 / 16)
    have h10 : ¬((1 : Fin 2) = 0) := by decide
    rw [if_neg h10]
  refine ⟨h0, h1, ?_, rfl, ?_, fun _ => rfl⟩
  · rw [h1]
    norm_num
  · show ((4 : ℕ) : ℝ) / 6 = 2 / 3
    norm_num

/-- **THEOREM (T4, signed log ratios).** The concrete instance's log
ratios carry the deficit signs: log x_0 > 0 (source +1/16) and
log x_1 < 0 (source -1/16). The derived bridge genuinely stores signed
information in log x, which the ledger-deficit observables cannot carry
(`ratioBridge_separates_deficit_observables`); at concrete numbers this
non-vacuity is fully discharged. -/
theorem concreteStationarityBridge_logRatio_signed :
    0 < Real.log (concreteStationarityBridge.xRatio 0) ∧
      Real.log (concreteStationarityBridge.xRatio 1) < 0 := by
  constructor
  · refine ofStationarity_log_xRatio_pos 4 (by norm_num) (fun _ => 1)
      (fun σ => if σ = 0 then (1 : ℝ) / 16 else -(1 / 16)) (1 / 8)
      (by norm_num) concreteBridge_hdom 0 ?_
    show (0 : ℝ) < 1 * (if (0 : Fin 2) = 0 then (1 : ℝ) / 16 else -(1 / 16))
    rw [if_pos rfl]
    norm_num
  · refine ofStationarity_log_xRatio_neg 4 (by norm_num) (fun _ => 1)
      (fun σ => if σ = 0 then (1 : ℝ) / 16 else -(1 / 16)) (1 / 8)
      (by norm_num) concreteBridge_hdom 1 ?_
    show (1 : ℝ) * (if (1 : Fin 2) = 0 then (1 : ℝ) / 16 else -(1 / 16)) < 0
    have h10 : ¬((1 : Fin 2) = 0) := by decide
    rw [if_neg h10]
    norm_num

/-! ## §5. T5: status flags (documentation, not mathematics)

NOTE for the conductor: this module flips NO flag in `FullTheoryLedger`;
whether and how the campaign ledger records this closure is the
conductor's decision. -/

/-- Status flags for the stationarity-to-bridge closure (documentation
record; the mathematics lives in the theorems above, not in these
booleans).

* `constitutive_stationarity_bridge_closed = true` is grounded in the
  constructor `recognitionRatioBridge_ofStationarity` (which PROVES
  `ratio_relation` from `stationaryRatio_cubic`, taking only structural
  side conditions) together with the uniform-family theorem
  `quadraticSourceFamily_isAdmissible` and the concrete instance
  `concreteStationarityBridge`. The bridge is derived from an explicit
  deficit-source constitutive action plus J-stationarity, never from the
  bare RecognitionLedger.
* `derivation_from_bare_ledger = false` STAYS false: the deficit-source
  coupling inside `sourcedAction` is the disclosed constitutive MODEL
  premise, and the kernel-checked kill records in `HingeStationarityCore`
  (`closedCycle_coboundary_sum_eq_zero`,
  `budget_implies_ratio_without_stationarity`) prove the bare-ledger
  route is circular/dead. -/
structure StationarityBridgeClosureStatus where
  /-- THEOREM tier (this module): the ratio relation is derived from the
  constitutive action plus J-stationarity via the constructor. -/
  constitutive_stationarity_bridge_closed : Bool
  /-- Permanently false: the coupling is a MODEL premise; the bare-ledger
  route is killed in `HingeStationarityCore`. -/
  derivation_from_bare_ledger : Bool

/-- The canonical status record (documentation, not new mathematics). -/
def stationarityBridgeClosureStatus : StationarityBridgeClosureStatus where
  constitutive_stationarity_bridge_closed := true
  derivation_from_bare_ledger := false

/-- Status flags record (rfl-forced; documentation, not new
mathematics). -/
theorem stationarityBridgeClosureStatus_flags :
    stationarityBridgeClosureStatus.constitutive_stationarity_bridge_closed
        = true ∧
      stationarityBridgeClosureStatus.derivation_from_bare_ledger = false :=
  ⟨rfl, rfl⟩

end SevenGaps
end Gravity
end IndisputableMonolith
