import IndisputableMonolith.Gravity.SevenGaps.Gap5MomentumAdditivity
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket

/-!
# Momentum-magnitude bridge: exact reduction, named residual, open discharge lead

**Verdict, stated first.** The global kinetic condition `p z ^ 2 = imbalance z ^ 2`
for all `z : LedgerState` is **not** derived from substrate structure, and this
module does not close that gap. What is derived: on the open positive quadrant
the kinetic condition is *exactly equivalent* to a single named physical premise,

    `EnergyEqualsCost p` :=
      `∀ k t, 0 < k → p (orbitPoint k t) ^ 2 = 2 * k * Cost.Jlog t`

(the equivalence, not just the forward direction, is
`open_positive_kinetic_iff_energy_equals_cost`), and the premise plus continuity
yields the kinetic condition on the closed positive quadrant. The global
statement remains strictly larger: the orbit route cannot see Q2–Q4, and
`SwapOdd` maps the positive quadrant to itself, so it does not open them either.

**The residual premise is independent of the rest of the momentum package**:
`imbalance` satisfies it (`energy_equals_cost_of_imbalance`, the chart theorem
rearranged), while `2 * imbalance` is continuous, swap-odd, additive, and
balance-vanishing yet fails it (`two_imbalance_fails_energy_equals_cost`). So
`EnergyEqualsCost` is consistent, and it is not implied by the B1 package.

**The Hamiltonian discharge lead is open, not refuted.** The *named* candidates
the library offers fail: `HamDyn` on `PhaseSpace 2` has a nonzero gradient
sector at zero momenta (`hamDyn_gradient_sector_nonzero_at_zero_momenta`), and
`Jlog` is not the quadratic form `t ↦ t ^ 2 / 2` (`Jlog_ne_half_sq`). Matching
the HKT exact-cost quadratic `2 (lam * p) ^ 2` to orbit exactness is scalar
algebra that recovers the chart product `lam * p`
(`exact_cost_profile_recovers_chart_product`); it neither constructs nor
discharges the ledger-level premise. No carrier map between these
`PhaseSpace 2` objects and `LedgerState` observables is stated anywhere in the
library, so these failures say nothing about an arbitrary Hamiltonian on an
arbitrary carrier: a derivation of `EnergyEqualsCost` from the posting
dynamics' action principle remains the open frontier.

## What is derived

1. **L1 (orbit coverage).** Every state with `0 < z.1` and `0 < z.2` equals
   `orbitPoint (casimir z) (Real.log (z.1 / z.2))`.
2. **The exact reduction.** `EnergyEqualsCost p ↔ KineticOnOpenPositiveQuadrant p`.
3. **L3 (boundary extension).** With `Continuous p`, kinetic extends to the
   closed positive quadrant.
4. **Composition.** Residual premise + continuity ⇒ closed-positive kinetic.
5. **Balance on the positive diagonal** follows from the residual at `t = 0`.

## Scope

Chart carrier `LedgerState` only. No flag flip. No claim that B1 is
unconditional. No claim that the Hamiltonian lead is closed.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MomentumMagnitudeBridge

open ChartFromLedgerMomentum MomentumAdditivity
open DynamicStructureBracket HypersurfaceDeformation

private lemma sum_zmod2 (g : ZMod 2 → ℝ) : (∑ j : ZMod 2, g j) = g 0 + g 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]

noncomputable section

/-! ## §0. The residual premise, named -/

/-- **Per-orbit energy-equals-cost.** Residual physical premise of the
momentum-magnitude bridge. -/
def EnergyEqualsCost (p : LedgerState → ℝ) : Prop :=
  ∀ k t : ℝ, 0 < k → p (orbitPoint k t) ^ 2 = 2 * k * Cost.Jlog t

def KineticOnOpenPositiveQuadrant (p : LedgerState → ℝ) : Prop :=
  ∀ z : LedgerState, 0 < z.1 → 0 < z.2 → p z ^ 2 = imbalance z ^ 2

def KineticOnClosedPositiveQuadrant (p : LedgerState → ℝ) : Prop :=
  ∀ z : LedgerState, 0 ≤ z.1 → 0 ≤ z.2 → p z ^ 2 = imbalance z ^ 2

/-! ## §1. L1: orbit coverage -/

private theorem exp_log_div_two {a : ℝ} (ha : 0 < a) :
    Real.exp (Real.log a / 2) = Real.sqrt a := by
  have hmul : Real.exp (Real.log a / 2) * Real.exp (Real.log a / 2) = a := by
    rw [← Real.exp_add, show Real.log a / 2 + Real.log a / 2 = Real.log a from by ring,
      Real.exp_log ha]
  have hsq : (Real.exp (Real.log a / 2)) ^ 2 = (Real.sqrt a) ^ 2 := by
    rw [pow_two, hmul, pow_two, Real.mul_self_sqrt ha.le]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right (by
    intro hneg
    linarith [Real.exp_pos (Real.log a / 2), Real.sqrt_nonneg a])

private theorem sqrt_mul_sqrt_div {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    Real.sqrt (d * c) * Real.sqrt (d / c) = d := by
  have hprod : 0 ≤ d * c := (mul_pos hd hc).le
  have hquot : 0 < d / c := div_pos hd hc
  have hsq : (Real.sqrt (d * c) * Real.sqrt (d / c)) ^ 2 = d ^ 2 := by
    calc (Real.sqrt (d * c) * Real.sqrt (d / c)) ^ 2
        = (Real.sqrt (d * c)) ^ 2 * (Real.sqrt (d / c)) ^ 2 := by ring
      _ = (d * c) * (d / c) := by rw [Real.sq_sqrt hprod, Real.sq_sqrt hquot.le]
      _ = d ^ 2 := by field_simp
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right (by
    intro hneg
    have hpos : 0 < Real.sqrt (d * c) * Real.sqrt (d / c) :=
      mul_pos (Real.sqrt_pos.mpr (mul_pos hd hc)) (Real.sqrt_pos.mpr hquot)
    linarith)

private theorem exp_neg_log_div_two {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    Real.exp (-(Real.log (d / c) / 2)) = Real.sqrt (c / d) := by
  have hqi : 0 < c / d := div_pos hc hd
  have hlog : -(Real.log (d / c)) = Real.log (c / d) := by
    rw [← Real.log_inv, inv_div]
  have hform : -(Real.log (d / c) / 2) = (-Real.log (d / c)) / 2 := by ring
  rw [hform, hlog]
  exact exp_log_div_two hqi

private theorem orbit_fst (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    Real.sqrt (d * c) * Real.exp (Real.log (d / c) / 2) = d := by
  rw [exp_log_div_two (div_pos hd hc), sqrt_mul_sqrt_div hd hc]

private theorem orbit_snd (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    Real.sqrt (d * c) * Real.exp (-(Real.log (d / c)) / 2) = c := by
  have hform : -(Real.log (d / c)) / 2 = -(Real.log (d / c) / 2) := by ring
  rw [hform, exp_neg_log_div_two hd hc]
  have h := sqrt_mul_sqrt_div hc hd
  rwa [mul_comm c d] at h

/-- **L1.** Every open-positive-quadrant state lies on its Casimir orbit. -/
theorem orbit_coverage (z : LedgerState) (hd : 0 < z.1) (hc : 0 < z.2) :
    z = orbitPoint (casimir z) (Real.log (z.1 / z.2)) := by
  apply Prod.ext
  · -- fst
    have h := orbit_fst z.1 z.2 hd hc
    simpa [orbitPoint, casimir] using h.symm
  · -- snd: align `orbitPoint`'s `exp (-t/2)` spelling
    have h := orbit_snd z.1 z.2 hd hc
    have hform : (-(Real.log (z.1 / z.2)) / 2) = -(Real.log (z.1 / z.2) / 2) := by
      ring
    simpa [orbitPoint, casimir, hform] using h.symm

/-! ## §2. L2: per-orbit reduction -/

/-- **L2.** Under `EnergyEqualsCost`, kinetic holds on the open positive quadrant. -/
theorem energy_equals_cost_implies_kinetic_on_open_positive
    {p : LedgerState → ℝ} (hE : EnergyEqualsCost p) :
    KineticOnOpenPositiveQuadrant p := by
  intro z hd hc
  have hz := orbit_coverage z hd hc
  have hk : 0 < casimir z := mul_pos hd hc
  have hke := hE (casimir z) (Real.log (z.1 / z.2)) hk
  have hkin := kinetic_on_orbit (casimir z) (Real.log (z.1 / z.2)) hk hke
  rw [hz]; exact hkin

theorem balance_vanishing_on_positive_diagonal_of_energy_equals_cost
    {p : LedgerState → ℝ} (hE : EnergyEqualsCost p) (k : ℝ) (hk : 0 < k) :
    p (orbitPoint k 0) = 0 := by
  have hke := hE k 0 hk
  have hJ : Cost.Jlog 0 = 0 := by
    rw [Cost.Jlog_as_cosh, Real.cosh_zero]; norm_num
  rw [hJ, mul_zero] at hke
  exact sq_eq_zero_iff.mp hke

/-! ## §3. L3: continuous extension -/

theorem continuous_imbalance : Continuous (imbalance : LedgerState → ℝ) :=
  continuous_fst.sub continuous_snd

/-- **L3.** Continuity extends open-positive kinetic to the closed positive quadrant. -/
theorem kinetic_extends_to_closed_positive_quadrant
    {p : LedgerState → ℝ} (hcont : Continuous p)
    (hopen : KineticOnOpenPositiveQuadrant p) :
    KineticOnClosedPositiveQuadrant p := by
  intro z hd hc
  by_cases hstrict : 0 < z.1 ∧ 0 < z.2
  · exact hopen z hstrict.1 hstrict.2
  · let w : ℕ → LedgerState := fun n =>
      (z.1 + 1 / (n + 1 : ℝ), z.2 + 1 / (n + 1 : ℝ))
    have hw_open : ∀ n, 0 < (w n).1 ∧ 0 < (w n).2 := by
      intro n
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      exact ⟨by linarith [hd, hpos], by linarith [hc, hpos]⟩
    have hkin_w : ∀ n, p (w n) ^ 2 = imbalance (w n) ^ 2 := fun n =>
      hopen (w n) (hw_open n).1 (hw_open n).2
    have hw_tendsto : Filter.Tendsto w Filter.atTop (nhds z) := by
      have h1 : Filter.Tendsto (fun n : ℕ => z.1 + 1 / (n + 1 : ℝ)) Filter.atTop
          (nhds z.1) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add z.1 using 1
        simp
      have h2 : Filter.Tendsto (fun n : ℕ => z.2 + 1 / (n + 1 : ℝ)) Filter.atTop
          (nhds z.2) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add z.2 using 1
        simp
      exact h1.prodMk_nhds h2
    have hp_lim := (hcont.tendsto _).comp hw_tendsto
    have hi_lim := (continuous_imbalance.tendsto _).comp hw_tendsto
    have hpsq := (continuous_pow 2).continuousAt.tendsto.comp hp_lim
    have hisq := (continuous_pow 2).continuousAt.tendsto.comp hi_lim
    exact tendsto_nhds_unique hpsq (hisq.congr fun n => (hkin_w n).symm)

theorem energy_equals_cost_continuous_implies_kinetic_on_closed
    {p : LedgerState → ℝ} (hE : EnergyEqualsCost p) (hcont : Continuous p) :
    KineticOnClosedPositiveQuadrant p :=
  kinetic_extends_to_closed_positive_quadrant hcont
    (energy_equals_cost_implies_kinetic_on_open_positive hE)

/-! ## §4. SwapOdd / quadrant coverage -/

theorem swap_odd_preserves_kinetic_pointwise {p : LedgerState → ℝ}
    (hswap : SwapOdd p) (z : LedgerState)
    (hkin : p z ^ 2 = imbalance z ^ 2) :
    p (z.2, z.1) ^ 2 = imbalance (z.2, z.1) ^ 2 := by
  rw [hswap z, imbalance_swap z, neg_sq, neg_sq, hkin]

theorem swap_maps_open_positive_to_itself {z : LedgerState}
    (hd : 0 < z.1) (hc : 0 < z.2) :
    0 < (z.2, z.1).1 ∧ 0 < (z.2, z.1).2 :=
  ⟨hc, hd⟩

theorem orbitPoint_nonneg (k t : ℝ) (_hk : 0 ≤ k) :
    0 ≤ (orbitPoint k t).1 ∧ 0 ≤ (orbitPoint k t).2 := by
  simp only [orbitPoint]
  exact ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _),
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)⟩

theorem negative_quadrant_not_on_orbit (z : LedgerState)
    (hd : z.1 < 0) (_hc : z.2 < 0) (k t : ℝ) (hk : 0 ≤ k) :
    orbitPoint k t ≠ z := by
  intro heq
  have hnn := (orbitPoint_nonneg k t hk).1
  have h1 : (orbitPoint k t).1 = z.1 := congrArg Prod.fst heq
  linarith

/-! ## §5. Named candidate failures -/

/-- Gradient-only decoy: zero momenta, configurations `(0,1)`, lapse `N ≡ 2`. -/
theorem hamDyn_decoy_value :
    HamDyn (fun _ : ZMod 2 => (2 : ℝ))
        (fun j : ZMod 2 => if j = (0 : ZMod 2) then (0 : ℝ) else 1,
          fun _ : ZMod 2 => (0 : ℝ)) = 3 := by
  simp only [HamDyn]
  have h01 : (0 : ZMod 2) + 1 = 1 := by decide
  have h10 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [sum_zmod2]
  simp [h01, h10]
  norm_num

/-- **The named candidate `HamDyn` has a gradient sector at zero momenta.**
This is a fact about `HamDyn` on `PhaseSpace 2` only: no carrier map from
`PhaseSpace 2` objects to `LedgerState` observables is stated anywhere in the
library, so this theorem neither refutes nor discharges
`EnergyEqualsCost`, and no "is a `Jlog` Hamiltonian" predicate is formalized
for it to speak to. The general lead, some Hamiltonian on some carrier
deriving the residual premise, remains open. -/
theorem hamDyn_gradient_sector_nonzero_at_zero_momenta :
    ∃ (N : ZMod 2 → ℝ) (x : PhaseSpace 2),
      (∀ i : ZMod 2, x.2 i = 0) ∧ HamDyn N x ≠ 0 := by
  refine ⟨fun _ => 2, (fun j => if j = (0 : ZMod 2) then (0 : ℝ) else 1,
      fun _ => 0), fun _ => rfl, ?_⟩
  rw [hamDyn_decoy_value]; norm_num

/-- **Quadratic kinetic form is not Jlog.** Witness: at `t = 1`, equality would
force `sinh (1/2) ^ 2 = 1/4`, but `sinh` is strictly increasing through a
positive value smaller than `1/2` at a smaller argument, contradicting
`sinh x > x` failure — use the chart module's comparison style instead. -/
theorem Jlog_ne_half_sq : Cost.Jlog ≠ fun t : ℝ => t ^ 2 / 2 := by
  intro h
  have h1 := congrFun h 1
  rw [Jlog_eq_two_sinh_half_sq] at h1
  -- 2 * sinh(1/2)^2 = 1/2 ⇒ sinh(1/2)^2 = 1/4
  have hsq : Real.sinh (1 / 2 : ℝ) ^ 2 = (1 : ℝ) / 4 := by
    have : (2 : ℝ) * Real.sinh (1 / 2) ^ 2 = 1 / 2 := by
      convert h1 using 1; norm_num
    linarith
  -- sinh(1/2) > 0 and sinh(1/2) ≠ 1/2: compare to sinh of a smaller positive arg
  have hpos : 0 < Real.sinh (1 / 2 : ℝ) := by
    have := Real.sinh_lt_sinh.mpr (by norm_num : (0 : ℝ) < 1 / 2)
    simpa using this
  have hne : Real.sinh (1 / 2 : ℝ) ≠ 1 / 2 := by
    -- From cosh² - sinh² = 1: if sinh = 1/2 then cosh² = 5/4, cosh = √(5/4)
    -- and exp(1/2) = cosh + sinh. Use exp(1/2)^2 = exp 1 > 2.7, while
    -- (√(5/4) + 1/2)^2 = 5/4 + √(5/4) + 1/4 = 3/2 + √(5/4) < 3/2 + 1.2 = 2.7.
    intro hs
    have hid := Real.cosh_sq_sub_sinh_sq (1 / 2 : ℝ)
    rw [hs] at hid
    have hcosh_sq : Real.cosh (1 / 2) ^ 2 = 5 / 4 := by
      norm_num at hid; linarith
    have hcosh_pos : 0 < Real.cosh (1 / 2) := Real.cosh_pos _
    have hcosh_val : Real.cosh (1 / 2) = Real.sqrt (5 / 4) := by
      have h := sq_eq_sq_iff_eq_or_eq_neg.mp
        (hcosh_sq.trans (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)).symm)
      exact h.resolve_right (by intro hneg; linarith [hcosh_pos, Real.sqrt_nonneg (5/4:ℝ)])
    have hexp : Real.exp (1 / 2) = Real.cosh (1 / 2) + Real.sinh (1 / 2) := by
      rw [Real.cosh_eq, Real.sinh_eq]; ring
    rw [hs, hcosh_val] at hexp
    have hexp_sq : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hexp1_gt : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    -- √(5/4) < 1.2, so (√(5/4)+1/2)^2 < (1.2+0.5)^2 = 2.89, need tighter:
    -- √(5/4) = √1.25 < 1.12 since 1.12^2 = 1.2544 > 1.25
    have hsqrt_lt : Real.sqrt (5 / 4) < 1.12 := by
      apply (Real.sqrt_lt' (by norm_num)).2
      norm_num
    have hrhs_sq : (Real.sqrt (5 / 4) + 1 / 2) ^ 2 < 2.7 := by
      nlinarith [hsqrt_lt]
    have : (Real.exp (1 / 2)) ^ 2 < 2.7 := by
      rw [hexp]; exact hrhs_sq
    rw [hexp_sq] at this
    linarith
  -- From hsq, sinh = ±1/2; positivity kills the minus; hne kills the plus
  have : Real.sinh (1 / 2) = 1 / 2 ∨ Real.sinh (1 / 2) = -(1 / 2) := by
    have := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans (by norm_num :
      ((1 : ℝ) / 4) = (1 / 2) ^ 2))
    simpa using this
  rcases this with hpos' | hneg
  · exact hne hpos'
  · linarith [hpos]

private theorem chart_product_sq_form (k m : ℝ) (hk : 0 < k) :
    (m / (2 * Real.sqrt k)) ^ 2 = m ^ 2 / (4 * k) := by
  have hden : (2 * Real.sqrt k) ^ 2 = 4 * k := by
    calc (2 * Real.sqrt k) ^ 2
        = (2 : ℝ) ^ 2 * (Real.sqrt k) ^ 2 := by rw [mul_pow]
      _ = 4 * k := by rw [Real.sq_sqrt hk.le]; norm_num
  calc (m / (2 * Real.sqrt k)) ^ 2
      = m ^ 2 / (2 * Real.sqrt k) ^ 2 := by rw [div_pow]
    _ = m ^ 2 / (4 * k) := by rw [hden]

/-- **Profile-parameter matching is the chart product, stated as scalar
algebra.** Matching `2 (lam * p_val) ^ 2` to orbit exactness, for a *scalar*
`p_val`, is equivalent to the chart product form. This neither constructs nor
discharges the ledger-level `EnergyEqualsCost` premise: `p_val` here is a real
parameter, not a `LedgerState → ℝ` observable, and `EnergyEqualsCost` does not
appear in the statement. -/
theorem exact_cost_profile_recovers_chart_product
    (k t lam p_val : ℝ) (hk : 0 < k) :
    (2 * (lam * p_val) ^ 2 = imbalance (orbitPoint k t) ^ 2 / (2 * k)) ↔
      (lam * p_val) ^ 2 =
        (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) ^ 2 := by
  have hrhs := chart_product_sq_form k (imbalance (orbitPoint k t)) hk
  constructor
  · intro h
    calc (lam * p_val) ^ 2
        = (2 * (lam * p_val) ^ 2) / 2 := by ring
      _ = (imbalance (orbitPoint k t) ^ 2 / (2 * k)) / 2 := by rw [h]
      _ = imbalance (orbitPoint k t) ^ 2 / (4 * k) := by ring
      _ = (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) ^ 2 := hrhs.symm
  · intro h
    calc 2 * (lam * p_val) ^ 2
        = 2 * (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) ^ 2 := by rw [h]
      _ = 2 * (imbalance (orbitPoint k t) ^ 2 / (4 * k)) := by rw [hrhs]
      _ = imbalance (orbitPoint k t) ^ 2 / (2 * k) := by ring

theorem energy_equals_cost_of_imbalance : EnergyEqualsCost imbalance := by
  intro k t hk
  have h := Jlog_eq_imbalance_sq_div_two_casimir k t hk
  have hk2 : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk.ne'
  calc imbalance (orbitPoint k t) ^ 2
      = Cost.Jlog t * (2 * k) := by rw [h]; field_simp
    _ = 2 * k * Cost.Jlog t := by ring

theorem chart_product_fails_for_imbalance_at_unit_lam
    (k t : ℝ) (hk : 0 < k) (hkne : 4 * k ≠ 1)
    (hm : imbalance (orbitPoint k t) ≠ 0) :
    ¬ ((1 : ℝ) * imbalance (orbitPoint k t)) ^ 2 =
        (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) ^ 2 := by
  intro h
  have hrhs := chart_product_sq_form k (imbalance (orbitPoint k t)) hk
  have h' : imbalance (orbitPoint k t) ^ 2 =
      imbalance (orbitPoint k t) ^ 2 / (4 * k) := by
    rw [← hrhs]
    simpa only [one_mul] using h
  have hk4 : (4 : ℝ) * k ≠ 0 := mul_ne_zero (by norm_num) hk.ne'
  have hmul : imbalance (orbitPoint k t) ^ 2 * (4 * k) =
      imbalance (orbitPoint k t) ^ 2 :=
    (eq_div_iff hk4).mp h'
  have hfac : (4 : ℝ) * k = 1 :=
    mul_left_cancel₀ (pow_ne_zero 2 hm) (hmul.trans (mul_one _).symm)
  exact hkne hfac

/-! ## §5b. The reduction is an equivalence, and the residual is independent -/

/-- Orbit points at positive Casimir lie in the open positive quadrant. -/
theorem orbitPoint_pos (k t : ℝ) (hk : 0 < k) :
    0 < (orbitPoint k t).1 ∧ 0 < (orbitPoint k t).2 := by
  simp only [orbitPoint]
  exact ⟨mul_pos (Real.sqrt_pos.mpr hk) (Real.exp_pos _),
    mul_pos (Real.sqrt_pos.mpr hk) (Real.exp_pos _)⟩

/-- **The reduction is exact on the open positive quadrant.** The kinetic
condition there holds *if and only if* `EnergyEqualsCost p` holds: the premise
is a rewrite of the quadrant condition, not a strictly weaker residue. The
global gap (Q2–Q4, axes beyond continuity) is unchanged. -/
theorem open_positive_kinetic_iff_energy_equals_cost {p : LedgerState → ℝ} :
    KineticOnOpenPositiveQuadrant p ↔ EnergyEqualsCost p := by
  constructor
  · intro h k t hk
    have hpos := orbitPoint_pos k t hk
    have hk2 := h (orbitPoint k t) hpos.1 hpos.2
    have hchart := Jlog_eq_imbalance_sq_div_two_casimir k t hk
    have hne : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk.ne'
    calc p (orbitPoint k t) ^ 2
        = imbalance (orbitPoint k t) ^ 2 := hk2
      _ = Cost.Jlog t * (2 * k) := by rw [hchart]; field_simp
      _ = 2 * k * Cost.Jlog t := by ring
  · exact energy_equals_cost_implies_kinetic_on_open_positive

/-- **Independence countermodel.** Twice the imbalance fails the residual
premise: at `k = t = 1` the premise would force `8 * Jlog 1 = 2 * Jlog 1`,
but `Jlog 1 > 0`. -/
theorem two_imbalance_fails_energy_equals_cost :
    ¬ EnergyEqualsCost (fun z : LedgerState => 2 * imbalance z) := by
  intro h
  have h1 := h 1 1 one_pos
  change (2 * imbalance (orbitPoint (1:ℝ) (1:ℝ))) ^ 2 =
    2 * (1:ℝ) * Cost.Jlog 1 at h1
  have hsq : imbalance (orbitPoint (1:ℝ) (1:ℝ)) ^ 2 = 2 * Cost.Jlog 1 := by
    have hc := Jlog_eq_imbalance_sq_div_two_casimir (1:ℝ) 1 one_pos
    calc imbalance (orbitPoint (1:ℝ) (1:ℝ)) ^ 2
        = Cost.Jlog 1 * (2 * 1) := by rw [hc]; field_simp
      _ = 2 * Cost.Jlog 1 := by ring
  have hsin : 0 < Real.sinh (1 / 2 : ℝ) := by
    have := Real.sinh_lt_sinh.mpr (by norm_num : (0 : ℝ) < 1 / 2)
    simpa using this
  have hJpos : 0 < Cost.Jlog 1 := by
    rw [Jlog_eq_two_sinh_half_sq]
    have hsq_pos : 0 < Real.sinh (1 / 2 : ℝ) ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hsin)
    linarith
  rw [show (2 * imbalance (orbitPoint (1:ℝ) (1:ℝ))) ^ 2 =
      4 * (imbalance (orbitPoint (1:ℝ) (1:ℝ)) ^ 2) from by ring, hsq] at h1
  have hz : Cost.Jlog 1 = 0 := by linarith
  linarith

/-- **The residual is independent of the momentum package.** `2 * imbalance`
satisfies every derived property of the B1 package (continuity, swap-oddness,
additivity, balance-vanishing) and fails `EnergyEqualsCost`. -/
theorem two_imbalance_package :
    Continuous (fun z : LedgerState => 2 * imbalance z) ∧
    SwapOdd (fun z : LedgerState => 2 * imbalance z) ∧
    (∀ z w : LedgerState,
      2 * imbalance (z + w) = 2 * imbalance z + 2 * imbalance w) ∧
    (∀ z : LedgerState, Balanced z → 2 * imbalance z = 0) ∧
    ¬ EnergyEqualsCost (fun z : LedgerState => 2 * imbalance z) :=
  ⟨continuous_const.mul continuous_imbalance,
    fun z => by
      show 2 * imbalance (z.2, z.1) = -(2 * imbalance z)
      rw [imbalance_swap]; ring,
    fun z w => by
      rw [imbalance_add]; ring,
    fun z hz => by
      show 2 * (z.1 - z.2) = 0
      have hz' : z.1 = z.2 := hz
      rw [hz', sub_self, mul_zero],
    two_imbalance_fails_energy_equals_cost⟩

/-! ## §6. Certificate -/

structure MomentumMagnitudeBridgeVerdict : Prop where
  orbit_coverage_holds : ∀ z : LedgerState, 0 < z.1 → 0 < z.2 →
    z = orbitPoint (casimir z) (Real.log (z.1 / z.2))
  energy_equals_cost_implies_open_kinetic :
    ∀ p : LedgerState → ℝ, EnergyEqualsCost p → KineticOnOpenPositiveQuadrant p
  continuous_extends_kinetic : ∀ p : LedgerState → ℝ, Continuous p →
    KineticOnOpenPositiveQuadrant p → KineticOnClosedPositiveQuadrant p
  composition : ∀ p : LedgerState → ℝ, EnergyEqualsCost p → Continuous p →
    KineticOnClosedPositiveQuadrant p
  balance_on_positive_diagonal_from_residual :
    ∀ p : LedgerState → ℝ, EnergyEqualsCost p → ∀ k : ℝ, 0 < k →
      p (orbitPoint k 0) = 0
  swap_preserves_kinetic_stays_in_quadrant :
    (∀ p : LedgerState → ℝ, SwapOdd p → ∀ z : LedgerState,
      p z ^ 2 = imbalance z ^ 2 →
        p (z.2, z.1) ^ 2 = imbalance (z.2, z.1) ^ 2) ∧
    (∀ z : LedgerState, 0 < z.1 → 0 < z.2 →
      0 < (z.2, z.1).1 ∧ 0 < (z.2, z.1).2)
  negative_quadrant_uncovered :
    ∀ z : LedgerState, z.1 < 0 → z.2 < 0 → ∀ k t : ℝ, 0 ≤ k → orbitPoint k t ≠ z
  /-- The reduction is an exact equivalence on the open positive quadrant. -/
  reduction_exact_on_open_quadrant : ∀ p : LedgerState → ℝ,
    KineticOnOpenPositiveQuadrant p ↔ EnergyEqualsCost p
  /-- The residual is independent of the momentum package: `2 * imbalance`
  satisfies continuity, swap-oddness, additivity, and balance-vanishing, and
  fails the premise. -/
  residual_independent :
    Continuous (fun z : LedgerState => 2 * imbalance z) ∧
    SwapOdd (fun z : LedgerState => 2 * imbalance z) ∧
    (∀ z w : LedgerState,
      2 * imbalance (z + w) = 2 * imbalance z + 2 * imbalance w) ∧
    (∀ z : LedgerState, Balanced z → 2 * imbalance z = 0) ∧
    ¬ EnergyEqualsCost (fun z : LedgerState => 2 * imbalance z)
  /-- The *named* Hamiltonian candidates fail: `HamDyn` has a gradient sector
  at zero momenta, and `Jlog` is not the quadratic form. These are facts about
  named objects on their own carriers; the general lead (an arbitrary
  Hamiltonian deriving the premise) is neither discharged nor refuted. -/
  named_bracket_candidates_fail :
    (∃ (N : ZMod 2 → ℝ) (x : PhaseSpace 2),
      (∀ i : ZMod 2, x.2 i = 0) ∧ HamDyn N x ≠ 0) ∧
    Cost.Jlog ≠ fun t : ℝ => t ^ 2 / 2
  /-- Profile-parameter matching is the chart product (scalar algebra; the
  ledger-level premise is not mentioned). -/
  profile_matching_recovers_chart_product : ∀ (k t lam p_val : ℝ), 0 < k →
    ((2 * (lam * p_val) ^ 2 = imbalance (orbitPoint k t) ^ 2 / (2 * k)) ↔
      (lam * p_val) ^ 2 =
        (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) ^ 2)
  residual_inhabited_and_not_discharged_by_unit_lam_profile :
    EnergyEqualsCost imbalance ∧
      (∀ k t : ℝ, 0 < k → 4 * k ≠ 1 → imbalance (orbitPoint k t) ≠ 0 →
        ¬ ((1 : ℝ) * imbalance (orbitPoint k t)) ^ 2 =
            (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) ^ 2)

theorem momentumMagnitudeBridgeVerdict : MomentumMagnitudeBridgeVerdict where
  orbit_coverage_holds := orbit_coverage
  energy_equals_cost_implies_open_kinetic := fun _ =>
    energy_equals_cost_implies_kinetic_on_open_positive
  continuous_extends_kinetic := fun _ => kinetic_extends_to_closed_positive_quadrant
  composition := fun _ => energy_equals_cost_continuous_implies_kinetic_on_closed
  balance_on_positive_diagonal_from_residual := fun _ =>
    balance_vanishing_on_positive_diagonal_of_energy_equals_cost
  swap_preserves_kinetic_stays_in_quadrant :=
    ⟨fun _ => swap_odd_preserves_kinetic_pointwise,
      fun _ => swap_maps_open_positive_to_itself⟩
  negative_quadrant_uncovered := negative_quadrant_not_on_orbit
  reduction_exact_on_open_quadrant := fun _ =>
    open_positive_kinetic_iff_energy_equals_cost
  residual_independent := two_imbalance_package
  named_bracket_candidates_fail :=
    ⟨hamDyn_gradient_sector_nonzero_at_zero_momenta, Jlog_ne_half_sq⟩
  profile_matching_recovers_chart_product := exact_cost_profile_recovers_chart_product
  residual_inhabited_and_not_discharged_by_unit_lam_profile :=
    ⟨energy_equals_cost_of_imbalance, chart_product_fails_for_imbalance_at_unit_lam⟩

/-! ## Axiom audit -/

#print axioms orbit_coverage
#print axioms energy_equals_cost_implies_kinetic_on_open_positive
#print axioms balance_vanishing_on_positive_diagonal_of_energy_equals_cost
#print axioms kinetic_extends_to_closed_positive_quadrant
#print axioms energy_equals_cost_continuous_implies_kinetic_on_closed
#print axioms swap_odd_preserves_kinetic_pointwise
#print axioms negative_quadrant_not_on_orbit
#print axioms orbitPoint_pos
#print axioms open_positive_kinetic_iff_energy_equals_cost
#print axioms two_imbalance_fails_energy_equals_cost
#print axioms two_imbalance_package
#print axioms hamDyn_gradient_sector_nonzero_at_zero_momenta
#print axioms hamDyn_decoy_value
#print axioms Jlog_ne_half_sq
#print axioms exact_cost_profile_recovers_chart_product
#print axioms energy_equals_cost_of_imbalance
#print axioms chart_product_fails_for_imbalance_at_unit_lam
#print axioms momentumMagnitudeBridgeVerdict

end
end MomentumMagnitudeBridge
end SevenGaps
end Gravity
end IndisputableMonolith
