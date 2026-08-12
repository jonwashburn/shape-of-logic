import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusOneSidedRate

/-!
# Gap 2 / C11 / A51: the sharp-rate gap and the conditional assembly
(TARGET 3 two-sided half, TARGET 4)

The A50 arc turned the anomaly fraction into an evaluated ratio
(`Gap2CensusVarianceSep.qfrac_eval`):

  `q(c) = (nvarSum c + ‖r(m)‖²·m0sum c) / dsum c`,

and the A51 one-sided module (`Gap2CensusOneSidedRate`) evaluated that ratio at
the A48 split scale `2√(c·log c)`, banking `q(c) = O(1/(c·log c))` and
`q(c) = o(1/√(c·log c))`.  The remaining distance to the sharp rate
`q(c) = (log c)/(2c²)·(1+o(1))` is exactly the two-sided saddle concentration
at the true Laplace saddle `n*` with `n*·log n* = 2c`:

* per cell the variance weight is `(k/n)(1−1/n)` and the proper second-moment
  weight is `k²(1−1/n)² + (k/n)(1−1/n) ~ k²`.  At the saddle the census mass
  sits at `n ~ n*` and `k ~ c`, where `k/n ~ c/n* ~ (log n*)/2 ~ (log c)/2`.
  Hence the believed first orders `nvarSum ~ ((log c)/2)·m0sum`,
  `dsum ~ c²·m0sum`, whose ratio is `(log c)/(2c²)`.
* the A48 machinery only reaches the split scale `2√(c·log c) = o(n*)`, where
  the same ratio evaluates to `Θ(1/(c·log c))` — the banked one-sided rate.
  Closing the gap needs the two-sided concentration of the moment sums at
  `n*`, i.e. the asymptotic equalities below, not merely upper bounds.

## What is proved here (kernel strength, no new axioms, no sorry)

* `SharpRateGap`: the named gap, three `Filter.Tendsto` first-order
  evaluations: the variance numerator at the sharp scale, the negligibility of
  the mean-residual at the sharp scale, and the saddle first order of the
  proper second moment.
* `qfrac_sharp_rate_of_gap`: **conditional assembly** —
  `SharpRateGap → q(c)·(2c²/log c) → 1`.
* `qfrac_sharp_rate_one_add_o1`: the same in `(1+o(1))` form,
  `q(c) / ((log c)/(2c²)) → 1`.

The gap fields are HYPOTHESIS-grade: they state the missing analytic content
in checkable form.  The two assembly theorems are kernel theorems from the gap
as hypothesis; no field of the gap is proved here.

All results audit to the base triple `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of the file).
-/

namespace Gap2SharpRateGap

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Finset Filter

/-- **The sharp-rate gap (named, HYPOTHESIS-grade).**  The three first-order
evaluations of the A50 variance decomposition at the true Laplace saddle
`n*` (`n*·log n* = 2c`), each stated as a `Filter.Tendsto` limit:

* `nvar_sharp`: the conditional-variance numerator is exactly the sharp rate
  times the proper second moment, `nvarSum c ~ (log c)/(2c²)·dsum c`.  This is
  the two-sided concentration of the variance-weighted moment sum at the
  saddle, where the per-cell weight `(k/n)(1−1/n)` evaluates to `(log c)/2`
  against `dsum`'s `k² ~ c²`.
* `resid_negligible`: the mean-residual contributes nothing at the sharp
  scale, `‖r(m)‖²·m0sum c = o((log c)/(2c²)·dsum c)`.  The A51 one-sided
  bound controls this piece only up to `O(1/(c·log c))·dsum c`.
* `dsum_saddle`: the proper second moment's saddle first order,
  `dsum c ~ c²·m0sum c` (the cell weight `k²(1−1/n)² ~ c²` at `k ~ c`,
  `n ~ n*`).  This is the two-sided concentration certificate for the mass
  itself; it is not used by the assembly (the ratio cancels it) but it is the
  scale that pins `nvarSum c ~ ((log c)/2)·m0sum c`, and it is the field a
  future saddle-concentration proof must deliver first. -/
structure SharpRateGap : Prop where
  nvar_sharp : Filter.Tendsto
    (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
    Filter.atTop (nhds 1)
  resid_negligible : Filter.Tendsto
    (fun c : ℕ =>
      ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
    Filter.atTop (nhds 0)
  dsum_saddle : Filter.Tendsto
    (fun c : ℕ => dsum c / ((c : ℝ) ^ 2 * m0sum c)) Filter.atTop (nhds 1)

/-- **Conditional assembly of the sharp rate (TARGET 4).**  From the gap, the
anomaly fraction obeys `q(c)·(2c²/log c) → 1`: the A50 evaluated ratio plus
field algebra, with no further analysis.  Eventually `c ≥ 2` gives
`qfrac_eval`, `dsum c > 0` and `log c ≠ 0`, and then

  `q(c)·(2c²/log c) = nvarSum·(2c²)/(log c·dsum) + ‖r(m)‖²·m0sum·(2c²)/(log c·dsum)`,

the sum of the first two gap fields, which tends to `1 + 0 = 1`. -/
theorem qfrac_sharp_rate_of_gap (hgap : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) := by
  have heq : (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      =ᶠ[Filter.atTop] (fun c : ℕ =>
        nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
          + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
            * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)) := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    have hd : (0 : ℝ) < dsum c := dsum_pos c hc
    have hlog : Real.log (c : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < c))).ne'
    rw [qfrac_eval c hc]
    field_simp [hd.ne', hlog]
  have hadd := hgap.nvar_sharp.add hgap.resid_negligible
  rw [add_zero] at hadd
  exact hadd.congr' heq.symm

/-- **The sharp rate in `(1+o(1))` form.**  From the gap,
`q(c) / ((log c)/(2c²)) → 1`, i.e. `q(c) = (log c)/(2c²)·(1+o(1))`: the C11
lane's sharp-rate claim, conditional on the named saddle concentration. -/
theorem qfrac_sharp_rate_one_add_o1 (hgap : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => qfrac c / (Real.log c / (2 * (c : ℝ) ^ 2)))
      Filter.atTop (nhds 1) := by
  have h := qfrac_sharp_rate_of_gap hgap
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with c hc
  have hlog : Real.log (c : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < c))).ne'
  have h2c : (2 : ℝ) * (c : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast (by omega : c ≠ 0)))
  field_simp [hlog, h2c]

#print axioms qfrac_sharp_rate_of_gap
#print axioms qfrac_sharp_rate_one_add_o1

end Gap2SharpRateGap
