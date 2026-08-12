import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusDsumSaddle

/-!
# Audit / red test for `Gap2CensusDsumSaddle.dsum_saddle`

This module kernel-verifies that the proved theorem
`Gap2CensusDsumSaddle.dsum_saddle` has **exactly** the type of the third field
of `Gap2SharpRateGap.SharpRateGap`, by constructing a `SharpRateGap` from it
(given the other two fields).  If the proved statement ever drifted from the
field type, the structure instance below would fail to elaborate.

It also re-prints the axiom audit so the kernel-cleanliness receipt
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) is checked on every
build of this module.
-/

open Gap2SharpRateGap Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Finset Filter

namespace DsumSaddleCheck

/-- **Field-match red test.**  Package the proved `dsum_saddle` with the two
remaining (still open) fields to form a `SharpRateGap`.  This elaborates only
because `Gap2CensusDsumSaddle.dsum_saddle` has the field's exact type; it is the
kernel check that the A51 result discharges the third field of the gap, leaving
only `nvar_sharp` and `resid_negligible` for the full sharp rate. -/
def gapWithDsumSaddle
    (h1 : Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 1))
    (h2 : Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0)) :
    SharpRateGap :=
  { nvar_sharp := h1
    resid_negligible := h2
    dsum_saddle := Gap2CensusDsumSaddle.dsum_saddle }

#print axioms Gap2CensusDsumSaddle.dsum_saddle
#print axioms gapWithDsumSaddle

end DsumSaddleCheck
