import IndisputableMonolith.Economics.Recognition.RatioEngine

/-!
# Index-Number Properties of the Jevons Projection

The CPT projection step in `RatioEngine` isolates the common log level. Its
exponential is the Jevons/geometric-mean index. This module proves the two
clean index-number properties available directly at the log-projection layer:
time reversal and multiplicative transitivity.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

open scoped BigOperators

noncomputable section

theorem logMean_neg {ι : Type*} [Fintype ι] (y : LogPanel ι) :
    logMean (fun i : ι => -y i) = -logMean y := by
  unfold logMean
  rw [Finset.sum_neg_distrib]
  ring

/-- Time reversal: reversing every price relative inverts the Jevons level. -/
theorem jevons_time_reversal {ι : Type*} [Fintype ι] (y : LogPanel ι) :
    jevonsLevel (fun i : ι => -y i) = (jevonsLevel y)⁻¹ := by
  unfold jevonsLevel
  rw [logMean_neg]
  exact Real.exp_neg (logMean y)

theorem logMean_add {ι : Type*} [Fintype ι] (y z : LogPanel ι) :
    logMean (fun i : ι => y i + z i) = logMean y + logMean z := by
  unfold logMean
  rw [Finset.sum_add_distrib]
  ring

/-- Multiplicative transitivity in log coordinates: the Jevons level of composed
relatives is the product of the two Jevons levels. -/
theorem jevons_transitivity {ι : Type*} [Fintype ι] (y z : LogPanel ι) :
    jevonsLevel (fun i : ι => y i + z i) = jevonsLevel y * jevonsLevel z := by
  unfold jevonsLevel
  rw [logMean_add]
  exact Real.exp_add (logMean y) (logMean z)

end

end Recognition
end Economics
end IndisputableMonolith
