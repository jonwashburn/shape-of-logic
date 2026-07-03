import Mathlib

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge
namespace Constants

/-- Probability that `n_domains` independent selections from a range of size `range_size`
    all land within a window of radius `tolerance`. -/
noncomputable def coincidenceProbability (n_domains : ℕ)
    (range_size : ℝ) (tolerance : ℝ) : ℝ :=
  (tolerance / range_size) ^ n_domains

lemma coincidenceProbability_net_radius :
    coincidenceProbability 4 1 0.04 = (0.04 : ℝ) ^ 4 := by
  simp [coincidenceProbability]

lemma net_radius_probability_small :
    coincidenceProbability 4 1 0.04 < (1 : ℝ) / 100000 := by
  -- (0.04)^4 = 1 / 390625 < 1 / 100000
  have hcalc : coincidenceProbability 4 1 0.04 = (1 : ℝ) / 390625 := by
    norm_num [coincidenceProbability]
  have : (1 : ℝ) / 390625 < 1 / 100000 := by
    norm_num
  simpa [hcalc] using this

/-- Conservative combined coincidence probability using auxiliary bounds for
    projection constants and dyadic schedules. -/
lemma combined_probability_small :
    let pNet := coincidenceProbability 4 1 0.04
    let pProj : ℝ := 1 / 100
    let pDyadic : ℝ := 1 / 1000
    pNet * pProj * pDyadic < (1 : ℝ) / 1000000000 := by
  intro pNet pProj pDyadic
  have : (0.04 : ℝ) ^ 4 / 100 / 1000 < (1 : ℝ) / 1000000000 := by
    norm_num
  simpa [pNet, pProj, pDyadic, coincidenceProbability] using this

end Constants
end CPMBridge
end Verification
end IndisputableMonolith
