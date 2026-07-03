import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

namespace IndisputableMonolith.Data

structure Measurement where
  name : String
  value : ℝ
  error : ℝ

/-- Hardcoded measurements for now (JSON parsing blocked by Mathlib version). -/
def import_measurements : List Measurement :=
  [
    { name := "AlphaInvPrediction", value := (137.035999084 : ℝ), error := (0.000000084 : ℝ) },
    { name := "Sin2ThetaW_at_MZ", value := (0.23121 : ℝ), error := (0.00004 : ℝ) },
    { name := "AlphaS_at_MZ", value := (0.1179 : ℝ), error := (0.0009 : ℝ) },
    { name := "ElectronG2", value := (0.00115965218073 : ℝ), error := (2.8e-13 : ℝ) },
    { name := "MuonG2", value := (0.00116592062 : ℝ), error := (4.1e-10 : ℝ) },
    { name := "MW_over_MZ", value := (0.88153 : ℝ), error := (0.00018 : ℝ) }
  ]

end IndisputableMonolith.Data
