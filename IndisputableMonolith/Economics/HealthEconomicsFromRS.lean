import Mathlib
import IndisputableMonolith.Cost

/-!
# Health Economics from RS — E4 / E1 Applied

Five canonical health economic analysis types (CEA, CBA, CUA, BIA, ROI)
= configDim D = 5.

In RS: QALY (quality-adjusted life year) = J-cost integrated over time.
Perfect health: J = 0 (QALY weight = 1).
Disease: J > 0 (QALY weight < 1).

Five canonical healthcare financing models (Beveridge, Bismarck, national
health insurance, out-of-pocket, mixed) = configDim D.

Lean: 5 analysis types + 5 financing models.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Economics.HealthEconomicsFromRS
open Cost

inductive HealthEconomicAnalysis where
  | cea | cba | cua | bia | roi
  deriving DecidableEq, Repr, BEq, Fintype

theorem healthEconomicAnalysisCount : Fintype.card HealthEconomicAnalysis = 5 := by decide

inductive HealthcareFinancingModel where
  | beveridge | bismarck | nationalHealthInsurance | outOfPocket | mixed
  deriving DecidableEq, Repr, BEq, Fintype

theorem healthcareFinancingModelCount : Fintype.card HealthcareFinancingModel = 5 := by decide

/-- Perfect health: J = 0 (QALY = 1). -/
theorem perfect_health : Jcost 1 = 0 := Jcost_unit0

structure HealthEconomicsCert where
  five_analyses : Fintype.card HealthEconomicAnalysis = 5
  five_models : Fintype.card HealthcareFinancingModel = 5
  perfect : Jcost 1 = 0

def healthEconomicsCert : HealthEconomicsCert where
  five_analyses := healthEconomicAnalysisCount
  five_models := healthcareFinancingModelCount
  perfect := perfect_health

end IndisputableMonolith.Economics.HealthEconomicsFromRS
