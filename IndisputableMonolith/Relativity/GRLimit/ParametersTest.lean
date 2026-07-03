import Mathlib
import IndisputableMonolith.Relativity.GRLimit.Parameters

/-!
# Smoke Tests for GRLimitParameterFacts

Verifies that the rigorous instance `grLimitParameterFacts_proven` is available
and that all bounds hold as expected.
-/

namespace IndisputableMonolith
namespace Relativity
namespace GRLimit

-- Smoke test: instance is available
example : GRLimitParameterFacts := inferInstance

-- Smoke test: individual bounds hold
example : alpha_from_phi < 1 := by
  have := GRLimitParameterFacts.rs_params_small (self := inferInstance)
  exact this.1

example : cLag_from_phi < 1 := by
  have := GRLimitParameterFacts.rs_params_small (self := inferInstance)
  exact this.2

example : |alpha_from_phi * cLag_from_phi| < 0.02 := by
  exact GRLimitParameterFacts.coupling_product_small (self := inferInstance)

example : |alpha_from_phi * cLag_from_phi| < 0.1 := by
  exact GRLimitParameterFacts.rs_params_perturbative (self := inferInstance)

-- Smoke test: numeric bounds are as expected
example : alpha_from_phi < 1 / 2 := alpha_lt_half
example : cLag_from_phi < 1 / 10 := cLag_lt_one_tenth

-- Smoke test: positivity
example : 0 < alpha_from_phi := rs_params_positive.1
example : 0 < cLag_from_phi := rs_params_positive.2

#check grLimitParameterFacts_proven
#check alpha_from_phi
#check cLag_from_phi

end GRLimit
end Relativity
end IndisputableMonolith
