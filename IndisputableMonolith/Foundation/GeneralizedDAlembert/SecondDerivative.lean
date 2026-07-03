import IndisputableMonolith.Foundation.GeneralizedDAlembert

/-!
  Second-derivative obstruction for the continuous-combiner route.

  The residual input `continuous_combiner_second_derivative_identity` cannot
  be proved from the current hypotheses alone. The quartic log-cost
  `G(t) = t^4`, already used in the paper as the finite-polynomial-closure
  counterexample, has `G''(0) = 0` but `G''(1) = 12`. Hence no function
  `ψ` can satisfy

    `2 * G''(t) = ψ (G t) * G''(0)`

  for every `t`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace GeneralizedDAlembert
namespace SecondDerivative

private theorem quartic_second_derivative :
    deriv (deriv (fun t : ℝ => t^4)) = fun t => 12*t^2 := by
  funext t
  rw [show deriv (fun t : ℝ => t^4) = fun t => 4*t^3 by
    funext x
    norm_num [deriv_pow]]
  rw [show deriv (fun t : ℝ => 4*t^3) t = 4 * (3*t^2) by
    norm_num [deriv_const_mul, deriv_pow]]
  ring

theorem quartic_not_aczel_second_derivative_identity :
    ¬ AczelSecondDerivativeIdentity (fun t : ℝ => t^4) := by
  intro h
  rcases h with ⟨ψ, hψ⟩
  have h1 := hψ 1
  rw [quartic_second_derivative] at h1
  norm_num at h1

end SecondDerivative
end GeneralizedDAlembert
end Foundation
end IndisputableMonolith
