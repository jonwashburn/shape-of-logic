import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor
import IndisputableMonolith.Relativity.Geometry.Curvature
import IndisputableMonolith.Relativity.Calculus.Derivatives

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

open Calculus

/-- **Covariant Derivative** of a (1,2) tensor $T^\lambda_{\mu\nu}$.
    $\nabla_\rho T^\lambda_{\mu\nu} = \partial_\rho T^\lambda_{\mu\nu} + \Gamma^\lambda_{\rho\sigma} T^\sigma_{\mu\nu} - \Gamma^\sigma_{\rho\mu} T^\lambda_{\sigma\nu} - \Gamma^\sigma_{\rho\nu} T^\lambda_{\mu\sigma}$. -/
noncomputable def cov_deriv_1_2 (g : MetricTensor) (T : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (rho lambda mu nu : Fin 4) : ℝ :=
  let Γ := christoffel g x
  partialDeriv_v2 (fun y => T y lambda mu nu) rho x +
  Finset.univ.sum (fun sigma => Γ lambda rho sigma * T x sigma mu nu) -
  Finset.univ.sum (fun sigma => Γ sigma rho mu * T x lambda sigma nu) -
  Finset.univ.sum (fun sigma => Γ sigma rho nu * T x lambda mu sigma)

end Geometry
end Relativity
end IndisputableMonolith
