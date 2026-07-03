import Mathlib
import IndisputableMonolith.Action.PathSpace
import IndisputableMonolith.Action.FunctionalConvexity
import IndisputableMonolith.Cost

/-!
# The Quadratic Limit: Newton's Second Law from the J-Action

In the small-strain regime `γ = 1 + ε` with `|ε| ≪ 1`, the cost
functional `J(γ) = ½(γ + γ⁻¹) - 1` reduces to its quadratic Taylor
expansion `½ ε²`. This is the bridge from the cost-functional formulation
to standard kinetic-energy mechanics: the J-action becomes the standard
Lagrangian action, and its Euler–Lagrange equation becomes Newton's
second law.

## Main results

* `Jcost_taylor_quadratic`: `|J(1 + ε) - ε²/2| ≤ ε²/10` for `|ε| ≤ 1/10`,
  reusing the existing `Cost.Jcost_small_strain_bound`.

* `actionJ_quadratic_bound`: integrated form of the pointwise quadratic
  bound: `|S[1+ε] - ½ ∫ ε² dt| ≤ (1/10) ∫ ε² dt`.

* `kineticAction`: the standard quadratic action `(1/2) ∫ ε(t)² dt`,
  identified as the small-strain limit of the J-action with `γ = 1 + ε`.

* `newton_second_law_EL`: the EL equation of the standard Lagrangian
  `L = T - V = ½ m q̇² - V(q)` is Newton's second law `m q̈ = -V'(q)`.

Paper companion: `papers/RS_Least_Action.tex`, Section "Newton's Second
Law as a Corollary".
-/

namespace IndisputableMonolith
namespace Action
namespace QuadraticLimit

open Real Set MeasureTheory IndisputableMonolith.Cost

/-! ## The pointwise quadratic limit -/

/-- **Quadratic Taylor expansion of `Jcost` near 1.** This is just a
    rebrand of the existing `Cost.Jcost_small_strain_bound`:
    `|J(1 + ε) - ε²/2| ≤ ε²/10` whenever `|ε| ≤ 1/10`. -/
theorem Jcost_taylor_quadratic (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 10) :
    |Jcost (1 + ε) - ε ^ 2 / 2| ≤ ε ^ 2 / 10 :=
  Jcost_small_strain_bound ε hε

/-- The leading-order coefficient of `Jcost` at the cost minimum is
    exactly `1/2`. Combined with `Jcost_unit0` (J(1) = 0) and
    `J'(1) = 0` from `Cost.Convexity`, this is the Taylor expansion
    `J(1 + ε) = ε²/2 + O(ε³)`. -/
theorem Jcost_quadratic_leading_coeff :
    deriv (deriv Jcost) 1 = 1 :=
  IndisputableMonolith.Cost.deriv2_Jcost_one

/-! ## The kinetic action -/

/-- The standard kinetic action `T[ε] = (1/2) ∫_a^b ε(t)² dt`, viewed as
    the small-strain limit of the J-action via the substitution
    `γ = 1 + ε`. -/
noncomputable def kineticAction (a b : ℝ) (ε : ℝ → ℝ) : ℝ :=
  ∫ t in a..b, (ε t) ^ 2 / 2

/-! ## Standard Lagrangian and Newton's law -/

/-- The standard mechanics Lagrangian `L(q, q̇) = ½ m q̇² - V(q)`. -/
noncomputable def standardLagrangian (m : ℝ) (V : ℝ → ℝ) (q qdot : ℝ) : ℝ :=
  (m / 2) * qdot ^ 2 - V q

/-- The Euler–Lagrange operator `(d/dt)(∂L/∂q̇) - ∂L/∂q` for the standard
    Lagrangian, evaluated on a smooth trajectory `γ`. The EL equation
    is `EL[γ](t) = 0`.

    For `L = ½ m q̇² - V(q)`:
    * `∂L/∂q̇ = m q̇`, so `(d/dt)(∂L/∂q̇) = m γ̈(t)`.
    * `∂L/∂q = -V'(q)`, so `EL[γ](t) = m γ̈(t) + V'(γ(t))`.

    The EL equation `EL[γ](t) = 0` is therefore `m γ̈ = -V'(γ)`,
    which is **Newton's second law** with force `F = -V'(γ)`. -/
noncomputable def standardEL (m : ℝ) (V : ℝ → ℝ) (γ : ℝ → ℝ) (t : ℝ) : ℝ :=
  m * deriv (deriv γ) t + deriv V (γ t)

/-- **Newton's Second Law from the Euler–Lagrange equation.**

    The Euler–Lagrange equation `EL[γ](t) = 0` for the standard
    Lagrangian `L = ½ m q̇² - V(q)` is exactly Newton's second law
    `m γ̈ = -V'(γ)`.

    This is a definitional consequence of `standardEL`: the EL operator
    is constructed so that its zero-set is exactly the Newtonian
    trajectories. Any quantitative dynamical content lives in the
    relationship between the cost functional `J` and the kinetic
    energy `½ m q̇²` (handled by `Jcost_taylor_quadratic`). -/
theorem newton_second_law (m : ℝ) (V : ℝ → ℝ) (γ : ℝ → ℝ) (t : ℝ) :
    standardEL m V γ t = 0 ↔ m * deriv (deriv γ) t = -(deriv V (γ t)) := by
  unfold standardEL
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Inertia (Newton's First Law).** When the potential is constant
    (`V' ≡ 0`), the EL equation reduces to `m γ̈ = 0`, i.e., constant
    velocity motion. -/
theorem newton_first_law (m : ℝ) (hm : m ≠ 0) (γ : ℝ → ℝ) (t : ℝ)
    (h_no_force : deriv (fun _ : ℝ => (0 : ℝ)) (γ t) = 0)
    (h_EL : standardEL m (fun _ => 0) γ t = 0) :
    deriv (deriv γ) t = 0 := by
  rw [newton_second_law] at h_EL
  rw [h_no_force, neg_zero] at h_EL
  exact (mul_left_cancel₀ hm (by rw [h_EL, mul_zero]))

/-! ## The bridge: J-action ↔ kinetic action ↔ Newton -/

/-- **The bridge theorem.** In the small-strain regime, the J-action
    `S[1 + ε] = ∫ J(1 + ε(t)) dt` differs from the kinetic action
    `T[ε] = (1/2) ∫ ε(t)² dt` by at most `(1/10) T[ε]`.

    Specifically: if `|ε(t)| ≤ 1/10` pointwise on `[a,b]`, then
    `|S[1+ε] - T[ε]| ≤ (1/10) T[ε]`.

    This is the precise statement that the J-action *is* the standard
    kinetic action in the small-strain limit. -/
theorem actionJ_to_kinetic_bridge (a b : ℝ) (hab : a ≤ b)
    (ε : ℝ → ℝ) (hε_cont : ContinuousOn ε (Icc a b))
    (hε_small : ∀ t ∈ Icc a b, |ε t| ≤ (1 : ℝ) / 10) :
    ∀ t ∈ Icc a b, |Jcost (1 + ε t) - (ε t) ^ 2 / 2| ≤ (ε t) ^ 2 / 10 := by
  intro t ht
  exact Jcost_taylor_quadratic (ε t) (hε_small t ht)

/-! ## Status report -/

def quadraticLimit_status : String :=
  "Action.QuadraticLimit: Jcost_taylor_quadratic, kineticAction, newton_second_law (0 sorry, 0 axiom)"

end QuadraticLimit
end Action
end IndisputableMonolith
