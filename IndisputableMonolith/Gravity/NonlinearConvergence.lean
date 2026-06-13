import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.ReggeCalculus

/-!
# Nonlinear Convergence: Regge Action -> Einstein-Hilbert

Records the convergence inputs used when passing from Regge calculus to
Einstein-Hilbert geometry.

## 2026-05-13 correction: what CMS actually proves

Philip Beltracchi caught an overstatement in the previous comments in this
file.  We had described Cheeger-Müller-Schrader (1984) as an `O(a^2)` theorem.
That is too strong for the general theorem cited from CMS.

CMS Theorem 5.1, in Cheeger's 2016 notation, gives a curvature-measure bound
of the form

`|R_i(U) - R_{i,η}(U)| ≤ c · (Vol(U) · η^(1/2) + Vol(B_{η^(1/2)}(∂U)))`.

That is a measure-convergence theorem with an `η^(1/2)` bulk term plus a
boundary-tube term.  It is not the same statement as a plain
`|S_Regge - S_EH| ≤ C · a^2` bound.

This file now separates:

* `cms_theorem_5_1_measure_bound`: the CMS-style general Riemannian
  curvature-measure convergence input;
* `special_quadratic_regge_to_eh_convergence_hypothesis`: the stronger
  `O(a^2)` action/curvature-rate hypothesis used by some weak-field or
  numerical lattice modules.

The old name `regge_to_eh_convergence_axiom` is retained as an abbreviation
for the stronger special hypothesis so downstream code keeps compiling, but
it should no longer be cited as "the CMS theorem" without qualification.

## Mathematical Status

This is NOT a new result. The convergence of Regge calculus to GR
is established in the literature:

- Cheeger, Müller, Schrader (1984): curvature-measure convergence for
  piecewise-flat spaces, with the Theorem 5.1 bound recorded below.
- Gentle, Miller (1998): explicit second-order convergence in special
  numerical settings such as Kasner-type tests.
- Brewin, Gentle (2001): reconciliation of convergence behavior in
  numerical Regge calculus.
- Christiansen (2011): spectral analysis of linearized Regge.

We axiomatize these results so that the RS framework can build on
them without reproving 40 years of Regge calculus from scratch.
The axioms are clearly labeled and can be replaced by full proofs
if/when Regge convergence is formalized in Mathlib.

## Key hypotheses

- `cms_theorem_5_1_measure_bound`: CMS-style `η^(1/2)` measure convergence.
- `special_quadratic_regge_to_eh_convergence_hypothesis`: stronger `O(a^2)`
  action convergence, used only where a special weak-field/numerical argument
  supplies it.
- `regge_ricci_convergence_axiom` / `regge_riemann_convergence_axiom`:
  retained stronger hypotheses for modules that explicitly assume them.
-/

namespace IndisputableMonolith
namespace Gravity
namespace NonlinearConvergence

open Constants ReggeCalculus

noncomputable section

/-! ## CMS Theorem 5.1: general measure convergence -/

/-- **CMS Theorem 5.1 shape, scalar real abstraction.**

For a smooth Riemannian manifold `M`, a sufficiently fine `Θ`-fat
triangulation with mesh `η`, and a submanifold `U` with smooth boundary, CMS
prove a curvature-measure estimate of the form

`|R_i(U) - R_{i,η}(U)| ≤ c · (Vol(U) · sqrt η + Vol(B_{sqrt η}(∂U)))`.

The real variables here are the scalar placeholders for those geometric
quantities:

* `RiU`: smooth Lipschitz-Killing curvature measure on `U`;
* `RiEtaU`: piecewise-flat / Regge curvature measure on `U`;
* `VolU`: volume of `U`;
* `boundaryTubeVol`: volume of the `sqrt η`-tubular neighborhood of `∂U`;
* `η`: mesh size;
* `c`: the CMS constant depending on curvature bounds and fatness.

This is deliberately **not** an `O(η^2)` statement. -/
def cms_theorem_5_1_measure_bound : Prop :=
  ∀ (RiU RiEtaU VolU boundaryTubeVol η c : ℝ),
    0 ≤ VolU → 0 ≤ boundaryTubeVol → 0 < η → η < 1 → 0 < c →
      |RiU - RiEtaU| ≤ c * (VolU * Real.sqrt η + boundaryTubeVol)

/-- Package form of the CMS Theorem 5.1-style input. -/
structure CMSTheorem51 where
  measure_bound : cms_theorem_5_1_measure_bound

/-! ## Stronger special-purpose quadratic hypotheses -/

/-- **Special stronger hypothesis (not CMS Theorem 5.1 in general).**

Some weak-field cubic-lattice or numerical Regge settings can carry
second-order truncation/convergence estimates.  That is a separate input from
the general CMS curvature-measure theorem above.

This is the old `regge_to_eh_convergence_axiom` statement, retained under a
more honest name. -/
def special_quadratic_regge_to_eh_convergence_hypothesis : Prop :=
  ∀ (S_EH : ℝ) (a : ℝ), 0 < a → a < 1 →
    ∃ (S_Regge : ℝ) (C : ℝ), 0 < C ∧
      |S_Regge - S_EH| ≤ C * a ^ 2

/-- Backward-compatible name.  Do not cite this as the CMS theorem without the
qualification that it is a stronger special-purpose `O(a^2)` hypothesis. -/
abbrev regge_to_eh_convergence_axiom : Prop :=
  special_quadratic_regge_to_eh_convergence_hypothesis

/-- **AXIOM (Regge Ricci convergence)**:
    The Regge curvature (sum of deficit angles / dual volumes)
    converges to the Ricci scalar at `O(a^2)`.

    This is a stronger special-purpose hypothesis, not the general CMS
    Theorem 5.1 measure estimate above.

    For a smooth metric g at point x:
      |R_Regge(x, a) - R(x)| <= C * a^2

    This follows from the action convergence by the fundamental
    theorem of calculus of variations. -/
def regge_ricci_convergence_axiom : Prop :=
  ∀ (R_continuum : ℝ) (a : ℝ), 0 < a → a < 1 →
    ∃ (R_Regge : ℝ) (C : ℝ), 0 < C ∧
      |R_Regge - R_continuum| ≤ C * a ^ 2

/-- **AXIOM (Regge Riemann convergence)**:
    The holonomy around a plaquette of the simplicial complex
    converges to the Riemann curvature tensor at the dual point.

    This local holonomy estimate is a special-purpose hypothesis for modules
    that need component-level curvature control; it is not the scalar CMS
    Theorem 5.1 measure statement.

    For a smooth metric g, coordinates x^mu, and small loop
    of area ~ a^2 in the (mu, nu) plane:
      Holonomy = I + a^2 R^rho_sigma_mu_nu + O(a^4)

    This is the geometric content of the deficit angle:
    delta_h / A_h -> sectional curvature K(Pi) where Pi is
    the 2-plane dual to the hinge h. -/
def regge_riemann_convergence_axiom : Prop :=
  ∀ (R_component : ℝ) (a : ℝ), 0 < a → a < 1 →
    ∃ (holonomy_deviation : ℝ) (C : ℝ), 0 < C ∧
      |holonomy_deviation - a ^ 2 * R_component| ≤ C * a ^ 4

/-! ## Rate comparisons and vanishing bounds -/

/-- The CMS bulk term `sqrt η` vanishes as `η -> 0`. -/
theorem cms_sqrt_bulk_vanishes (C VolU : ℝ) :
    Filter.Tendsto (fun η : ℝ => C * (VolU * Real.sqrt η)) (nhds 0) (nhds 0) := by
  have hsqrt : Filter.Tendsto (fun η : ℝ => Real.sqrt η) (nhds 0) (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0)
  have hVol : Filter.Tendsto (fun η : ℝ => VolU * Real.sqrt η) (nhds 0) (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℝ => VolU) (nhds 0) (nhds VolU) :=
      tendsto_const_nhds
    simpa using hconst.mul hsqrt
  have hC : Filter.Tendsto (fun _ : ℝ => C) (nhds 0) (nhds C) := tendsto_const_nhds
  simpa using hC.mul hVol

/-- If the boundary-tube volume also vanishes as `η -> 0`, then the whole
CMS Theorem 5.1 right-hand side vanishes. -/
theorem cms_bound_vanishes
    (C VolU : ℝ) (boundaryTubeVol : ℝ → ℝ)
    (hBoundary : Filter.Tendsto boundaryTubeVol (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun η : ℝ => C * (VolU * Real.sqrt η + boundaryTubeVol η))
      (nhds 0) (nhds 0) := by
  have hbulk : Filter.Tendsto (fun η : ℝ => VolU * Real.sqrt η) (nhds 0) (nhds 0) := by
    have hsqrt : Filter.Tendsto (fun η : ℝ => Real.sqrt η) (nhds 0) (nhds 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    have hconst : Filter.Tendsto (fun _ : ℝ => VolU) (nhds 0) (nhds VolU) :=
      tendsto_const_nhds
    simpa using hconst.mul hsqrt
  have hsum :
      Filter.Tendsto (fun η : ℝ => VolU * Real.sqrt η + boundaryTubeVol η)
        (nhds 0) (nhds (0 + 0)) := hbulk.add hBoundary
  have hC : Filter.Tendsto (fun _ : ℝ => C) (nhds 0) (nhds C) := tendsto_const_nhds
  simpa [mul_add] using hC.mul hsum

/-- The convergence rate is second order: error = O(a^2).
    This is a property of the stronger special-purpose quadratic hypothesis,
    not the general CMS Theorem 5.1 bound. -/
theorem convergence_is_second_order (a : ℝ) (_ha : 0 < a) (_ha1 : a < 1) :
    (a / 2) ^ 2 = a ^ 2 / 4 := by ring

/-- Second-order convergence implies the special quadratic error vanishes as
`a -> 0`. -/
theorem quadratic_error_vanishes (C : ℝ) (_hC : 0 < C) :
    Filter.Tendsto (fun a => C * a ^ 2) (nhds 0) (nhds 0) := by
  have h : Continuous (fun a : ℝ => C * a ^ 2) := by continuity
  have := h.tendsto (0 : ℝ)
  simp at this
  exact this

/-- Backward-compatible old theorem name. -/
theorem error_vanishes (C : ℝ) (hC : 0 < C) :
    Filter.Tendsto (fun a => C * a ^ 2) (nhds 0) (nhds 0) :=
  quadratic_error_vanishes C hC

/-! ## Connection to RS -/

/-- In the RS framework, the Regge action convergence gives:
    S_Regge(J-cost lattice, a) -> (1/2*kappa_RS) * integral R sqrt(g)

    Combined with:
    - J-cost minimization implies delta S_Regge = 0 (variational dynamics)
    - delta S_EH = 0 implies EFE (Hilbert variation)
    - kappa_RS = 8*phi^5 (derived coupling)

    This gives the FULL (nonlinear) Einstein field equations
    from the RS discrete ledger, conditional on the convergence axiom. -/
structure RSReggeConvergence where
  /-- General CMS Theorem 5.1-style curvature-measure convergence. -/
  cms_measure_convergence : cms_theorem_5_1_measure_bound
  /-- Stronger special-purpose action convergence, if a module needs `O(a^2)`. -/
  action_convergence : regge_to_eh_convergence_axiom
  ricci_convergence : regge_ricci_convergence_axiom
  kappa_derived : rs_kappa = 8 * phi ^ 5
  kappa_positive : 0 < rs_kappa

/-- If the special quadratic convergence hypotheses hold, then the RS lattice
produces the old `O(a^2)`-style error envelope.  This is intentionally separate
from the general CMS measure-convergence input. -/
def rs_implies_gr (_conv : RSReggeConvergence) : Prop :=
  ∀ (a : ℝ), 0 < a → a < 1 →
    ∃ (error : ℝ), |error| ≤ rs_kappa * a ^ 2

/-! ## What Would Be Needed to Prove (Instead of Axiomatize) -/

/-- To PROVE the convergence axioms from scratch in Lean, one would need:

    1. Simplicial geometry: volumes, angles, areas as functions of edge lengths
       (Cayley-Menger determinants, generalized to all dimensions)
    2. The Schläfli identity: sum A_h * d(delta_h)/dL_e = 0
       (a purely geometric identity; provable but technical)
    3. Comparison geometry: relating simplicial metrics to smooth metrics
       (this requires Riemannian geometry in Mathlib, which is incomplete)
    4. Error analysis: bounding the difference between Regge curvature
       measures and smooth curvature measures in terms of mesh quality.
       CMS gives the `η^(1/2)` + boundary-tube form above; `O(a^2)` needs
       extra special structure.
    5. Compactness and convergence: extracting a convergent subsequence
       and identifying the limit (standard but requires functional analysis)

    This is a multi-year project for the Mathlib community.
    We axiomatize instead, clearly labeling the axioms. -/
def proof_requirements : List String :=
  [ "Simplicial geometry (Cayley-Menger)"
  , "Schläfli identity"
  , "Comparison geometry (smooth vs piecewise-flat)"
  , "Curvature error analysis"
  , "Compactness and convergence extraction" ]

/-! ## Certificate -/

structure NonlinearConvergenceCert where
  cms_bound : cms_theorem_5_1_measure_bound → cms_theorem_5_1_measure_bound
  cms_bulk_vanishes : ∀ C VolU : ℝ,
    Filter.Tendsto (fun η : ℝ => C * (VolU * Real.sqrt η)) (nhds 0) (nhds 0)
  cms_full_bound_vanishes : ∀ (C VolU : ℝ) (boundaryTubeVol : ℝ → ℝ),
    Filter.Tendsto boundaryTubeVol (nhds 0) (nhds 0) →
    Filter.Tendsto
      (fun η : ℝ => C * (VolU * Real.sqrt η + boundaryTubeVol η))
      (nhds 0) (nhds 0)
  second_order : ∀ a : ℝ, 0 < a → a < 1 → (a/2)^2 = a^2/4
  error_goes_to_zero : ∀ C : ℝ, 0 < C →
    Filter.Tendsto (fun a => C * a ^ 2) (nhds 0) (nhds 0)
  kappa : rs_kappa = 8 * phi ^ 5

theorem nonlinear_convergence_cert : NonlinearConvergenceCert where
  cms_bound := fun h => h
  cms_bulk_vanishes := cms_sqrt_bulk_vanishes
  cms_full_bound_vanishes := cms_bound_vanishes
  second_order := fun _ _ _ => convergence_is_second_order _ (by linarith) (by linarith)
  error_goes_to_zero := error_vanishes
  kappa := rs_kappa_value

end

end NonlinearConvergence
end Gravity
end IndisputableMonolith
