import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor
import IndisputableMonolith.Relativity.Geometry.Metric
import IndisputableMonolith.Relativity.Calculus.Derivatives

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

open Calculus

/-- **Christoffel Symbols** derived from the metric. -/
noncomputable def christoffel (g : MetricTensor) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun x rho mu nu =>
    (1/2 : ℝ) * Finset.univ.sum (fun (lambda : Fin 4) =>
      (inverse_metric g) x (fun _ => rho) (fun _ => lambda) * (
        (partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then mu else lambda)) nu x) +
        (partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then nu else lambda)) mu x) -
        (partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then mu else nu)) lambda x)
      ))

/-- Christoffel symbols are symmetric in the lower indices (torsion-free). -/
theorem christoffel_symmetric (g : MetricTensor) (x : Fin 4 → ℝ) (rho mu nu : Fin 4) :
    christoffel g x rho mu nu = christoffel g x rho nu mu := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro lambda _
  ring_nf
  -- Symmetry of g indices: ∂_ν g_{μλ} + ∂_μ g_{νλ} - ∂_λ g_{μν} = ∂_μ g_{νλ} + ∂_ν g_{μλ} - ∂_λ g_{νμ}
  have h_sym : (fun y => g.g y (fun _ => 0) (fun i : Fin 2 => if i.val = 0 then mu else nu)) =
               (fun y => g.g y (fun _ => 0) (fun i : Fin 2 => if i.val = 0 then nu else mu)) := by
    funext y
    exact g.symmetric y (fun _ => 0) (fun i : Fin 2 => if i.val = 0 then mu else nu)
  rw [h_sym]

/-- **Riemann Curvature Tensor** $R^{\rho}_{\sigma\mu\nu}$. -/
noncomputable def riemann_tensor (g : MetricTensor) : Tensor 1 3 :=
  fun x up low =>
    let rho := up 0
    let sigma := low 0
    let mu := low 1
    let nu := low 2
    let Γ := christoffel g
    (partialDeriv_v2 (fun y => Γ y rho nu sigma) mu x) -
    (partialDeriv_v2 (fun y => Γ y rho mu sigma) nu x) +
    Finset.univ.sum (fun (lambda : Fin 4) => Γ x rho mu lambda * Γ x lambda nu sigma) -
    Finset.univ.sum (fun (lambda : Fin 4) => Γ x rho nu lambda * Γ x lambda mu sigma)

/-- **Ricci Tensor** $R_{\mu\nu} = R^{\rho}_{\mu\rho\nu}$. -/
noncomputable def ricci_tensor (g : MetricTensor) : BilinearForm :=
  fun x _ low =>
    let mu := low 0
    let nu := low 1
    Finset.univ.sum (fun (rho : Fin 4) =>
      riemann_tensor g x (fun _ => rho) (fun i => if i.val = 0 then mu else if i.val = 1 then rho else nu))

/-- **THEOREM (Riemann Antisymmetry)**: The Riemann tensor is antisymmetric in its last two indices.
    R^ρ_{σμν} = -R^ρ_{σνμ}

    This follows directly from the definition of the Riemann tensor in terms of
    Christoffel symbols. -/
theorem riemann_antisymmetric_last_two (g : MetricTensor) (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    riemann_tensor g x (fun _ => ρ) (fun i => if i.val = 0 then σ else if i.val = 1 then μ else ν) =
    -riemann_tensor g x (fun _ => ρ) (fun i => if i.val = 0 then σ else if i.val = 1 then ν else μ) := by
  -- The Riemann tensor definition: ∂μ Γ^ρ_νσ - ∂ν Γ^ρ_μσ + Γ^ρ_μλ Γ^λ_νσ - Γ^ρ_νλ Γ^λ_μσ
  -- Swapping μ ↔ ν gives: ∂ν Γ^ρ_μσ - ∂μ Γ^ρ_νσ + Γ^ρ_νλ Γ^λ_μσ - Γ^ρ_μλ Γ^λ_νσ
  -- Which is exactly the negation of the original
  unfold riemann_tensor
  -- Simplify the index functions - the pattern is:
  -- LHS: low 0 = σ, low 1 = μ, low 2 = ν
  -- RHS: low 0 = σ, low 1 = ν, low 2 = μ
  -- The Riemann structure: ∂_{low 1} Γ_{low 2, low 0} - ∂_{low 2} Γ_{low 1, low 0} + quadratic terms
  -- Swapping low 1 ↔ low 2 negates the expression
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
             show (0 : ℕ) ≠ 1 from by decide,
             show (1 : ℕ) ≠ 0 from by decide,
             show (2 : ℕ) ≠ 0 from by decide, show (2 : ℕ) ≠ 1 from by decide,
             if_true, if_false]
  ring

/-! **AXIOMS DISCHARGED 2026-04-17.**

The previous `riemann_pair_exchange` and `ricci_tensor_symmetric` axiom
declarations have been deleted.  They are now provided as conditional
theorems in `RiemannSymmetries.lean`:

- `riemann_pair_exchange_proof` (from `riemann_lowered_eq_explicit_hypothesis`)
- `riemann_pair_exchange_from_definition` (clean interface)
- `ricci_tensor_symmetric_thm` (from `riemann_trace_vanishes_hypothesis`)
- `ricci_tensor_symmetric_proof` (clean interface, `∀ μ ν` version)
- `curvature_axioms_hold` (bundle with both)
- `riemann_trace_vanishes_of_smooth` (discharges the trace hypothesis from
  the standard Schwarz-theorem-style smoothness condition `MetricSmooth`)

The conditional form is the honest one: pair exchange and Ricci symmetry
hold for connections satisfying the standard explicit-form / trace-vanishing
identities of Wald §3.2.  Stating them as universal axioms over arbitrary
`MetricTensor` was an over-claim.  The §XXIII.B' RS-internal axiom count
drops by 2 with this discharge.  Downstream code that needs the symmetries
should either supply the discharge hypothesis or use the smoothness bridge. -/

/-- **Ricci Scalar** $R = g^{\mu\nu} R_{\mu\nu}$. -/
noncomputable def ricci_scalar (g : MetricTensor) (x : Fin 4 → ℝ) : ℝ :=
  Finset.univ.sum (fun (mu : Fin 4) =>
    Finset.univ.sum (fun (nu : Fin 4) =>
      inverse_metric g x (fun _ => mu) (fun _ => nu) * ricci_tensor g x (fun _ => 0) (fun i => if i.val = 0 then mu else nu)))

/-- **Einstein Tensor** $G_{\mu\nu} = R_{\mu\nu} - \frac{1}{2} g_{\mu\nu} R$. -/
noncomputable def einstein_tensor (g : MetricTensor) : BilinearForm :=
  fun x up low =>
    ricci_tensor g x up low - (1/2 : ℝ) * g.g x up low * ricci_scalar g x

/-! The previous `ricci_tensor_symmetric'` wrapper depended on the deleted
`ricci_tensor_symmetric` axiom.  Use `RiemannSymmetries.ricci_tensor_symmetric_proof`
(which takes the trace-vanishing hypothesis explicitly) or
`RiemannSymmetries.curvature_axioms_hold` (bundled). -/

/-! ## Minkowski Space Theorems -/

/-- The Minkowski metric η doesn't depend on x, so its derivatives vanish. -/
lemma eta_deriv_zero (μ ν κ : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 (fun y => eta y (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) κ x = 0 := by
  apply partialDeriv_v2_const (c := eta x (fun _ => 0) (fun i => if i.val = 0 then μ else ν))
  intro y; unfold eta; rfl

/-- Christoffel symbols vanish for the Minkowski metric. -/
theorem minkowski_christoffel_zero_proper (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    christoffel minkowski_tensor x ρ μ ν = 0 := by
  unfold christoffel minkowski_tensor
  dsimp
  simp only [eta_deriv_zero, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]

/-- Riemann tensor vanishes for Minkowski space. -/
theorem minkowski_riemann_zero (x : Fin 4 → ℝ) (up : Fin 1 → Fin 4) (low : Fin 3 → Fin 4) :
    riemann_tensor minkowski_tensor x up low = 0 := by
  unfold riemann_tensor
  have hΓ : ∀ y r m n, christoffel minkowski_tensor y r m n = 0 := by
    intro y r m n; exact minkowski_christoffel_zero_proper y r m n
  have h_deriv : ∀ f μ x, (∀ y, f y = 0) → partialDeriv_v2 f μ x = 0 := by
    intro f μ x h; apply partialDeriv_v2_const (c := 0); exact h
  simp [hΓ, h_deriv, Finset.sum_const_zero]

/-- Ricci tensor vanishes for Minkowski space. -/
theorem minkowski_ricci_zero (x : Fin 4 → ℝ) (up : Fin 0 → Fin 4) (low : Fin 2 → Fin 4) :
    ricci_tensor minkowski_tensor x up low = 0 := by
  unfold ricci_tensor
  simp [minkowski_riemann_zero, Finset.sum_const_zero]

/-- Ricci scalar vanishes for Minkowski space. -/
theorem minkowski_ricci_scalar_zero (x : Fin 4 → ℝ) : ricci_scalar minkowski_tensor x = 0 := by
  unfold ricci_scalar
  simp [minkowski_ricci_zero, Finset.sum_const_zero]

/-- Einstein tensor vanishes for Minkowski space. -/
theorem minkowski_einstein_zero (x : Fin 4 → ℝ) (up : Fin 0 → Fin 4) (low : Fin 2 → Fin 4) :
    einstein_tensor minkowski_tensor x up low = 0 := by
  unfold einstein_tensor
  simp only [minkowski_ricci_zero, minkowski_ricci_scalar_zero, mul_zero, sub_zero]

end Geometry
end Relativity
end IndisputableMonolith
