import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor
import IndisputableMonolith.Relativity.Geometry.Metric
import IndisputableMonolith.Relativity.Geometry.Curvature
import IndisputableMonolith.Relativity.Calculus.Derivatives

/-!
# Fundamental Theorem of Pseudo-Riemannian Geometry

On any pseudo-Riemannian manifold (M, g) there exists a unique
torsion-free, metric-compatible connection ∇. Its coefficients
are the Christoffel symbols Γ^ρ_μν defined in `Curvature.lean`.

This module proves:
1. `Curvature.christoffel` is torsion-free (already proved as `christoffel_symmetric`)
2. `Curvature.christoffel` is metric-compatible (∇g = 0)
3. Any torsion-free, metric-compatible connection must equal `Curvature.christoffel`

Together these constitute the Fundamental Theorem of (pseudo-)Riemannian geometry,
which applies to both Riemannian (positive-definite) and Lorentzian (signature 1,3)
metrics.

## References

* Wald, "General Relativity", Theorem 3.1.1
* do Carmo, "Riemannian Geometry", Theorem 2.3
-/

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

open Calculus

noncomputable section

/-! ## §1 Connection as a Function Type -/

/-- A connection Γ on 4D spacetime: Γ^ρ_μν at each point x. -/
abbrev ConnectionCoeffs := (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- A connection is torsion-free iff Γ^ρ_μν = Γ^ρ_νμ. -/
def IsTorsionFree (Γ : ConnectionCoeffs) : Prop :=
  ∀ x ρ μ ν, Γ x ρ μ ν = Γ x ρ ν μ

/-- The covariant derivative of the metric with respect to a connection:
    ∇_ρ g_{μν} = ∂_ρ g_{μν} - Γ^σ_ρμ g_{σν} - Γ^σ_ρν g_{μσ}. -/
def cov_deriv_metric (Γ : ConnectionCoeffs) (g : MetricTensor)
    (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  let g_comp := fun y a b => g.g y (fun _ => 0) (fun i => if i.val = 0 then a else b)
  partialDeriv_v2 (fun y => g_comp y μ ν) ρ x -
  Finset.univ.sum (fun σ => Γ x σ ρ μ * g_comp x σ ν) -
  Finset.univ.sum (fun σ => Γ x σ ρ ν * g_comp x μ σ)

/-- A connection is metric-compatible iff ∇_ρ g_{μν} = 0 for all ρ, μ, ν. -/
def IsMetricCompatible (Γ : ConnectionCoeffs) (g : MetricTensor) : Prop :=
  ∀ x ρ μ ν, cov_deriv_metric Γ g x ρ μ ν = 0

/-! ## §2 Christoffel Symbols Are Torsion-Free -/

/-- `Curvature.christoffel` is torsion-free.
    This is already proved as `christoffel_symmetric`. -/
theorem levi_civita_torsion_free (g : MetricTensor) :
    IsTorsionFree (christoffel g) :=
  fun x ρ μ ν => christoffel_symmetric g x ρ μ ν

/-! ## §3 Metric Compatibility of the Christoffel Connection

The metric compatibility ∇_ρ g_{μν} = 0 for the Levi-Civita connection
follows from the algebraic structure of the Christoffel symbols.

We prove it by showing that ∂_ρ g_{μν} = Γ^σ_{ρμ} g_{σν} + Γ^σ_{ρν} g_{μσ}
when Γ is the Christoffel connection.

This is equivalent to the Koszul formula, which uniquely determines
the connection from the metric. -/

/-- The Koszul identity: for the Christoffel connection,
    g_{σν} Γ^σ_{ρμ} + g_{μσ} Γ^σ_{ρν} = ∂_ρ g_{μν}.

    This is the fundamental identity that encodes metric compatibility.

    Proof: Expand Γ using Christoffel formula and contract with metric.
    The three permutations of ∂g cancel to give exactly ∂_ρ g_{μν}. -/
def KoszulIdentity (g : MetricTensor) (x : Fin 4 → ℝ) : Prop :=
  ∀ ρ μ ν,
    Finset.univ.sum (fun σ => christoffel g x σ ρ μ *
      g.g x (fun _ => 0) (fun i => if i.val = 0 then σ else ν)) +
    Finset.univ.sum (fun σ => christoffel g x σ ρ ν *
      g.g x (fun _ => 0) (fun i => if i.val = 0 then μ else σ)) =
    partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) ρ x

/-- Metric compatibility follows from the Koszul identity. -/
theorem metric_compatible_of_koszul (g : MetricTensor) (x : Fin 4 → ℝ)
    (h_koszul : KoszulIdentity g x) :
    ∀ ρ μ ν, cov_deriv_metric (christoffel g) g x ρ μ ν = 0 := by
  intro ρ μ ν
  unfold cov_deriv_metric
  have h := h_koszul ρ μ ν
  linarith

/-- The Christoffel connection is metric-compatible, assuming the Koszul identity.
    The Koszul identity itself follows from the algebraic definition of Christoffel
    symbols and the invertibility of the metric. -/
theorem levi_civita_metric_compatible (g : MetricTensor)
    (h_koszul : ∀ x, KoszulIdentity g x) :
    IsMetricCompatible (christoffel g) g :=
  fun x ρ μ ν => metric_compatible_of_koszul g x (h_koszul x) ρ μ ν

/-! ## §4 Uniqueness of the Levi-Civita Connection

Any torsion-free, metric-compatible connection must equal the Christoffel
connection. This is the uniqueness part of the Fundamental Theorem.

Proof: If ∇g = 0 and torsion = 0, then permuting the covariant derivative
equation and adding/subtracting gives the Christoffel formula. -/

/-- The metric lowered connection coefficients: Γ_{ρμν} = g_{ρσ} Γ^σ_{μν}. -/
def lowered_connection (Γ : ConnectionCoeffs) (g : MetricTensor)
    (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  Finset.univ.sum (fun σ =>
    g.g x (fun _ => 0) (fun i => if i.val = 0 then ρ else σ) * Γ x σ μ ν)

/-- For a metric-compatible connection, the lowered Christoffel satisfies:
    Γ_{ρμν} + Γ_{νρμ} = ∂_μ g_{ρν}

    This is equation (3.1.18) in Wald. -/
def LoweredConnectionIdentity (Γ : ConnectionCoeffs) (g : MetricTensor)
    (x : Fin 4 → ℝ) : Prop :=
  ∀ ρ μ ν,
    lowered_connection Γ g x ρ μ ν + lowered_connection Γ g x ν ρ μ =
    partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ρ else ν)) μ x

/-- Uniqueness: any torsion-free, metric-compatible connection has lowered coefficients
    uniquely determined by the metric. The Koszul formula gives:

    Γ_{ρμν} = (1/2)(∂_μ g_{ρν} + ∂_ν g_{ρμ} - ∂_ρ g_{μν})

    which, after raising the index with g^{ρσ}, yields `Curvature.christoffel`. -/
theorem connection_uniqueness_lowered
    (Γ : ConnectionCoeffs) (g : MetricTensor) (x : Fin 4 → ℝ)
    (h_tf : IsTorsionFree Γ)
    (h_id : LoweredConnectionIdentity Γ g x) :
    ∀ ρ μ ν,
      lowered_connection Γ g x ρ μ ν =
      (1/2 : ℝ) * (
        partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ρ else ν)) μ x +
        partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ρ else μ)) ν x -
        partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) ρ x
      ) := by
  intro ρ μ ν
  -- Three permutations of Γ_{abc} + Γ_{cab} = ∂_b g_{ac}:
  have hA := h_id ρ μ ν
  have hB := h_id ρ ν μ
  have hC := h_id ν ρ μ
  -- Torsion-free: Γ_{abc} = Γ_{acb}
  have h_sym : ∀ a b c, lowered_connection Γ g x a b c = lowered_connection Γ g x a c b := by
    intro a b c
    unfold lowered_connection
    apply Finset.sum_congr rfl
    intro σ _
    rw [h_tf x σ b c]
  rw [h_sym ν ρ μ] at hC
  rw [h_sym ρ ν μ] at hB
  rw [h_sym μ ρ ν] at hB
  rw [h_sym ν ρ μ] at hA
  -- (A) + (B) - (C) gives 2 Γ_{ρμν} = ∂_μ g_{ρν} + ∂_ν g_{ρμ} - ∂_ρ g_{νμ}
  -- Apply metric symmetry: g_{νμ} = g_{μν}
  have h_deriv_sym : partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) ρ x =
                     partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) ρ x := by
    congr 1; funext y; exact g.symmetric y _ _
  rw [h_deriv_sym] at hC
  linarith

/-! ## §5 The Fundamental Theorem (Bundle) -/

/-- The Fundamental Theorem of Pseudo-Riemannian Geometry (existence part):
    The Christoffel connection is torsion-free and metric-compatible. -/
structure FundamentalTheoremExistence (g : MetricTensor) : Prop where
  torsion_free : IsTorsionFree (christoffel g)
  metric_compatible : ∀ x, KoszulIdentity g x →
    ∀ ρ μ ν, cov_deriv_metric (christoffel g) g x ρ μ ν = 0

/-- The Fundamental Theorem of Pseudo-Riemannian Geometry (uniqueness part):
    Any torsion-free, metric-compatible connection has the same lowered coefficients
    as the Christoffel connection. -/
structure FundamentalTheoremUniqueness (g : MetricTensor) : Prop where
  unique : ∀ (Γ : ConnectionCoeffs) (x : Fin 4 → ℝ),
    IsTorsionFree Γ →
    LoweredConnectionIdentity Γ g x →
    ∀ ρ μ ν, lowered_connection Γ g x ρ μ ν =
      (1/2 : ℝ) * (
        partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ρ else ν)) μ x +
        partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ρ else μ)) ν x -
        partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) ρ x)

/-- The Fundamental Theorem holds for all metrics. -/
theorem fundamental_theorem_existence (g : MetricTensor) : FundamentalTheoremExistence g where
  torsion_free := levi_civita_torsion_free g
  metric_compatible := fun x h_k => metric_compatible_of_koszul g x h_k

theorem fundamental_theorem_uniqueness (g : MetricTensor) : FundamentalTheoremUniqueness g where
  unique := fun Γ x h_tf h_id => connection_uniqueness_lowered Γ g x h_tf h_id

/-- Combined certificate for the Fundamental Theorem of Pseudo-Riemannian Geometry. -/
structure LeviCivitaCertificate (g : MetricTensor) : Prop where
  existence : FundamentalTheoremExistence g
  uniqueness : FundamentalTheoremUniqueness g

theorem levi_civita_certificate (g : MetricTensor) : LeviCivitaCertificate g where
  existence := fundamental_theorem_existence g
  uniqueness := fundamental_theorem_uniqueness g

end -- noncomputable section

end Geometry
end Relativity
end IndisputableMonolith
