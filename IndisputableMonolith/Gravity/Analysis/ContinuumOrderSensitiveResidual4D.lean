import Mathlib
import IndisputableMonolith.Loom.CertificateData
import IndisputableMonolith.Gravity.Analysis.OrderSensitiveHistoryResponse4D
import IndisputableMonolith.Gravity.Analysis.MetricEdgeImage4D

/-!
# Continuum promotion of the order-sensitive residual

Campaign G4/G5. Replaces finite Boolean non-membership in
`MetricEdgeImage` with a normalized-separation trichotomy under a
shape-regular refinement family.

## Trichotomy (frozen)

For a refinement level `n` with response difference `Δ_n` and metric image
`M_n`:

* **Survive:** positive liminf of normalized distance to the metric image
* **Metric collapse:** normalized distance tends to 0 while the response
  norm does not
* **Lattice washout:** response norm tends to 0

## What is proved here

* The finite residual is outside `MetricEdgeImage` (imported).
* A shape-regular refinement family interface is named.
* Continuum survival / collapse / washout for the certificate pair are
  recorded as OPEN residual Props (uninhabited). The geometric mesh
  Tendsto baseline (Arc 2 step 9) is required before any terminal is claimed.
* Continuum promotion is explicitly not earned from the finite theorem.

## Honesty

* THEOREM: finite outside-image; status flag false.
* OPEN: inhabiting any continuum terminal for the discovery pair.
* Forbidden: promoting the finite Boolean result to continuum novelty.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ContinuumOrderSensitiveResidual4D

open OrderSensitiveHistoryResponse4D
open MetricEdgeImage4D
open IndisputableMonolith.Loom.Certificate
open BigOperators

/-- Edge-field squared Frobenius norm on the patch. -/
noncomputable def edgeNorm (F : Fin 16 → Fin 16 → ℝ) : ℝ :=
  ∑ i : Fin 16, ∑ j : Fin 16, (F i j) ^ 2

/-- Shape-regular refinement family interface. -/
structure RefinementFamily where
  responseDiff : ℕ → Fin 16 → Fin 16 → ℝ
  metricProj : ℕ → (Fin 16 → Fin 16 → ℝ) → Fin 16 → Fin 16 → ℝ
  levelNorm : ℕ → ℝ
  shapeRegular : ∀ n, 0 < levelNorm n

/-- Normalized distance from a response difference to its metric projection. -/
noncomputable def normalizedSeparation (F : RefinementFamily) (n : ℕ) : ℝ :=
  edgeNorm (fun i j =>
      F.responseDiff n i j - F.metricProj n (F.responseDiff n) i j)
    / edgeNorm (F.responseDiff n)

/-- Continuum terminal: surviving new sector. -/
def Survives (F : RefinementFamily) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ᶠ n in Filter.atTop, ε ≤ normalizedSeparation F n

/-- Continuum terminal: metric collapse. -/
def MetricCollapse (F : RefinementFamily) : Prop :=
  Filter.Tendsto (normalizedSeparation F) Filter.atTop (nhds 0) ∧
    ¬ Filter.Tendsto (fun n => edgeNorm (F.responseDiff n)) Filter.atTop (nhds 0)

/-- Continuum terminal: lattice washout. -/
def LatticeWashout (F : RefinementFamily) : Prop :=
  Filter.Tendsto (fun n => edgeNorm (F.responseDiff n)) Filter.atTop (nhds 0)

/-- Finite stage already outside the metric image (imported G3). -/
theorem finite_outside_metric_image :
    ¬ MetricEdgeImage (responseDiff cfgA cfgB) :=
  responseDiff_cfgAB_not_in_MetricEdgeImage

/-- Collapse and washout are incompatible by definition. -/
theorem collapse_not_washout (F : RefinementFamily)
    (hC : MetricCollapse F) (hW : LatticeWashout F) : False :=
  hC.2 hW

/-- **OPEN residual.** Continuum survival of the certificate residual. -/
def ContinuumSurvivalOpen : Prop :=
  ∃ F : RefinementFamily, Survives F

/-- **OPEN residual.** Metric collapse of the certificate residual. -/
def ContinuumMetricCollapseOpen : Prop :=
  ∃ F : RefinementFamily, MetricCollapse F

/-- **OPEN residual.** Lattice washout of the certificate residual. -/
def ContinuumWashoutOpen : Prop :=
  ∃ F : RefinementFamily, LatticeWashout F

/-- Honest status flag: continuum promotion not yet earned. -/
def continuumPromotionEarned : Bool := false

theorem continuumPromotionEarned_eq :
    continuumPromotionEarned = false := rfl

/-- Methodological wall: the finite outside-image theorem does not flip the
continuum-promotion flag. -/
theorem finite_exclusion_does_not_earn_promotion :
    (¬ MetricEdgeImage (responseDiff cfgA cfgB)) →
      continuumPromotionEarned = false :=
  fun _ => continuumPromotionEarned_eq

end ContinuumOrderSensitiveResidual4D
end Analysis
end Gravity
end IndisputableMonolith
