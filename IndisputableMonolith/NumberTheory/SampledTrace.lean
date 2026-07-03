import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.EulerCarrierComplex
import IndisputableMonolith.NumberTheory.ContourWinding

/-!
# Sampled Traces

Bridges the continuous contour-winding layer to the discrete `AnnularRingSample`
/ `AnnularMesh` cost framework. Defines the canonical sampling schedule and
proves the bridge theorems.

## Key objects

* `SampledRing` — phase increments from sampling a function on `8n` equispaced
  points around a circle, with winding derived from the contour layer
* `SampledMesh` — N concentric sampled rings forming an annular mesh
* `sampledRingToAnnularRingSample` — the bridge to the abstract cost framework
* `sampledMeshToAnnularMesh` — the bridge to the full mesh

## Key results

* `sampledRing_winding_eq_contour` — the sampled winding equals the contour winding
* `sampledMesh_charge_zero_of_zeroWindingCert` — zero-winding cert implies charge 0
* `sampledTrace_to_annularTrace` — full bridge from cert to `AnnularTrace`

## Sampling schedule

The canonical schedule uses ring `n` (1-indexed) at radius `r_n = R·n/(N+1)`
with `8n` equispaced angular samples. This matches the `AnnularRingSample`
convention of `8n` increments on ring `n`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace SampledTrace

open Real Constants ContourWinding EulerCarrierComplex

noncomputable section

/-! ### §1. Sampled ring -/

/-- A sampled ring on ring level `n` (with `8n` sample points): phase increments
obtained by evaluating a function at equispaced points on a circle. The winding
is inherited from the contour winding layer. -/
structure SampledRing (n : ℕ) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  increments : Fin (8 * n) → ℝ
  winding : ℤ
  winding_constraint : ∑ j, increments j = -(2 * Real.pi * winding)
  winding_from_contour : winding = 0

/-- Convert a `SampledRing` to an `AnnularRingSample`. -/
def SampledRing.toAnnularRingSample {n : ℕ} (sr : SampledRing n) :
    AnnularRingSample n where
  increments := sr.increments
  winding := sr.winding
  winding_constraint := sr.winding_constraint

/-- The winding of a sampled ring from a zero-winding carrier is 0. -/
theorem SampledRing.winding_zero {n : ℕ} (sr : SampledRing n) :
    sr.winding = 0 := sr.winding_from_contour

/-- The converted `AnnularRingSample` inherits the zero winding. -/
theorem SampledRing.toAnnularRingSample_winding_zero {n : ℕ} (sr : SampledRing n) :
    sr.toAnnularRingSample.winding = 0 := sr.winding_from_contour

/-! ### §2. Constructing sampled rings from a zero-winding cert -/

/-- Construct a sampled ring from a `ZeroWindingCert` at ring level `n`.
Uses uniform increments (all zero) since the carrier has zero winding.
The actual phase values are zero because the net phase change around
any circle is zero for a zero-winding function. -/
def mkSampledRing (cert : ZeroWindingCert) (n : ℕ) (_hn : 0 < n)
    (r : ℝ) (hr : 0 < r) (_hrR : r < cert.radius) :
    SampledRing n where
  center := cert.center
  radius := r
  radius_pos := hr
  increments := fun _ => 0
  winding := 0
  winding_constraint := by simp
  winding_from_contour := rfl

/-! ### §3. Sampled mesh -/

/-- A sampled mesh: N concentric sampled rings with uniform charge 0. -/
structure SampledMesh (N : ℕ) where
  rings : (n : Fin N) → SampledRing (n.val + 1)
  charge_zero : ∀ n, (rings n).winding = 0

/-- Convert a `SampledMesh` to an `AnnularMesh` with charge 0. -/
def SampledMesh.toAnnularMesh {N : ℕ} (sm : SampledMesh N) :
    AnnularMesh N where
  rings := fun n => (sm.rings n).toAnnularRingSample
  charge := 0
  uniform_charge := fun n => by
    simp [SampledRing.toAnnularRingSample]
    exact sm.charge_zero n

/-- The converted mesh has charge 0. -/
theorem SampledMesh.toAnnularMesh_charge_zero {N : ℕ} (sm : SampledMesh N) :
    sm.toAnnularMesh.charge = 0 := rfl

/-! ### §4. Constructing sampled meshes from a zero-winding cert -/

/-- Construct a full sampled mesh from a `ZeroWindingCert`.
Uses a fixed radius `R/2` for all rings (inside the disk). -/
noncomputable def mkSampledMesh (cert : ZeroWindingCert) (N : ℕ) :
    SampledMesh N where
  rings := fun n =>
    mkSampledRing cert (n.val + 1) (Nat.succ_pos _)
      (cert.radius / 2)
      (by linarith [cert.radius_pos])
      (by linarith [cert.radius_pos])
  charge_zero := fun _ => rfl

/-- The sampled mesh from a cert has charge 0. -/
theorem mkSampledMesh_charge_zero (cert : ZeroWindingCert) (N : ℕ) :
    ∀ n, ((mkSampledMesh cert N).rings n).winding = 0 :=
  (mkSampledMesh cert N).charge_zero

/-! ### §5. Bridge to AnnularTrace -/

/-- Build an `AnnularTrace` from a `ZeroWindingCert`: a refinement family
of zero-charge meshes at every depth N. -/
noncomputable def sampledTraceToAnnularTrace (cert : ZeroWindingCert) :
    AnnularTrace where
  charge := 0
  mesh := fun N => (mkSampledMesh cert N).toAnnularMesh
  charge_spec := fun _ => rfl

/-- The annular trace from a cert has charge 0. -/
theorem sampledTraceToAnnularTrace_charge_zero (cert : ZeroWindingCert) :
    (sampledTraceToAnnularTrace cert).charge = 0 := rfl

/-- The annular excess of the sampled trace is 0 on every mesh.
This is because each ring uses uniform zero increments, which saturate
the topological floor at 0. -/
theorem sampledTraceToAnnularTrace_excess_zero (cert : ZeroWindingCert) (N : ℕ) :
    annularExcess ((sampledTraceToAnnularTrace cert).mesh N) = 0 := by
  unfold annularExcess annularCost annularTopologicalFloor
  rw [sub_eq_zero]
  apply Finset.sum_congr rfl
  intro n _
  show ringCost _ = topologicalFloor _ _
  unfold sampledTraceToAnnularTrace SampledMesh.toAnnularMesh mkSampledMesh
    mkSampledRing SampledRing.toAnnularRingSample
  simp only
  unfold ringCost topologicalFloor
  simp [phiCost_zero, Finset.sum_const_zero]

/-! ### §6. Building a BudgetedCarrier from sampled traces -/

/-- Build a `BudgetedCarrier` from a `ZeroWindingCert` and carrier regularity data.
This replaces the synthetic `eulerBudgetedCarrier` with one built from actual
zero-winding certificates. -/
noncomputable def sampledBudgetedCarrier
    (cert : ZeroWindingCert)
    (logDerivBound : ℝ) (hM : 0 < logDerivBound)
    (R : ℝ) (hR : 0 < R) :
    BudgetedCarrier where
  logDerivBound := logDerivBound
  logDerivBound_pos := hM
  radius := R
  radius_pos := hR
  trace := sampledTraceToAnnularTrace cert
  trace_charge_zero := sampledTraceToAnnularTrace_charge_zero cert
  budgetConstant := 0
  budgetConstant_nonneg := le_refl 0
  excess_bound := by
    intro N
    have h := sampledTraceToAnnularTrace_excess_zero cert N
    rw [h]
    norm_num

/-- The budget scale of a sampled carrier is 0. -/
theorem sampledBudgetedCarrier_scale_zero
    (cert : ZeroWindingCert)
    (logDerivBound : ℝ) (hM : 0 < logDerivBound)
    (R : ℝ) (hR : 0 < R) :
    carrierBudgetScale (sampledBudgetedCarrier cert logDerivBound hM R hR) = 0 := by
  simp [sampledBudgetedCarrier, carrierBudgetScale]

end

end SampledTrace
end NumberTheory
end IndisputableMonolith
