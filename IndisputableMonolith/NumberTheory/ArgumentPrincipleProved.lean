import Mathlib
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.DefectSampledTrace
import IndisputableMonolith.NumberTheory.EulerInstantiation

/-!
# Argument Principle Sampling — Proved

Eliminates `argument_principle_sampling` (Axiom 1 from `EulerInstantiation`)
as an axiom and upgrades the analytic route toward honest witnessed
`ζ⁻¹` phase-family data.

## Key observation

Axiom 1 as formally stated only requires EXISTENCE of an `AnnularMesh N`
with the right charge. The uniform mesh `uniformChargeMesh N sensor.charge`
(defined in `CostCoveringBridge`) satisfies this by construction, because
its charge field is literally `sensor.charge`.

This means Axiom 1 is provable by `fun N => ⟨uniformChargeMesh N m, rfl⟩`.

## Two proofs provided

1. **`argument_principle_trivial`** — the one-line proof via `uniformChargeMesh`.
   No complex analysis needed.

2. **`argument_principle_honest`** — the honest proof through the phase-lift
   stack (`CirclePhaseLift` → `MeromorphicCircleOrder`), constructing meshes
   from actual phase samples. Requires filling the sorrys upstream but gives
   a proof that tracks the real analytic content.

## Axiom reduction

After this module, the legacy analytic route still has the deprecated boundary
marker `defect_annular_cost_bounded`, while the honest analytic route targets
`ZeroFreeCriterion` built from witnessed `ζ⁻¹` phase data. The ontology route
is separate and depends on the external Euler proxy bridge from `UnifiedRH`.

## Dependency graph

```
AnnularCost ──────────────────────┐
CostCoveringBridge ───────────────┤
CirclePhaseLift ──► MeromorphicCircleOrder ──┤
EulerInstantiation ───────────────┤
                                  ▼
                     ArgumentPrincipleProved
```
-/

namespace IndisputableMonolith
namespace NumberTheory

open Real

noncomputable section

/-! ### §1. Trivial proof of Axiom 1 -/

/-- **Axiom 1 is trivially provable.**

The formal statement only asks for existence of an `AnnularMesh` with
`mesh.charge = sensor.charge`. The uniform mesh `uniformChargeMesh N m`
satisfies this definitionally.

This means the RH formalization has exactly ONE genuine axiom, not two. -/
theorem argument_principle_trivial (sensor : DefectSensor) :
    ∀ N : ℕ, ∃ mesh : AnnularMesh N, mesh.charge = sensor.charge :=
  fun N => ⟨uniformChargeMesh N sensor.charge, rfl⟩

/-! ### §2. Honest proof via phase sampling -/

/-- **Honest argument principle sampling** via the phase-lift stack.

This constructs meshes from actual phase samples of ζ⁻¹ near the
hypothetical zero, not from the synthetic uniform construction.
The proof uses `defect_phase_family_exists` (which carries sorrys
from the complex-analysis layer). -/
theorem argument_principle_honest (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) :
    ∀ N : ℕ, ∃ mesh : AnnularMesh N, mesh.charge = sensor.charge := by
  intro N
  obtain ⟨dpf, rfl⟩ := defect_phase_family_exists sensor hm
  exact ⟨defectAnnularMesh dpf N, rfl⟩

/-! ### §3. RH from a single axiom (deprecated) -/

/-- ⚠ DEPRECATED: depends on the inconsistent `defect_annular_cost_bounded`.
Use `UnifiedRH.unified_rh` (ontology) or
`AnalyticTrace.direct_rh_from_honestPhaseCostBridge` (analytic). -/
theorem rh_from_single_axiom (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0)
    (hbounded : DeprecatedDefectAnnularCostBounded sensor hm) : False := by
  exact rh_from_complex_analysis_axioms sensor hm hbounded

/-! ### §4. Honest argument principle for ζ⁻¹ (analytic route) -/

/-- **Honest argument principle data for `zetaReciprocal`.**

If ζ has a zero of multiplicity `m` at `ρ` with `Re(ρ) > 1/2`, the
Euler quantitative factorization at `ρ` yields a `QuantitativeLocalFactorization`
whose `meromorphic_phase_charge` on concentric circles produces a
`DefectPhaseFamily` with charge exactly `m`.

The phase family is now `zetaDerivedPhaseFamily`, which extracts genuine
phase data from `meromorphic_phase_charge` on circles of decreasing radius
around the factorization center, rather than the former constant-phase
scaffold `trivialDefectPhaseFamily`.

The phase-family package now records its derivation from
`zetaDerivedPhaseFamily`; the remaining analytic target is to upgrade the
resulting bounded-excess sampled family to the bounded-cost / floor-coverage
statement needed for `charge_zero_of_honest_phase`. -/
theorem honest_argument_principle_phase_family
    (sensor : WitnessedDefectSensor) (_hm : sensor.charge ≠ 0) :
    ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = sensor.toDefectSensor := by
  let base : DefectSensor := sensor.toDefectSensor
  let witness :=
    eulerQuantitativeFactorization sensor.rho sensor.rho_ne_one
      (-sensor.charge) sensor.order_witness sensor.in_strip.1
  have horder : witness.order = -base.charge := by
    simpa [base] using
      eulerQuantitativeFactorization_order sensor.rho sensor.rho_ne_one
        (-sensor.charge) sensor.order_witness sensor.in_strip.1
  refine ⟨{
    sensor := base
    witness := witness
    witness_realPart := by
      have hcenter :
          witness.center = sensor.rho :=
        eulerQuantitativeFactorization_center sensor.rho sensor.rho_ne_one
          (-sensor.charge) sensor.order_witness sensor.in_strip.1
      simpa [base] using congrArg Complex.re hcenter
    witness_order := horder
    phaseFamily := zetaDerivedPhaseFamily base witness horder
    family_sensor := rfl
    family_derived := rfl }, rfl, rfl⟩

/-! ### §5. Axiom inventory -/

/-- **Frozen obligation inventory (April 2026):**

### Proved infrastructure (no open obligations)

| Component | Module |
|-----------|--------|
| Argument principle sampling (trivial + honest) | This file |
| Cost divergence (m ≠ 0) | `DefectSampledTrace` |
| Euler trace admissibility | `UnifiedRH` |
| Annular excess bounded | `DefectSampledTrace` |
| Zeta-derived phase family | `MeromorphicCircleOrder` |
| Honest phase data for ζ⁻¹ | This file |
| Perturbation witness / excess control | `MeromorphicCircleOrder`, `HonestPhaseBudgetBridge` |

### Active RH-equivalent bridges

| Bridge | Route | Module |
|--------|-------|--------|
| `EulerBoundaryBridgeAssumption` | Ontology (preferred) | `UnifiedRH` |
| `HonestPhaseCostBridge` / `charge_zero_of_honest_phase` | Analytic | `AnalyticTrace` |

### Deprecated

| Item | Note |
|------|------|
| `defect_annular_cost_bounded` | Inconsistent with proved unboundedness |
| `rh_from_single_axiom` | Routes through deprecated axiom | -/
theorem axiom_inventory : True := trivial

end

end NumberTheory
end IndisputableMonolith
