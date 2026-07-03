import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.EulerCarrierComplex
import IndisputableMonolith.NumberTheory.ContourWinding
import IndisputableMonolith.NumberTheory.SampledTrace
import IndisputableMonolith.NumberTheory.EulerInstantiation
import IndisputableMonolith.NumberTheory.MeromorphicCircleOrder
import IndisputableMonolith.NumberTheory.ArgumentPrincipleProved
import IndisputableMonolith.NumberTheory.HonestPhaseBudgetBridge
import IndisputableMonolith.NumberTheory.ZeroCompositionInterface
import IndisputableMonolith.Unification.UnifiedRH

/-!
# Analytic Trace Interface — Axiom-Free Version

Assembles the full RH bridge from the analytic trace infrastructure.

## Former axioms — now eliminated

The previous version of this module contained two axioms:
* `zeroWindingOfHolNonvanishing` — replaced by `EulerCarrierComplex.contourWinding`
  (which derives zero winding from holomorphy + nonvanishing)
* `argument_principle_forces_charge_zero` — replaced by the floor-coverage
  iff theorem `eulerSampledFloorCovered_iff_charge_zero`

## Current axiom status

Two routes to RH exist:

1. **Ontology route** (`UnifiedRH.lean`): external bridge hypothesis
   `EulerBoundaryBridgeAssumption`.
   Preferred path. See `UnifiedRH.unified_rh`.

2. **Pure analytic route**: targets a `ZeroFreeCriterion` from honest ζ⁻¹ phase
   data. `defect_annular_cost_bounded` in `EulerInstantiation.lean` remains as
   a deprecated RH-equivalent boundary marker.

## This module's contribution

Carrier-side infrastructure (axiom-free):
* The sampled Euler package has budget 0 (from zero-winding cert)
* Floor coverage holds iff charge = 0 (proved, not assumed)
* Any sensor with charge ≠ 0 cannot be floor-covered (proved)
* Direct RH from `ZeroFreeCriterion` (analytic route target)
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace AnalyticTrace

open Real Constants Cost
open EulerCarrierComplex ContourWinding SampledTrace

/-! ### §1. The sampled Euler package -/

/-- The sampled Euler `CostCoveringPackage` for any σ₀ > 1/2.
Built from the zero-winding certificate, not from a synthetic zero-charge trace. -/
noncomputable def eulerSampledCoveringPackage (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    CostCoveringPackage :=
  eulerSampledPackage σ₀ hσ

/-! ### §2. Floor coverage iff charge = 0 (proved, not axiomatized) -/

/-- The defect topological floor is covered by the sampled Euler package
if and only if the sensor charge is 0. -/
theorem floorCovered_iff_charge_zero (σ₀ : ℝ) (hσ : 1/2 < σ₀)
    (sensor : DefectSensor) :
    DefectTopologicalFloorCovered (eulerSampledCoveringPackage σ₀ hσ) sensor ↔
      sensor.charge = 0 :=
  eulerSampledFloorCovered_iff_charge_zero σ₀ hσ sensor

/-! ### §3. Carrier-side RH obstruction (no axioms) -/

/-- A DefectSensor with charge ≠ 0 can never have its floor covered by
the sampled Euler package. The defect floor grows as m² log N while the
carrier budget is 0. -/
theorem carrier_side_obstruction (sensor : DefectSensor) (hm : sensor.charge ≠ 0) :
    ¬ DefectTopologicalFloorCovered
        (eulerSampledCoveringPackage sensor.realPart sensor.in_strip.1) sensor :=
  not_DefectTopologicalFloorCovered _ sensor hm

/-- If floor coverage holds for the sampled package, the charge must be 0. -/
theorem charge_zero_of_covered (σ₀ : ℝ) (hσ : 1/2 < σ₀)
    (sensor : DefectSensor)
    (hcover : DefectTopologicalFloorCovered (eulerSampledCoveringPackage σ₀ hσ) sensor) :
    sensor.charge = 0 :=
  (floorCovered_iff_charge_zero σ₀ hσ sensor).mp hcover

/-! ### §4. Zero-free criterion (analytic route target) -/

/-- The zero-free criterion for the pure analytic route.

This structure packages the honest analytic target: witnessed ζ⁻¹ defect data
in the strip gives an honest phase-family package, and analytic estimates then
force the corresponding defect charge to vanish.

**Field status (April 2026):**
- `logDeriv_bounded_on_strip`: **PROVED** (`carrierDerivBound_pos`).
- `carrier_nonvanishing_on_strip`: **PROVED** (`carrier_nonvanishing`).
- `honest_phase_family`: **PROVED** via `honest_argument_principle_phase_family`,
  now using `zetaDerivedPhaseFamily` (genuine phase data from meromorphic
  factorization) rather than the former `trivialDefectPhaseFamily` scaffold.
- `charge_zero_of_honest_phase`: **NARROWED TARGET**. Honest phase data now
  comes with a canonical perturbation witness, and the present sampled family
  sits exactly on the topological floor (`annularExcess = 0`). The remaining
  content is to upgrade the honest sampled family to bounded total cost / floor
  coverage, forcing charge = 0.

This replaces the deprecated `defect_annular_cost_bounded` as the proper
analytic-route target. -/
structure ZeroFreeCriterion where
  logDeriv_bounded_on_strip :
    ∀ σ, 1/2 < σ → 0 < carrierDerivBound σ
  carrier_nonvanishing_on_strip :
    ∀ σ, 1/2 < σ → carrierValue σ ≠ 0
  honest_phase_family :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 →
      ∃ zfd : ZetaPhaseFamilyData,
        zfd.sensor = sensor.toDefectSensor ∧
          zfd.phaseFamily.sensor = sensor.toDefectSensor
  charge_zero_of_honest_phase :
    ∀ (sensor : WitnessedDefectSensor),
      (∃ zfd : ZetaPhaseFamilyData,
        zfd.sensor = sensor.toDefectSensor ∧
          zfd.phaseFamily.sensor = sensor.toDefectSensor) →
        sensor.charge = 0

/-- A `ZeroFreeCriterion` gives the RH directly. -/
theorem rh_from_zero_free_criterion (zfc : ZeroFreeCriterion) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False := by
  intro sensor hm
  obtain ⟨zfd, hzfd, hfamily⟩ := zfc.honest_phase_family sensor hm
  have hzero : sensor.charge = 0 :=
    zfc.charge_zero_of_honest_phase sensor ⟨zfd, hzfd, hfamily⟩
  exact hm hzero

/-! ### §4b. Vector C insertion point -/

/-- A minimal Euler/Hadamard-side bridge for the honest analytic route.

The current code already supplies perturbation control, and the present honest
sampled family has exact zero excess. The remaining bridge is to show that the
honest sampled family also has bounded total annular cost. Once that is known,
the general defect-cost theorem forces zero charge immediately. -/
structure HonestPhaseCostBridge where
  cost_bounded_of_honest_phase :
    ∀ (sensor : WitnessedDefectSensor) (zfd : ZetaPhaseFamilyData),
      zfd.sensor = sensor.toDefectSensor →
        RealizedDefectAnnularCostBounded (zfd.phaseFamily.toSampledFamily)

/-- Any honest-phase cost bridge discharges the sole remaining analytic
charge-zero target. -/
theorem charge_zero_of_honest_phase_of_costBridge
    (hb : HonestPhaseCostBridge)
    (sensor : WitnessedDefectSensor)
    (hzfd : ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = sensor.toDefectSensor) :
    sensor.charge = 0 := by
  rcases hzfd with ⟨zfd, hzsensor, _hzfamily⟩
  have hcost : RealizedDefectAnnularCostBounded (zfd.phaseFamily.toSampledFamily) :=
    hb.cost_bounded_of_honest_phase sensor zfd hzsensor
  have hzero_sensor : zfd.sensor.charge = 0 :=
    honestPhaseFamily_charge_zero_of_costBounded zfd hcost
  have hzero_base : sensor.toDefectSensor.charge = 0 := by
    simpa [hzsensor] using hzero_sensor
  simpa using hzero_base

/-- Therefore a bounded-cost bridge for honest phase data already yields a full
analytic `ZeroFreeCriterion`, independently of Vector C. -/
noncomputable def zeroFreeCriterion_of_honestPhaseCostBridge
    (hb : HonestPhaseCostBridge) :
    ZeroFreeCriterion where
  logDeriv_bounded_on_strip := fun _ hσ => carrierDerivBound_pos hσ
  carrier_nonvanishing_on_strip := fun _ hσ => carrier_nonvanishing hσ
  honest_phase_family := honest_argument_principle_phase_family
  charge_zero_of_honest_phase := charge_zero_of_honest_phase_of_costBridge hb

/-- Consequently any honest-phase bounded-cost bridge proves RH through the
existing analytic route. -/
theorem direct_rh_from_honestPhaseCostBridge (hb : HonestPhaseCostBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  rh_from_zero_free_criterion (zeroFreeCriterion_of_honestPhaseCostBridge hb)

/-! ### §4b'. Route C bottleneck — exact current analytic state -/

/-- Honest zeta phase data already has bounded excess, but bounded total cost
is equivalent to zero charge.  This records the exact Route C bottleneck:
the perturbative/excess estimate is complete; the missing analytic content is
the upgrade from bounded excess to zero charge (or an equivalent admissibility
principle). -/
theorem honestPhase_routeC_bottleneck (zfd : ZetaPhaseFamilyData) :
    RealizedDefectAnnularExcessBounded (zfd.phaseFamily.toSampledFamily) ∧
      (RealizedDefectAnnularCostBounded (zfd.phaseFamily.toSampledFamily) ↔
        zfd.sensor.charge = 0) :=
  ⟨honestPhaseFamily_excess_bounded zfd,
    honestPhaseFamily_cost_bounded_iff_charge_zero zfd⟩

/-- A direct charge-zero bridge for honest zeta phase data.  This is weaker
and cleaner than asking for bounded total cost: it states exactly the charge
conclusion needed by the analytic route. -/
structure HonestPhaseChargeZeroBridge where
  charge_zero_of_honest_phase :
    ∀ zfd : ZetaPhaseFamilyData, zfd.sensor.charge = 0

/-- A direct honest-phase charge-zero bridge discharges the `ZeroFreeCriterion`
charge-zero field. -/
theorem charge_zero_of_honest_phase_of_chargeZeroBridge
    (hb : HonestPhaseChargeZeroBridge)
    (sensor : WitnessedDefectSensor)
    (hzfd : ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = sensor.toDefectSensor) :
    sensor.charge = 0 := by
  rcases hzfd with ⟨zfd, hzsensor, _hzfamily⟩
  have hz : zfd.sensor.charge = 0 := hb.charge_zero_of_honest_phase zfd
  have hs : sensor.toDefectSensor.charge = 0 := by
    simpa [hzsensor] using hz
  simpa using hs

/-- A direct charge-zero bridge gives a full `ZeroFreeCriterion`. -/
noncomputable def zeroFreeCriterion_of_honestPhaseChargeZeroBridge
    (hb : HonestPhaseChargeZeroBridge) :
    ZeroFreeCriterion where
  logDeriv_bounded_on_strip := fun _ hσ => carrierDerivBound_pos hσ
  carrier_nonvanishing_on_strip := fun _ hσ => carrier_nonvanishing hσ
  honest_phase_family := honest_argument_principle_phase_family
  charge_zero_of_honest_phase :=
    charge_zero_of_honest_phase_of_chargeZeroBridge hb

/-- Any direct honest-phase charge-zero bridge proves the analytic RH core. -/
theorem direct_rh_from_honestPhaseChargeZeroBridge
    (hb : HonestPhaseChargeZeroBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  rh_from_zero_free_criterion
    (zeroFreeCriterion_of_honestPhaseChargeZeroBridge hb)

/-! ### §4c. Vector C insertion point -/

/-- A successful Vector C bridge is exactly a mechanism that turns honest
zeta-derived phase data into a `ZeroCompositionWitness` for the witnessed zero.

Once this structure is instantiated, the existing analytic RH route closes
without any further changes to the `ZeroFreeCriterion` contract. -/
structure VectorCChargeZeroBridge where
  witness_of_honest_phase :
    ∀ (sensor : WitnessedDefectSensor),
      (∃ zfd : ZetaPhaseFamilyData,
        zfd.sensor = sensor.toDefectSensor ∧
          zfd.phaseFamily.sensor = sensor.toDefectSensor) →
        ZeroCompositionWitness sensor.rho

/-- Any Vector C bridge discharges the sole open analytic target:
`charge_zero_of_honest_phase`. -/
theorem charge_zero_of_honest_phase_of_vectorC
    (vc : VectorCChargeZeroBridge)
    (sensor : WitnessedDefectSensor)
    (hzfd : ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = sensor.toDefectSensor) :
    sensor.charge = 0 := by
  have hline : OnCriticalLine sensor.rho :=
    zeroCompositionWitness_forces_on_critical_line
      (vc.witness_of_honest_phase sensor hzfd)
  have hcontr : False := by
    have hstrip : 1 / 2 < sensor.rho.re := sensor.in_strip.1
    have hre : sensor.rho.re = 1 / 2 := hline
    linarith
  exact False.elim hcontr

/-- A successful Vector C bridge upgrades the proved Euler-carrier and honest
phase-family infrastructure into a complete `ZeroFreeCriterion`. -/
noncomputable def zeroFreeCriterion_of_vectorC
    (vc : VectorCChargeZeroBridge) :
    ZeroFreeCriterion where
  logDeriv_bounded_on_strip := fun _ hσ => carrierDerivBound_pos hσ
  carrier_nonvanishing_on_strip := fun _ hσ => carrier_nonvanishing hσ
  honest_phase_family := honest_argument_principle_phase_family
  charge_zero_of_honest_phase := charge_zero_of_honest_phase_of_vectorC vc

/-- Therefore any successful Vector C bridge proves RH via the existing
analytic route. -/
theorem direct_rh_from_vectorC_bridge (vc : VectorCChargeZeroBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  rh_from_zero_free_criterion (zeroFreeCriterion_of_vectorC vc)

/-! ### §5. Full RH from complex-analysis axioms (legacy path)

**WARNING**: The theorems below depend on the deprecated axiom
`defect_annular_cost_bounded` which is logically inconsistent with proved
results. They are retained only as the legacy reference path. The preferred
routes are:
- Ontology: `UnifiedRH.unified_rh` (external bridge hypothesis)
- Analytic: `ZeroFreeCriterion` via honest ζ⁻¹ phase data (§4 above) -/

/-- **The Riemann Hypothesis (legacy analytic route).**

⚠ DEPRECATED: depends on `defect_annular_cost_bounded`.
For the preferred route, see `UnifiedRH.unified_rh` (ontology) or
`direct_rh_from_zero_free_criterion` (analytic). -/
theorem analytic_rh (sensor : DefectSensor) (hm : sensor.charge ≠ 0)
    (hbounded : DeprecatedDefectAnnularCostBounded sensor hm) :
    False :=
  rh_from_complex_analysis_axioms sensor hm hbounded

/-! ### §5. Direct RH from zero-free criterion (analytic route target) -/

/-- **Direct RH from a zero-free criterion.**

The honest analytic route targets a `ZeroFreeCriterion` (§4 above) which
packages bounded log-derivative + carrier nonvanishing + honest phase-family
data for witnessed zeros. Once realized, this gives RH without the cost
framework contradiction. -/
theorem direct_rh_from_zero_free_criterion (zfc : ZeroFreeCriterion) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  rh_from_zero_free_criterion zfc

/-! ### §6. Canonical frontier inventory -/

/-- **Architecture summary (April 2026, inventory frozen):**

### Classification of open obligations

**ACTIVE** (on critical path to unconditional RH):

| Item | Kind | Module | Route |
|------|------|--------|-------|
| `EulerBoundaryBridgeAssumption` | explicit hypothesis | `UnifiedRH` | Ontology (preferred) |
| `HonestPhaseCostBridge` | structure | `AnalyticTrace` | Analytic |
| `charge_zero_of_honest_phase` | field in `ZeroFreeCriterion` | `AnalyticTrace` | Analytic |

Both active bridges are RH-equivalent:
- `EBBA_iff_rh` : `EulerBoundaryBridgeAssumption ↔ (∀ sensor, sensor.charge ≠ 0 → False)`
- `HonestPhaseCostBridge_iff_rh` : `HonestPhaseCostBridge ↔ (∀ sensor, sensor.charge = 0)`

**ALTERNATE** (valid but not primary):

| Item | Kind | Module | Note |
|------|------|--------|------|
| `VectorCChargeZeroBridge` | structure | `AnalyticTrace` | Requires extra input (`VectorCSymmetryOnlyNoGo`) |
| `CompositionClosureHypothesis` | structure | `CompositionDivergence` | Separate conditional certificate |

**DEPRECATED** (inconsistent or routed through inconsistent axiom):

| Item | Kind | Module |
|------|------|--------|
| `defect_annular_cost_bounded` | `axiom` | `EulerInstantiation` |
| `analytic_rh` | theorem | `AnalyticTrace` |
| `rh_chain_summary_legacy` | theorem | `AnalyticTrace` |
| `rh_from_single_axiom` | theorem | `ArgumentPrincipleProved` |

### Ontology route (preferred, single bridge hypothesis)
1. Every sensor has admissible Euler trace. **Proved.**
2. Nonzero charge forces cost divergence. **Proved.**
3. Collapse-to-proxy transport bridge. **`EulerBoundaryBridgeAssumption` (RH-equivalent).**
4. No nonzero-charge sensor exists. **Proved from 1+2+3.**

### Pure analytic route
1. Euler carrier convergent, nonvanishing, bounded log-derivative. **Proved.**
2. Floor coverage ↔ charge = 0. **Proved.**
3. Honest witnessed ζ⁻¹ phase data → `ZetaPhaseFamilyData`. **Proved.**
4. Honest phase data gives perturbation control and exact zero excess. **Proved.**
5. Bounded total cost → charge = 0. **`HonestPhaseCostBridge` (RH-equivalent).** -/
theorem rh_frontier_inventory : True := trivial

/-- ⚠ DEPRECATED: routes through the inconsistent `defect_annular_cost_bounded`.
Use `unified_rh` (ontology) or `direct_rh_from_honestPhaseCostBridge` (analytic). -/
theorem rh_chain_summary_legacy :
    (∀ (sensor : DefectSensor) (hm : sensor.charge ≠ 0),
      DeprecatedDefectAnnularCostBounded sensor hm) →
    ∀ (sensor : DefectSensor), sensor.charge ≠ 0 → False :=
  fun hbounded sensor hm => analytic_rh sensor hm (hbounded sensor hm)

/-! ### §7. Cross-route connection and RH-equivalence

The ontology route (`EulerBoundaryBridgeAssumption`) and the analytic route
(`HonestPhaseCostBridge`) are both RH-equivalent. The ontology route is
strictly stronger: it works for all `DefectSensor`s (abstract), while the
analytic route covers `WitnessedDefectSensor`s (actual zeros of ζ).

Closing EBBA immediately supplies HonestPhaseCostBridge, ZeroFreeCriterion,
and all downstream analytic certificates. -/

/-- RH (for witnessed sensors) implies `HonestPhaseCostBridge`. If every
witnessed sensor has charge 0, then every honest sampled family has
bounded cost because zero-charge families have zero topological floor. -/
theorem HonestPhaseCostBridge_of_rh
    (hrh : ∀ sensor : WitnessedDefectSensor, sensor.charge = 0) :
    HonestPhaseCostBridge where
  cost_bounded_of_honest_phase := by
    intro sensor zfd hzsensor
    have hcharge_sensor : sensor.charge = 0 := hrh sensor
    have hcharge_ds : zfd.sensor.charge = 0 := by
      simpa [hzsensor] using hcharge_sensor
    have hcharge_fam : (zfd.phaseFamily.toSampledFamily).sensor.charge = 0 := by
      simpa [DefectPhaseFamily.toSampledFamily, zfd.family_sensor] using hcharge_ds
    exact realizedDefectCostBounded_of_charge_zero_and_excessBounded
      (zfd.phaseFamily.toSampledFamily) hcharge_fam
      (honestPhaseFamily_excess_bounded zfd)

/-- `HonestPhaseCostBridge` is logically equivalent to RH (for witnessed
sensors).

This theorem makes machine-checkable the observation that the bounded-cost
bridge is not weaker than RH — it IS RH expressed through the sampled-cost
framework. The proof uses `not_realizedDefectAnnularCostBounded` (which
shows bounded cost is impossible for nonzero charge) for the forward
direction, and zero-charge bounded-cost for the backward direction. -/
theorem HonestPhaseCostBridge_iff_rh :
    HonestPhaseCostBridge ↔
      (∀ sensor : WitnessedDefectSensor, sensor.charge = 0) :=
  ⟨fun hb sensor => by
    by_contra hm
    exact direct_rh_from_honestPhaseCostBridge hb sensor hm,
   HonestPhaseCostBridge_of_rh⟩

/-! ### §8. Cross-route connection: ontology → analytic -/

/-- The ontology bridge immediately supplies the honest-phase cost bridge.
This proves closing EBBA closes ALL active routes simultaneously. -/
theorem honestPhaseCostBridge_of_EBBA
    (bridge : Unification.UnifiedRH.EulerBoundaryBridgeAssumption) :
    HonestPhaseCostBridge :=
  HonestPhaseCostBridge_of_rh (fun sensor => by
    by_contra hm
    exact Unification.UnifiedRH.unified_rh bridge sensor.toDefectSensor (by simpa using hm))

/-- The ontology bridge also supplies a complete `ZeroFreeCriterion`. -/
noncomputable def zeroFreeCriterion_of_EBBA
    (bridge : Unification.UnifiedRH.EulerBoundaryBridgeAssumption) :
    ZeroFreeCriterion :=
  zeroFreeCriterion_of_honestPhaseCostBridge (honestPhaseCostBridge_of_EBBA bridge)

/-- Direct witnessed-sensor RH from the ontology bridge through the analytic route. -/
theorem direct_rh_from_EBBA_via_analytic
    (bridge : Unification.UnifiedRH.EulerBoundaryBridgeAssumption) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  rh_from_zero_free_criterion (zeroFreeCriterion_of_EBBA bridge)

end AnalyticTrace
end NumberTheory
end IndisputableMonolith
