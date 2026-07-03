import Mathlib
import IndisputableMonolith.Foundation.RSCoupledAxis
import IndisputableMonolith.Physics.AtmosphericPhysicsFromRS
import IndisputableMonolith.Physics.GeophysicsFromRS
import IndisputableMonolith.Physics.OceanographyFromRS

/-!
# C2: Planetary 15-Stratum Direct Sum

The planet carries three independent 5-strata stacks:

* atmosphere,
* solid Earth,
* ocean.

This is an RS disjoint sum, not a tensor product. A physical parcel belongs
to one stratum in one stack; the three stacks add to 15 = 3 x 5.

The wave-speed phi-ratio prediction remains empirical. This module only proves
the finite structural claim.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Physics
namespace PlanetStrataC2

open Foundation.RSCoupledAxis
open AtmosphericPhysicsFromRS
open GeophysicsFromRS
open OceanographyFromRS

def atmosphereAxis : CoupledAxis 5 where
  Ix := AtmosphericLayer
  finite := inferInstance
  card_eq := atmosphericLayerCount
  primitive := RSPrimitive.phiLadder

def earthAxis : CoupledAxis 5 where
  Ix := EarthLayer
  finite := inferInstance
  card_eq := earthLayerCount
  primitive := RSPrimitive.jCost

def oceanAxis : CoupledAxis 5 where
  Ix := OceanLayer
  finite := inferInstance
  card_eq := oceanLayerCount
  primitive := RSPrimitive.sigmaCharge

def planetStrataSum : RSDisjointSum3 5 where
  axis1 := atmosphereAxis
  axis2 := earthAxis
  axis3 := oceanAxis
  indep12 := by simp [independent, atmosphereAxis, earthAxis]
  indep13 := by simp [independent, atmosphereAxis, oceanAxis]
  indep23 := by simp [independent, earthAxis, oceanAxis]

theorem planet_strata_total_15 :
    Fintype.card AtmosphericLayer + Fintype.card EarthLayer +
      Fintype.card OceanLayer = 15 := by
  rw [atmosphericLayerCount, earthLayerCount, oceanLayerCount]

theorem planet_strata_disjoint_sum_15 :
    @Fintype.card planetStrataSum.axis1.Ix planetStrataSum.axis1.finite +
      @Fintype.card planetStrataSum.axis2.Ix planetStrataSum.axis2.finite +
      @Fintype.card planetStrataSum.axis3.Ix planetStrataSum.axis3.finite = 15 := by
  rw [disjoint_sum_card planetStrataSum]

structure PlanetStrataCert where
  atmospheric_count : Fintype.card AtmosphericLayer = 5
  earth_count : Fintype.card EarthLayer = 5
  ocean_count : Fintype.card OceanLayer = 5
  total_15 : Fintype.card AtmosphericLayer + Fintype.card EarthLayer +
    Fintype.card OceanLayer = 15
  rs_sum_15 :
    @Fintype.card planetStrataSum.axis1.Ix planetStrataSum.axis1.finite +
      @Fintype.card planetStrataSum.axis2.Ix planetStrataSum.axis2.finite +
      @Fintype.card planetStrataSum.axis3.Ix planetStrataSum.axis3.finite = 15

def planetStrataCert : PlanetStrataCert where
  atmospheric_count := atmosphericLayerCount
  earth_count := earthLayerCount
  ocean_count := oceanLayerCount
  total_15 := planet_strata_total_15
  rs_sum_15 := planet_strata_disjoint_sum_15

end PlanetStrataC2
end Physics
end IndisputableMonolith
