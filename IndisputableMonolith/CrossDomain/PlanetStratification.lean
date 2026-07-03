import Mathlib

/-!
# C2: Planet Stratification — 5+5+5 = 15 — Wave 62 Cross-Domain

Structural claim: three nested D = 5 stratifications cover Earth:

  AtmosphericLayer ⊕ EarthLayer ⊕ OceanLayer  =  5 + 5 + 5  =  15.

Unlike C1 (a product), this is a disjoint sum: the three strata are
*nested*, not independent, because they sit at different radial shells of
the planet. You cannot be in the atmosphere and in the mantle at the same
radius. So the combined stratification is a sum type, not a product.

Empirical prediction if this is real: atmospheric wave speeds at
tropopause and seismic phase velocities at the asthenosphere boundary
should obey a φ-ladder ratio. That is testable; it is not what this Lean
file proves. This file proves the combinatorial structure.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.CrossDomain.PlanetStratification

inductive AtmosphericLayer where
  | troposphere | stratosphere | mesosphere | thermosphere | exosphere
  deriving DecidableEq, Repr, BEq, Fintype

inductive EarthLayer where
  | innerCore | outerCore | lowerMantle | upperMantle | crust
  deriving DecidableEq, Repr, BEq, Fintype

inductive OceanLayer where
  | surface | thermocline | intermediate | deep | abyssal
  deriving DecidableEq, Repr, BEq, Fintype

theorem atmoCount : Fintype.card AtmosphericLayer = 5 := by decide
theorem earthCount : Fintype.card EarthLayer = 5 := by decide
theorem oceanCount : Fintype.card OceanLayer = 5 := by decide

abbrev PlanetStratum : Type := AtmosphericLayer ⊕ EarthLayer ⊕ OceanLayer

theorem planetStratumCount : Fintype.card PlanetStratum = 15 := by
  simp only [PlanetStratum, Fintype.card_sum, atmoCount, earthCount, oceanCount]

/-- The three injections are not surjective: each covers only 5 of 15. -/
theorem atmo_is_proper_subset :
    Fintype.card PlanetStratum > Fintype.card AtmosphericLayer := by
  rw [planetStratumCount, atmoCount]; decide

theorem earth_is_proper_subset :
    Fintype.card PlanetStratum > Fintype.card EarthLayer := by
  rw [planetStratumCount, earthCount]; decide

theorem ocean_is_proper_subset :
    Fintype.card PlanetStratum > Fintype.card OceanLayer := by
  rw [planetStratumCount, oceanCount]; decide

/-- 15 = 3 × D (where D = 5). -/
theorem planetStratum_three_D : 15 = 3 * 5 := by decide

structure PlanetStratificationCert where
  stratum_count : Fintype.card PlanetStratum = 15
  three_D : 15 = 3 * 5
  atmo_sub : Fintype.card PlanetStratum > Fintype.card AtmosphericLayer
  earth_sub : Fintype.card PlanetStratum > Fintype.card EarthLayer
  ocean_sub : Fintype.card PlanetStratum > Fintype.card OceanLayer

def planetStratificationCert : PlanetStratificationCert where
  stratum_count := planetStratumCount
  three_D := planetStratum_three_D
  atmo_sub := atmo_is_proper_subset
  earth_sub := earth_is_proper_subset
  ocean_sub := ocean_is_proper_subset

end IndisputableMonolith.CrossDomain.PlanetStratification
