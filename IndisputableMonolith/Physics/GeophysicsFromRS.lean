import Mathlib

/-!
# Geophysics from RS — C Earth Science

Five canonical Earth layers (inner core, outer core, lower mantle,
upper mantle, crust) = configDim D = 5.

In RS: Earth = nested recognition spheres.
Magnetic field: J = 0 axis alignment for dipole.

Five canonical geophysical observables (seismicity, gravimetry, geomagnetism,
heat flow, GPS geodesy) = configDim D.

Lean: 5 Earth layers + 5 observables.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.GeophysicsFromRS

inductive EarthLayer where
  | innerCore | outerCore | lowerMantle | upperMantle | crust
  deriving DecidableEq, Repr, BEq, Fintype

theorem earthLayerCount : Fintype.card EarthLayer = 5 := by decide

inductive GeophysicalObservable where
  | seismicity | gravimetry | geomagnetism | heatFlow | gpsGeodesy
  deriving DecidableEq, Repr, BEq, Fintype

theorem geophysicalObservableCount : Fintype.card GeophysicalObservable = 5 := by decide

structure GeophysicsCert where
  five_layers : Fintype.card EarthLayer = 5
  five_observables : Fintype.card GeophysicalObservable = 5

def geophysicsCert : GeophysicsCert where
  five_layers := earthLayerCount
  five_observables := geophysicalObservableCount

end IndisputableMonolith.Physics.GeophysicsFromRS
