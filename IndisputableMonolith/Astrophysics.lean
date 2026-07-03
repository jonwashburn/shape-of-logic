import IndisputableMonolith.Astrophysics.MassToLight
import IndisputableMonolith.Astrophysics.StellarAssembly
import IndisputableMonolith.Astrophysics.NucleosynthesisTiers
import IndisputableMonolith.Astrophysics.ObservabilityLimits

/-!
# Astrophysics Module Aggregator

Central import point for RS astrophysics derivations:
- Mass-to-light ratio (M/L) derivation with three parallel strategies
- Stellar assembly via recognition-weighted collapse
- φ-tier nucleosynthesis
- Observability limits from λ_rec, τ0 constraints

## Main Results

- `ml_derivation_complete`: Unified M/L derivation from all three strategies
- `ml_solar_units_prediction`: Predicted M/L ~ 0.8-3.0 solar units
- `stellar_ml_on_phi_ladder`: M/L ratios fall on φ^n sequence

## Status

This completes the derivation chain for RS, eliminating the last remaining
external calibration. With M/L derived, RS achieves true zero-parameter status:
all fundamental constants (c,ℏ,G,α⁻¹) and astrophysical calibrations are
derived from the Meta-Principle.

## Usage

```lean
import IndisputableMonolith.Astrophysics

open IndisputableMonolith.Astrophysics

#check ml_derivation_complete
#check ml_phi_ladder_from_costs
#check ml_from_geometry_only
```

## References

- Source.txt @M_OVER_L_DERIVATION lines 875-933
- Source.txt @PARAMETER_POLICY lines 329-361
-/

namespace IndisputableMonolith

namespace Astrophysics
-- Re-export main theorems and structures

-- From MassToLight:
-- - StellarConfiguration
-- - mass_to_light
-- - RecognitionCostDifferential
-- - PhiTierStructure
-- - ObservabilityConstraints
-- - ml_derivation_complete

-- From StellarAssembly (Strategy 1):
-- - equilibrium_ml_from_j_minimization
-- - ml_phi_ladder_from_costs
-- - ml_increases_with_stellar_mass

-- From NucleosynthesisTiers (Strategy 2):
-- - stellar_ml_on_phi_ladder
-- - eight_tick_nucleosynthesis_quantizes_density
-- - recognition_bandwidth_quantizes_luminosity

-- From ObservabilityLimits (Strategy 3):
-- - ml_from_j_minimization
-- - ml_from_geometry_only
-- - imf_from_j_minimization

end Astrophysics

end IndisputableMonolith









