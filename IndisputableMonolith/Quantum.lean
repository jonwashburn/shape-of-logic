import IndisputableMonolith.Quantum.RecognitionFirst.EightTickWeyl
import IndisputableMonolith.Quantum.PureTwoQubit.EntropyConcurrence
import IndisputableMonolith.Quantum.HolographicBound
import IndisputableMonolith.Quantum.BornRule

/-!
# IndisputableMonolith.Quantum

Quantum module facade — re-exports the public quantum-layer formalizations that
derive standard quantum structure from the recognition substrate:

- `Quantum.RecognitionFirst.EightTickWeyl`: the finite Heisenberg–Weyl relation on
  the 8-tick recognition cycle `ZMod 8`. `clock ∘ shift = ω • (shift ∘ clock)` with
  `ω` a primitive 8th root of unity (`eightTick_weyl`), so occupation and cost-rate do
  not commute (`canonical_noncommutativity`). This is the recognition root of the
  canonical commutator `[x,p] ≠ 0`; the continuum limit `[x,p] = iℏ` and the magnitude
  `ℏ = φ⁻⁵` are OPEN, not asserted here. Axiom-clean.

- `Quantum.PureTwoQubit.EntropyConcurrence`: the Wootters `concurrence` of a pure
  two-qubit amplitude matrix and its entanglement entropy. `concurrence_nonneg`,
  `concurrence_eq_zero_iff_det_zero`, the binary entropy `h(p)`, and the certificate
  `PureTwoQubitConcurrenceEntropyCert` linking positive concurrence to positive entropy.

- `Quantum.HolographicBound`: the holographic bound `S ≤ A/(4 l_P²)` (`holographic_bound`),
  its derivation from ledger projection (`holography_from_ledger`), the Bekenstein bound,
  and the area-scaling of information.

- `Quantum.BornRule`: the Born rule from the recognition cost functional. The
  measurement weight `r ↦ r²` is forced by the two-branch geodesic action and the
  kernel-match certificate (`born_rule_from_jcost`), and `gleason_from_rs` packages the
  Gleason-style derivation from the recognition substrate. Its dependency base is the
  neutral `Spectral.DFT8` backbone and the `Foundation.ComplexStructureForcing` /
  `Foundation.BornRuleForcing` chain, all Mathlib-only and axiom-clean. This replaces the
  earlier note that the Born-rule derivation remained private: its measurement
  certificates (`Measurement.PathAction`, `TwoBranchGeodesic`, `KernelMatch`, `C2ABridge`,
  `Verification.TwoOutcomeBornCert`) have been refactored onto the clean substrate.

These export no later-physics or private application verticals.
-/

namespace IndisputableMonolith
namespace Quantum

end Quantum
end IndisputableMonolith
