import IndisputableMonolith.Constants.AlphaGenesis.ResummationForcing
import IndisputableMonolith.Constants.AlphaGenesis.PatternForcing
import IndisputableMonolith.Constants.AlphaGenesis.LoopCertificate
import IndisputableMonolith.Constants.AlphaGenesis.ResidualTarget
import IndisputableMonolith.Constants.AlphaGenesis.CalibrationForcing
import IndisputableMonolith.Constants.AlphaGenesis.SpectralForcing
import IndisputableMonolith.Constants.AlphaGenesis.MeasurementVerdict
import IndisputableMonolith.Constants.AlphaGenesis.KappaGammaIrreducibility

/-!
# Alpha Genesis (aggregator)

The forward derivation of the fine-structure constant, replacing the
backwards (display-first) assembly. Mirror of the mass-derivation program.

* `ResummationForcing` (M1): the exponential dressing is forced by the same
  factorization premise that forces the T9 measure; the additive form (A) is
  excluded. `alphaInv = seed · contWeight(w₈/seed)`: the α dressing IS the
  forced measure.
* `PatternForcing` (M2): the φ-pattern is forced by T6 self-similarity on
  the T7 carrier; the spectral decay envelope IS the forced measure; pattern
  and measure are reciprocal displays.
* `LoopCertificate` (M3): the EM recognition loop (channel budget = Gauss-
  Bonnet × passive edges), the forward definition `alphaInvGenesis`, the
  identity with the certified pipeline, the proved band, and
  `AlphaGenesisCert`. One named BRIDGE input: the channel-budget reading.
* `ResidualTarget` (M4, quarantine): the only module that sees CODATA.
  Residual bounds, the unique `closingLoad`, and the seam-derivation
  falsifier with the binding anti-epicycle rule.
* `CalibrationForcing` (M5): the calibration is NOT an input. A
  factorizing, antitone response whose step satisfies the self-similar
  balance is forced to `φ⁻ᵗ` with zero normalization choices; the M1
  calibrated response is its natural-units display.
* `SpectralForcing` (M6): the `sin²(kπ/8)` oscillation factor IS one
  quarter of the difference-operator spectrum on the DFT-8 eigenbasis
  (trig closure `|ω₈ᵏ−1|² = 4sin²(kπ/8)`); every nonzero mode weight
  factors as spectrum × forced measure.

* `MeasurementVerdict` (M7): the measurement verdict on the first-order
  construction. `alphaInvGenesis > alpha_inv_CODATA + 0.0007`, i.e. the
  first-order value is excluded at more than 30,000σ. Any build that carries
  the construction also carries its measured exclusion.
* `KappaGammaIrreducibility` (M8): the structural reason the miss cannot be
  repaired by more forced kinematics. Every listed forced-closure fact on Q₃
  is κ_γ-independent, `α⁻¹ = κ_γ × (forced stiffness)` sweeps every positive
  value with the closure intact (`alphaInv_irreducible_under_closure`), and no
  normalization-blind condition whatever can pin the coupling
  (`kappa_blind_closure_cannot_pin`). Within RS the exact value of `α⁻¹(0)` is
  the free U(1) kinetic normalization: a boundary datum, not a derived
  constant.

M1–M3 and M5–M6 are blind to measurement by construction. M7 is the
quarantined CODATA contact; importing it HERE (at the aggregator, downstream
of the whole forward chain) preserves the quarantine while making the verdict
reachable from every build target that carries the construction.

CANONICAL POSITION (post-retraction): the forced content of the photon sector
is kinematic (channel, 4π closure, cycle rank b₁ = 5); the coupling's value is
the free normalization κ_γ (M8); the first-order construction value is excluded
by measurement (M7); the unique second-order closing load δ₂ (M4) is OPEN and
may not be reverse-engineered from proximity to CODATA.
-/
