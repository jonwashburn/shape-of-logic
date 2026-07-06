import IndisputableMonolith.Foundation.NothingToDistinction
import IndisputableMonolith.Foundation.TMinus1ToT8Bridge
import IndisputableMonolith.RecognitionCore
import IndisputableMonolith.LedgerFloor
import IndisputableMonolith.Gravity
import IndisputableMonolith.Foundation.MeasureForcing
import IndisputableMonolith.Constants.AlphaGenesis
import IndisputableMonolith.Quantum

/-!
# Shape of Logic — root module

Public root for the core Shape of Logic release. This repository exports the
core theory of `/reality`: the T-2 through T8 theorem spine, the recognition
geometry that carries observable content, and the core gravity (ILG) layer. It
exports no later-physics or private application verticals; those remain in the
`/reality` repository.

## Forcing-chain spine

* `NothingToDistinction.nothingToDistinctionCert`
* `TMinus1ToT8Bridge.complete_forcing_chain_tminus2_to_t8`
* `CircleWindingChain.circleH1ZNonzero_unconditional`
* `CircleWindingChain.circleH1ZIsoInt_holds`

## Recognition core (T0 / T4 layer)

* `RecognitionCore.forced_quotient_iff`
* `RecognitionCore.signature_complete_iff_separating`
* `RecognitionCore.one_bit_not_complete_boundary`
* `RecognitionCore.recognizer_refinement`

## Ledger floor (Boolean shadow of the extensive recognition ledger)

* `LedgerFloor.DefectLedger`
* `LedgerFloor.ledger_floor_t0_bridge`
* `LedgerFloor.ledger_t0_identification_certificate`
* `LedgerFloor.two_independent_same_defects`

## Core gravity (ILG)

* `Gravity.ILG` — information-limited-gravity time-kernel and weight functions
* `Gravity.Rotation` — Newtonian rotation-curve identities

## Forced measure (T9) and Alpha Genesis

* `Foundation.MeasureForcing.t9_measure_forced` — the recognition measure
  `w(n) = φ⁻ⁿ` is forced (lattice + continuum layers, Gibbs form,
  partition function `Z = φ²`)
* `Constants.AlphaGenesis.DressingResponse.response_forced` — the
  exponential dressing of the α seed is forced (factorization + unit
  response); the additive form is excluded
* `Constants.AlphaGenesis.EightTickLadder.pattern_forced` — the φ-pattern
  on the 8-tick carrier is forced by T6 self-similarity
* `Constants.AlphaGenesis.alphaInv_eq_seed_mul_forced_weight` —
  `α⁻¹ = (4π·11) · contWeight(w₈/(4π·11))`: the dressing shape is the forced
  measure at the spectral gap load. HONEST STATUS: the seed `4π·11` is an
  identification, not a derived coupling, and the first-order value is
  excluded by measurement (see `MeasurementVerdict` below); exact `α⁻¹(0)`
  is a boundary condition, OPEN
* `Constants.AlphaGenesis.AlphaGenesisCert.verified_any` — the seven-clause
  forward-derivation certificate (M1–M3 reference no measured value)
* `Constants.AlphaGenesis.existsUnique_closingLoad` — the second-order
  residual problem has exactly one answer in load units (quarantine module)
* `Constants.AlphaGenesis.MeasurementVerdict.alphaInvGenesis_exceeds_CODATA_by_0007`
  — the measurement verdict: the first-order construction value exceeds
  CODATA by more than `7×10⁻⁴`, an exclusion at more than 30,000σ
  (`margin_0007_gt_30000_sigma`)
* `Constants.AlphaGenesis.KappaGamma.alpha_not_pinned_by_forcedClosure` and
  `kappa_blind_closure_cannot_pin` — the irreducibility theorems: the forced
  closure is κ_γ-independent and no normalization-blind condition can pin
  the coupling, so within RS the exact value of `α⁻¹` is a free boundary
  datum (the U(1) kinetic normalization), not a derived constant
* `Gravity.DerivedFactors` — HSB suppression from SevenBeatViolation saturation

## Quantum layer (recognition-first)

* `Quantum.RecognitionFirst.eightTick_weyl` — the finite Heisenberg–Weyl relation on
  the 8-tick recognition cycle; `canonical_noncommutativity` is the recognition root of
  `[x,p] ≠ 0` (continuum `[x,p]=iℏ` and `ℏ=φ⁻⁵` remain OPEN)
* `Quantum.PureTwoQubit.EntropyConcurrence` — Wootters concurrence and the
  concurrence→entropy certificate for pure two-qubit states
* `Quantum.HolographicBound.holographic_bound` — `S ≤ A/(4 l_P²)` from ledger projection
-/
