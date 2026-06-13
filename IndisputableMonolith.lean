import IndisputableMonolith.Foundation.NothingToDistinction
import IndisputableMonolith.Foundation.TMinus1ToT8Bridge
import IndisputableMonolith.RecognitionCore
import IndisputableMonolith.LedgerFloor
import IndisputableMonolith.Gravity
import IndisputableMonolith.Foundation.MeasureForcing
import IndisputableMonolith.Constants.AlphaGenesis

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
  `α⁻¹ = (4π·11) · contWeight(w₈/(4π·11))`: the α dressing IS the forced
  measure at the spectral gap load
* `Constants.AlphaGenesis.AlphaGenesisCert.verified_any` — the seven-clause
  forward-derivation certificate (M1–M3 reference no measured value)
* `Constants.AlphaGenesis.existsUnique_closingLoad` — the second-order
  residual problem has exactly one answer in load units (quarantine module)
* `Gravity.DerivedFactors` — HSB suppression from SevenBeatViolation saturation
-/
