/-
  PrimitiveRecognitionCalculus/Factorization/SubstrateDichotomy.lean

  The factoring-speedup fork, stated honestly.

  The arithmetic layer is closed: the orbit semiring is isomorphic to `Nat` as an
  ordered commutative semiring, so any factoring procedure expressible in orbit
  arithmetic has the same operation count as the corresponding `Nat` procedure
  (transport). No arithmetic speedup is possible.

  The only surviving channel is a physical recognition readout (Door B,
  `PhysicalPeriodReadout`). This module records the resulting dichotomy:

  * Branch B (coherent substrate). If the substrate supplies a certified factor
    readout, `N` factors nontrivially. This conditional is PROVED.
  * Branch A (definite ledger). The magnitude observable available to a
    definite-ledger substrate cannot extract a factor coordinate. PROVED.

  Which branch the RS substrate realizes for factorization is still open. A
  previous reading treated the proved `Signal8` interference layer as only
  constant-dimensional and concluded that the current substrate is Branch A.
  That reading was too strong: `Gravity.MacroscopicLedger` formalizes finite
  many-body ledger carriers as `PiTensorProduct` powers of `Signal8`, and
  `Gravity.QuantumChannel.PhysicalChannelAmplitudeLinear` proves amplitude
  linearity for the many-body physical channel lift.

  The remaining open node is narrower and sharper: no theorem here constructs a
  period-readout dynamics on that many-body amplitude carrier, nor proves that
  such a readout has polynomial resource scaling. The tensor/amplitude substrate
  exists; the factoring-specific transform does not.

  This file asserts neither branch antecedent. It proves both conditionals and
  names the open node.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PhysicalPeriodReadout

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- Branch B antecedent: the substrate supplies a certified factor readout for
some base modulo `N`. This is exactly the Door B oracle. It is NOT proved to hold
for the RS substrate; see the module docstring. A factoring *speedup* is the
stronger claim that this antecedent can be delivered uniformly in `N` at cost
below classical factoring, which is the open performance problem. -/
def CoherentSubstrateDeliversFactor (N : DistinctionNat) (hN : N ≠ zero) : Prop :=
  ∃ a : DistinctionNat, Nonempty (CertifiedFactorReadout N hN a)

/-- Branch B conditional (PROVED): if the substrate delivers a certified factor
readout, `N` factors nontrivially. The reduction is unconditional; only the
antecedent is open. -/
theorem coherentSubstrate_delivers_factorization
    {N : DistinctionNat} {hN : N ≠ zero}
    (h : CoherentSubstrateDeliversFactor N hN) :
    nontrivialFactorization N := by
  rcases h with ⟨a, ⟨r⟩⟩
  exact certifiedFactorReadout_to_nontrivialFactorization r

/-- Branch A obstruction (PROVED, restated from the recognition lower bound): the
product-magnitude observable available to a definite-ledger substrate cannot
extract a factor coordinate. A definite ledger that reads only Archimedean
magnitude is blind to the factor chart. -/
theorem definiteLedger_magnitude_cannot_extract_factor :
    ¬ MagnitudeOnlyObservable (fun a _ => a.toNat) :=
  leftFactorObservable_not_magnitudeOnly

/-- The honest dichotomy certificate. Both conditionals are theorems. The Branch B
antecedent `CoherentSubstrateDeliversFactor` is the open foundational node and is
NOT asserted here. -/
structure SubstrateDichotomyCertificate : Prop where
  branchB_conditional :
    ∀ {N : DistinctionNat} {hN : N ≠ zero},
      CoherentSubstrateDeliversFactor N hN → nontrivialFactorization N
  branchA_obstruction :
    ¬ MagnitudeOnlyObservable (fun a _ => a.toNat)

theorem substrate_dichotomy_certificate : SubstrateDichotomyCertificate where
  branchB_conditional := by
    intro N hN h
    exact coherentSubstrate_delivers_factorization h
  branchA_obstruction := definiteLedger_magnitude_cannot_extract_factor

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
