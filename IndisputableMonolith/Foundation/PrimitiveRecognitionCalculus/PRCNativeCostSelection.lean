/-
  PrimitiveRecognitionCalculus/PRCNativeCostSelection.lean

  Round-trip source:
    δ/plans/JCost_Free_Side_Mint_Prereg_20260724.json   (frozen prereg)
    plans/Delta_JCost_Free_Side_Rederivation_Session_Prompt_20260724.txt

  The free-side mint of the cost-selection keystone (campaign P-delta-jfree).

  `PublicSpine.cost_selection_holds` deposits J-uniqueness at
  `StrengthTag.traceClosure`: its statement lives on the completed line and
  consumes continuity (`law_of_logic_forces_jcost`). This module deposits the
  δ-native counterpart on the countable carrier `RatioOrbit`, at
  `StrengthTag.deltaOnly`, together with the typed wall naming exactly what
  the continuum premise was buying.

  WIN-A (`cost_selection_native_holds`): every native cost satisfying the
  itemized algebraic premise ledger (reciprocity, normalization invariance,
  canonical RCL on nonzero orbits, unit-zero, prime-pair product calibration,
  signed-unit calibration, all-prime-axis calibration, zero-orbit trace
  calibration) is crossEq-pointwise the canonical `onRatioOrbit` cost. The
  package also carries non-vacuity (an explicit witness inhabits the full
  hypothesis class) and the frozen decoy exclusions (the constant-zero cost
  and the linear cost fail the class).

  WIN-B (`continuum_price_residue_wall_tagged`): the residue of the continuum
  price, stated as theorems. The proven necessity chain is STAGED: the base
  ledger fails (two-adic twist), the pair-strengthened ledger fails
  (absolute-value cost), and the prime-signed ledger without zero-orbit
  calibration fails (zero-flat cost). Separately, every prime axis is an
  independent CHARACTER-orientation freedom. Honesty note (cross-family
  review, 2026-07-24): the per-axis freedom is a character-level statement;
  at the cost level a single-axis twist is invisible on its own axis (J is
  reciprocal) and is caught by the pair-product field, so minimality of the
  all-prime calibration family relative to the base+pairs+sign ledger is
  OPEN (`PRCSignedStrengthenedNativeCostUniquenessTarget` is undetermined in
  the parent module). The wall is tagged `classicalExtension` because its
  countermodel characters are classical verifier-side constructions
  (panel K2: classical negatives never ride under `deltaOnly`).

  Scope: this module only reads `PRCNativeCostUniqueness.lean` and
  `PublicSpine.lean`. It never edits `cost_selection_holds` or its tag.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostUniqueness
import IndisputableMonolith.Foundation.PublicSpine

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

/-! ## Non-vacuity witness

The raw `onRatioOrbit` cannot inhabit `PRCNativeCostHypotheses` verbatim: the
`unit_zero` field demands the literal `RatioOrbit.zero` representative, while
`onRatioOrbit RatioOrbit.one` computes to the crossEq-equal but structurally
distinct representative `0/2`. The selected witness routes the unit display to
the canonical zero representative and is elsewhere the canonical cost. Its
verifier display is the J formula everywhere, including at the unit. -/

/-- The canonical selected native cost: the J cost with the unit orbit sent to
the literal zero representative. This is the non-vacuity witness for the full
zero-calibrated prime-signed strengthened hypothesis class. -/
def canonicalSelectedNativeCost (q : RatioOrbit) : RatioOrbit :=
  if q.toRat = 1 then RatioOrbit.zero else onRatioOrbit q

/-- The selected witness displays as the J formula on every orbit; on the
unit-display branch both sides are `0`. -/
theorem canonicalSelectedNativeCost_toRat (q : RatioOrbit) :
    (canonicalSelectedNativeCost q).toRat = (q.toRat + q.toRat⁻¹) / 2 - 1 := by
  rw [canonicalSelectedNativeCost]
  by_cases h : q.toRat = 1
  · rw [if_pos h, RatioOrbit.zero_toRat, h]
    norm_num
  · rw [if_neg h, onRatioOrbit_toRat]

/-- The selected witness is crossEq-pointwise the canonical cost. -/
theorem canonicalSelectedNativeCost_crossEq_onRatioOrbit (q : RatioOrbit) :
    RatioOrbit.crossEq (canonicalSelectedNativeCost q) (onRatioOrbit q) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, canonicalSelectedNativeCost_toRat,
    onRatioOrbit_toRat]

/-- The selected witness satisfies the base native-cost hypotheses. -/
theorem canonicalSelectedNativeCost_native_hypotheses :
    PRCNativeCostHypotheses canonicalSelectedNativeCost where
  reciprocal := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, canonicalSelectedNativeCost_toRat,
      canonicalSelectedNativeCost_toRat, RatioOrbit.recip_toRat]
    by_cases hq : q.toRat = 0
    · simp [hq]
    · field_simp [hq]
      ring
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, canonicalSelectedNativeCost_toRat,
      canonicalSelectedNativeCost_toRat, DistinctionNat.normalizeRatio_toRat]
  canonical_rcl := by
    intro x y hx hy
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    simp only [RatioOrbit.add_toRat, RatioOrbit.mul_toRat,
      canonicalSelectedNativeCost_toRat, div_toRat, two_toRat]
    have hxy : x.toRat * y.toRat ≠ 0 := mul_ne_zero hx hy
    field_simp [hx, hy, hxy]
    ring_nf
  unit_zero := by
    rw [canonicalSelectedNativeCost, if_pos RatioOrbit.one_toRat]
  two_calibrated := canonicalSelectedNativeCost_crossEq_onRatioOrbit two

/-- The selected witness satisfies the full zero-calibrated prime-signed
strengthened hypothesis class: the frozen ledger is non-vacuous. -/
theorem canonicalSelectedNativeCost_full_hypotheses :
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses
      canonicalSelectedNativeCost where
  prime_signed :=
    { signed_strengthened :=
        { strengthened :=
            { native := canonicalSelectedNativeCost_native_hypotheses
              prime_pair_product_cost := fun p hp r hr =>
                canonicalSelectedNativeCost_crossEq_onRatioOrbit
                  (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)) }
          signed_unit :=
            canonicalSelectedNativeCost_crossEq_onRatioOrbit negativeOneRatio }
      prime_direction_cost := fun p hp =>
        canonicalSelectedNativeCost_crossEq_onRatioOrbit (primeDirection p hp) }
  zero_calibrated := by
    rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq]
    simp only [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
      canonicalSelectedNativeCost_toRat, RatioOrbit.zero_toRat]
    norm_num

/-! ## Frozen decoys

Preregistered known-wrong costs (prereg PREREG-jfree-mint-20260724). Both must
fail the frozen hypothesis class; the failure point is the two-calibration
field, exactly as frozen before proving. These two are smoke tests: they die
at the shallowest field. The layer-wise near-miss decoys are the wall's
countermodels themselves (two-adic twist, absolute-value cost, zero-flat
cost), each of which passes every ledger layer above the one it refutes. -/

/-- Decoy 1: the constant-zero cost. -/
def constantZeroNativeCost : RatioOrbit → RatioOrbit :=
  fun _ => RatioOrbit.zero

/-- Decoy 2: the linear cost `q - 1`. -/
def linearNativeCost (q : RatioOrbit) : RatioOrbit :=
  RatioOrbit.sub q RatioOrbit.one

/-- The constant-zero cost already fails the base hypothesis ledger: the
canonical cost of the two orbit displays as `1/4`, not `0`. -/
theorem constantZeroNativeCost_not_native_hypotheses :
    ¬ PRCNativeCostHypotheses constantZeroNativeCost := by
  intro h
  have h2 := h.two_calibrated
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h2
  simp only [constantZeroNativeCost, RatioOrbit.zero_toRat, onRatioOrbit_toRat,
    two_toRat] at h2
  norm_num at h2

/-- The linear cost already fails the base hypothesis ledger: `2 - 1 = 1` is
not the canonical display `1/4`. -/
theorem linearNativeCost_not_native_hypotheses :
    ¬ PRCNativeCostHypotheses linearNativeCost := by
  intro h
  have h2 := h.two_calibrated
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h2
  simp only [linearNativeCost, RatioOrbit.sub_toRat, RatioOrbit.one_toRat,
    onRatioOrbit_toRat, two_toRat] at h2
  norm_num at h2

/-- Decoy exclusion 1 against the full frozen class. -/
theorem constantZeroNativeCost_excluded :
    ¬ PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses
        constantZeroNativeCost :=
  fun h =>
    constantZeroNativeCost_not_native_hypotheses
      h.prime_signed.signed_strengthened.strengthened.native

/-- Decoy exclusion 2 against the full frozen class. -/
theorem linearNativeCost_excluded :
    ¬ PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses
        linearNativeCost :=
  fun h =>
    linearNativeCost_not_native_hypotheses
      h.prime_signed.signed_strengthened.strengthened.native

/-! ## Zero-orbit calibration is necessary (the missing necessity witness)

The prime-signed strengthened ledger WITHOUT zero-orbit calibration does not
force uniqueness: `zeroFlatNativeCost` (canonical away from zero, flat at the
zero orbit) satisfies every field of that ledger, because the canonical RCL
only constrains nonzero orbits and every calibration probe is nonzero, yet it
disagrees with the canonical cost at the zero orbit. -/

/-- The zero-flat countermodel satisfies the prime-signed strengthened ledger
(everything except zero-orbit calibration). -/
theorem zeroFlatNativeCost_prime_signed_strengthened_hypotheses :
    PRCPrimeSignedStrengthenedNativeCostHypotheses zeroFlatNativeCost where
  signed_strengthened :=
    { strengthened :=
        { native := zeroFlatNativeCost_hypotheses
          prime_pair_product_cost := by
            intro p hp r hr
            refine zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero ?_
            rw [RatioOrbit.mul_toRat]
            exact mul_ne_zero (primeDirection_toRat_ne_zero p hp)
              (primeDirection_toRat_ne_zero r hr) }
      signed_unit := by
        refine zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero ?_
        rw [negativeOneRatio_toRat]
        norm_num }
  prime_direction_cost := fun p hp =>
    zeroFlatNativeCost_crossEq_onRatioOrbit_of_nonzero
      (primeDirection_toRat_ne_zero p hp)

/-- **Zero-orbit calibration is irreducible.** Without it, the prime-signed
strengthened ledger admits the zero-flat countermodel: uniqueness fails at the
zero orbit, where the canonical cost displays `-1` and the countermodel
displays `0`. -/
theorem PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_refuted :
    ¬ PRCPrimeSignedStrengthenedNativeCostUniquenessTarget := by
  intro h
  have hzero :=
    h zeroFlatNativeCost zeroFlatNativeCost_prime_signed_strengthened_hypotheses
      RatioOrbit.zero
  rw [zeroFlatNativeCost_zero, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.zero_toRat, onRatioOrbit_toRat, RatioOrbit.zero_toRat] at hzero
  norm_num at hzero

/-! ## WIN-A: the native cost-selection deposit -/

/-- **The native cost-selection package** (prereg PREREG-jfree-mint-20260724).
The δ-native counterpart of `PublicSpine.CostSelectionPackage`:

* `j_unique_native`: every native cost satisfying the itemized ledger
  (base hypotheses + prime-pair products + signed unit + all prime axes +
  zero orbit) is crossEq-pointwise the canonical `onRatioOrbit` cost.
* `non_vacuous`: an explicit witness inhabits the full ledger and agrees with
  the canonical cost, so the class is neither empty nor drifted.
* `zero_cost_excluded` / `linear_cost_excluded`: the frozen known-wrong costs
  fail the ledger, so the predicate discriminates.

Read this as CONDITIONAL δ-native rigidity: the RCL plus an explicit
countable J-valued calibration ledger (prime, pair, sign, zero) determines J
on `RatioOrbit`. It removes the completion cost of the continuum deposit; it
does not remove the calibration cost, which is the ledger itself. The
uniqueness content is real (calibration lives on generators; the RCL must
still propagate it to every orbit, and the parent module's refuted
propagation targets show that step is not free), but the honest name is
rigidity from extensive calibration data, not an economical selector.

Every hypothesis in the ledger is an algebraic condition on the countable
carrier `RatioOrbit` (countable quantification over prime orbits included):
the statement consumes no completed orbit, no trace closure, no continuity.
The tag is an audit assertion under the PublicSpine statement-carrier
convention, not a kernel-derived semantic grade; the classical proof shell
is disclosed by the axiom audit receipts and never upgrades the statement
grade. -/
structure CostSelectionPackageNative : Prop where
  j_unique_native :
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget
  non_vacuous :
    ∃ F : RatioOrbit → RatioOrbit,
      PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses F ∧
        ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)
  zero_cost_excluded :
    ¬ PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses
        constantZeroNativeCost
  linear_cost_excluded :
    ¬ PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses
        linearNativeCost

/-- The native cost-selection package holds. -/
theorem costSelectionPackageNative_holds : CostSelectionPackageNative where
  j_unique_native :=
    PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget_proved
  non_vacuous :=
    ⟨canonicalSelectedNativeCost, canonicalSelectedNativeCost_full_hypotheses,
      canonicalSelectedNativeCost_crossEq_onRatioOrbit⟩
  zero_cost_excluded := constantZeroNativeCost_excluded
  linear_cost_excluded := linearNativeCost_excluded

/-- **WIN-A deposit: cost selection on the free side of the meter.** The
selection of J on the δ-native countable carrier, tagged strictly below the
continuum deposit (`cost_selection_holds` at `traceClosure`). -/
theorem cost_selection_native_holds :
    PublicSpine.Tagged StrengthTag.deltaOnly CostSelectionPackageNative where
  holds := costSelectionPackageNative_holds

/-- The native deposit sits strictly below the continuum deposit on the K1
strength ledger. -/
theorem native_deposit_strictly_below_continuum_deposit :
    StrengthTag.deltaOnly < StrengthTag.traceClosure :=
  StrengthTag.deltaOnly_lt_traceClosure

/-! ## WIN-B: the continuum price residue, as a typed wall -/

/-- **The irreducible residue of the continuum price** (prereg
PREREG-jfree-mint-20260724). What `ContinuousOn` plus one-point calibration
buys in `law_of_logic_forces_jcost`, the δ-native carrier must purchase as an
infinite independent calibration family. Each field is a kernel-checked
theorem:

* `base_insufficient`: the base ledger admits the two-adic axis twist.
* `strengthened_insufficient`: adding prime-pair products still admits the
  absolute-value countermodel (the signed unit is invisible).
* `prime_signed_insufficient`: adding the signed unit and every prime axis
  still admits the zero-flat countermodel (the zero orbit is invisible to the
  nonzero RCL).
* `every_prime_axis_free`: for every prime orbit there is a ratio character
  fixing all other prime axes and inverting that one. This is
  character-orientation freedom, exactly as stated; whether a proper
  subfamily of the cost-level prime calibrations suffices (given pairs and
  sign) remains OPEN, because J's reciprocity hides a single-axis twist on
  its own axis.
* `zero_spike_still_excluded`: the frozen zero-spike decoy keeps failing the
  zero-orbit calibration that repairs it. -/
structure ContinuumPriceResidueWall : Prop where
  base_insufficient : ¬ PRCNativeCostUniquenessTarget
  strengthened_insufficient : ¬ PRCStrengthenedNativeCostUniquenessTarget
  prime_signed_insufficient :
    ¬ PRCPrimeSignedStrengthenedNativeCostUniquenessTarget
  every_prime_axis_free :
    ∀ (p : DistinctionNat) (hp : DistinctionNat.primeOrbit p),
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCRatioCharacter χ ∧
          (∀ (r : DistinctionNat) (hr : DistinctionNat.primeOrbit r),
            r ≠ p →
              RatioOrbit.crossEq (χ (primeDirection r hr))
                (primeDirection r hr)) ∧
          ¬ RatioOrbit.crossEq (χ (primeDirection p hp)) (primeDirection p hp)
  zero_spike_still_excluded :
    ¬ PRCDoubledTraceZeroCalibrated zeroSpikeDoubledTrace

/-- The continuum price residue wall holds. -/
theorem continuumPriceResidueWall_holds : ContinuumPriceResidueWall where
  base_insufficient := PRCNativeCostUniquenessTarget_refuted
  strengthened_insufficient := PRCStrengthenedNativeCostUniquenessTarget_refuted
  prime_signed_insufficient :=
    PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_refuted
  every_prime_axis_free := prc_every_prime_axis_orientation_free
  zero_spike_still_excluded := zeroSpikeDoubledTrace_not_zero_calibrated

/-- **WIN-B deposit: the residue wall, honestly tagged.** The countermodel
characters are classical verifier-side constructions, so the wall rides at
`classicalExtension` (panel K2). -/
theorem continuum_price_residue_wall_tagged :
    PublicSpine.Tagged StrengthTag.classicalExtension ContinuumPriceResidueWall
    where
  holds := continuumPriceResidueWall_holds

/-! ## The premise ledger (design requirement 1)

Every hypothesis that replaces continuity, itemized with the grade it costs on
the K1 strength ledger, each with its necessity witness. The highest-cost
premise sets the tag of the deposit; every item below is `deltaOnly`, so the
deposit is `deltaOnly`. -/

/-- The itemized premise ledger for the native cost-selection deposit. -/
def nativeCostSelectionPremiseLedger : List StrengthClaim :=
  [ { label := "base"
      tag := StrengthTag.deltaOnly
      statement := "Reciprocity, normalization invariance, canonical RCL on \
nonzero orbits, unit-zero, two-calibration (PRCNativeCostHypotheses). \
Necessity: PRCNativeCostUniquenessTarget_refuted (two-adic axis twist)." }
  , { label := "prime_pair_products"
      tag := StrengthTag.deltaOnly
      statement := "Calibration on products of two prime directions \
(PRCNativeCostPrimePairProductCalibrated). Necessity: the two-adic generated \
cost slips through the base ledger exactly on such products." }
  , { label := "signed_unit"
      tag := StrengthTag.deltaOnly
      statement := "Calibration at the signed unit -1 \
(PRCNativeCostSignedUnitCalibrated). Necessity: \
PRCStrengthenedNativeCostUniquenessTarget_refuted (absolute-value cost)." }
  , { label := "all_prime_axes"
      tag := StrengthTag.deltaOnly
      statement := "Calibration on every native prime direction, a countable \
family (PRCNativeCostPrimeDirectionCalibrated). Character-level necessity: \
prc_every_prime_axis_orientation_free (every axis is an independent \
character-orientation freedom). Cost-level minimality relative to \
base+pairs+sign is OPEN (PRCSignedStrengthenedNativeCostUniquenessTarget \
undetermined)." }
  , { label := "zero_orbit"
      tag := StrengthTag.deltaOnly
      statement := "Zero-orbit calibration of the doubled trace \
(PRCDoubledTraceZeroCalibrated). Necessity: \
PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_refuted (zero-flat \
countermodel); the nonzero RCL never sees the zero orbit." }
  ]

/-- The ledger is uniformly at the δ-only floor: the weakest link of the
deposit is `deltaOnly`. -/
theorem nativeCostSelectionPremiseLedger_all_deltaOnly :
    ∀ c ∈ nativeCostSelectionPremiseLedger, c.tag = StrengthTag.deltaOnly := by
  intro c hc
  simp only [nativeCostSelectionPremiseLedger, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h <;> subst h <;> rfl

/-! ## Axiom audit (headline receipts) -/

#print axioms costSelectionPackageNative_holds
#print axioms cost_selection_native_holds
#print axioms continuumPriceResidueWall_holds
#print axioms continuum_price_residue_wall_tagged
#print axioms canonicalSelectedNativeCost_full_hypotheses
#print axioms PRCPrimeSignedStrengthenedNativeCostUniquenessTarget_refuted

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
