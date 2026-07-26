/-
  PrimitiveRecognitionCalculus/PRCNativeCostMinimality.lean

  Round-trip source:
    δ/plans/JCost_AllPrime_CostLevel_Minimality_Prereg_20260724.json (frozen)
    plans/Delta_JCost_AllPrime_CostLevel_Minimality_Session_Prompt_20260724.txt

  Cost-level minimality of the all-prime calibration family (P-delta-jfree,
  round 2). The round-1 mint (`PRCNativeCostSelection.lean`) deposited
  `CostSelectionPackageNative` at `deltaOnly` over a ledger whose largest item
  is calibration on EVERY native prime axis, and left OPEN whether that
  countable family is necessary at the cost level. This module settles it:

  * REDUNDANT. `PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget`
    is proved: the slim ledger (base + prime-pair products + signed unit +
    zero orbit, WITHOUT the all-prime field) already forces the canonical
    cost. The new mathematical content is
    `character_pair_two_calibration_forces_prime_calibration`: for a ratio
    character, prime-pair product cost consistency plus the base ledger's
    single two-point calibration force cost calibration on every prime axis.
    The dichotomies J(x)=J(y) ⟺ y ∈ {x, 1/x} at the orbits 2, 2p, p·p leave
    exactly the identity and reciprocal branches; every mixed branch dies on
    integer arithmetic (16·P⁴ = 1 or 16 = 1 with P ≥ 1).

  * The launch prompt's named target
    `PRCSignedStrengthenedNativeCostUniquenessTarget` (slim ledger WITHOUT the
    zero field) is REFUTED: the round-1 zero-flat witness satisfies the
    STRONGER prime-signed ledger, hence also this weaker one, and differs
    from the canonical cost at the zero orbit. This is the uninteresting
    refutation: it says only that the zero orbit stays invisible to the
    nonzero RCL.

  * `cost_selection_native_slim_holds` mints the contracted deposit at
    `deltaOnly`: uniqueness over the slim ledger, non-vacuity, the frozen
    decoy exclusions, and the layer-discrimination pair for the zero-flat
    cost (passes the slim ledger minus zero, fails the slim ledger).

  Honest reading: the round-1 deposit's ledger was honest but fat. After the
  zero-orbit calibration supplies the character factorization, the orbit-2
  anchor together with the (2,p) and (p,p) pair probes forces every
  prime-axis cost calibration; the signed unit plays no role in this
  transport step. What remains genuinely open, with countermodel sketches
  recorded in the prereg: cost-level necessity of the two-point calibration
  itself relative to pairs+sign+zero (paper-level countermodel: the
  Liouville-type sign twist χ(q) = λ(q)·q, which passes pairs because signs
  cancel on products of two primes; within the slim ledger it fails exactly
  the two-point calibration, while against the round-1 full ledger it also
  fails every prime-axis field), and a formalized necessity witness for the
  pair field relative to base+sign+zero.

  Scope: reads `PRCNativeCostSelection.lean` (round-1 witnesses and decoys)
  and through it `PRCNativeCostUniqueness.lean`. It edits neither, and never
  touches `cost_selection_holds`, `cost_selection_native_holds`, or their
  tags.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostSelection

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

/-! ## The named launch target, settled: REFUTED by inclusion

The signed-strengthened ledger carries no zero-orbit field, so the round-1
zero-flat witness (which satisfies the STRONGER prime-signed ledger, hence
also this weaker one) already defeats it. -/

/-- **The launch prompt's named target is refuted.** The signed-strengthened
ledger (base + pairs + signed unit, no zero field) admits the zero-flat
countermodel: every one of its fields lives on nonzero orbits. -/
theorem PRCSignedStrengthenedNativeCostUniquenessTarget_refuted :
    ¬ PRCSignedStrengthenedNativeCostUniquenessTarget := by
  intro h
  have hzero :=
    h zeroFlatNativeCost
      zeroFlatNativeCost_prime_signed_strengthened_hypotheses.signed_strengthened
      RatioOrbit.zero
  rw [zeroFlatNativeCost_zero, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.zero_toRat, onRatioOrbit_toRat, RatioOrbit.zero_toRat] at hzero
  norm_num at hzero

/-- Corollary: the signed-strengthened ledger cannot factor every inhabitant
through a signed-admissible character (the zero-flat cost cannot factor, since
character-generated costs are canonical at the zero orbit). -/
theorem PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget_refuted :
    ¬ PRCSignedStrengthenedNativeCostSignedAdmissibleCharacterFactorizationTarget :=
  fun h =>
    PRCSignedStrengthenedNativeCostUniquenessTarget_refuted
      (PRCSignedStrengthenedNativeCostUniquenessTarget_of_signed_admissible_factorization
        h)

/-! ## The core new lemma: pairs + the two-point calibration force every axis

Pure rational case analysis behind the transport. `u` is the character value
at the two axis, `v` at the probed prime axis, `P ≥ 1` the prime display. -/

private lemma pair_two_case_split {u v P : ℚ} (hP : P ≠ 0) (hP1 : 1 ≤ P)
    (hu : u = 2 ∨ u = 2⁻¹)
    (huv : u * v = 2 * P ∨ u * v = (2 * P)⁻¹)
    (hvv : v * v = P * P ∨ v * v = (P * P)⁻¹) :
    v = P ∨ v = P⁻¹ := by
  have hpow : (1:ℚ) ≤ P ^ 4 := one_le_pow₀ hP1
  have h2P : (2:ℚ) * P ≠ 0 := mul_ne_zero (by norm_num) hP
  have hPP : P * P ≠ 0 := mul_ne_zero hP hP
  rcases hu with hu | hu
  · subst hu
    rcases huv with huv | huv
    · left
      linarith
    · exfalso
      have h1 : 4 * P * v = 1 := by
        linear_combination (2 * P) * huv + mul_inv_cancel₀ h2P
      rcases hvv with hvv | hvv
      · have h16 : (16:ℚ) * P ^ 4 = 1 := by
          linear_combination (4 * P * v + 1) * h1 - 16 * P ^ 2 * hvv
        linarith
      · have hvvP : v * v * (P * P) = 1 := by
          rw [hvv]
          exact inv_mul_cancel₀ hPP
        have h15 : (15:ℚ) = 0 := by
          linear_combination (4 * P * v + 1) * h1 - 16 * hvvP
        norm_num at h15
  · subst hu
    rcases huv with huv | huv
    · exfalso
      have h1 : v = 4 * P := by
        linear_combination 2 * huv
      rcases hvv with hvv | hvv
      · have h15 : (15:ℚ) * P ^ 2 = 0 := by
          linear_combination hvv - (v + 4 * P) * h1
        have hpos : (0:ℚ) < P ^ 2 := by positivity
        nlinarith
      · have hvvP : v * v * (P * P) = 1 := by
          rw [hvv]
          exact inv_mul_cancel₀ hPP
        have h16 : (16:ℚ) * P ^ 4 = 1 := by
          linear_combination hvvP - (v * P ^ 2 + 4 * P ^ 3) * h1
        linarith
    · right
      have h1 : v * P = 1 := by
        linear_combination 2 * P * huv + mul_inv_cancel₀ h2P
      field_simp
      linear_combination h1

/-- **Prime-pair products plus the base two-point calibration force cost
calibration on every native prime axis.** This is the transport the round-1
premise ledger was missing: the all-prime family is not independent data once
the pair field and the base ledger's two-calibration are present. -/
theorem character_pair_two_calibration_forces_prime_calibration
    {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ)
    (hpair : PRCCharacterPrimePairProductCostConsistent χ)
    (htwo : RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two)) :
    PRCCharacterPrimeDirectionCalibrated χ := by
  intro p hp
  -- displays
  have hPne : (primeDirection p hp).toRat ≠ 0 := primeDirection_toRat_ne_zero p hp
  have hvne : (χ (primeDirection p hp)).toRat ≠ 0 := hχ.nonzero_preserving hPne
  have hPnat : p.toNat ≠ 0 := by
    have h := hPne
    rw [primeDirection_toRat] at h
    exact_mod_cast h
  have hP1 : (1:ℚ) ≤ (p.toNat : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hPnat
  have hPQ : ((p.toNat : ℚ)) ≠ 0 := by
    rw [← primeDirection_toRat p hp]
    exact hPne
  have hpd2Rat : (primeDirection twoOrbit twoOrbit_primeOrbit).toRat = 2 := by
    rw [primeDirection_toRat, twoOrbit_toNat]
    norm_num
  -- the character respects crossEq (native GCD normalization is canonical)
  have hrespect : PRCCharacterRespectsCrossEq χ :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved
  -- transfer the two-point calibration to the two prime direction
  have h2cross :
      RatioOrbit.crossEq two (primeDirection twoOrbit twoOrbit_primeOrbit) := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, two_toRat, hpd2Rat]
  have hχtwoEq :
      (χ two).toRat = (χ (primeDirection twoOrbit twoOrbit_primeOrbit)).toRat := by
    have h := hrespect two (primeDirection twoOrbit twoOrbit_primeOrbit) h2cross
    rw [RatioOrbit.crossEq_iff_toRat_eq] at h
    exact h
  -- dichotomy at the two orbit
  have h2ne : (two : RatioOrbit).toRat ≠ 0 := by
    rw [two_toRat]
    norm_num
  have hχ2ne : (χ two).toRat ≠ 0 := hχ.nonzero_preserving h2ne
  have hu :
      (χ (primeDirection twoOrbit twoOrbit_primeOrbit)).toRat = 2 ∨
        (χ (primeDirection twoOrbit twoOrbit_primeOrbit)).toRat = 2⁻¹ := by
    rcases jcost_eq_forces_same_or_reciprocal hχ2ne h2ne
        (by simpa [costFromCharacter] using htwo) with h | h
    · left
      rw [RatioOrbit.crossEq_iff_toRat_eq, two_toRat] at h
      rw [← hχtwoEq]
      exact h
    · right
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat, two_toRat] at h
      rw [← hχtwoEq]
      exact h
  -- dichotomy at the pair (2, p)
  have h2pne :
      (RatioOrbit.mul (primeDirection twoOrbit twoOrbit_primeOrbit)
        (primeDirection p hp)).toRat ≠ 0 := by
    rw [RatioOrbit.mul_toRat, hpd2Rat]
    exact mul_ne_zero (by norm_num) hPne
  have hmul2p :
      (χ (RatioOrbit.mul (primeDirection twoOrbit twoOrbit_primeOrbit)
        (primeDirection p hp))).toRat =
        (χ (primeDirection twoOrbit twoOrbit_primeOrbit)).toRat *
          (χ (primeDirection p hp)).toRat := by
    have h := hχ.multiplicative (primeDirection twoOrbit twoOrbit_primeOrbit)
      (primeDirection p hp)
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat] at h
    exact h
  have huv :
      (χ (primeDirection twoOrbit twoOrbit_primeOrbit)).toRat *
          (χ (primeDirection p hp)).toRat =
        2 * (p.toNat : ℚ) ∨
      (χ (primeDirection twoOrbit twoOrbit_primeOrbit)).toRat *
          (χ (primeDirection p hp)).toRat =
        (2 * (p.toNat : ℚ))⁻¹ := by
    have hχ2pne :
        (χ (RatioOrbit.mul (primeDirection twoOrbit twoOrbit_primeOrbit)
          (primeDirection p hp))).toRat ≠ 0 :=
      hχ.nonzero_preserving h2pne
    rcases jcost_eq_forces_same_or_reciprocal hχ2pne h2pne
        (by simpa [costFromCharacter]
          using hpair twoOrbit twoOrbit_primeOrbit p hp) with h | h
    · left
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat, hpd2Rat,
        primeDirection_toRat] at h
      rw [← hmul2p]
      exact h
    · right
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
        RatioOrbit.mul_toRat, hpd2Rat, primeDirection_toRat] at h
      rw [← hmul2p]
      exact h
  -- dichotomy at the pair (p, p)
  have hppne :
      (RatioOrbit.mul (primeDirection p hp) (primeDirection p hp)).toRat ≠ 0 := by
    rw [RatioOrbit.mul_toRat]
    exact mul_ne_zero hPne hPne
  have hmulpp :
      (χ (RatioOrbit.mul (primeDirection p hp) (primeDirection p hp))).toRat =
        (χ (primeDirection p hp)).toRat * (χ (primeDirection p hp)).toRat := by
    have h := hχ.multiplicative (primeDirection p hp) (primeDirection p hp)
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat] at h
    exact h
  have hvv :
      (χ (primeDirection p hp)).toRat * (χ (primeDirection p hp)).toRat =
        (p.toNat : ℚ) * (p.toNat : ℚ) ∨
      (χ (primeDirection p hp)).toRat * (χ (primeDirection p hp)).toRat =
        ((p.toNat : ℚ) * (p.toNat : ℚ))⁻¹ := by
    have hχppne :
        (χ (RatioOrbit.mul (primeDirection p hp) (primeDirection p hp))).toRat ≠
          0 :=
      hχ.nonzero_preserving hppne
    rcases jcost_eq_forces_same_or_reciprocal hχppne hppne
        (by simpa [costFromCharacter] using hpair p hp p hp) with h | h
    · left
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
        primeDirection_toRat] at h
      rw [← hmulpp]
      exact h
    · right
      rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
        RatioOrbit.mul_toRat, primeDirection_toRat] at h
      rw [← hmulpp]
      exact h
  -- the case split leaves the identity or reciprocal branch
  have hbranch :
      (χ (primeDirection p hp)).toRat = (p.toNat : ℚ) ∨
        (χ (primeDirection p hp)).toRat = ((p.toNat : ℚ))⁻¹ :=
    pair_two_case_split hPQ hP1 hu huv hvv
  -- both branches carry the same J display
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat, onRatioOrbit_toRat,
    primeDirection_toRat]
  rcases hbranch with h | h
  · rw [h]
  · rw [h, inv_inv]
    ring

/-! ## The slim ledger and its uniqueness theorem -/

/-- The slim hypothesis class: the round-1 minted ledger WITHOUT the all-prime
axis field. Base (reciprocity, normalization invariance, nonzero RCL,
unit-zero, two-calibration) + prime-pair products + signed unit + zero orbit. -/
structure PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  signed_strengthened : PRCSignedStrengthenedNativeCostHypotheses F
  zero_calibrated :
    PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

/-- Uniqueness over the slim ledger. -/
def PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- **The slim ledger already forces J.** Factorization needs only base + zero;
the pair and sign fields transfer to the factor character; the new transport
lemma recovers per-prime calibration from the pair field and the base
two-calibration; the existing signed-admissible rigidity closes. -/
theorem PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget_proved :
    PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget := by
  intro F hF q
  rcases PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved F
      hF.signed_strengthened.strengthened.native hF.zero_calibrated with
    ⟨χ, hχ, hFχ⟩
  have hpair : PRCCharacterPrimePairProductCostConsistent χ := by
    intro p hp r hr
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm
        (hFχ (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))))
      (hF.signed_strengthened.strengthened.prime_pair_product_cost p hp r hr)
  have htwoCal :
      RatioOrbit.crossEq (costFromCharacter χ two) (onRatioOrbit two) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ two))
      hF.signed_strengthened.strengthened.native.two_calibrated
  have hprime : PRCCharacterPrimeDirectionCalibrated χ :=
    character_pair_two_calibration_forces_prime_calibration hχ hpair htwoCal
  have hsignCost :
      RatioOrbit.crossEq (costFromCharacter χ negativeOneRatio)
        (onRatioOrbit negativeOneRatio) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ negativeOneRatio))
      hF.signed_strengthened.signed_unit
  have hsign : PRCCharacterSignedUnitCalibrated χ :=
    costFromCharacter_negativeOne_forces_signed_unit hχ hsignCost
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ
      ⟨⟨hχ, hprime, hpair⟩, hsign⟩ q)

/-! ## The ledger contraction, stated -/

/-- **The all-prime axis field is redundant.** Every inhabitant of the slim
ledger is automatically calibrated on every native prime axis. -/
theorem all_prime_axis_field_redundant
    (F : RatioOrbit → RatioOrbit)
    (hF : PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F) :
    PRCNativeCostPrimeDirectionCalibrated F := fun p hp =>
  PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget_proved
    F hF (primeDirection p hp)

/-- The slim ledger and the round-1 minted ledger carve out the same class of
native costs. -/
theorem slim_class_iff_full_class (F : RatioOrbit → RatioOrbit) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ↔
      PRCZeroCalibratedPrimeSignedStrengthenedNativeCostHypotheses F := by
  constructor
  · intro hF
    exact
      { prime_signed :=
          { signed_strengthened := hF.signed_strengthened
            prime_direction_cost := all_prime_axis_field_redundant F hF }
        zero_calibrated := hF.zero_calibrated }
  · intro hF
    exact
      { signed_strengthened := hF.prime_signed.signed_strengthened
        zero_calibrated := hF.zero_calibrated }

/-! ## Witness and decoys against the slim class -/

/-- The round-1 non-vacuity witness inhabits the slim class. -/
theorem canonicalSelectedNativeCost_slim_hypotheses :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses
      canonicalSelectedNativeCost :=
  (slim_class_iff_full_class canonicalSelectedNativeCost).mpr
    canonicalSelectedNativeCost_full_hypotheses

/-- Decoy exclusion 1 against the slim class (dies at the base
two-calibration). -/
theorem constantZeroNativeCost_slim_excluded :
    ¬ PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses
        constantZeroNativeCost :=
  fun h =>
    constantZeroNativeCost_not_native_hypotheses
      h.signed_strengthened.strengthened.native

/-- Decoy exclusion 2 against the slim class (dies at the base
two-calibration). -/
theorem linearNativeCost_slim_excluded :
    ¬ PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses linearNativeCost :=
  fun h =>
    linearNativeCost_not_native_hypotheses
      h.signed_strengthened.strengthened.native

/-- Layer discrimination: the zero-flat cost passes every slim field except
the zero orbit (round-1 theorem gives it the larger prime-signed class), and
fails the slim class exactly there. -/
theorem zeroFlatNativeCost_slim_excluded :
    ¬ PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses
        zeroFlatNativeCost := by
  intro h
  have hz := h.zero_calibrated
  rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq] at hz
  simp only [nativeCostDoubledTrace, doubledTraceValue, zeroFlatNativeCost_zero,
    RatioOrbit.mul_toRat, RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
    RatioOrbit.zero_toRat] at hz
  norm_num at hz

/-! ## The contracted deposit -/

/-- **The slim native cost-selection package** (prereg
PREREG-jfree-minimality-20260724). The round-1 package with the all-prime
axis field deleted from the ledger:

* `j_unique_native_slim`: every native cost satisfying base + prime-pair
  products + signed unit + zero orbit is crossEq-pointwise the canonical
  cost.
* `non_vacuous`: the round-1 witness inhabits the slim class.
* `zero_cost_excluded` / `linear_cost_excluded`: the frozen known-wrong costs
  fail the slim class.
* `zero_flat_passes_without_zero` / `zero_flat_excluded`: the
  layer-discrimination pair; the slim class's zero field is doing real work.

Same honest reading as round 1 (conditional δ-native rigidity, statement on
the countable carrier, classical proof shell disclosed by the axiom audit),
with one item less to pay for: the calibration ledger is now finite data on
the generators 2 and -1, the pair products, and the zero orbit. -/
structure CostSelectionPackageNativeSlim : Prop where
  j_unique_native_slim :
    PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget
  non_vacuous :
    ∃ F : RatioOrbit → RatioOrbit,
      PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ∧
        ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)
  zero_cost_excluded :
    ¬ PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses
        constantZeroNativeCost
  linear_cost_excluded :
    ¬ PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses linearNativeCost
  zero_flat_passes_without_zero :
    PRCSignedStrengthenedNativeCostHypotheses zeroFlatNativeCost
  zero_flat_excluded :
    ¬ PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses zeroFlatNativeCost

/-- The slim package holds. -/
theorem costSelectionPackageNativeSlim_holds : CostSelectionPackageNativeSlim where
  j_unique_native_slim :=
    PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget_proved
  non_vacuous :=
    ⟨canonicalSelectedNativeCost, canonicalSelectedNativeCost_slim_hypotheses,
      canonicalSelectedNativeCost_crossEq_onRatioOrbit⟩
  zero_cost_excluded := constantZeroNativeCost_slim_excluded
  linear_cost_excluded := linearNativeCost_slim_excluded
  zero_flat_passes_without_zero :=
    zeroFlatNativeCost_prime_signed_strengthened_hypotheses.signed_strengthened
  zero_flat_excluded := zeroFlatNativeCost_slim_excluded

/-- **The contracted deposit.** Same grade as round 1 (`deltaOnly`, statement
on the countable carrier under the PublicSpine statement-carrier convention),
with the all-prime calibration family removed from the price. -/
theorem cost_selection_native_slim_holds :
    PublicSpine.Tagged StrengthTag.deltaOnly CostSelectionPackageNativeSlim where
  holds := costSelectionPackageNativeSlim_holds

/-! ## The contracted premise ledger

Round 1's `nativeCostSelectionPremiseLedger` listed five items and left the
all-prime item's cost-level minimality OPEN. This session closes that item:
it is DERIVABLE, so the contracted ledger has four. -/

/-- The contracted premise ledger for the slim deposit. -/
def nativeCostSelectionSlimPremiseLedger : List StrengthClaim :=
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
  , { label := "zero_orbit"
      tag := StrengthTag.deltaOnly
      statement := "Zero-orbit calibration of the doubled trace \
(PRCDoubledTraceZeroCalibrated). Necessity: \
PRCSignedStrengthenedNativeCostUniquenessTarget_refuted (zero-flat \
countermodel, this module); the nonzero RCL never sees the zero orbit." }
  ]

/-- The contracted ledger stays at the δ-only floor. -/
theorem nativeCostSelectionSlimPremiseLedger_all_deltaOnly :
    ∀ c ∈ nativeCostSelectionSlimPremiseLedger,
      c.tag = StrengthTag.deltaOnly := by
  intro c hc
  simp only [nativeCostSelectionSlimPremiseLedger, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h <;> subst h <;> rfl

/-! ## Axiom audit (headline receipts) -/

#print axioms PRCSignedStrengthenedNativeCostUniquenessTarget_refuted
#print axioms character_pair_two_calibration_forces_prime_calibration
#print axioms PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget_proved
#print axioms all_prime_axis_field_redundant
#print axioms slim_class_iff_full_class
#print axioms costSelectionPackageNativeSlim_holds
#print axioms cost_selection_native_slim_holds

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
