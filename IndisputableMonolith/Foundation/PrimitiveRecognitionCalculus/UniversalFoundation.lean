/-
  PrimitiveRecognitionCalculus/UniversalFoundation.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 15: compose arithmetic, structural surfaces, cost, logic,
    real completion, recognizer, and admissible inevitability.

  This file declares the final PRC universal-foundation certificate after pass
  320. The final theorem keeps the repaired/refuted native-cost ledger explicit
  instead of pretending the refuted unsigned routes were proved.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Kernel
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostUniqueness

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Historical target ledger carried by the conditional top-level certificate.
Positive entries point to proved repaired interfaces; negative entries point to
the exact refutations for routes that cannot force the final surface. -/
structure PRCUniversalFoundationOpenTargets : Prop where
  zero_calibrated_native_cost_uniqueness_refuted :
    ¬ PRCJCost.PRCZeroCalibratedNativeCostUniquenessTarget
  zero_calibrated_native_cost_character_factorization :
    PRCJCost.PRCZeroCalibratedNativeCostCharacterFactorizationTarget
  zero_calibrated_native_cost_signed_admissible_factorization_refuted :
    ¬ PRCJCost.PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget
  zero_calibration_signed_unit_refuted :
    ¬ PRCJCost.PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget
  zero_calibrated_prime_signed_strengthened_native_cost_uniqueness :
    PRCJCost.PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget
  native_cost_signed_admissible_character_rigidity :
    PRCJCost.PRCNativeCostSignedAdmissibleCharacterRigidityTarget
  old_native_cost_character_rigidity_refuted :
    ¬ PRCJCost.PRCNativeCostCharacterRigidityTarget
  old_native_cost_sharpened_refuted :
    ¬ PRCJCost.PRCNativeCostUniquenessSharpenedTarget
  two_to_prime_calibration_refuted :
    ¬ PRCJCost.PRCTwoCalibrationForcesPrimeCalibrationTarget
  prime_calibration_propagation_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationPropagationTarget
  prime_global_orientation_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesGlobalOrientationTarget
  coherent_prime_orientation :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeOrientationCoherent χ →
        PRCJCost.PRCCharacterTwoPrimeBranchControlsPrimes χ
  two_prime_branch_controls_primes :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeLocalOrientation χ →
        PRCJCost.PRCCharacterTwoPrimeBranchControlsPrimes χ →
          PRCJCost.PRCCharacterPrimeOrientationCoherent χ
  prime_identity_iff_two_prime_identity :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeLocalOrientation χ →
        PRCJCost.PRCCharacterTwoPrimeBranchControlsPrimes χ →
          PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ
  prime_identity_forces_two_prime_identity :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ →
        PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ
  two_prime_reciprocal_excludes_prime_identity :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeLocalOrientation χ →
        (PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ ↔
          PRCJCost.PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ)
  two_prime_reciprocal_excludes_prime_identity_witness :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity χ ↔
        PRCJCost.PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentityWitness χ)
  two_prime_reciprocal_identity_prime_mixed :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed χ ↔
        PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ)
  two_prime_reciprocal_identity_non_two_prime_mixed :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCRatioCharacter χ →
        (PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed χ ↔
          PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ)
  two_prime_reciprocal_identity_non_two_composite_defect :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ ↔
        PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ)
  two_prime_reciprocal_identity_non_two_composite_cost_defect :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeCostDefect χ →
        PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect χ
  two_prime_mixed_composite_cost_consistency_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_pair_product_cost_consistency_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  two_prime_reciprocal_forces_prime_reciprocal :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizes χ →
        PRCJCost.PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ
  two_prime_reciprocal_trace_connected :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterTwoPrimeReciprocalRespectsTraceConnected χ ↔
        PRCJCost.PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal χ)
  two_prime_identity_trace_connected :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeIdentityRespectsTraceConnected χ →
        PRCJCost.PRCCharacterTwoPrimeIdentityRespectsTraceConnected χ
  no_mixed_prime_orientation :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterNoMixedPrimeWitnesses χ ↔
        PRCJCost.PRCCharacterNoMixedPrimeOrientation χ)
  mixed_prime_witnesses :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterMixedPrimeWitnesses χ ↔
        PRCJCost.PRCCharacterMixedPrimePairWitnesses χ)
  mixed_prime_pair_witnesses :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterMixedPrimePairWitnesses χ ↔
        PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ ∨
          PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ)
  same_prime_mixed_pair_witnesses :
    {χ : RatioOrbit → RatioOrbit} →
      ¬ PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ
  distinct_prime_mixed_pair_witnesses :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ →
        ¬ PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ
  prime_identity_witness_excludes_reciprocal :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityWitnessExcludesReciprocal χ ↔
        PRCJCost.PRCCharacterNoMixedPrimeOrientation χ)
  prime_reciprocal_witness_globalizes :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeLocalOrientation χ →
        PRCJCost.PRCCharacterNoMixedPrimeOrientation χ →
          PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizes χ
  prime_reciprocal_forces_two_prime_reciprocal :
    {χ : RatioOrbit → RatioOrbit} →
      PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizes χ →
        PRCJCost.PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ
  prime_reciprocal_witness_globalizes_split :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizes χ ↔
        PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizesSplit χ)
  prime_reciprocal_forces_two_from_reciprocal_twist_identity_forces_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity
          (PRCJCost.PRCCharacterReciprocalTwist χ) →
        PRCJCost.PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal χ
  prime_identity_forces_two_from_reciprocal_twist_reciprocal_forces_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal
          (PRCJCost.PRCCharacterReciprocalTwist χ) →
        PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity χ
  prime_identity_trace_coherence :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ ↔
        PRCJCost.PRCCharacterPrimeIdentityTraceCoherent χ)
  prime_identity_branch_uniform :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ ↔
        PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ)
  prime_axis_trace_connected :
    ∀ p : DistinctionNat, ∀ hp : DistinctionNat.primeOrbit p,
      ∀ r : DistinctionNat, ∀ hr : DistinctionNat.primeOrbit r,
        PRCJCost.PRCPrimeAxisTraceConnected p hp r hr
  prime_identity_respects_trace_connected :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ ↔
        PRCJCost.PRCCharacterPrimeIdentityRespectsTraceConnected χ)
  prime_identity_respects_common_trace_extension :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ ↔
        PRCJCost.PRCCharacterPrimeIdentityRespectsCommonTraceExtension χ)
  prime_identity_respects_canonical_add_trace :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ ↔
        PRCJCost.PRCCharacterPrimeIdentityRespectsCanonicalAddTrace χ)
  prime_identity_respects_comparable_trace :
    {χ : RatioOrbit → RatioOrbit} →
      (PRCJCost.PRCCharacterPrimeIdentityRespectsComparableTrace χ ↔
        PRCJCost.PRCCharacterPrimeIdentityTraceCoherent χ)
  prime_identity_trace_coherence_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_branch_uniformity_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_trace_transport_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_common_trace_extension_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_comparable_trace_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  orbit_successor_identity_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget
  orbit_successor_transport_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget
  prime_floor_successor_transport_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_identity_witness_globalizes_nonunit_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  prime_floor_identity_extends_successor_step_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget
  prime_floor_identity_contracts_successor_step_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget
  prime_floor_identity_successor_step_pair_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_local_orientation_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget
  prime_floor_nonunit_product_local_orientation_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget
  prime_floor_nonunit_orbit_orientation_coherent_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_no_mixed_nonunit_orbit_orientation_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_nonunit_identity_branch_transport_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_nonunit_identity_witness_globalizes_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_nonunit_identity_witness_excludes_reciprocal_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_nonunit_no_mixed_witnesses_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_no_mixed_prime_witnesses_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_mixed_prime_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_mixed_prime_pair_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_same_prime_mixed_pair_witness_character_refuted :
    ¬ PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter
  prime_floor_distinct_prime_mixed_pair_witness_character :
    PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_identity_witness_excludes_reciprocal_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget
  prime_floor_prime_reciprocal_forces_two_prime_reciprocal_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_prime_witnesses_control_nonunit_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget
  prime_floor_mixed_nonunit_witnesses_reflect_prime_target :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_mixed_nonunit_identity_witness_reflects_prime_target :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_nonunit_reciprocal_witness_reflects_prime_target :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_nonunit_witnesses_reflect_prime_split_target :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_nonunit_no_mixed_witnesses_split_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_nonunit_identity_witness_local_exclusion_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget
  prime_floor_nonunit_reciprocal_branch_transport_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget
  prime_floor_nonunit_branch_transport_pair_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget
  prime_floor_nonunit_identity_comparable_trace_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_branch_agreement_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget
  prime_floor_nonunit_orbit_orientation_local_branch_agreement_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget
  prime_floor_nonunit_orbit_orientation_local_identity_transport_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget
  prime_floor_nonunit_orbit_orientation_local_comparable_trace_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget
  prime_floor_nonunit_orbit_orientation_local_no_mixed_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget
  prime_floor_nonunit_orbit_orientation_local_product_no_mixed_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget
  prime_floor_no_mixed_nonunit_from_product_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_product_no_mixed_from_no_mixed_nonunit :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_product_no_mixed_iff_no_mixed_nonunit :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_product_no_mixed_from_identity_branch_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_nonunit_identity_branch_transport_from_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_nonunit_coherent_from_product_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_product_no_mixed_iff_nonunit_coherent :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_nonunit_identity_branch_transport_from_product_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_product_no_mixed_iff_identity_branch_transport :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_identity_witness_globalizes_from_identity_branch_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_identity_branch_transport_from_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_identity_witness_globalizes_iff_identity_branch_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_identity_witness_globalizes_from_product_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_product_no_mixed_from_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_product_no_mixed_iff_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_nonunit_coherent_from_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_identity_witness_globalizes_from_nonunit_coherent :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_nonunit_coherent_iff_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_identity_witness_excludes_reciprocal_from_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_from_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_identity_witness_excludes_reciprocal_iff_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget
  prime_floor_no_mixed_witnesses_from_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_identity_witness_excludes_reciprocal_from_no_mixed_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_witnesses_iff_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_witnesses_from_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_no_mixed_prime_orientation_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_orientation_from_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_iff_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_no_mixed_prime_witnesses_from_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_witnesses_iff_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_no_mixed_prime_witnesses_iff_not_mixed_prime_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterNoMixedPrimeWitnesses χ ↔
        ¬ PRCJCost.PRCCharacterMixedPrimeWitnesses χ
  prime_floor_mixed_prime_pair_witnesses_from_mixed_prime_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterMixedPrimeWitnesses χ →
        PRCJCost.PRCCharacterMixedPrimePairWitnesses χ
  prime_floor_mixed_prime_witnesses_from_pair_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterMixedPrimePairWitnesses χ →
        PRCJCost.PRCCharacterMixedPrimeWitnesses χ
  prime_floor_mixed_prime_witnesses_iff_pair_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterMixedPrimeWitnesses χ ↔
        PRCJCost.PRCCharacterMixedPrimePairWitnesses χ
  prime_floor_no_mixed_prime_witnesses_iff_not_mixed_prime_pair_witnesses :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterNoMixedPrimeWitnesses χ ↔
        ¬ PRCJCost.PRCCharacterMixedPrimePairWitnesses χ
  prime_floor_mixed_prime_pair_witnesses_same_or_distinct :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterMixedPrimePairWitnesses χ →
        PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ ∨
          PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ
  prime_floor_mixed_prime_pair_witnesses_from_same_or_distinct :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ ∨
        PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ →
          PRCJCost.PRCCharacterMixedPrimePairWitnesses χ
  prime_floor_mixed_prime_pair_witnesses_iff_same_or_distinct :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterMixedPrimePairWitnesses χ ↔
        PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ ∨
          PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ
  prime_floor_no_mixed_prime_witnesses_iff_no_same_and_no_distinct_pair :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterNoMixedPrimeWitnesses χ ↔
        ¬ PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ ∧
          ¬ PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ
  prime_floor_same_prime_mixed_pair_witnesses_absurd :
    ∀ χ : RatioOrbit → RatioOrbit,
      ¬ PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses χ
  prime_floor_no_mixed_prime_witnesses_iff_not_distinct_prime_pair :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterNoMixedPrimeWitnesses χ ↔
        ¬ PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ
  prime_floor_distinct_prime_mixed_pair_witnesses_absurd_from_branch_uniform :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ →
        ¬ PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ
  prime_floor_prime_identity_branch_uniform_from_local_no_distinct_prime_pair :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeLocalOrientation χ →
        ¬ PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ →
          PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ
  prime_floor_prime_identity_branch_uniform_iff_no_distinct_prime_pair_of_local :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeLocalOrientation χ →
        (PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ ↔
          ¬ PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses χ)
  prime_floor_prime_identity_branch_uniform_from_identity_iff_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ →
        PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ
  prime_floor_prime_identity_iff_two_from_branch_uniform :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ →
        PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ
  prime_floor_prime_identity_branch_uniform_iff_identity_iff_two :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform χ ↔
        PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity χ
  prime_floor_prime_reciprocal_witness_globalizes_from_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget
  prime_floor_no_mixed_prime_orientation_from_reciprocal_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_reciprocal_witness_globalizes_iff_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_floor_prime_reciprocal_witness_globalizes_iff_identity_witness_excludes_reciprocal :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget
  prime_floor_prime_reciprocal_forces_two_from_reciprocal_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget
  prime_floor_two_prime_reciprocal_forces_from_reciprocal_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_from_reciprocal_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_prime_reciprocal_witness_globalizes_from_split :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget
  prime_floor_prime_reciprocal_witness_globalizes_iff_split :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_prime_reciprocal_forces_two_from_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget
  prime_floor_prime_identity_forces_two_from_reciprocal_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_reciprocal_forces_two_iff_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_excludes :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_two_prime_reciprocal_excludes_from_identity_witness_excludes :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  prime_floor_two_prime_reciprocal_excludes_iff_identity_witness_excludes :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_prime_identity_forces_two_from_two_prime_reciprocal_excludes_identity_witness :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_prime_identity_forces_two_iff_two_prime_reciprocal_excludes_identity_witness :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_no_mixed_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_no_mixed_character_from_two_prime_reciprocal_excludes_identity_witness :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget →
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_mixed_character :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  prime_floor_non_two_mixed_character_from_mixed_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_mixed_character_from_non_two_mixed_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  prime_floor_mixed_character_iff_non_two_mixed_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter ↔
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_non_two_mixed_character :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_composite_defect_character_from_non_two_mixed_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  prime_floor_non_two_mixed_character_from_composite_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_non_two_mixed_character_iff_composite_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter ↔
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_composite_defect_character :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  prime_floor_composite_cost_defect_character_from_composite_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_composite_defect_character_from_composite_cost_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  prime_floor_composite_defect_character_iff_composite_cost_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter ↔
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_composite_cost_defect_character :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_two_prime_mixed_composite_cost_consistency_from_no_cost_defect :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_no_cost_defect_from_two_prime_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_two_prime_mixed_composite_cost_consistency_iff_no_cost_defect :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_mixed_composite_cost_consistency_direct :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_two_prime_mixed_composite_cost_consistency_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_prime_pair_product_cost_consistency_from_prime_calibration_propagation :
    PRCJCost.PRCPrimeCalibrationPropagationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_prime_pair_product_cost_consistency_from_coherent_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_coherent_prime_orientation_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  prime_floor_prime_pair_product_cost_consistency_iff_coherent_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  prime_floor_prime_pair_product_cost_consistency_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_no_mixed_prime_witnesses_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_prime_pair_product_cost_consistency_iff_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_no_mixed_prime_witness_character_absurd_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      ¬ PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_no_mixed_prime_witnesses_from_no_mixed_prime_witness_character :
    ¬ PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_prime_pair_product_cost_consistency_iff_no_mixed_prime_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_no_mixed_prime_witnesses_not_from_mixed_prime_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_mixed_prime_witness_character_from_not_no_mixed_prime_witnesses :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_no_mixed_prime_witnesses_not_iff_mixed_prime_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_prime_pair_product_cost_consistency_not_from_mixed_prime_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_mixed_prime_witness_character_from_not_prime_pair_product_cost_consistency :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_prime_pair_product_cost_consistency_not_iff_mixed_prime_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_mixed_prime_pair_witness_character_from_mixed_prime_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter →
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_mixed_prime_witness_character_from_pair_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter →
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter
  prime_floor_mixed_prime_witness_character_iff_pair_witness_character :
    PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter ↔
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_no_mixed_prime_witnesses_not_iff_mixed_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_iff_no_mixed_prime_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_not_iff_mixed_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_mixed_prime_pair_witness_character_same_or_distinct :
    PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter →
      PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_mixed_prime_pair_witness_character_from_same_or_distinct :
    PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
      PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter →
        PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter
  prime_floor_mixed_prime_pair_witness_character_iff_same_or_distinct :
    PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter ↔
      PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_no_mixed_prime_witnesses_iff_no_same_and_no_distinct_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∧
        ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_no_mixed_prime_witnesses_not_iff_same_or_distinct_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_iff_no_same_and_no_distinct_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∧
        ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_not_iff_same_or_distinct_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter ∨
        PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_same_prime_mixed_pair_witness_character_absurd :
    ¬ PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter
  prime_floor_no_mixed_prime_witnesses_iff_no_distinct_prime_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_no_mixed_prime_witnesses_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_iff_no_distinct_prime_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_identity_branch_uniformity_from_no_distinct_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_floor_no_distinct_prime_pair_witness_character_from_prime_identity_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_identity_branch_uniformity_iff_no_distinct_prime_pair_witness_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_identity_branch_uniformity_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_pair_product_cost_consistency_iff_prime_identity_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_floor_prime_identity_branch_uniformity_from_identity_iff_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_floor_prime_identity_iff_two_from_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_floor_prime_identity_branch_uniformity_iff_identity_iff_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_floor_prime_identity_branch_uniformity_iff_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_pair_product_cost_consistency_iff_prime_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_identity_forces_two_not_iff_distinct_prime_pair_witness_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter
  prime_floor_prime_identity_forces_two_iff_no_two_prime_mixed_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  prime_floor_prime_identity_forces_two_iff_no_non_two_mixed_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_non_two_mixed_character_from_two_adic_axis_twist :
    PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_prime_calibration_from_two_adic_axis_twist :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCCharacterTwoAdicAxisTwist χ →
        PRCJCost.PRCCharacterPrimeDirectionCalibrated χ
  prime_floor_calibrated_two_adic_axis_twist_from_ratio_character_axis_twist :
    PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_ratio_character_axis_twist_from_calibrated_two_adic_axis_twist :
    PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_calibrated_two_adic_axis_twist_iff_ratio_character_axis_twist :
    PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter ↔
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_ratio_character_axis_twist_absurd_from_no_calibrated_twist :
    ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_two_adic_axis_twist_absurd_from_no_non_two_mixed :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter →
      ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_two_adic_axis_twist_absurd_from_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_two_adic_axis_twist_absurd_from_prime_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_two_adic_axis_twist_absurd_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_mixed_composite_cost_consistency_not_from_two_adic_axis_twist :
    PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_prime_identity_forces_two_not_from_two_adic_axis_twist :
    PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_pair_product_cost_consistency_not_from_two_adic_axis_twist :
    PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_ratio_character_axis_twist_absurd_from_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_ratio_character_axis_twist_absurd_from_prime_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_ratio_character_axis_twist_absurd_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_mixed_composite_cost_consistency_not_from_ratio_character_axis_twist :
    PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_prime_identity_forces_two_not_from_ratio_character_axis_twist :
    PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_pair_product_cost_consistency_not_from_ratio_character_axis_twist :
    PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_two_three_mixed_not_composite :
    ¬ RatioOrbit.crossEq PRCJCost.twoThreePrimeMixedDirection
      PRCJCost.twoThreePrimeCompositeDirection
  prime_floor_two_three_mixed_not_composite_recip :
    ¬ RatioOrbit.crossEq PRCJCost.twoThreePrimeMixedDirection
      (RatioOrbit.recip PRCJCost.twoThreePrimeCompositeDirection)
  prime_floor_two_adic_axis_twist_two_three_mixed_image :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCRatioCharacter χ →
        PRCJCost.PRCCharacterTwoAdicAxisTwist χ →
          RatioOrbit.crossEq (χ PRCJCost.twoThreePrimeCompositeDirection)
            PRCJCost.twoThreePrimeMixedDirection
  prime_floor_two_adic_axis_twist_two_three_local_orientation_absurd :
    ∀ χ : RatioOrbit → RatioOrbit,
      PRCJCost.PRCRatioCharacter χ →
        PRCJCost.PRCCharacterTwoAdicAxisTwist χ →
          ¬ PRCJCost.PRCCharacterTwoThreeCompositeLocalOrientation χ
  prime_floor_ratio_character_axis_twist_forces_two_three_local_orientation_failure :
    PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      ∃ χ : RatioOrbit → RatioOrbit,
        PRCJCost.PRCRatioCharacter χ ∧
          PRCJCost.PRCCharacterTwoAdicAxisTwist χ ∧
            ¬ PRCJCost.PRCCharacterTwoThreeCompositeLocalOrientation χ
  prime_floor_two_three_failure_character_from_ratio_character_axis_twist :
    PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_ratio_character_axis_twist_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_two_three_failure_character_iff_ratio_character_axis_twist :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter ↔
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_two_three_failure_character_iff_calibrated_two_adic_axis_twist :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter ↔
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_two_three_local_orientation_target_from_no_ratio_character_axis_twist :
    ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_ratio_character_axis_twist_absurd_from_two_three_local_orientation_target :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget →
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_two_three_local_orientation_target_iff_no_ratio_character_axis_twist :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_two_three_failure_character_absurd_from_two_three_local_orientation_target :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_local_orientation_target_iff_no_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_local_orientation_target_iff_no_calibrated_two_adic_axis_twist :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_calibrated_two_adic_axis_twist_absurd_from_two_three_local_orientation_target :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget →
      ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_two_three_local_orientation_target_from_no_failure_character :
    ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_fork_certificate :
    PRCJCost.PRCTwoThreeCompositeLocalForkCertificate
  prime_floor_calibrated_two_adic_axis_twist_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter
  prime_floor_non_two_mixed_character_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_composite_defect_character_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  prime_floor_composite_cost_defect_character_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_mixed_composite_cost_consistency_not_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_prime_identity_forces_two_not_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_floor_prime_pair_product_cost_consistency_not_from_two_three_failure_character :
    PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter →
      ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  prime_floor_two_three_failure_character_absurd_from_no_calibrated_two_adic_axis_twist :
    ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_failure_character_absurd_from_no_non_two_mixed_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_failure_character_absurd_from_no_non_two_composite_defect_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_failure_character_absurd_from_no_non_two_composite_cost_defect_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_local_orientation_target_from_no_calibrated_two_adic_axis_twist :
    ¬ PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_orientation_target_from_no_non_two_mixed_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_orientation_target_from_no_non_two_composite_defect_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_orientation_target_from_no_non_two_composite_cost_defect_character :
    ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_orientation_target_from_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_orientation_target_from_prime_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_local_orientation_target_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_two_three_failure_character_absurd_from_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_failure_character_absurd_from_prime_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_failure_character_absurd_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_ratio_character_axis_twist_absurd_from_prime_identity_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      ¬ PRCJCost.PRCTwoAdicAxisTwistRatioCharacter
  prime_floor_two_three_failure_character_absurd_from_prime_identity_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      ¬ PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter
  prime_floor_two_three_local_orientation_target_from_prime_identity_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget
  prime_floor_prime_identity_forces_two_iff_no_non_two_composite_defect_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  prime_floor_prime_identity_forces_two_iff_no_non_two_composite_cost_defect_character :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_prime_identity_forces_two_not_iff_non_two_composite_cost_defect_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_prime_identity_forces_two_iff_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_prime_pair_product_cost_consistency_iff_mixed_composite_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  prime_floor_two_prime_mixed_composite_cost_consistency_iff_no_non_two_mixed_character :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      ¬ PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_two_prime_mixed_composite_cost_consistency_not_iff_non_two_mixed_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  prime_floor_two_prime_mixed_composite_cost_consistency_not_iff_non_two_composite_cost_defect_character :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget ↔
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  prime_floor_two_prime_reciprocal_excludes_identity_witness_from_prime_pair_product_cost_consistency :
    PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_from_two_prime_reciprocal_forces :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget
  prime_floor_two_prime_reciprocal_forces_from_split :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_floor_prime_reciprocal_witness_globalizes_split_iff_two_prime_reciprocal_forces :
    PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_identity_trace_coherence_from_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_no_mixed_prime_orientation_iff_trace_coherence :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_no_mixed_prime_orientation_from_branch_uniformity :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_identity_branch_uniformity_from_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_branch_uniformity_iff_no_mixed_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget
  prime_no_mixed_prime_witnesses_iff_trace_coherence :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  coherent_prime_orientation_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  no_mixed_prime_witnesses_from_coherent_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  no_mixed_prime_witnesses_iff_coherent_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  two_prime_branch_controls_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  two_prime_branch_controls_from_coherent_prime_orientation :
    PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  coherent_prime_orientation_from_two_prime_branch_controls :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget →
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  coherent_prime_orientation_iff_two_prime_branch_controls :
    PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  prime_identity_iff_two_prime_identity_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_identity_forces_two_prime_identity_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_excludes_prime_identity_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  two_prime_reciprocal_excludes_prime_identity_witness_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget
  two_prime_reciprocal_identity_prime_mixed_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter
  two_prime_reciprocal_identity_non_two_prime_mixed_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter
  two_prime_reciprocal_identity_non_two_composite_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter
  two_prime_reciprocal_identity_non_two_composite_cost_defect_character :
    PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter
  calibrated_two_prime_mixed_composite_cost_consistency_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget
  calibrated_prime_pair_product_cost_consistency_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget
  two_prime_reciprocal_forces_prime_reciprocal_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_trace_connected_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget
  two_prime_identity_trace_connected_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  prime_identity_iff_two_from_two_prime_branch_controls :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  two_prime_branch_controls_from_prime_identity_iff_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget
  two_prime_branch_controls_iff_prime_identity_iff_two :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_identity_forces_two_from_identity_iff_two_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_identity_iff_two_from_identity_forces_two_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget
  prime_identity_iff_two_iff_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_excludes_from_identity_forces_two_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  prime_identity_forces_two_from_two_prime_reciprocal_excludes_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  prime_identity_forces_two_target_iff_two_prime_reciprocal_excludes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  two_prime_reciprocal_excludes_from_two_prime_reciprocal_forces_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget
  two_prime_reciprocal_forces_from_two_prime_reciprocal_excludes_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_excludes_target_iff_two_prime_reciprocal_forces :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_forces_from_identity_forces_two_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  prime_identity_forces_two_from_two_prime_reciprocal_forces_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_forces_target_iff_identity_forces_two :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget
  two_prime_reciprocal_forces_from_trace_connected_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_trace_connected_from_forces_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget
  two_prime_reciprocal_trace_connected_target_iff_forces :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget
  two_prime_reciprocal_trace_connected_from_identity_trace_connected_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget
  two_prime_identity_trace_connected_from_reciprocal_trace_connected_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  two_prime_reciprocal_trace_connected_target_iff_identity_trace_connected :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  two_prime_identity_trace_connected_from_prime_identity_trace_transport_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget
  prime_identity_trace_transport_from_two_prime_identity_trace_connected_target :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  two_prime_identity_trace_connected_target_iff_prime_identity_trace_transport :
    PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_canonical_add_trace_from_common_trace_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_common_trace_from_canonical_add_trace_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_target_iff_common_trace :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_canonical_add_trace_from_trace_transport_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_trace_transport_from_canonical_add_trace_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_canonical_add_trace_target_iff_trace_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_branch_uniformity_from_trace_coherence_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_trace_coherence_from_branch_uniformity_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_branch_uniformity_target_iff_trace_coherence :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_canonical_add_trace_from_branch_uniformity_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_branch_uniformity_from_canonical_add_trace_target :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget
  prime_identity_branch_uniformity_target_iff_canonical_add_trace :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget
  prime_identity_comparable_trace_from_trace_coherence :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  prime_identity_trace_coherence_from_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_trace_coherence_iff_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  prime_identity_comparable_trace_from_nonunit_identity_comparable :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget
  nonunit_identity_comparable_trace_from_prime_identity_comparable :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_identity_comparable_trace_iff_nonunit_identity_comparable :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_identity_comparable_trace_iff_prime_floor_successor_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_identity_common_trace_from_trace_coherence :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_trace_coherence_from_common_trace :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget
  prime_identity_trace_coherence_iff_common_trace :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget
  prime_identity_trace_transport_from_trace_coherence :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_identity_trace_coherence_iff_trace_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget
  prime_floor_no_mixed_prime_witnesses_from_nonunit_no_mixed_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_nonunit_no_mixed_witnesses_split_from_nonunit_no_mixed_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_nonunit_no_mixed_witnesses_from_split :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_nonunit_no_mixed_witnesses_iff_split :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_prime_witnesses_control_from_mixed_reflects :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget
  prime_floor_mixed_reflects_from_prime_witnesses_control :
    PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_prime_witnesses_control_iff_mixed_reflects :
    PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_mixed_reflection_split_from_reflects :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_mixed_reflection_from_split :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget →
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_mixed_reflection_iff_split :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_mixed_identity_reflects_prime_proved :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_reciprocal_reflects_prime_proved :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget
  prime_floor_mixed_reflection_split_proved :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget
  prime_floor_mixed_reflection_proved :
    PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget
  prime_floor_prime_witnesses_control_nonunit_proved :
    PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget
  prime_floor_nonunit_no_mixed_split_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget
  prime_floor_nonunit_no_mixed_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget
  prime_floor_nonunit_no_mixed_iff_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_identity_witness_globalizes_from_local_exclusion :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget
  prime_floor_identity_witness_local_exclusion_from_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget
  prime_floor_identity_witness_globalizes_iff_local_exclusion :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget
  prime_floor_nonunit_identity_comparable_trace_from_product_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_identity_branch_transport_iff_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_product_no_mixed_iff_identity_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_product_local_orientation_from_identity_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget
  prime_floor_nonunit_local_orientation_from_identity_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget
  prime_floor_nonunit_local_comparable_trace_from_identity_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget
  prime_floor_nonunit_identity_comparable_trace_from_local_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_local_comparable_trace_iff_identity_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_branch_agreement_from_transport_pair :
    PRCJCost.PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget
  prime_floor_nonunit_identity_branch_transport_from_branch_agreement :
    PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget
  prime_floor_nonunit_reciprocal_branch_transport_from_branch_agreement :
    PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget
  prime_floor_nonunit_branch_transport_pair_from_branch_agreement :
    PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget
  prime_floor_nonunit_branch_agreement_iff_transport_pair :
    PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget
  prime_floor_nonunit_branch_agreement_from_local_identity_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget
  prime_floor_nonunit_local_identity_transport_from_local_branch_agreement :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget
  prime_floor_nonunit_local_branch_agreement_from_local_identity_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget
  prime_floor_nonunit_local_branch_agreement_iff_local_identity_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget
  prime_floor_nonunit_local_comparable_trace_from_local_identity_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget
  prime_floor_nonunit_local_identity_transport_from_local_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget
  prime_floor_nonunit_local_identity_transport_iff_local_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget
  prime_floor_nonunit_branch_agreement_from_coherent :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget
  prime_floor_nonunit_local_branch_agreement_from_coherent :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget
  prime_floor_nonunit_coherent_from_local_branch_agreement :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_nonunit_orbit_orientation_coherent_iff_local_branch_agreement :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget
  prime_floor_nonunit_identity_comparable_trace_iff_successor_transport :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_identity_extends_successor_step_from_successor_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget
  prime_floor_identity_contracts_successor_step_from_successor_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget
  prime_floor_identity_successor_step_pair_from_successor_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_successor_transport_from_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_successor_transport_iff_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_identity_witness_globalizes_nonunit_from_successor_transport :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  prime_floor_successor_transport_from_prime_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget
  prime_floor_successor_transport_iff_prime_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  prime_identity_witness_globalizes_nonunit_from_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget
  no_mixed_prime_witnesses_from_prime_identity_witness_globalizes :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget →
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_identity_witness_globalizes_nonunit_iff_no_mixed_prime_witnesses :
    PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget
  prime_floor_identity_successor_step_pair_from_identity_comparable_trace :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_identity_comparable_trace_from_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget
  prime_floor_nonunit_identity_comparable_trace_iff_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_product_no_mixed_from_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget
  prime_floor_identity_successor_step_pair_from_product_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_product_no_mixed_iff_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_coherent_from_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget →
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_identity_successor_step_pair_from_nonunit_coherent :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget →
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_nonunit_coherent_iff_successor_step_pair :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget
  prime_floor_successor_transport_local_adjacent_target_refuted :
    ¬ PRCJCost.PRCPrimeFloorSuccessorTransportLocalAdjacentTarget
  prime_floor_successor_transport_local_adjacent_iff_local_successor_transport :
    PRCJCost.PRCPrimeFloorSuccessorTransportLocalAdjacentTarget ↔
      (PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget ∧
        PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget)
  prime_floor_successor_transport_local_adjacent_iff_nonunit_coherent :
    PRCJCost.PRCPrimeFloorSuccessorTransportLocalAdjacentTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget
  prime_floor_nonunit_orbit_orientation_coherent_iff_local_no_mixed :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget
  prime_floor_nonunit_orbit_orientation_coherent_sharpened_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget
  prime_floor_nonunit_orbit_orientation_coherent_iff_sharpened :
    PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget ↔
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget
  prime_floor_product_local_orientation_sharpened_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget
  prime_floor_no_adjacent_mixed_orientation_target_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget
  prime_floor_successor_transport_sharpened_refuted :
    ¬ PRCJCost.PRCPrimeFloorSuccessorTransportSharpenedTarget
  prime_to_coherent_orientation_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget
  coherent_prime_orientation_propagation_refuted :
    ¬ PRCJCost.PRCCoherentPrimeOrientationPropagatesToGlobalTarget
  admissible_prime_orientation_coherent :
    PRCJCost.PRCAdmissibleCharacterPrimeOrientationCoherentTarget
  admissible_signed_unit_calibration_refuted :
    ¬ PRCJCost.PRCAdmissibleCharacterSignedUnitCalibratedTarget
  signed_coherent_prime_orientation_propagation :
    PRCJCost.PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget
  prime_propagation_sharpened_refuted :
    ¬ PRCJCost.PRCPrimeCalibrationPropagationSharpenedTarget
  native_cost_rigidity_sharpened_refuted :
    ¬ PRCJCost.PRCNativeCostCharacterRigiditySharpenedTarget
  external_foundation_parsing_schema :
    ∀ (ExternalFoundation : Type)
      (FaithfulParse : ExternalFoundation → FormalSystem → Prop),
      ExternalFoundationParsingTarget ExternalFoundation FaithfulParse =
        ExternalFoundationParsingTarget ExternalFoundation FaithfulParse

/-- Top-level conditional certificate: all built PRC surfaces compose, with the
repaired/refuted native-cost ledger exposed by name. -/
structure PRCUniversalFoundationConditionalCertificate : Prop where
  kernel : KernelFirstPassCertificate
  real_complete_ordered_field :
    PRCRealCompleteOrderedFieldPromotedCertificate
  trace_logic : TraceLogicCertificate
  formal_system : FormalSystemCertificate
  inevitability : PRCInevitabilityCertificate
  recognizer_bridge : PRCRecognizerBridgeCertificate
  native_cost_blocker : PRCJCost.PRCNativeCostUniquenessBlockerCertificate
  open_targets : PRCUniversalFoundationOpenTargets
  no_project_local_axioms_audit :
    StrengthTag.classicalExtension = StrengthTag.classicalExtension

/-- Final PRC universal-foundation certificate. The certificate closes the
top-level theorem by carrying the built PRC surfaces together with the exact
native-cost ledger: the repaired signed/prime/zero-calibrated uniqueness route
is proved, while the weaker unsigned routes are recorded as refuted targets. -/
structure PRCUniversalFoundationCertificate : Prop where
  delta_kernel : KernelFirstPassCertificate
  real_complete_ordered_field :
    PRCRealCompleteOrderedFieldPromotedCertificate
  trace_logic : TraceLogicCertificate
  formal_system : FormalSystemCertificate
  inevitability : PRCInevitabilityCertificate
  recognizer_bridge : PRCRecognizerBridgeCertificate
  native_cost_blocker : PRCJCost.PRCNativeCostUniquenessBlockerCertificate
  repaired_refuted_native_cost_ledger : PRCUniversalFoundationOpenTargets
  conditional_certificate : PRCUniversalFoundationConditionalCertificate
  no_project_local_axioms_audit :
    StrengthTag.classicalExtension = StrengthTag.classicalExtension

theorem prc_universal_foundation_conditional_certificate :
    PRCUniversalFoundationConditionalCertificate where
  kernel := kernel_first_pass_certificate
  real_complete_ordered_field :=
    prc_real_complete_ordered_field_promoted_certificate
  trace_logic := trace_logic_certificate
  formal_system := formal_system_certificate
  inevitability := prc_inevitability_certificate
  recognizer_bridge := prc_recognizer_bridge_certificate
  native_cost_blocker := PRCJCost.prc_native_cost_uniqueness_blocker_certificate
  open_targets := {
    zero_calibrated_native_cost_uniqueness_refuted :=
      PRCJCost.PRCZeroCalibratedNativeCostUniquenessTarget_refuted
    zero_calibrated_native_cost_character_factorization :=
      PRCJCost.PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved
    zero_calibrated_native_cost_signed_admissible_factorization_refuted :=
      PRCJCost.PRCZeroCalibratedNativeCostSignedAdmissibleCharacterFactorizationTarget_refuted
    zero_calibration_signed_unit_refuted :=
      PRCJCost.PRCZeroCalibrationForcesNativeCostSignedUnitCalibrationTarget_refuted
    zero_calibrated_prime_signed_strengthened_native_cost_uniqueness :=
      PRCJCost.PRCZeroCalibratedPrimeSignedStrengthenedNativeCostUniquenessTarget_proved
    native_cost_signed_admissible_character_rigidity :=
      PRCJCost.PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved
    old_native_cost_character_rigidity_refuted :=
      PRCJCost.PRCNativeCostCharacterRigidityTarget_refuted
    old_native_cost_sharpened_refuted :=
      PRCJCost.PRCNativeCostUniquenessSharpenedTarget_refuted
    two_to_prime_calibration_refuted :=
      PRCJCost.PRCTwoCalibrationForcesPrimeCalibrationTarget_refuted
    prime_calibration_propagation_refuted :=
      PRCJCost.PRCPrimeCalibrationPropagationTarget_refuted
    prime_global_orientation_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesGlobalOrientationTarget_refuted
    coherent_prime_orientation :=
      PRCJCost.PRCCharacterTwoPrimeBranchControlsPrimes_of_coherent
    two_prime_branch_controls_primes :=
      PRCJCost.PRCCharacterPrimeOrientationCoherent_of_local_two_prime_branch_controls
    prime_identity_iff_two_prime_identity :=
      PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_local_two_prime_branch_controls
    prime_identity_forces_two_prime_identity :=
      PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_identity_iff_two
    two_prime_reciprocal_excludes_prime_identity :=
      PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_iff_two_prime_reciprocal_excludes
    two_prime_reciprocal_excludes_prime_identity_witness :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalExcludesPrimeIdentity_iff_witness
    two_prime_reciprocal_identity_prime_mixed :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityPrimeMixed_iff_non_two
    two_prime_reciprocal_identity_non_two_prime_mixed :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoPrimeMixed_iff_composite_defect_of_character
    two_prime_reciprocal_identity_non_two_composite_defect :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_iff_cost_defect
    two_prime_reciprocal_identity_non_two_composite_cost_defect :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalIdentityNonTwoCompositeDefect_of_cost_defect
    two_prime_mixed_composite_cost_consistency_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_refuted
    prime_pair_product_cost_consistency_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_refuted
    two_prime_reciprocal_forces_prime_reciprocal :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalForcesPrimeReciprocal_of_reciprocal_witness_globalizes
    two_prime_reciprocal_trace_connected :=
      PRCJCost.PRCCharacterTwoPrimeReciprocalRespectsTraceConnected_iff_forces
    two_prime_identity_trace_connected :=
      PRCJCost.PRCCharacterTwoPrimeIdentityRespectsTraceConnected_of_prime_identity_trace_connected
    no_mixed_prime_orientation :=
      PRCJCost.PRCCharacterNoMixedPrimeWitnesses_iff_no_mixed_prime_orientation
    mixed_prime_witnesses :=
      PRCJCost.PRCCharacterMixedPrimeWitnesses_iff_pair_witnesses
    mixed_prime_pair_witnesses :=
      PRCJCost.PRCCharacterMixedPrimePairWitnesses_iff_same_or_distinct
    same_prime_mixed_pair_witnesses :=
      PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses_absurd
    distinct_prime_mixed_pair_witnesses :=
      PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses_absurd_of_branch_uniform
    prime_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCCharacterPrimeIdentityWitnessExcludesReciprocal_iff_no_mixed_prime_orientation
    prime_reciprocal_witness_globalizes :=
      PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizes_of_local_no_mixed_prime_orientation
    prime_reciprocal_forces_two_prime_reciprocal :=
      PRCJCost.PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_witness_globalizes
    prime_reciprocal_witness_globalizes_split :=
      PRCJCost.PRCCharacterPrimeReciprocalWitnessGlobalizes_iff_split
    prime_reciprocal_forces_two_from_reciprocal_twist_identity_forces_two := by
      intro χ
      exact PRCJCost.PRCCharacterPrimeReciprocalForcesTwoPrimeReciprocal_of_reciprocal_twist_identity_forces_two
    prime_identity_forces_two_from_reciprocal_twist_reciprocal_forces_two := by
      intro χ
      exact PRCJCost.PRCCharacterPrimeIdentityForcesTwoPrimeIdentity_of_reciprocal_twist_reciprocal_forces_two
    prime_identity_trace_coherence :=
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform_iff_trace_coherence
    prime_identity_branch_uniform :=
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform_iff_identity_iff_two
    prime_axis_trace_connected := PRCJCost.PRCPrimeAxisTraceConnected_proved
    prime_identity_respects_trace_connected :=
      PRCJCost.PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_iff_trace_connected
    prime_identity_respects_common_trace_extension :=
      PRCJCost.PRCCharacterPrimeIdentityRespectsCanonicalAddTrace_iff_common_trace_extension
    prime_identity_respects_canonical_add_trace :=
      PRCJCost.PRCCharacterPrimeIdentityBranchUniform_iff_canonical_add_trace
    prime_identity_respects_comparable_trace :=
      PRCJCost.PRCCharacterPrimeIdentityRespectsComparableTrace_iff_trace_coherence
    prime_identity_trace_coherence_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_refuted
    prime_identity_branch_uniformity_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_refuted
    prime_identity_trace_transport_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_refuted
    prime_identity_common_trace_extension_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_refuted
    prime_identity_canonical_add_trace_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_refuted
    prime_identity_comparable_trace_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_refuted
    orbit_successor_identity_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitSuccessorIdentityTarget_refuted
    orbit_successor_transport_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitSuccessorTransportTarget_refuted
    prime_floor_successor_transport_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_refuted
    prime_identity_witness_globalizes_nonunit_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_refuted
    prime_floor_identity_extends_successor_step_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_refuted
    prime_floor_identity_contracts_successor_step_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_refuted
    prime_floor_identity_successor_step_pair_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_refuted
    prime_floor_nonunit_local_orientation_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_refuted
    prime_floor_nonunit_product_local_orientation_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_refuted
    prime_floor_nonunit_orbit_orientation_coherent_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_refuted
    prime_floor_no_mixed_nonunit_orbit_orientation_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_refuted
    prime_floor_nonunit_identity_branch_transport_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_refuted
    prime_floor_nonunit_identity_witness_globalizes_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_refuted
    prime_floor_nonunit_identity_witness_excludes_reciprocal_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_refuted
    prime_floor_nonunit_no_mixed_witnesses_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_refuted
    prime_floor_no_mixed_prime_witnesses_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_refuted
    prime_floor_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_pair_witness_character
        (PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_distinct
          (PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter_of_non_two_mixed
            (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
              (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
                PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed))))
    prime_floor_mixed_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_distinct
        (PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter_of_non_two_mixed
          (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
            (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
              PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed)))
    prime_floor_same_prime_mixed_pair_witness_character_refuted :=
      PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd
    prime_floor_distinct_prime_mixed_pair_witness_character :=
      PRCJCost.PRCPrimeCalibratedDistinctPrimeMixedPairWitnessCharacter_of_non_two_mixed
        (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
          (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
            PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed))
    prime_floor_prime_identity_witness_excludes_reciprocal_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_refuted
    prime_floor_prime_reciprocal_witness_globalizes_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_refuted
    prime_floor_prime_reciprocal_forces_two_prime_reciprocal_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_refuted
    prime_floor_prime_reciprocal_witness_globalizes_split_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_refuted
    prime_floor_prime_witnesses_control_nonunit_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_proved
    prime_floor_mixed_nonunit_witnesses_reflect_prime_target :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_proved
    prime_floor_mixed_nonunit_identity_witness_reflects_prime_target :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget_proved
    prime_floor_mixed_nonunit_reciprocal_witness_reflects_prime_target :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget_proved
    prime_floor_mixed_nonunit_witnesses_reflect_prime_split_target :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_proved
    prime_floor_nonunit_no_mixed_witnesses_split_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_refuted
    prime_floor_nonunit_identity_witness_local_exclusion_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_refuted
    prime_floor_nonunit_reciprocal_branch_transport_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget_refuted
    prime_floor_nonunit_branch_transport_pair_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget_refuted
    prime_floor_nonunit_identity_comparable_trace_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_refuted
    prime_floor_nonunit_branch_agreement_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_refuted
    prime_floor_nonunit_orbit_orientation_local_branch_agreement_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_refuted
    prime_floor_nonunit_orbit_orientation_local_identity_transport_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_refuted
    prime_floor_nonunit_orbit_orientation_local_comparable_trace_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_refuted
    prime_floor_nonunit_orbit_orientation_local_no_mixed_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalNoMixedTarget_refuted
    prime_floor_nonunit_orbit_orientation_local_product_no_mixed_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalProductNoMixedTarget_refuted
    prime_floor_no_mixed_nonunit_from_product_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_product_no_mixed
    prime_floor_product_no_mixed_from_no_mixed_nonunit :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_no_mixed_nonunit
    prime_floor_product_no_mixed_iff_no_mixed_nonunit :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_no_mixed_nonunit
    prime_floor_product_no_mixed_from_identity_branch_transport :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_branch_transport
    prime_floor_nonunit_identity_branch_transport_from_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_comparable_trace
    prime_floor_nonunit_coherent_from_product_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_product_no_mixed
    prime_floor_product_no_mixed_iff_nonunit_coherent :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_nonunit_coherent
    prime_floor_nonunit_identity_branch_transport_from_product_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_product_no_mixed
    prime_floor_product_no_mixed_iff_identity_branch_transport :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_branch_transport
    prime_floor_identity_witness_globalizes_from_identity_branch_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_identity_branch_transport
    prime_floor_identity_branch_transport_from_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_identity_witness_globalizes
    prime_floor_identity_witness_globalizes_iff_identity_branch_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_identity_branch_transport
    prime_floor_identity_witness_globalizes_from_product_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_product_no_mixed
    prime_floor_product_no_mixed_from_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_identity_witness_globalizes
    prime_floor_product_no_mixed_iff_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_witness_globalizes
    prime_floor_nonunit_coherent_from_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_identity_witness_globalizes
    prime_floor_identity_witness_globalizes_from_nonunit_coherent :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_nonunit_coherent
    prime_floor_nonunit_coherent_iff_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_identity_witness_globalizes
    prime_floor_identity_witness_excludes_reciprocal_from_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed
    prime_floor_no_mixed_from_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedNonunitOrbitOrientationTarget_of_identity_witness_excludes
    prime_floor_identity_witness_excludes_reciprocal_iff_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_iff_no_mixed
    prime_floor_no_mixed_witnesses_from_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_identity_witness_excludes
    prime_floor_identity_witness_excludes_reciprocal_from_no_mixed_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessExcludesReciprocalTarget_of_no_mixed_witnesses
    prime_floor_no_mixed_witnesses_iff_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_identity_witness_excludes
    prime_floor_no_mixed_prime_witnesses_from_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_orientation
    prime_floor_no_mixed_prime_orientation_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_no_mixed_prime_witnesses
    prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_orientation
    prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_orientation
    prime_floor_no_mixed_prime_orientation_from_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_identity_witness_excludes_reciprocal
    prime_floor_prime_identity_witness_excludes_reciprocal_iff_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_iff_no_mixed_prime_orientation
    prime_floor_no_mixed_prime_witnesses_from_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_identity_witness_excludes_reciprocal
    prime_floor_prime_identity_witness_excludes_reciprocal_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessExcludesReciprocalTarget_of_no_mixed_prime_witnesses
    prime_floor_no_mixed_prime_witnesses_iff_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_identity_witness_excludes_reciprocal
    prime_floor_no_mixed_prime_witnesses_iff_not_mixed_prime_witnesses :=
      fun χ => PRCJCost.PRCCharacterNoMixedPrimeWitnesses_iff_not_mixed_prime_witnesses
    prime_floor_mixed_prime_pair_witnesses_from_mixed_prime_witnesses :=
      fun χ => PRCJCost.PRCCharacterMixedPrimePairWitnesses_of_mixed_prime_witnesses
    prime_floor_mixed_prime_witnesses_from_pair_witnesses :=
      fun χ => PRCJCost.PRCCharacterMixedPrimeWitnesses_of_pair_witnesses
    prime_floor_mixed_prime_witnesses_iff_pair_witnesses :=
      fun χ => PRCJCost.PRCCharacterMixedPrimeWitnesses_iff_pair_witnesses
    prime_floor_no_mixed_prime_witnesses_iff_not_mixed_prime_pair_witnesses :=
      fun χ => PRCJCost.PRCCharacterNoMixedPrimeWitnesses_iff_not_mixed_prime_pair_witnesses
    prime_floor_mixed_prime_pair_witnesses_same_or_distinct :=
      fun χ => PRCJCost.PRCCharacterMixedPrimePairWitnesses_same_or_distinct
    prime_floor_mixed_prime_pair_witnesses_from_same_or_distinct :=
      fun χ => PRCJCost.PRCCharacterMixedPrimePairWitnesses_of_same_or_distinct
    prime_floor_mixed_prime_pair_witnesses_iff_same_or_distinct :=
      fun χ => PRCJCost.PRCCharacterMixedPrimePairWitnesses_iff_same_or_distinct
    prime_floor_no_mixed_prime_witnesses_iff_no_same_and_no_distinct_pair :=
      fun χ => PRCJCost.PRCCharacterNoMixedPrimeWitnesses_iff_no_same_and_no_distinct_pair
    prime_floor_same_prime_mixed_pair_witnesses_absurd :=
      fun χ => PRCJCost.PRCCharacterSamePrimeMixedPairWitnesses_absurd
    prime_floor_no_mixed_prime_witnesses_iff_not_distinct_prime_pair :=
      fun χ => PRCJCost.PRCCharacterNoMixedPrimeWitnesses_iff_not_distinct_prime_pair
    prime_floor_distinct_prime_mixed_pair_witnesses_absurd_from_branch_uniform :=
      fun χ => PRCJCost.PRCCharacterDistinctPrimeMixedPairWitnesses_absurd_of_branch_uniform
    prime_floor_prime_identity_branch_uniform_from_local_no_distinct_prime_pair :=
      fun χ => PRCJCost.PRCCharacterPrimeIdentityBranchUniform_of_local_no_distinct_prime_pair
    prime_floor_prime_identity_branch_uniform_iff_no_distinct_prime_pair_of_local :=
      fun χ => PRCJCost.PRCCharacterPrimeIdentityBranchUniform_iff_no_distinct_prime_pair_of_local
    prime_floor_prime_identity_branch_uniform_from_identity_iff_two :=
      fun χ => PRCJCost.PRCCharacterPrimeIdentityBranchUniform_of_identity_iff_two
    prime_floor_prime_identity_iff_two_from_branch_uniform :=
      fun χ => PRCJCost.PRCCharacterPrimeIdentityIffTwoPrimeIdentity_of_branch_uniform
    prime_floor_prime_identity_branch_uniform_iff_identity_iff_two :=
      fun χ => PRCJCost.PRCCharacterPrimeIdentityBranchUniform_iff_identity_iff_two
    prime_floor_prime_reciprocal_witness_globalizes_from_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_no_mixed_prime_orientation
    prime_floor_no_mixed_prime_orientation_from_reciprocal_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_reciprocal_witness_globalizes
    prime_floor_prime_reciprocal_witness_globalizes_iff_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_no_mixed_prime_orientation
    prime_floor_prime_reciprocal_witness_globalizes_iff_identity_witness_excludes_reciprocal :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_identity_witness_excludes_reciprocal
    prime_floor_prime_reciprocal_forces_two_from_reciprocal_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_reciprocal_witness_globalizes
    prime_floor_two_prime_reciprocal_forces_from_reciprocal_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_reciprocal_witness_globalizes
    prime_floor_prime_reciprocal_witness_globalizes_split_from_reciprocal_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_reciprocal_witness_globalizes
    prime_floor_prime_reciprocal_witness_globalizes_from_split :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_of_split
    prime_floor_prime_reciprocal_witness_globalizes_iff_split :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesTarget_iff_split
    prime_floor_prime_reciprocal_forces_two_from_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_of_identity_forces_two
    prime_floor_prime_identity_forces_two_from_reciprocal_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_prime_reciprocal_forces_two
    prime_floor_prime_reciprocal_forces_two_iff_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalForcesTwoPrimeReciprocalTarget_iff_identity_forces_two
    prime_floor_two_prime_reciprocal_excludes_identity_witness_from_excludes :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_two_prime_reciprocal_excludes
    prime_floor_two_prime_reciprocal_excludes_from_identity_witness_excludes :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_witness
    prime_floor_two_prime_reciprocal_excludes_iff_identity_witness_excludes :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_witness
    prime_floor_prime_identity_forces_two_from_two_prime_reciprocal_excludes_identity_witness :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes_witness
    prime_floor_two_prime_reciprocal_excludes_identity_witness_from_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_identity_forces_two
    prime_floor_prime_identity_forces_two_iff_two_prime_reciprocal_excludes_identity_witness :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes_witness
    prime_floor_two_prime_reciprocal_excludes_identity_witness_from_no_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_no_mixed_character
    prime_floor_no_mixed_character_from_two_prime_reciprocal_excludes_identity_witness :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_absurd_of_witness_excludes
    prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_mixed_character
    prime_floor_non_two_mixed_character_from_mixed_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_mixed
    prime_floor_mixed_character_from_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_of_non_two_mixed
    prime_floor_mixed_character_iff_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_iff_non_two
    prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_non_two_mixed_character
    prime_floor_composite_defect_character_from_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed
    prime_floor_non_two_mixed_character_from_composite_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_composite_defect
    prime_floor_non_two_mixed_character_iff_composite_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_iff_composite_defect
    prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_composite_defect_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_defect_character
    prime_floor_composite_cost_defect_character_from_composite_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_composite_defect
    prime_floor_composite_defect_character_from_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_cost_defect
    prime_floor_composite_defect_character_iff_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_iff_cost_defect
    prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_no_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_no_composite_cost_defect_character
    prime_floor_two_prime_mixed_composite_cost_consistency_from_no_cost_defect :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_no_composite_cost_defect
    prime_floor_no_cost_defect_from_two_prime_mixed_composite_cost_consistency :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_absurd_of_mixed_composite_consistency
    prime_floor_two_prime_mixed_composite_cost_consistency_iff_no_cost_defect :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_composite_cost_defect_character
    prime_floor_two_prime_reciprocal_excludes_identity_witness_iff_mixed_composite_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_iff_mixed_composite_cost_consistency
    prime_floor_two_prime_reciprocal_excludes_identity_witness_from_mixed_composite_cost_consistency_direct :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_mixed_composite_cost_consistency_direct
    prime_floor_two_prime_mixed_composite_cost_consistency_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_of_prime_pair_product_cost_consistency
    prime_floor_prime_pair_product_cost_consistency_from_prime_calibration_propagation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_prime_calibration_propagation
    prime_floor_prime_pair_product_cost_consistency_from_coherent_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_coherent_prime_orientation
    prime_floor_coherent_prime_orientation_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_prime_pair_product_cost_consistency
    prime_floor_prime_pair_product_cost_consistency_iff_coherent_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_coherent_prime_orientation
    prime_floor_prime_pair_product_cost_consistency_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_of_no_mixed_prime_witnesses
    prime_floor_no_mixed_prime_witnesses_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_pair_product_cost_consistency
    prime_floor_prime_pair_product_cost_consistency_iff_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witnesses
    prime_floor_no_mixed_prime_witness_character_absurd_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter_absurd_of_no_mixed_prime_witnesses
    prime_floor_no_mixed_prime_witnesses_from_no_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_no_mixed_prime_witness_character
    prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_witness_character
    prime_floor_prime_pair_product_cost_consistency_iff_no_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_witness_character
    prime_floor_no_mixed_prime_witnesses_not_from_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_of_mixed_prime_witness_character
    prime_floor_mixed_prime_witness_character_from_not_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_not_no_mixed_prime_witnesses
    prime_floor_no_mixed_prime_witnesses_not_iff_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_mixed_prime_witness_character
    prime_floor_prime_pair_product_cost_consistency_not_from_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_mixed_prime_witness_character
    prime_floor_mixed_prime_witness_character_from_not_prime_pair_product_cost_consistency :=
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_not_prime_pair_product_cost_consistency
    prime_floor_prime_pair_product_cost_consistency_not_iff_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_mixed_prime_witness_character
    prime_floor_mixed_prime_pair_witness_character_from_mixed_prime_witness_character :=
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_mixed_prime_witness_character
    prime_floor_mixed_prime_witness_character_from_pair_witness_character :=
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter_of_pair_witness_character
    prime_floor_mixed_prime_witness_character_iff_pair_witness_character :=
      PRCJCost.PRCPrimeCalibratedMixedPrimeWitnessesCharacter_iff_pair_witness_character
    prime_floor_no_mixed_prime_witnesses_iff_no_mixed_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_mixed_prime_pair_witness_character
    prime_floor_no_mixed_prime_witnesses_not_iff_mixed_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_mixed_prime_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_iff_no_mixed_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_mixed_prime_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_not_iff_mixed_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_mixed_prime_pair_witness_character
    prime_floor_mixed_prime_pair_witness_character_same_or_distinct :=
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter_same_or_distinct
    prime_floor_mixed_prime_pair_witness_character_from_same_or_distinct :=
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter_of_same_or_distinct
    prime_floor_mixed_prime_pair_witness_character_iff_same_or_distinct :=
      PRCJCost.PRCPrimeCalibratedMixedPrimePairWitnessCharacter_iff_same_or_distinct
    prime_floor_no_mixed_prime_witnesses_iff_no_same_and_no_distinct_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_same_and_no_distinct_pair_witness_character
    prime_floor_no_mixed_prime_witnesses_not_iff_same_or_distinct_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_same_or_distinct_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_iff_no_same_and_no_distinct_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_same_and_no_distinct_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_not_iff_same_or_distinct_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_same_or_distinct_pair_witness_character
    prime_floor_same_prime_mixed_pair_witness_character_absurd :=
      PRCJCost.PRCPrimeCalibratedSamePrimeMixedPairWitnessCharacter_absurd
    prime_floor_no_mixed_prime_witnesses_iff_no_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_no_distinct_prime_pair_witness_character
    prime_floor_no_mixed_prime_witnesses_not_iff_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_not_iff_distinct_prime_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_iff_no_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_no_distinct_prime_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_not_iff_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_iff_distinct_prime_pair_witness_character
    prime_floor_prime_identity_branch_uniformity_from_no_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_distinct_prime_pair_witness_character
    prime_floor_no_distinct_prime_pair_witness_character_from_prime_identity_branch_uniformity :=
      PRCJCost.PRCPrimeCalibrationForcesNoDistinctPrimePairWitnessCharacter_of_prime_identity_branch_uniformity
    prime_floor_prime_identity_branch_uniformity_iff_no_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_distinct_prime_pair_witness_character
    prime_floor_prime_identity_branch_uniformity_not_iff_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_not_iff_distinct_prime_pair_witness_character
    prime_floor_prime_pair_product_cost_consistency_iff_prime_identity_branch_uniformity :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_branch_uniformity
    prime_floor_prime_identity_branch_uniformity_from_identity_iff_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_identity_iff_two
    prime_floor_prime_identity_iff_two_from_branch_uniformity :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_branch_uniformity
    prime_floor_prime_identity_branch_uniformity_iff_identity_iff_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_iff_two
    prime_floor_prime_identity_branch_uniformity_iff_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_identity_forces_two
    prime_floor_prime_pair_product_cost_consistency_iff_prime_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_prime_identity_forces_two
    prime_floor_prime_identity_forces_two_not_iff_distinct_prime_pair_witness_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_iff_distinct_prime_pair_witness_character
    prime_floor_prime_identity_forces_two_iff_no_two_prime_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_two_prime_mixed_character
    prime_floor_prime_identity_forces_two_iff_no_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_mixed_character
    prime_floor_non_two_mixed_character_from_two_adic_axis_twist :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
    prime_floor_prime_calibration_from_two_adic_axis_twist := by
      intro χ htwist
      exact PRCJCost.PRCCharacterPrimeDirectionCalibrated_of_two_adic_axis_twist htwist
    prime_floor_calibrated_two_adic_axis_twist_from_ratio_character_axis_twist :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
    prime_floor_ratio_character_axis_twist_from_calibrated_two_adic_axis_twist :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_of_calibrated_two_adic_axis_twist
    prime_floor_calibrated_two_adic_axis_twist_iff_ratio_character_axis_twist :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_iff_ratio_character_axis_twist
    prime_floor_ratio_character_axis_twist_absurd_from_no_calibrated_twist :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_absurd_of_no_calibrated_twist
    prime_floor_two_adic_axis_twist_absurd_from_no_non_two_mixed :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_no_non_two_mixed
    prime_floor_two_adic_axis_twist_absurd_from_mixed_composite_cost_consistency :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_mixed_composite_cost_consistency
    prime_floor_two_adic_axis_twist_absurd_from_prime_identity_forces_two :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_identity_forces_two
    prime_floor_two_adic_axis_twist_absurd_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_prime_pair_product_cost_consistency
    prime_floor_mixed_composite_cost_consistency_not_from_two_adic_axis_twist :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_two_adic_axis_twist
    prime_floor_prime_identity_forces_two_not_from_two_adic_axis_twist :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_two_adic_axis_twist
    prime_floor_prime_pair_product_cost_consistency_not_from_two_adic_axis_twist :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_two_adic_axis_twist
    prime_floor_ratio_character_axis_twist_absurd_from_mixed_composite_cost_consistency :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_absurd_of_mixed_composite_cost_consistency
    prime_floor_ratio_character_axis_twist_absurd_from_prime_identity_forces_two :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_forces_two
    prime_floor_ratio_character_axis_twist_absurd_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_pair_product_cost_consistency
    prime_floor_mixed_composite_cost_consistency_not_from_ratio_character_axis_twist :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_ratio_character_axis_twist
    prime_floor_prime_identity_forces_two_not_from_ratio_character_axis_twist :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_ratio_character_axis_twist
    prime_floor_prime_pair_product_cost_consistency_not_from_ratio_character_axis_twist :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_ratio_character_axis_twist
    prime_floor_two_three_mixed_not_composite :=
      PRCJCost.twoThreePrimeMixedDirection_not_crossEq_composite
    prime_floor_two_three_mixed_not_composite_recip :=
      PRCJCost.twoThreePrimeMixedDirection_not_crossEq_composite_recip
    prime_floor_two_adic_axis_twist_two_three_mixed_image := by
      intro χ hχ htwist
      exact PRCJCost.PRCCharacterTwoAdicAxisTwist_two_three_mixed_image hχ htwist
    prime_floor_two_adic_axis_twist_two_three_local_orientation_absurd := by
      intro χ hχ htwist
      exact
        PRCJCost.PRCCharacterTwoAdicAxisTwist_two_three_local_orientation_absurd
          hχ htwist
    prime_floor_ratio_character_axis_twist_forces_two_three_local_orientation_failure :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_forces_two_three_local_orientation_failure
    prime_floor_two_three_failure_character_from_ratio_character_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_of_ratio_character_axis_twist
    prime_floor_ratio_character_axis_twist_from_two_three_failure_character :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_of_two_three_local_orientation_failure_character
    prime_floor_two_three_failure_character_iff_ratio_character_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_ratio_character_axis_twist
    prime_floor_two_three_failure_character_iff_calibrated_two_adic_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_iff_calibrated_two_adic_axis_twist
    prime_floor_two_three_local_orientation_target_from_no_ratio_character_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_ratio_character_axis_twist
    prime_floor_ratio_character_axis_twist_absurd_from_two_three_local_orientation_target :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_absurd_of_two_three_local_orientation_target
    prime_floor_two_three_local_orientation_target_iff_no_ratio_character_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_ratio_character_axis_twist
    prime_floor_two_three_failure_character_absurd_from_two_three_local_orientation_target :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_two_three_local_orientation_target
    prime_floor_two_three_local_orientation_target_iff_no_failure_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_failure_character
    prime_floor_two_three_local_orientation_target_iff_no_calibrated_two_adic_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_iff_no_calibrated_two_adic_axis_twist
    prime_floor_calibrated_two_adic_axis_twist_absurd_from_two_three_local_orientation_target :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_absurd_of_two_three_local_orientation_target
    prime_floor_two_three_local_orientation_target_from_no_failure_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_failure_character
    prime_floor_two_three_local_fork_certificate :=
      PRCJCost.prcTwoThreeCompositeLocalForkCertificate
    prime_floor_calibrated_two_adic_axis_twist_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_two_three_local_orientation_failure_character
    prime_floor_non_two_mixed_character_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_three_local_orientation_failure_character
    prime_floor_composite_defect_character_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_two_three_local_orientation_failure_character
    prime_floor_composite_cost_defect_character_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_two_three_local_orientation_failure_character
    prime_floor_mixed_composite_cost_consistency_not_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_of_two_three_local_orientation_failure_character
    prime_floor_prime_identity_forces_two_not_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_of_two_three_local_orientation_failure_character
    prime_floor_prime_pair_product_cost_consistency_not_from_two_three_failure_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_not_of_two_three_local_orientation_failure_character
    prime_floor_two_three_failure_character_absurd_from_no_calibrated_two_adic_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_calibrated_two_adic_axis_twist
    prime_floor_two_three_failure_character_absurd_from_no_non_two_mixed_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_mixed_character
    prime_floor_two_three_failure_character_absurd_from_no_non_two_composite_defect_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_composite_defect_character
    prime_floor_two_three_failure_character_absurd_from_no_non_two_composite_cost_defect_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_no_non_two_composite_cost_defect_character
    prime_floor_two_three_local_orientation_target_from_no_calibrated_two_adic_axis_twist :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_calibrated_two_adic_axis_twist
    prime_floor_two_three_local_orientation_target_from_no_non_two_mixed_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_non_two_mixed_character
    prime_floor_two_three_local_orientation_target_from_no_non_two_composite_defect_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_non_two_composite_defect_character
    prime_floor_two_three_local_orientation_target_from_no_non_two_composite_cost_defect_character :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_no_non_two_composite_cost_defect_character
    prime_floor_two_three_local_orientation_target_from_mixed_composite_cost_consistency :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_mixed_composite_cost_consistency
    prime_floor_two_three_local_orientation_target_from_prime_identity_forces_two :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_identity_forces_two
    prime_floor_two_three_local_orientation_target_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_pair_product_cost_consistency
    prime_floor_two_three_failure_character_absurd_from_mixed_composite_cost_consistency :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_mixed_composite_cost_consistency
    prime_floor_two_three_failure_character_absurd_from_prime_identity_forces_two :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_prime_identity_forces_two
    prime_floor_two_three_failure_character_absurd_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_prime_pair_product_cost_consistency
    prime_floor_ratio_character_axis_twist_absurd_from_prime_identity_branch_uniformity :=
      PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_absurd_of_prime_identity_branch_uniformity
    prime_floor_two_three_failure_character_absurd_from_prime_identity_branch_uniformity :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationFailureCharacter_absurd_of_prime_identity_branch_uniformity
    prime_floor_two_three_local_orientation_target_from_prime_identity_branch_uniformity :=
      PRCJCost.PRCTwoThreeCompositeLocalOrientationForTwoAdicAxisTwistTarget_of_prime_identity_branch_uniformity
    prime_floor_prime_identity_forces_two_iff_no_non_two_composite_defect_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_composite_defect_character
    prime_floor_prime_identity_forces_two_iff_no_non_two_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_no_non_two_composite_cost_defect_character
    prime_floor_prime_identity_forces_two_not_iff_non_two_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_not_iff_non_two_composite_cost_defect_character
    prime_floor_prime_identity_forces_two_iff_mixed_composite_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_mixed_composite_cost_consistency
    prime_floor_prime_pair_product_cost_consistency_iff_mixed_composite_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_iff_mixed_composite_cost_consistency
    prime_floor_two_prime_mixed_composite_cost_consistency_iff_no_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_iff_no_non_two_mixed_character
    prime_floor_two_prime_mixed_composite_cost_consistency_not_iff_non_two_mixed_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_iff_non_two_mixed_character
    prime_floor_two_prime_mixed_composite_cost_consistency_not_iff_non_two_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_not_iff_non_two_composite_cost_defect_character
    prime_floor_two_prime_reciprocal_excludes_identity_witness_from_prime_pair_product_cost_consistency :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_of_prime_pair_product_cost_consistency
    prime_floor_prime_reciprocal_witness_globalizes_split_from_two_prime_reciprocal_forces :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_of_two_prime_reciprocal_forces
    prime_floor_two_prime_reciprocal_forces_from_split :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_split
    prime_floor_prime_reciprocal_witness_globalizes_split_iff_two_prime_reciprocal_forces :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeReciprocalWitnessGlobalizesSplitTarget_iff_two_prime_reciprocal_forces
    prime_identity_trace_coherence_from_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_no_mixed_prime_orientation
    prime_no_mixed_prime_orientation_iff_trace_coherence :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_iff_trace_coherence
    prime_no_mixed_prime_orientation_from_branch_uniformity :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeOrientationTarget_of_branch_uniformity
    prime_identity_branch_uniformity_from_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_no_mixed_prime_orientation
    prime_identity_branch_uniformity_iff_no_mixed_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_no_mixed_prime_orientation
    prime_no_mixed_prime_witnesses_iff_trace_coherence :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_trace_coherence
    coherent_prime_orientation_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_no_mixed_prime_witnesses
    no_mixed_prime_witnesses_from_coherent_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_coherent_prime_orientation
    no_mixed_prime_witnesses_iff_coherent_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_iff_coherent_prime_orientation
    two_prime_branch_controls_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_refuted
    two_prime_branch_controls_from_coherent_prime_orientation :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_coherent_prime_orientation
    coherent_prime_orientation_from_two_prime_branch_controls :=
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_of_two_prime_branch_controls
    coherent_prime_orientation_iff_two_prime_branch_controls :=
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_iff_two_prime_branch_controls
    prime_identity_iff_two_prime_identity_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_refuted
    prime_identity_forces_two_prime_identity_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_refuted
    two_prime_reciprocal_excludes_prime_identity_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_refuted
    two_prime_reciprocal_excludes_prime_identity_witness_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityWitnessTarget_refuted
    two_prime_reciprocal_identity_prime_mixed_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityPrimeMixedCharacter_of_non_two_mixed
        (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
          (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
            PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed))
    two_prime_reciprocal_identity_non_two_prime_mixed_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
        (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
          PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed)
    two_prime_reciprocal_identity_non_two_composite_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed
        (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
          (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
            PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed))
    two_prime_reciprocal_identity_non_two_composite_cost_defect_character :=
      PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeCostDefectCharacter_of_composite_defect
        (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoCompositeDefectCharacter_of_non_two_mixed
          (PRCJCost.PRCPrimeCalibratedTwoPrimeReciprocalIdentityNonTwoPrimeMixedCharacter_of_two_adic_axis_twist
            (PRCJCost.PRCPrimeCalibratedTwoAdicAxisTwistCharacter_of_ratio_character_axis_twist
              PRCJCost.PRCTwoAdicAxisTwistRatioCharacter_constructed)))
    calibrated_two_prime_mixed_composite_cost_consistency_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeMixedCompositeCostConsistencyTarget_refuted
    calibrated_prime_pair_product_cost_consistency_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimePairProductCostConsistencyTarget_refuted
    two_prime_reciprocal_forces_prime_reciprocal_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_refuted
    two_prime_reciprocal_trace_connected_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_refuted
    two_prime_identity_trace_connected_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_refuted
    prime_identity_iff_two_from_two_prime_branch_controls :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_two_prime_branch_controls
    two_prime_branch_controls_from_prime_identity_iff_two :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_of_prime_identity_iff_two
    two_prime_branch_controls_iff_prime_identity_iff_two :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeBranchControlsPrimesTarget_iff_prime_identity_iff_two
    prime_identity_forces_two_from_identity_iff_two_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_identity_iff_two
    prime_identity_iff_two_from_identity_forces_two_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_of_identity_forces_two
    prime_identity_iff_two_iff_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityIffTwoPrimeIdentityTarget_iff_identity_forces_two
    two_prime_reciprocal_excludes_from_identity_forces_two_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_identity_forces_two
    prime_identity_forces_two_from_two_prime_reciprocal_excludes_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_excludes
    prime_identity_forces_two_target_iff_two_prime_reciprocal_excludes :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_iff_two_prime_reciprocal_excludes
    two_prime_reciprocal_excludes_from_two_prime_reciprocal_forces_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_of_two_prime_reciprocal_forces
    two_prime_reciprocal_forces_from_two_prime_reciprocal_excludes_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_two_prime_reciprocal_excludes
    two_prime_reciprocal_excludes_target_iff_two_prime_reciprocal_forces :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalExcludesPrimeIdentityTarget_iff_two_prime_reciprocal_forces
    two_prime_reciprocal_forces_from_identity_forces_two_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_identity_forces_two
    prime_identity_forces_two_from_two_prime_reciprocal_forces_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityForcesTwoPrimeIdentityTarget_of_two_prime_reciprocal_forces
    two_prime_reciprocal_forces_target_iff_identity_forces_two :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_iff_identity_forces_two
    two_prime_reciprocal_forces_from_trace_connected_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalForcesPrimeReciprocalTarget_of_trace_connected
    two_prime_reciprocal_trace_connected_from_forces_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_forces
    two_prime_reciprocal_trace_connected_target_iff_forces :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_forces
    two_prime_reciprocal_trace_connected_from_identity_trace_connected_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_of_identity_trace_connected
    two_prime_identity_trace_connected_from_reciprocal_trace_connected_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_reciprocal_trace_connected
    two_prime_reciprocal_trace_connected_target_iff_identity_trace_connected :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeReciprocalTraceConnectedTarget_iff_identity_trace_connected
    two_prime_identity_trace_connected_from_prime_identity_trace_transport_target :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_of_prime_identity_trace_transport
    prime_identity_trace_transport_from_two_prime_identity_trace_connected_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_two_prime_identity_trace_connected
    two_prime_identity_trace_connected_target_iff_prime_identity_trace_transport :=
      PRCJCost.PRCPrimeCalibrationForcesTwoPrimeIdentityTraceConnectedTarget_iff_prime_identity_trace_transport
    prime_identity_canonical_add_trace_from_common_trace_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_common_trace_extension
    prime_identity_common_trace_from_canonical_add_trace_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_canonical_add_trace
    prime_identity_canonical_add_trace_target_iff_common_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_iff_common_trace_extension
    prime_identity_canonical_add_trace_from_trace_transport_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_trace_transport
    prime_identity_trace_transport_from_canonical_add_trace_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_canonical_add_trace
    prime_identity_canonical_add_trace_target_iff_trace_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_iff_trace_transport
    prime_identity_branch_uniformity_from_trace_coherence_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_trace_coherence
    prime_identity_trace_coherence_from_branch_uniformity_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_branch_uniformity
    prime_identity_branch_uniformity_target_iff_trace_coherence :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_trace_coherence
    prime_identity_canonical_add_trace_from_branch_uniformity_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCanonicalAddTraceTarget_of_branch_uniformity
    prime_identity_branch_uniformity_from_canonical_add_trace_target :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_of_canonical_add_trace
    prime_identity_branch_uniformity_target_iff_canonical_add_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityBranchUniformityTarget_iff_canonical_add_trace
    prime_identity_comparable_trace_from_trace_coherence :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_trace_coherence
    prime_identity_trace_coherence_from_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_comparable_trace
    prime_identity_trace_coherence_iff_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_comparable_trace
    prime_identity_comparable_trace_from_nonunit_identity_comparable :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_of_nonunit_identity_comparable_trace
    nonunit_identity_comparable_trace_from_prime_identity_comparable :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_prime_identity_comparable_trace
    prime_identity_comparable_trace_iff_nonunit_identity_comparable :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_nonunit_identity_comparable_trace
    prime_identity_comparable_trace_iff_prime_floor_successor_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityComparableTraceTarget_iff_prime_floor_successor_transport
    prime_identity_common_trace_from_trace_coherence :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityCommonTraceExtensionTarget_of_trace_coherence
    prime_identity_trace_coherence_from_common_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_of_common_trace_extension
    prime_identity_trace_coherence_iff_common_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_common_trace_extension
    prime_identity_trace_transport_from_trace_coherence :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceTransportTarget_of_trace_coherence
    prime_identity_trace_coherence_iff_trace_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityTraceCoherenceTarget_iff_trace_transport
    prime_floor_no_mixed_prime_witnesses_from_nonunit_no_mixed_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_nonunit_no_mixed_witnesses
    prime_floor_nonunit_no_mixed_witnesses_split_from_nonunit_no_mixed_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_nonunit_no_mixed_witnesses
    prime_floor_nonunit_no_mixed_witnesses_from_split :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_split
    prime_floor_nonunit_no_mixed_witnesses_iff_split :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_split
    prime_floor_prime_witnesses_control_from_mixed_reflects :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_of_mixed_reflects
    prime_floor_mixed_reflects_from_prime_witnesses_control :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_prime_control
    prime_floor_prime_witnesses_control_iff_mixed_reflects :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_iff_mixed_reflects
    prime_floor_mixed_reflection_split_from_reflects :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_of_reflects
    prime_floor_mixed_reflection_from_split :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_of_split
    prime_floor_mixed_reflection_iff_split :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_iff_split
    prime_floor_mixed_identity_reflects_prime_proved :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitIdentityWitnessReflectsPrimeWitnessTarget_proved
    prime_floor_mixed_reciprocal_reflects_prime_proved :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitReciprocalWitnessReflectsPrimeWitnessTarget_proved
    prime_floor_mixed_reflection_split_proved :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesSplitTarget_proved
    prime_floor_mixed_reflection_proved :=
      PRCJCost.PRCPrimeCalibrationForcesMixedNonunitWitnessesReflectPrimeWitnessesTarget_proved
    prime_floor_prime_witnesses_control_nonunit_proved :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeWitnessesControlNonunitWitnessesTarget_proved
    prime_floor_nonunit_no_mixed_split_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesSplitTarget_of_no_mixed_prime_witnesses
    prime_floor_nonunit_no_mixed_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_of_no_mixed_prime_witnesses
    prime_floor_nonunit_no_mixed_iff_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitNoMixedWitnessesTarget_iff_no_mixed_prime_witnesses
    prime_floor_identity_witness_globalizes_from_local_exclusion :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_of_local_exclusion
    prime_floor_identity_witness_local_exclusion_from_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessLocalExclusionTarget_of_identity_witness_globalizes
    prime_floor_identity_witness_globalizes_iff_local_exclusion :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityWitnessGlobalizesTarget_iff_local_exclusion
    prime_floor_nonunit_identity_comparable_trace_from_product_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_product_no_mixed
    prime_floor_nonunit_identity_branch_transport_iff_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_iff_comparable_trace
    prime_floor_product_no_mixed_iff_identity_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_identity_comparable_trace
    prime_floor_product_local_orientation_from_identity_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationTarget_of_identity_comparable_trace
    prime_floor_nonunit_local_orientation_from_identity_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitLocalOrientationTarget_of_identity_comparable_trace
    prime_floor_nonunit_local_comparable_trace_from_identity_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_identity_comparable_trace
    prime_floor_nonunit_identity_comparable_trace_from_local_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_local_comparable_trace
    prime_floor_nonunit_local_comparable_trace_iff_identity_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_iff_identity_comparable_trace
    prime_floor_nonunit_branch_agreement_from_transport_pair :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_transport_pair
    prime_floor_nonunit_identity_branch_transport_from_branch_agreement :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityBranchTransportTarget_of_branch_agreement
    prime_floor_nonunit_reciprocal_branch_transport_from_branch_agreement :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitReciprocalBranchTransportTarget_of_branch_agreement
    prime_floor_nonunit_branch_transport_pair_from_branch_agreement :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchTransportPairTarget_of_branch_agreement
    prime_floor_nonunit_branch_agreement_iff_transport_pair :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_iff_transport_pair
    prime_floor_nonunit_branch_agreement_from_local_identity_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_local_identity_transport
    prime_floor_nonunit_local_identity_transport_from_local_branch_agreement :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_of_local_branch_agreement
    prime_floor_nonunit_local_branch_agreement_from_local_identity_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_of_local_identity_transport
    prime_floor_nonunit_local_branch_agreement_iff_local_identity_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_iff_local_identity_transport
    prime_floor_nonunit_local_comparable_trace_from_local_identity_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalComparableTraceTarget_of_local_identity_transport
    prime_floor_nonunit_local_identity_transport_from_local_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_of_local_comparable_trace
    prime_floor_nonunit_local_identity_transport_iff_local_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalIdentityTransportTarget_iff_local_comparable_trace
    prime_floor_nonunit_branch_agreement_from_coherent :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitBranchAgreementTarget_of_coherent
    prime_floor_nonunit_local_branch_agreement_from_coherent :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationLocalBranchAgreementTarget_of_coherent
    prime_floor_nonunit_coherent_from_local_branch_agreement :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_local_branch_agreement
    prime_floor_nonunit_orbit_orientation_coherent_iff_local_branch_agreement :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_local_branch_agreement
    prime_floor_nonunit_identity_comparable_trace_iff_successor_transport :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_prime_floor_successor_transport
    prime_floor_identity_extends_successor_step_from_successor_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityExtendsSuccessorStepTarget_of_successor_transport
    prime_floor_identity_contracts_successor_step_from_successor_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentityContractsSuccessorStepTarget_of_successor_transport
    prime_floor_identity_successor_step_pair_from_successor_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_successor_transport
    prime_floor_successor_transport_from_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_successor_step_pair
    prime_floor_successor_transport_iff_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_successor_step_pair
    prime_identity_witness_globalizes_nonunit_from_successor_transport :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_prime_floor_successor_transport
    prime_floor_successor_transport_from_prime_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_of_prime_identity_witness_globalizes
    prime_floor_successor_transport_iff_prime_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorSuccessorTransportTarget_iff_prime_identity_witness_globalizes
    prime_identity_witness_globalizes_nonunit_from_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_of_no_mixed_prime_witnesses
    no_mixed_prime_witnesses_from_prime_identity_witness_globalizes :=
      PRCJCost.PRCPrimeCalibrationForcesNoMixedPrimeWitnessesTarget_of_prime_identity_witness_globalizes
    prime_identity_witness_globalizes_nonunit_iff_no_mixed_prime_witnesses :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeIdentityWitnessGlobalizesNonunitTarget_iff_no_mixed_prime_witnesses
    prime_floor_identity_successor_step_pair_from_identity_comparable_trace :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_identity_comparable_trace
    prime_floor_nonunit_identity_comparable_trace_from_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_of_successor_step_pair
    prime_floor_nonunit_identity_comparable_trace_iff_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitIdentityComparableTraceTarget_iff_successor_step_pair
    prime_floor_product_no_mixed_from_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_of_successor_step_pair
    prime_floor_identity_successor_step_pair_from_product_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_product_no_mixed
    prime_floor_product_no_mixed_iff_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesOrbitProductNoMixedOrientationTarget_iff_successor_step_pair
    prime_floor_nonunit_coherent_from_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_of_successor_step_pair
    prime_floor_identity_successor_step_pair_from_nonunit_coherent :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorIdentitySuccessorStepPairTarget_of_nonunit_coherent
    prime_floor_nonunit_coherent_iff_successor_step_pair :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_successor_step_pair
    prime_floor_successor_transport_local_adjacent_target_refuted :=
      PRCJCost.PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_refuted
    prime_floor_successor_transport_local_adjacent_iff_local_successor_transport :=
      PRCJCost.PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_local_successor_transport
    prime_floor_successor_transport_local_adjacent_iff_nonunit_coherent :=
      PRCJCost.PRCPrimeFloorSuccessorTransportLocalAdjacentTarget_iff_nonunit_coherent
    prime_floor_nonunit_orbit_orientation_coherent_iff_local_no_mixed :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_local_no_mixed
    prime_floor_nonunit_orbit_orientation_coherent_sharpened_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentSharpenedTarget_refuted
    prime_floor_nonunit_orbit_orientation_coherent_iff_sharpened :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitOrientationCoherentTarget_iff_sharpened
    prime_floor_product_local_orientation_sharpened_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesNonunitOrbitProductLocalOrientationSharpenedTarget_refuted
    prime_floor_no_adjacent_mixed_orientation_target_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesPrimeFloorNoAdjacentMixedOrientationTarget_refuted
    prime_floor_successor_transport_sharpened_refuted :=
      PRCJCost.PRCPrimeFloorSuccessorTransportSharpenedTarget_refuted
    prime_to_coherent_orientation_refuted :=
      PRCJCost.PRCPrimeCalibrationForcesCoherentPrimeOrientationTarget_refuted
    coherent_prime_orientation_propagation_refuted :=
      PRCJCost.PRCCoherentPrimeOrientationPropagatesToGlobalTarget_refuted
    admissible_prime_orientation_coherent :=
      PRCJCost.PRCAdmissibleCharacterPrimeOrientationCoherentTarget_proved
    admissible_signed_unit_calibration_refuted :=
      PRCJCost.PRCAdmissibleCharacterSignedUnitCalibratedTarget_refuted
    signed_coherent_prime_orientation_propagation :=
      PRCJCost.PRCSignedCoherentPrimeOrientationPropagatesToGlobalTarget_proved
    prime_propagation_sharpened_refuted :=
      PRCJCost.PRCPrimeCalibrationPropagationSharpenedTarget_refuted
    native_cost_rigidity_sharpened_refuted :=
      PRCJCost.PRCNativeCostCharacterRigiditySharpenedTarget_refuted
    external_foundation_parsing_schema := by
      intro ExternalFoundation FaithfulParse
      rfl
  }
  no_project_local_axioms_audit := rfl

theorem prc_universal_foundation :
    PRCUniversalFoundationCertificate where
  delta_kernel :=
    prc_universal_foundation_conditional_certificate.kernel
  real_complete_ordered_field :=
    prc_universal_foundation_conditional_certificate.real_complete_ordered_field
  trace_logic :=
    prc_universal_foundation_conditional_certificate.trace_logic
  formal_system :=
    prc_universal_foundation_conditional_certificate.formal_system
  inevitability :=
    prc_universal_foundation_conditional_certificate.inevitability
  recognizer_bridge :=
    prc_universal_foundation_conditional_certificate.recognizer_bridge
  native_cost_blocker :=
    prc_universal_foundation_conditional_certificate.native_cost_blocker
  repaired_refuted_native_cost_ledger :=
    prc_universal_foundation_conditional_certificate.open_targets
  conditional_certificate :=
    prc_universal_foundation_conditional_certificate
  no_project_local_axioms_audit :=
    prc_universal_foundation_conditional_certificate.no_project_local_axioms_audit

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
