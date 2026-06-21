import IndisputableMonolith.Gravity.MasterTheorem
import IndisputableMonolith.Gravity.MasterTheoremHandoffIntegration
import IndisputableMonolith.Gravity.PageCurveDynamical
import IndisputableMonolith.Gravity.PageCurveOperatorEntropy
import IndisputableMonolith.Gravity.PageCurveNontrivial
import IndisputableMonolith.Gravity.PTAStructural
import IndisputableMonolith.Gravity.QGObservableSignalModels
import IndisputableMonolith.Gravity.StrongFieldStructural

/-!
# Gravity: Unconditional Master-Theorem Closure Surface

This module installs theorem-built witnesses for the five inputs that the older
`rs_quantum_gravity_master_conditional` theorem accepted as arguments.  The
conditional theorem remains the audit surface; this file supplies the canonical
zero-argument route through it.

## D2 witness: physical convergence route (Session 566)

The D2 witness was originally routed through three endpoint receipt propositions
from `MasterTheoremHandoffIntegration` (Track 1 single-slice, varying-
cardinality, and physical-D2 master-witness endpoints).  That route is retained
as `canonicalRegEHContinuumAndBianchiWitness_endpointRoute` for audit.

The primary D2 witness now names the physical content directly:
* Regge/EH clause: for any product-filter refinement data on the canonical
  periodic six-tet cubic torus, the normalized full nonlinear Regge aggregate
  converges to the supplied continuum EH integral on the product filter.
* Bianchi clause: for any vertex and bond types, every Schläfli-satisfying
  Regge datum obeys the contracted discrete Bianchi identity at every vertex.
-/

namespace IndisputableMonolith
namespace Gravity
namespace MasterTheoremUnconditional

open Gravity.PhysicalSixTetCubicDirichletInstance

/-! ## §0. Concrete physical D2 witness (primary route) -/

/-- Physical D2 Regge/EH proposition: for any product-filter refinement data,
the full nonlinear Regge aggregate converges to the supplied continuum
Einstein-Hilbert/Dirichlet integral on the product filter.  This names the
convergence content that the Regge calculus physically requires. -/
def concretePhysicalRegEHContinuumProp : Prop :=
  ∀ {α ρ : Type} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l),
    Track1BCPhysicalResidual.PhysicalReggeEHConcreteProductFilterTarget D

theorem concretePhysicalRegEHContinuumProp_holds :
    concretePhysicalRegEHContinuumProp :=
  fun D => Track1BCPhysicalResidual.physicalReggeEHConcreteProductFilterTarget_holds D

/-- Physical D2 Bianchi proposition: for any vertex and bond types, every
Schläfli-satisfying Regge datum obeys the contracted discrete Bianchi identity
at every vertex. -/
def concretePhysicalBianchiProp : Prop :=
  ∀ (V B : Type) [Fintype B],
    Track1BCPhysicalResidual.physicalSchlafliBianchiMasterProp V B

theorem concretePhysicalBianchiProp_holds :
    concretePhysicalBianchiProp := by
  intro V B _
  exact Track1BCPhysicalResidual.physicalSchlafliBianchiMasterProp_holds V B

/-- **Primary D2 witness for the master theorem.**  The Regge/EH clause
carries the physical product-filter convergence theorem; the Bianchi clause
carries the Schläfli-based contracted discrete Bianchi identity.  No endpoint
receipt indirection. -/
def canonicalRegEHContinuumAndBianchiWitness :
    MasterTheorem.RegEHContinuumAndBianchi where
  regge_to_einstein_hilbert_continuum := concretePhysicalRegEHContinuumProp
  regge_holds := concretePhysicalRegEHContinuumProp_holds
  discrete_bianchi_contracted := concretePhysicalBianchiProp
  bianchi_holds := concretePhysicalBianchiProp_holds

/-! ## §0b. Endpoint-receipt D2 witness (audit route) -/

/-- Endpoint-receipt D2 Regge/EH proposition: packages the proved single-slice,
varying-cardinality, and physical-D2 witness endpoints from Track 1.
Retained as an audit route; the primary route above is preferred. -/
def endpointRouteRegEHContinuumProp : Prop :=
  MasterTheoremHandoffIntegration.Track1SingleSliceProductFilterDataEndpoint.{0} ∧
  MasterTheoremHandoffIntegration.Track1VaryingCardinalityProductFilterDataEndpoint.{0, 0} ∧
  MasterTheoremHandoffIntegration.Track1PhysicalD2MasterWitnessEndpoint.{0, 0}

theorem endpointRouteRegEHContinuumProp_holds :
    endpointRouteRegEHContinuumProp :=
  ⟨MasterTheoremHandoffIntegration.track1_single_slice_product_filter_data_endpoint_holds,
   MasterTheoremHandoffIntegration.track1_varying_cardinality_product_filter_data_endpoint_holds,
   MasterTheoremHandoffIntegration.track1_physical_d2_master_witness_endpoint_holds⟩

/-- Endpoint-receipt D2 witness (audit route). -/
def canonicalRegEHContinuumAndBianchiWitness_endpointRoute :
    MasterTheorem.RegEHContinuumAndBianchi where
  regge_to_einstein_hilbert_continuum := endpointRouteRegEHContinuumProp
  regge_holds := endpointRouteRegEHContinuumProp_holds
  discrete_bianchi_contracted := concretePhysicalBianchiProp
  bianchi_holds := concretePhysicalBianchiProp_holds

/-! ## §1. D3, D4, D5 witnesses (unchanged) -/

/-- D3 proposition strengthened to include the many-body `PiTensorProduct`
endpoint, not only the binary physical-channel certificate. -/
def canonicalAmplitudeLinearManyBodyProp : Prop :=
  Nonempty
    QuantumChannel.AmplitudeLinearForced.PhysicalChannelAmplitudeLinearCert ∧
  Nonempty
    QuantumChannel.AmplitudeLinearForced.ManyBodyPhysicalChannelAmplitudeLinearCert ∧
  MasterTheoremHandoffIntegration.Track2ManyBodyEndpoint

theorem canonicalAmplitudeLinearManyBodyProp_holds :
    canonicalAmplitudeLinearManyBodyProp :=
  ⟨QuantumChannel.AmplitudeLinearForced.physicalChannelAmplitudeLinearCert_inhabited,
   QuantumChannel.AmplitudeLinearForced.manyBodyPhysicalChannelAmplitudeLinearCert_inhabited,
   MasterTheoremHandoffIntegration.track2_many_body_endpoint_holds⟩

/-- Canonical theorem-built D3 witness for the master theorem. -/
def canonicalAmplitudeLinearForcedWitness :
    MasterTheorem.AmplitudeLinearForcedUnconditional where
  amplitude_linear_forced_unconditional := canonicalAmplitudeLinearManyBodyProp
  holds := canonicalAmplitudeLinearManyBodyProp_holds

/-- Canonical theorem-built D4 witness, strengthened to the **nontrivial**
Page process on `Fin 2 ⊗ Fin 2`: an arbitrary-tick-budget triangular Page
curve with derived (capacity-curve) entropy readout, interior peak
`= S_BH/2`, monotone rise before the peak, monotone fall after it, and
strict rise/fall across the peak.  This supersedes the degenerate
`Fin 1`/identity/zero-entropy witness (peer-review finding F3). -/
def canonicalPageCurveDerivedWitness :
    MasterTheorem.PageCurveDerived :=
  PageCurveNontrivial.nontrivialPageCurveDerivedWitness

/-- Audit: the operator-derived Schmidt-saturated witness is still valid
(degenerate `Fin 1` route, retained for provenance). -/
def canonicalPageCurveDerivedWitness_operatorRoute :
    MasterTheorem.PageCurveDerived :=
  PageCurveOperatorEntropy.operatorPageCurveDerivedWitness

/-- Audit: the older recognition-tick witness is still valid. -/
def canonicalPageCurveDerivedWitness_tickRoute :
    MasterTheorem.PageCurveDerived :=
  PageCurveDynamical.pageCurveDerivedWitness_recognitionTicks

/-- Canonical theorem-built PTA witness, strengthened to a typed
observation-channel signal model with formula-level separation. -/
noncomputable def canonicalPTADistinctWitness :
    MasterTheorem.PTAStochasticGWDistinctFromInflation :=
  QGObservableSignalModels.ptaSignalModelWitness

/-- Audit: the older PTA observable-band witness is still valid. -/
noncomputable def canonicalPTADistinctWitness_bandRoute :
    MasterTheorem.PTAStochasticGWDistinctFromInflation :=
  PTAStructural.ptaStochasticGWObservableBandWitness

/-- Canonical theorem-built strong-field witness, strengthened to typed
observation-channel signal models for EHT, S-star, and Cassini.  Ringdown echo
algebra is quarantined in `QGObservableSignalModels` and is not consumed as a
closed physical strong-field witness. -/
noncomputable def canonicalStrongFieldDistinctWitness :
    MasterTheorem.StrongFieldTestsDistinctFromGR :=
  QGObservableSignalModels.strongFieldSignalModelWitness

/-- Audit: the older strong-field observable channel witness is still valid. -/
noncomputable def canonicalStrongFieldDistinctWitness_channelRoute :
    MasterTheorem.StrongFieldTestsDistinctFromGR :=
  StrongFieldStructural.strongFieldObservableDistinctFromGRWitness

/-! ## §2. Scoped theorem-built master assembly -/

/-- **Scoped theorem-built quantum-gravity master assembly.**  The five formerly
external master inputs are supplied here by canonical theorem-built witnesses:
D2 physical Regge/EH product-filter convergence plus Schläfli Bianchi,
D3 many-body amplitude-linearity, D4 recognition-tick Page transfer,
D5 PTA observable band, and D5 named strong-field channels.

This is a zero-argument Lean assembly theorem for the current witness route.
It is **not** a claim that the full physical quantum-gravity framework is
closed from primitives.  The D2 route remains scoped to the canonical
product-filter six-tet torus surface, the general triangulation and Lorentzian
causal-simplex problems remain open, and the black-hole echo mechanism is not
yet horizon-consistent.  See `closureStatus_unconditional` below for the
machine-readable physical-scope audit. -/
theorem rs_quantum_gravity_master_unconditional :
    MasterTheorem.RSQuantumGravityMaster
      canonicalRegEHContinuumAndBianchiWitness
      canonicalAmplitudeLinearForcedWitness
      canonicalPageCurveDerivedWitness
      canonicalPTADistinctWitness
      canonicalStrongFieldDistinctWitness :=
  MasterTheorem.rs_quantum_gravity_master_conditional
    canonicalRegEHContinuumAndBianchiWitness
    canonicalAmplitudeLinearForcedWitness
    canonicalPageCurveDerivedWitness
    canonicalPTADistinctWitness
    canonicalStrongFieldDistinctWitness

/-! ## §3. Audit route master theorem -/

/-- Both D2 routes produce valid master theorem outputs.  The endpoint route
is not dead code; it documents the Track 1 integration path. -/
theorem endpointRoute_master_theorem_valid :
    MasterTheorem.RSQuantumGravityMaster
      canonicalRegEHContinuumAndBianchiWitness_endpointRoute
      canonicalAmplitudeLinearForcedWitness
      canonicalPageCurveDerivedWitness
      canonicalPTADistinctWitness
      canonicalStrongFieldDistinctWitness :=
  MasterTheorem.rs_quantum_gravity_master_conditional
    canonicalRegEHContinuumAndBianchiWitness_endpointRoute
    canonicalAmplitudeLinearForcedWitness
    canonicalPageCurveDerivedWitness
    canonicalPTADistinctWitness
    canonicalStrongFieldDistinctWitness

/-! ## §4. Physical-scope closure status -/

/-- Honest status for the zero-argument master assembly above.

The first field records the Lean fact: theorem-built witnesses have been
installed for the older conditional master theorem.  The remaining fields record
the physical-scope frontier that those witnesses do **not** close. -/
structure MasterTheoremUnconditionalClosureStatus where
  theorem_built_witnesses_installed : Bool
  full_physical_closure : Bool
  d2_quadrature_open : Bool
  general_triangulation_open : Bool
  tensor_tt_recovery_open : Bool
  lorentzian_causal_triangulations_open : Bool
  boundary_ghy_open : Bool
  echo_mechanism_open_or_rejected : Bool

/-- The theorem-built assembly exists, but the full physical quantum-gravity
framework is not closed.  This record is intentionally conservative: it keeps
the useful master theorem available while preventing downstream papers or
certificates from counting scoped witnesses as complete physical recovery. -/
def closureStatus_unconditional : MasterTheoremUnconditionalClosureStatus where
  theorem_built_witnesses_installed := true
  full_physical_closure := false
  d2_quadrature_open := true
  general_triangulation_open := true
  tensor_tt_recovery_open := true
  lorentzian_causal_triangulations_open := true
  boundary_ghy_open := true
  echo_mechanism_open_or_rejected := true

/-- The current zero-argument master assembly must not be cited as full
physical closure. -/
theorem closureStatus_unconditional_not_full_physical_closure :
    closureStatus_unconditional.theorem_built_witnesses_installed = true ∧
    closureStatus_unconditional.full_physical_closure = false :=
  ⟨rfl, rfl⟩

/-- At least one load-bearing physical target remains open; in fact D2
quadrature is still open on the current scoped route. -/
theorem closureStatus_unconditional_has_open_target :
    closureStatus_unconditional.d2_quadrature_open = true ∨
    closureStatus_unconditional.general_triangulation_open = true ∨
    closureStatus_unconditional.tensor_tt_recovery_open = true ∨
    closureStatus_unconditional.lorentzian_causal_triangulations_open = true ∨
    closureStatus_unconditional.boundary_ghy_open = true ∨
    closureStatus_unconditional.echo_mechanism_open_or_rejected = true :=
  Or.inl rfl

end MasterTheoremUnconditional
end Gravity
end IndisputableMonolith
