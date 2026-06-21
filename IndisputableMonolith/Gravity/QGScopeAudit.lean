import IndisputableMonolith.Gravity.PathSumUVBound
import IndisputableMonolith.Gravity.RecognitionLedger
import IndisputableMonolith.Gravity.D2ScopingAudit
import IndisputableMonolith.Gravity.TensorShearSector
import IndisputableMonolith.Gravity.BlackHoleEchoesFromBounce
import IndisputableMonolith.Gravity.Track1BCorrectedQuadratic
-- §5 consolidation (2026-06-21): the eight contingency/tightening modules
import IndisputableMonolith.Gravity.ReggeConvergenceRegistry
import IndisputableMonolith.Gravity.Track1BCompilerTrustStatus
import IndisputableMonolith.Gravity.D2ScalarDirichletQuadratureLimit
import IndisputableMonolith.Gravity.D2ScalarDirichletPartial
import IndisputableMonolith.Gravity.LedgerToGeometryBridge
import IndisputableMonolith.Gravity.EchoHorizonObstruction
import IndisputableMonolith.Gravity.CorrectedTaylorHigherCardinality
import IndisputableMonolith.Gravity.AdmissibleTriangulationProcedure
import IndisputableMonolith.Gravity.ConditionalSlot

/-!
# Quantum-Gravity Scope Audit

This module is the central honesty surface for the current QG framework.

It does not try to close new physics.  It records which bridge layers are
actually theorem-grade and which ones remain open, so paper and master-theorem
surfaces cannot accidentally count a scoped reduction or bridge condition as
full quantum gravity.

Status: THEOREM about current scope.  Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QGScopeAudit

/-! ## §1. Bridge-layer status record -/

/-- Current status of the bridge layers needed for a worked quantum-gravity
theory, beyond the algebraic RS substrate and scoped Regge reductions. -/
structure QGBridgeClosureStatus where
  /-- A concrete physical class of allowed triangulations has been specified for
  the full QG path sum. -/
  admissible_triangulation_class_specified : Bool
  /-- The equivalence relation or measure quotient on triangulations has been
  specified for the full QG path sum. -/
  path_sum_equivalence_relation_specified : Bool
  /-- A full measure/convergence theorem for the QG path sum is closed. -/
  path_sum_full_measure_theorem_closed : Bool
  /-- A substrate-to-hinge map constructing the comparison variable at each
  hinge has been derived from the discrete ledger. -/
  ledger_to_hinge_map_constructed : Bool
  /-- The paper's `log x_sigma = kappa_sigma delta_sigma + O(h^3)` relation is
  still a bridge condition rather than a derived construction. -/
  substrate_deficit_ratio_bridge_condition_open : Bool
  /-- Lorentzian causal simplex admissibility is closed. -/
  lorentzian_causal_simplex_class_closed : Bool
  /-- Hartle-Sorkin/GHY boundary recovery is closed. -/
  hartle_sorkin_ghy_boundary_closed : Bool
  /-- TT/Lichnerowicz gravitational-wave recovery is closed. -/
  tensor_tt_lichnerowicz_recovery_closed : Bool
  /-- Continuum Dirac constraint algebra recovery is closed. -/
  dirac_constraint_algebra_recovery_closed : Bool
  /-- The scalar/conformal canonical six-tet product route exists as a scoped
  reduction. -/
  scalar_conformal_six_tet_reduction_available : Bool
  /-- The conformal ansatz obstruction to representing shear is proved. -/
  conformal_shear_obstruction_proved : Bool
  /-- The corrected local-Taylor `N = 5` coefficient gate is closed. -/
  corrected_taylor_n5_gate_closed : Bool
  /-- The corrected Taylor all-cardinality extension remains open. -/
  corrected_taylor_all_cardinality_open : Bool
  /-- The discrete Bianchi row is closed on the Schläfli-compatible class. -/
  bianchi_schlafli_compatible_closed : Bool
  /-- The old black-hole bounce-through-horizon echo mechanism is rejected or
  open, not theorem-grade physical closure. -/
  echo_mechanism_open_or_rejected : Bool

/-- Honest QG scope status after the 2026-06-21 audit repair and the
consolidation pass.  `admissible_triangulation_class_specified` flipped to
`true` once `AdmissibleTriangulationProcedure` landed (the RS admissibility
predicate is now an explicit Lean object); the recognition-ratio bridge inside
it is still assumed, which `substrate_deficit_ratio_bridge_condition_open`
records. -/
def qgBridgeClosureStatus : QGBridgeClosureStatus where
  admissible_triangulation_class_specified := true
  path_sum_equivalence_relation_specified := false
  path_sum_full_measure_theorem_closed := false
  ledger_to_hinge_map_constructed := false
  substrate_deficit_ratio_bridge_condition_open := true
  lorentzian_causal_simplex_class_closed := false
  hartle_sorkin_ghy_boundary_closed := false
  tensor_tt_lichnerowicz_recovery_closed := false
  dirac_constraint_algebra_recovery_closed := false
  scalar_conformal_six_tet_reduction_available := true
  conformal_shear_obstruction_proved := true
  corrected_taylor_n5_gate_closed := true
  corrected_taylor_all_cardinality_open := true
  bianchi_schlafli_compatible_closed := true
  echo_mechanism_open_or_rejected := true

/-! ## §2. The status record carries open obligations -/

/-- The current QG bridge status is not full physical closure. -/
theorem qgBridgeClosureStatus_not_full_physical_closure :
    qgBridgeClosureStatus.path_sum_full_measure_theorem_closed = false ∧
    qgBridgeClosureStatus.ledger_to_hinge_map_constructed = false ∧
    qgBridgeClosureStatus.lorentzian_causal_simplex_class_closed = false ∧
    qgBridgeClosureStatus.tensor_tt_lichnerowicz_recovery_closed = false ∧
    qgBridgeClosureStatus.dirac_constraint_algebra_recovery_closed = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- At least one named bridge target is open; the path-sum equivalence relation
alone is already enough to prevent a full-closure reading. -/
theorem qgBridgeClosureStatus_has_open_target :
    qgBridgeClosureStatus.path_sum_equivalence_relation_specified = false ∨
    qgBridgeClosureStatus.ledger_to_hinge_map_constructed = false ∨
    qgBridgeClosureStatus.tensor_tt_lichnerowicz_recovery_closed = false :=
  Or.inl rfl

/-! ## §3. Links to existing theorem surfaces -/

/-- The D2 audit already says the scalar/conformal product route still has an
open quadrature target and an open general-triangulation extension. -/
theorem d2_scope_open_targets_carried :
    D2ScopingAudit.d2ScopeStatusDamped.quadrature_target_open = true ∧
    D2ScopingAudit.d2ScopeStatusDamped.general_triangulation_open = true :=
  ⟨rfl, rfl⟩

/-- The tensor/shear module proves that a nontrivial rectangle/shear mode cannot
be realized by the vertex-conformal scalar ansatz. -/
theorem conformal_ansatz_does_not_cover_shear :
    ∀ (h v : ℝ), h ≠ v →
      ¬ ∃ ξa ξb ξc ξd : ℝ,
        (ξa + ξb) / 2 = h ∧
        (ξc + ξd) / 2 = h ∧
        (ξb + ξc) / 2 = v ∧
        (ξd + ξa) / 2 = v :=
  TensorShearSector.nontrivial_rectangle_shear_not_vertexConformal

/-- The echo mechanism status is carried into the QG scope audit. -/
theorem echo_mechanism_quarantine_carried :
    BlackHoleEchoesFromBounce.blackHoleEchoMechanismStatus.bounce_escape_mechanism_rejected = true ∧
    BlackHoleEchoesFromBounce.blackHoleEchoMechanismStatus.astrophysical_echo_prediction_theorem_grade = false :=
  ⟨rfl, rfl⟩

/-- The corrected local-Taylor `N = 5` gate is no longer open in Lean. -/
theorem corrected_taylor_n5_gate_closed_carried :
    Track1BCorrectedQuadratic.correctedTrack1BStatus.gate_open = false ∧
    qgBridgeClosureStatus.corrected_taylor_n5_gate_closed = true ∧
    qgBridgeClosureStatus.corrected_taylor_all_cardinality_open = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## §4. Contingency register (2026-06-21)

Machine-visible inventory of the four contingency patterns flagged by the
audit ("a lot of the proofs are contingent on items that are definitions or
hypotheses").  This is the spine of the fix-it plan
(`plans/QG_Contingency_FixIt_Plan_20260621.html`): the counts and statuses
live in the type system, not only in prose. -/

/-- Per-pattern remedy classification used by the fix-it plan. -/
inductive ContingencyRemedy
  | dischargeFromPrimitives        -- R1
  | honestDowngradeScopeLock       -- R2
  | externalAxiomRegistry          -- R3
  deriving DecidableEq, Repr

/-- The contingency register: exact instance counts and remedy/closed flags for
each pattern.  Counts are from direct retrieval on 2026-06-21. -/
structure QGContingencyRegister where
  /-- Pattern A: vacuous `Σ(P:Prop),P` witness shells in `MasterTheorem.lean`. -/
  patternA_master_slots : Nat
  /-- Pattern A: vacuous shells in `QuantumGravitySufficientConditions.lean`. -/
  patternA_sufficient_condition_slots : Nat
  patternA_remedy : ContingencyRemedy
  patternA_closed : Bool
  /-- Pattern B: data-structure analytic hypothesis fields (quadrature/residual,
  local correspondence, Schläfli) consumed as proved. -/
  patternB_hypothesis_field_families : Nat
  patternB_remedy : ContingencyRemedy
  patternB_closed : Bool
  /-- Pattern C: external convergence Props axiomatized in `NonlinearConvergence.lean`. -/
  patternC_external_convergence_props : Nat
  patternC_remedy : ContingencyRemedy
  patternC_closed : Bool
  /-- Pattern D: compiler-trust closures (native_decide) in the QG surface. -/
  patternD_compiler_trust_closures : Nat
  patternD_remedy : ContingencyRemedy
  patternD_closed : Bool

/-- The register as of the 2026-06-21 audit.  All four patterns are still open
(the structural refactors have not yet landed); this records the starting
state so progress is machine-checkable. -/
def qgContingencyRegister : QGContingencyRegister where
  patternA_master_slots := 6
  patternA_sufficient_condition_slots := 51
  patternA_remedy := ContingencyRemedy.honestDowngradeScopeLock
  patternA_closed := false
  patternB_hypothesis_field_families := 3
  patternB_remedy := ContingencyRemedy.dischargeFromPrimitives
  patternB_closed := false
  patternC_external_convergence_props := 4
  patternC_remedy := ContingencyRemedy.externalAxiomRegistry
  patternC_closed := false
  patternD_compiler_trust_closures := 1
  patternD_remedy := ContingencyRemedy.honestDowngradeScopeLock
  patternD_closed := false

/-- Total number of vacuous `Σ(P:Prop),P` witness shells the Pattern-A refactor
must convert to parameterized `ConditionalSlot` types. -/
def qgContingencyRegister_patternA_total : Nat :=
  qgContingencyRegister.patternA_master_slots +
  qgContingencyRegister.patternA_sufficient_condition_slots

/-- The Pattern-A refactor target is 57 slots, and no contingency pattern is
closed yet.  This is the honest starting line for the fix-it plan. -/
theorem qgContingencyRegister_starting_state :
    qgContingencyRegister_patternA_total = 57 ∧
    qgContingencyRegister.patternA_closed = false ∧
    qgContingencyRegister.patternB_closed = false ∧
    qgContingencyRegister.patternC_closed = false ∧
    qgContingencyRegister.patternD_closed = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The can't-skip change: Pattern A is the gating contingency, so the framework
must not report full physical closure while Pattern A is open. -/
theorem qgContingencyRegister_patternA_gates_full_closure :
    qgContingencyRegister.patternA_closed = false ∧
    qgBridgeClosureStatus.path_sum_full_measure_theorem_closed = false :=
  ⟨rfl, rfl⟩

/-- One-statement audit: the current QG framework has a scoped scalar
Regge-reduction route and theorem-grade φ algebra, but it is not a fully worked
quantum-gravity theory until the listed bridge layers close. -/
theorem qg_scope_audit_one_statement :
    qgBridgeClosureStatus.scalar_conformal_six_tet_reduction_available = true ∧
    qgBridgeClosureStatus.conformal_shear_obstruction_proved = true ∧
    qgBridgeClosureStatus.corrected_taylor_n5_gate_closed = true ∧
    qgBridgeClosureStatus.path_sum_full_measure_theorem_closed = false ∧
    qgBridgeClosureStatus.ledger_to_hinge_map_constructed = false ∧
    qgBridgeClosureStatus.echo_mechanism_open_or_rejected = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5. Consolidation: the eight contingency/tightening modules wired in

This section makes the central audit transitively carry the eight modules
produced by the 2026-06-21 contingency fix and tightening grind, so a reader
who inspects (or `#print axioms`) this audit sees the real content, not just
prose claims.  Owning modules, one line each:

* Pattern C (external convergence) -> `ReggeConvergenceRegistry`
* Pattern D (compiler trust)       -> `Track1BCompilerTrustStatus`
* Pattern B reduction              -> `D2ScalarDirichletQuadratureLimit`
* Pattern B partial (named limit)  -> `D2ScalarDirichletPartial`
* Ledger->geometry bridge + GW     -> `LedgerToGeometryBridge`
* Echo horizon causal obstruction  -> `EchoHorizonObstruction`
* Taylor all-cardinality reduction -> `CorrectedTaylorHigherCardinality`
* Allowed-triangulation procedure  -> `AdmissibleTriangulationProcedure`
-/

/-- Consolidation status: which remedy/tightening module landed for each item.
A `true` flag means the named owning module exists and is built into this audit;
it does NOT mean the underlying physics is discharged from primitives (the open
analytic inputs are tracked by `qgBridgeClosureStatus`). -/
structure QGConsolidationStatus where
  /-- `ReggeConvergenceRegistry`: the four external convergence Props isolated
  into one registry with provenance (Pattern C, remedy R3). -/
  patternC_isolated_via_registry : Bool
  /-- `Track1BCompilerTrustStatus`: the native_decide axiom-basis extension is
  disclosed in a machine-checkable status (Pattern D, remedy R2). -/
  patternD_disclosed_via_status : Bool
  /-- `D2ScalarDirichletQuadratureLimit` + `D2ScalarDirichletPartial`: D2 is
  reduced to a single named scalar-Dirichlet `Tendsto` (Pattern B). -/
  patternB_reduced_to_named_limit : Bool
  /-- `LedgerToGeometryBridge`: the substrate-to-hinge map is a named, explicitly
  assumed bridge condition. -/
  ledger_to_geometry_bridge_named : Bool
  /-- `LedgerToGeometryBridge` / `TensorShearSector`: the conformal ansatz is
  proved insufficient for the transverse-traceless gravitational-wave sector. -/
  conformal_cannot_recover_gw_proved : Bool
  /-- `EchoHorizonObstruction`: the bounce-through-horizon echo is a proved
  causal impossibility. -/
  echo_horizon_obstruction_proved : Bool
  /-- `AdmissibleTriangulationProcedure`: the RS admissibility predicate is an
  explicit Lean object with a proved witness. -/
  admissible_triangulation_procedure_specified : Bool
  /-- `CorrectedTaylorHigherCardinality`: a real parameterized all-cardinality
  reduction plus a `norm_num`-proved algebraic lemma. -/
  taylor_all_cardinality_reduction_proved : Bool
  /-- The Pattern-A target type `ConditionalSlot` and its formal justification
  (old shell always inhabited; lifted slot inhabited iff its parameter) are in
  place via `ConditionalSlot`. -/
  patternA_target_and_justification_landed : Bool
  /-- The repo-wide Pattern-A `Σ(P:Prop),P -> ConditionalSlot` lift (the scripted
  transform over the ~48 shells the scanner finds).  Still pending: this is the
  one remaining can't-skip item. -/
  patternA_conditionalslot_lift_done : Bool

/-- The consolidation status after the 2026-06-21 pass: eight modules landed,
the Pattern-A lift still pending. -/
def qgConsolidationStatus : QGConsolidationStatus where
  patternC_isolated_via_registry := true
  patternD_disclosed_via_status := true
  patternB_reduced_to_named_limit := true
  ledger_to_geometry_bridge_named := true
  conformal_cannot_recover_gw_proved := true
  echo_horizon_obstruction_proved := true
  admissible_triangulation_procedure_specified := true
  taylor_all_cardinality_reduction_proved := true
  patternA_target_and_justification_landed := true
  patternA_conditionalslot_lift_done := false

/-! ### Carried theorems: the audit transitively witnesses each module -/

/-- Pattern C carried: the registry faithfully repackages the four external
convergence Props (projection/construction are inverses). -/
theorem regge_registry_faithful_carried :
    ∀ (r : ReggeConvergenceRegistry.ReggeConvergenceRegistry),
      ReggeConvergenceRegistry.mk r.cms_measure_bound r.special_quadratic
        r.ricci_convergence r.riemann_convergence r.provenance = r :=
  ReggeConvergenceRegistry.mk_roundtrip

/-- Pattern D carried: the compiler-trust disclosure is anchored to the real
closed N=5 gate. -/
theorem compiler_trust_disclosure_carried :
    Track1BCompilerTrustStatus.track1BCompilerTrustStatus.uses_native_decide = true ∧
    Track1BCorrectedQuadratic.correctedTrack1BStatus.gate_open = false :=
  Track1BCompilerTrustStatus.track1BCompilerTrustStatus_anchors_closed_gate

/-- Ledger->geometry carried: the bridge is assumed (not derived) and the
conformal route is insufficient for gravitational waves. -/
theorem ledger_bridge_status_carried :
    ledgerToGeometryBridgeStatus.bridge_is_assumed_not_derived = true ∧
    ledgerToGeometryBridgeStatus.conformal_route_insufficient_for_gw = true :=
  ledgerToGeometryBridgeStatus_flags

/-- Echo carried (status): the bounce-escape mechanism is rejected. -/
theorem echo_status_rejection_carried :
    BlackHoleEchoesFromBounce.blackHoleEchoMechanismStatus.bounce_escape_mechanism_rejected = true :=
  EchoHorizonObstruction.blackHoleEchoMechanismStatus_records_rejection

/-- Echo carried (the strong result): no exterior-return claim with an interior
bounce can exist; it is causally impossible. -/
theorem echo_exterior_return_impossible_carried :
    ∀ (M : EchoHorizonObstruction.CausalModel)
      (_claim : EchoHorizonObstruction.ExteriorReturnClaim M), False :=
  EchoHorizonObstruction.exterior_return_claim_impossible

/-- Allowed-triangulation carried: the RS admissibility predicate has a proved
witness. -/
theorem admissible_procedure_witness_carried :
    Nonempty (AdmissibleTriangulationProcedure.IsRSAdmissible
      AdmissibleTriangulationProcedure.rsAdmissibleWitness) :=
  AdmissibleTriangulationProcedure.exists_RSAdmissible

/-- Pattern-A target carried: the old vacuous shell is always inhabited (hides
its assumption), while the lifted `ConditionalSlot P` is inhabited iff `P`
(exposes its assumption). This is the formal justification for the lift. -/
theorem pattern_a_target_carried :
    Nonempty ConditionalSlot.VacuousWitnessShell ∧
    (∀ P : Prop, Nonempty (ConditionalSlot.ConditionalSlot P) ↔ P) :=
  ⟨ConditionalSlot.vacuousWitnessShell_always_inhabited,
   ConditionalSlot.conditionalSlot_nonempty_iff⟩

/-- **Consolidation one-statement.** Eight contingency/tightening modules are
wired into this audit and landed; the Pattern-A `ConditionalSlot` lift remains
the single pending can't-skip item. -/
theorem qg_consolidation_one_statement :
    qgConsolidationStatus.patternC_isolated_via_registry = true ∧
    qgConsolidationStatus.patternD_disclosed_via_status = true ∧
    qgConsolidationStatus.patternB_reduced_to_named_limit = true ∧
    qgConsolidationStatus.ledger_to_geometry_bridge_named = true ∧
    qgConsolidationStatus.conformal_cannot_recover_gw_proved = true ∧
    qgConsolidationStatus.echo_horizon_obstruction_proved = true ∧
    qgConsolidationStatus.admissible_triangulation_procedure_specified = true ∧
    qgConsolidationStatus.taylor_all_cardinality_reduction_proved = true ∧
    qgConsolidationStatus.patternA_target_and_justification_landed = true ∧
    qgConsolidationStatus.patternA_conditionalslot_lift_done = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end QGScopeAudit
end Gravity
end IndisputableMonolith
