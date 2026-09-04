# Shape of Logic

Machine-checked Lean 4 core for the Shape of Logic theorem spine: the T-2
through T8 forcing chain, the recognition geometry that carries observable
content, and the core gravity (ILG) layer.

This repository is the public core-theory slice of `/reality`. It is not a
mirror of the primary repo and must not grow application or domain layers.

## Read me first

Open `IndisputableMonolith/Verdict.lean`, the front door: every premise and every
conclusion of Recognition Science in one theorem signature,

```lean
Verdict.recognition_science (c : Cited) (P : Premises F κ D Fr H) : Conclusions F κ D Fr H
```

with consistency and independence theorems beside it. `Verdict_Read_Me_First.html`
walks a newcomer through what to open, what to check, and the exact sentence the
file licenses. `bash scripts/verify_rs.sh` (from the repository root, after
`lake exe cache get`) rebuilds the door, prints its axioms, walks its transitive
closure, and writes `Verdict_Report_<date>.html`; the 2026-09-03 run is committed.

Euclid's geometry is the axioms and everything the axioms force. Recognition
Science is the T-2 through T8 theorems and everything forced from them. That
the premises hold of the world is not proved here; what is proved is that
anyone who accepts them has accepted the conclusions, and that no premise is
hidden.

## Public Theorem Surface

### Forcing-chain spine (T-2 through T8)

```lean
NothingToDistinction.nothingToDistinctionCert
TMinus1ToT8Bridge.complete_forcing_chain_tminus2_to_t8
CircleWindingChain.circleH1ZNonzero_unconditional
CircleWindingChain.circleH1ZIsoInt_holds
```

### Recognition core (T0 / T4 observable layer)

```lean
RecognitionCore.forced_quotient_iff               -- signature determines state up to indistinguishability
RecognitionCore.gauge_from_indistinguishability   -- gauge = no distinguishing recognition act
RecognitionCore.signature_complete_iff_separating -- completeness iff the family separates points
RecognitionCore.one_bit_not_complete_boundary     -- one Boolean coordinate is atomic, not complete
RecognitionCore.recognizer_refinement             -- composing recognizers refines the quotient
RecognitionCore.recognizer_induces_logic          -- a recognizer supplies the Aristotelian conditions
RecognitionCore.multiplicative_recognizer_L4      -- composition consistency derived, not assumed
```

### Core gravity (ILG)

```lean
Gravity.ILG             -- information-limited-gravity time-kernel / weight functions
Gravity.Rotation        -- Newtonian rotation-curve identities
Gravity.DerivedFactors  -- HSB suppression from SevenBeatViolation saturation
```

### The unit of the recognition cost (T5 continued)

```lean
Cost.FunctionalEquation      -- law_of_logic_forces_jcost: the shape of J is forced
Cost.RealTraceRoot           -- realTraceRoot: the principal root of a doubled trace
Cost.RealCharacterFactorization
                             -- every anchor-free cost factors through a real character
Cost.MonotoneMultiplicativePower
                             -- Erdos's theorem, completely multiplicative case (Howe's proof)
Cost.TraceRationalExponent   -- rational traces force an integer exponent
Cost.GaugeOrbitFromRealCharacter
                             -- the sign cost and the signed power costs
Cost.GaugeOrbitClassification
                             -- the anchor-free cost ledger has one member per exponent
Cost.UnitFromMinimality      -- J is the strict least member once exponent zero is excluded
```

T5 forces the shape of the recognition cost and leaves its scale free. This slice
closes the scale question on the countable carrier. The classification
(`GaugeOrbitIsSignedPowerFamily_of_sixExponentials`) is complete up to one named
hypothesis, `TraceRationalExponent.SixExponentialsTraceInput`, which carries the six
exponentials theorem of transcendence theory; that hypothesis appears in the statement
of every result that uses it and is not an axiom. Erdos's theorem on monotone
multiplicative functions was the other external input and is now proved here. With the
classification in hand, `jcost_lt_pow` and `anchor_is_minimality_over_powers` say that
`J` is the cheapest member that charges anything, so the numeric unit is a consequence
of a least-cost rule rather than a stipulation. Papers: *The Cost of Distinction* and
*Monotonicity Replaces Continuity in the d'Alembert Equation over the Rationals*.

### Forced response / two-way traffic (cost-derived kinetics)

```lean
Thermodynamics.ForcedResponseLaw
Thermodynamics.ForcedResponseOddness
Thermodynamics.ForcedResponseLargeDeviationBridge
Thermodynamics.ForcedResponseSignBlindMobility
Thermodynamics.ForcedResponseDetailedBalanceNormalForm
Thermodynamics.ForcedResponseCostDeterminedActivity
Thermodynamics.ForcedResponseCostIsTheBarrier
```

These modules derive the detailed-balance normal form, sign-blind mobility,
and the recognition-cost barrier law used in *Two-Way Traffic from a Recognition
Cost*. Headline receipts include
`flux_eq_two_exp_deviation_mul_sinh_half`,
`barrier_law_implies_reciprocity`, and
`calibrated_activity_gt_marcus`. Build tip:

```bash
lake build IndisputableMonolith.Thermodynamics.ForcedResponseCostIsTheBarrier
```

The forcing-chain scope is:

```text
T-2  absolute nothing encoded as Empty
T-1  first distinction / absolute floor
T0   Boolean recognition-work split
T1   Meta-Principle at the cost floor
T2   discrete two-state floor
T3   additive ledger bookkeeping
T4   recognition witness
T5   canonical reciprocal cost J forced by the Law-of-Logic equation
T6   phi forced by self-similar hierarchy
T8   D = 3 from content-typed circle-complement linking
T7   eight-tick cube period downstream of D = 3
```

T8 is current with the `/reality` SOTA. The architecture authority is
`Foundation.PublicSpineLinkingClosure.forces_D3` /
`target_D3`: an embedded circle in `S^D` has nontrivial complement `H₁`
exactly when `D = 3`, over Mathlib singular homology, with no arithmetic
encoding. The circle-`H₁` handoff
(`circleH1ZNonzero_unconditional`, `circleH1ZIsoInt_holds`) is a premise of
that bridge. Legacy `Foundation.DimensionForcing.linking_requires_D3` and
`UnifiedForcingChain.t8_holds` remain certificates only.

The Recognition-to-detector identification is banked on the same tree, with
honest walls:

* `Foundation.RecognitionToLinkingSeam` — bare Recognition supply does not
  force the content-typed detector
* `Foundation.LinkingNecessity` — the Deformation-Erasure Principle is the
  named residual; it forces `D = 3` and is independent of the realization layer
* `Foundation.RecognitionProducedEmbedding` — a detecting embedding produced
  from the hierarchy winding, proved unequal to the bare unknot
* `Foundation.PublicSpine.PostingPhase3Wall` — the balanced six-cycle is a
  compiled countermodel; posting-derived predicates cannot force coverage
* `Foundation.PublicSpine.PartINamedAxiomClosure` — completeness is a
  disclosed `SemanticClockLaw`, not a consequence of balance

`Foundation/PublicSpine/CalibrationDischargeProbe.lean` is included as a
readable residual probe. It imports a scale-boundary module that is not in
this public slice, so it is a reference file rather than a core-build leaf.

## Boundary Rule

Allowed public content:

* Lean files needed by the T-2 through T8 proof spine.
* Circle-H1 files proving the T8 Mathlib H1 closure.
* The recognition-geometry core: recognizer, indistinguishability quotient,
  recognition signature, completeness condition, and recognizer composition
  (`RecogGeom/*`, the recognizer/observer/signature `Foundation/*` files).
* The core gravity (ILG) layer: the information-limited-gravity weight kernel,
  Newtonian rotation-curve identities, and the derived suppression factors
  (`Gravity/ILG`, `Gravity/Rotation`, `Gravity/DerivedFactors`,
  `Gravity/ParameterizationBridge`, `Gravity/GravityParameters`).
* Minimal scripts and CI needed to audit that slice.
* Core theory papers explaining the same proof surface.

Excluded content:

* No runtime, application, or research vertical outside the public theorem
  surface listed above.
* No deeper physics or engineering stack unless it is required to compile one
  of the allowed roots.
* Nothing else unless it is a direct import dependency of one of the allowed
  surfaces above.
* Exception: a small set of read-only reference modules (listed under
  "Reference modules" below) is included for external review of results cited in
  our papers. They are not built by the core target, are not import dependencies
  of the spine, and are not a commitment to publish the full application stack.

## Reference modules (read-only)

A small number of modules are included here for external review only. They are
not part of the core build slice above and do not compile standalone in this
repository, because they import declarations from the full Recognition Science
library that this public slice does not include. They are reproduced so
collaborators can read the exact source behind results referenced in our papers:

* `Gravity/QGScopeAudit`, `Gravity/ReggeConvergenceRegistry`,
  `Gravity/Track1BCompilerTrustStatus`, `Gravity/Track1BCorrectedQuadratic`,
  `Gravity/D2ScalarDirichletQuadratureLimit`, `Gravity/D2ScalarDirichletPartial`,
  `Gravity/D2DampedScheduleClosure`, `Gravity/D2QuadratureInstances`,
  `Gravity/AdmissibleTriangulationProcedure`,
  `Gravity/CorrectedTaylorHigherCardinality`
* `Foundation/BornRuleForcing`, `Foundation/HamiltonianEmergenceOperator`
* `Cosmology/VacuumHorizonForcing`, `Cosmology/DarkEnergyStrongClosure`,
  `Foundation/MaximalForcing/RSDarkEnergyShapeForcing`

These files are complete, and they build and typecheck cleanly in the full
`/reality` framework. That framework is not yet public, which is the only reason
they do not resolve all of their imports here. The core build target
(`lake build IndisputableMonolith`) compiles the T-2 through T8 spine, the
recognition core, and the ILG gravity core, and does not depend on any of the
reference modules above.

## Audit

Run:

```bash
python3 scripts/audit_public.py
lake build IndisputableMonolith
lake build IndisputableMonolith.Foundation.TMinus1ToT8Bridge
lake build IndisputableMonolith.RecognitionCore
lake build IndisputableMonolith.Gravity
```

The audit checks the public Lean slice for `sorry`, `admit`, local `axiom`
declarations, and deny-listed private/application material.

## Build

```bash
elan default leanprover/lean4:v4.27.0-rc1
lake exe cache get
lake build IndisputableMonolith
```

## Citation

Washburn, J. *Shape of Logic: a machine-checked T-2 through T8 forcing spine.*
Recognition Physics Institute, 2026.
