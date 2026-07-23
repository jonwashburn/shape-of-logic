# Shape of Logic

Machine-checked Lean 4 core for the Shape of Logic theorem spine: the T-2
through T8 forcing chain, the recognition geometry that carries observable
content, and the core gravity (ILG) layer.

This repository is the public core-theory slice of `/reality`. It is not a
mirror of the primary repo and must not grow application or domain layers.

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
`UnifiedForcingChain.t8_holds` remain certificates only. The physical claim
that Recognition requires this topological detector is OPEN and is not
discharged by the T8 Lean surface.

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
