import IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser

/-!
# Regge TT continuum closer: `ReggeTTContinuumIsotropyTarget` is closed

QG full-theory campaign, Paper C / Pillar 1, production stage C-DAG4, the
final stage of the panel-locked D-dag order (`ReggeTTBlochAssembly →
ReggeTTContinuumLimit → ReggeTTAlgebraicCloser → ReggeTTContinuumCloser`).

## The verbatim target

`ReggeTTSymbolPreflight.ReggeTTContinuumIsotropyTarget` (the named OPEN
target of the preflight, status flag `false` there): for every nonzero
integer wave vector `m` and every TT polarization `E`
(`IsTTPolarization`: symmetric, traceless, transverse, Frobenius-
normalized), the continuum TT Bloch symbol of the TRUE nonlinear Regge
action exists and equals `reggeTTContinuumCoefficient = -(1/4)`, the
linearized Einstein-Hilbert TT coefficient in these conventions.

`reggeTTContinuumIsotropyTarget_closed` below proves it.  The witness
sequence for `ReggeTTContinuumSymbolIs` is the actual reduced finite
symbol `canonicalFiniteH (j+3) E m`:

* fixed-`N` symbol existence: `planeWave_TTBlochSymbolIs_reduced` (Gate
  A1 + A2(b), the Schläfli-reduced second variation of the true action);
* normalized convergence to `-(1/4)`: the algebraic closer's composed
  headline `canonicalFiniteH_div_momentumNormSq_tendsto_isotropy`
  (P1.1a continuum limit + the C8 closed form
  `(1/2)·xᵀ·adj(E)·x` + the TT adjugate step).

## Scope disclosures (inherited, binding)

* This closes the 3D isotropy target.  It does NOT flip
  `gap_action_recovery`: the ledger names the 4D pair
  `edge_tt_decomposition` + `S_RS_converges_EH_4d` as that flag's closing
  theorems, and neither is proved here.
* Aliasing non-repair (inherited from the assembly stage): the finite
  assembly identity holds only at non-aliased side lengths and is
  consumed in eventual-filter form; no repair at aliased small `N` is
  attempted or needed for the limit.

No `sorry`, no `admit`, no new axioms, no `native_decide` in this file.
No `: True` or `Nonempty`-only headline.

## Inherited axiom footprint (disclosure, Elmo receipt 2026-07-17)

The convergence side is clean: the algebraic closer's composed headline
`canonicalFiniteH_div_momentumNormSq_tendsto_isotropy` and the P1.1a
limit carry exactly `[propext, Classical.choice, Quot.sound]`.  The
existence side (`planeWave_TTBlochSymbolIs_reduced`, Gate A1 + A2(b))
rides the certified periodic angle-sum chain and therefore ALSO carries
`Lean.ofReduceBool` and `Lean.trustCompiler` (inherited compiler-trust
disclosure, same as `ReggeTTHingeAwareZeroMode`; not new axioms).  All
three theorems below inherit that footprint through the existence
component.  `#print axioms` receipts at end of file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTContinuumCloser

open ReggeTTSymbolPreflight
open ReggeTTBlochInterfaceAudit

noncomputable section

/-- The reduced finite symbol IS a fixed-`N` TT Bloch symbol value: the
Gate A1 + A2(b) existence theorem restated on `canonicalFiniteH`. -/
theorem canonicalFiniteH_TTBlochSymbolIs (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) :
    TTBlochSymbolIs N E m (canonicalFiniteH N E m) :=
  ReggeTTFlatSecondVariation.planeWave_TTBlochSymbolIs_reduced N E m

/-- **THE VERBATIM 3D CLOSER (THEOREM): `ReggeTTContinuumIsotropyTarget`
holds.**  For every nonzero integer wave vector and every TT polarization,
the continuum TT Bloch symbol of the true Regge action exists and equals
`-(1/4)` — the symbol is isotropic with exactly the linearized
Einstein-Hilbert TT coefficient.  The preflight's OPEN target is closed;
the C10/C8 numerics are hereby superseded by kernel proof at 3D action
strength. -/
theorem reggeTTContinuumIsotropyTarget_closed :
    ReggeTTContinuumIsotropyTarget := by
  intro m E hm hTT
  have hm' : ∃ i : Fin 3, m i ≠ 0 := Function.ne_iff.mp hm
  refine ⟨fun j => @canonicalFiniteH (j + 3) (instNeZeroAddThree j) E m,
    fun j => canonicalFiniteH_TTBlochSymbolIs (j + 3) E m, ?_⟩
  exact
    ReggeTTAlgebraicCloser.canonicalFiniteH_div_momentumNormSq_tendsto_isotropy
      m E hm' hTT

/-- The closed target instantiated at the preflight's own non-vacuity
witnesses (axis wave vector, `+` polarization): the continuum symbol at
that concrete instance is `-(1/4)`.  Non-vacuity receipt. -/
theorem axis_plus_continuum_symbol :
    ReggeTTContinuumSymbolIs axisTTPolarizationPlus axisWaveVector
      reggeTTContinuumCoefficient :=
  reggeTTContinuumIsotropyTarget_closed axisWaveVector axisTTPolarizationPlus
    axisWaveVector_ne_zero axisTTPolarizationPlus_isTT

end

end ReggeTTContinuumCloser
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumCloser.canonicalFiniteH_TTBlochSymbolIs
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumCloser.reggeTTContinuumIsotropyTarget_closed
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumCloser.axis_plus_continuum_symbol
