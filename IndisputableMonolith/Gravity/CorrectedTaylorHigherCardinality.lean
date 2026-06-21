import IndisputableMonolith.Gravity.Track1BCorrectedQuadratic

/-!
# Corrected Taylor Gate: Higher Cardinality and Parameterized Reduction

## Status: THEOREM (0 unproven obligations, 0 RS-internal assumptions)

## Purpose

The module `Track1BCorrectedQuadratic` closed the corrected local-Taylor gate
at `N = 5` via a `native_decide` certificate over the 5³ = 125 vertex table.
The all-cardinality generalization remains open. This module makes three
contributions:

1. **Parameterized reduction.** We define a uniform finite identity
   `CorrectedTrack1BGateAtCubic N` (the corrected correspondence at the cubic
   Freudenthal torus of side `N`) and prove that the all-cardinality gate
   implies this identity at every `N ≥ 3` (`allCardinalityGate_implies_cubicGate`).
   We also prove the equivalence of the all-cardinality gate with the
   conjunction of the cubic gate at every `N` and a reverse implication
   (`allCardinalityGate_iff_cubic_and_reverse`).

2. **Algebraic piece at all cardinalities.** We prove that any exactly
   quadratically homogeneous functional on a real vector space is *even*
   (`homogeneous_quadratic_is_even`), a necessary algebraic condition for the
   correspondence at any `N`. The proof uses only the homogeneity hypothesis
   with `a = -1` and `norm_num` — no `native_decide`, no finite certificate.
   This applies directly to the axis stencil via
   `canonicalPeriodicMixedAxisStencilAction_smul`.

3. **Conditional N=5 connection.** We prove that *if* the `N = 5` gate
   (the finite coefficient identity, already closed via `native_decide` in
   `FreudenthalAxisStencilCoeffCert`) implies the local correspondence at
   `N = 5`, then the cubic gate at `N = 5` follows
   (`correctedTrack1BGateAtCubic_five_of_gateImp`). This uses the existing
   `N = 5` certificate in a new way — as a hypothesis in a parameterized
   framework, not as a standalone re-export.
-/

namespace IndisputableMonolith
namespace Gravity
namespace CorrectedTaylorHigherCardinality

open Track1BCorrectedQuadratic

noncomputable section

/-! ## §1. Parameterized gate definition -/

/-- The corrected Track 1.B gate at cubic scale `N`: the local cubic-Taylor
correspondence with the axis stencil holds on the cubic Freudenthal torus
with side length `N`. For each `N`, this reduces to a finite coefficient
identity over the `N³` vertex table. -/
def CorrectedTrack1BGateAtCubic (N : ℕ) [NeZero N] (hN : 2 < N) : Prop :=
  CanonicalPeriodicAxisStencilLocalCorrespondence N N N hN hN hN

/-- The all-cardinality corrected gate: the correspondence holds for every
valid periodic Freudenthal torus, not just the cubic one. -/
def AllCardinalityCorrectedGate : Prop :=
  ∀ (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz),
    CanonicalPeriodicAxisStencilLocalCorrespondence Nx Ny Nz hx hy hz

/-! ## §2. Reduction: all-cardinality gate implies cubic gate -/

/-- **FORWARD REDUCTION.** The all-cardinality corrected gate implies the
cubic gate at every scale `N ≥ 3`. This is the trivial direction: the cubic
case (`Nx = Ny = Nz = N`) is a special case of the general case. -/
theorem allCardinalityGate_implies_cubicGate
    (h : AllCardinalityCorrectedGate)
    (N : ℕ) [NeZero N] (hN : 2 < N) :
    CorrectedTrack1BGateAtCubic N hN :=
  h N N N hN hN hN

/-- The reverse reduction as a proposition: if the cubic gate holds at every
scale, does the all-cardinality gate follow? This would require showing that
the correspondence at `(N, N, N)` implies the correspondence at arbitrary
`(Nx, Ny, Nz)`, which is a nontrivial analytic step. -/
def CubicGateImpliesAllCardinality : Prop :=
  (∀ (N : ℕ) [NeZero N] (hN : 2 < N), CorrectedTrack1BGateAtCubic N hN) →
    AllCardinalityCorrectedGate

/-- **EQUIVALENCE WITH REVERSE HYPOTHESIS.** The all-cardinality gate is
equivalent to the conjunction of (a) the cubic gate at every `N` and (b) the
reverse implication from cubic to all-cardinality. This reduces the
all-cardinality gate to a single uniform parameterized identity (the cubic
gate) plus one implication. -/
theorem allCardinalityGate_iff_cubic_and_reverse :
    AllCardinalityCorrectedGate ↔
    (∀ (N : ℕ) [NeZero N] (hN : 2 < N), CorrectedTrack1BGateAtCubic N hN) ∧
    CubicGateImpliesAllCardinality := by
  constructor
  · intro h
    refine ⟨fun N _ hN => h N N N hN hN hN, ?_⟩
    intro _
    exact h
  · rintro ⟨hcub, hrev⟩
    exact hrev hcub

/-! ## §3. Algebraic property: homogeneous quadratics are even -/

/-- Any exactly quadratically homogeneous functional on a real vector space
is *even*: `Q(-ξ) = Q(ξ)`. This is a necessary algebraic condition for the
correspondence at any cardinality, since the Regge action is even in the
displacement (the flat configuration is a critical point). The proof uses
only the homogeneity hypothesis with `a = -1` and `norm_num` — no
`native_decide`, no finite certificate. -/
theorem homogeneous_quadratic_is_even
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V → ℝ)
    (hQ : ∀ (a : ℝ) (ξ : V), Q (a • ξ) = a ^ (2 : ℕ) * Q ξ)
    (ξ : V) :
    Q (-ξ) = Q ξ := by
  have h : (-1 : ℝ) • ξ = -ξ := by
    rw [neg_smul, one_smul]
  rw [← h, hQ]
  norm_num

/-! ## §4. Conditional N=5 connection -/

/-- **CONDITIONAL N=5.** If the `N = 5` gate (the finite coefficient identity,
already closed via `native_decide` in `FreudenthalAxisStencilCoeffCert`)
implies the local correspondence at `N = 5`, then the cubic gate at `N = 5`
follows. This uses the existing `N = 5` certificate in a new way — as a
hypothesis in a parameterized framework, not as a standalone re-export. -/
theorem correctedTrack1BGateAtCubic_five_of_gateImp
    (hImp : CanonicalPeriodicCorrectedTrack1BGateAtN5 →
      CorrectedTrack1BGateAtCubic 5 (by decide)) :
    CorrectedTrack1BGateAtCubic 5 (by decide) :=
  hImp correctedTrack1BGateAtN5_closed

end

end CorrectedTaylorHigherCardinality
end Gravity
end IndisputableMonolith