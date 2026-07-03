import Mathlib
import IndisputableMonolith.NumberTheory.ErdosStrausBoxPhase

/-!
# Subset-Product Phase Layer

This module isolates the finite subgroup-generation layer needed by the
Erdős-Straus residual proof.

The analytic prime-distribution theorem should not be asked to construct
the unit fractions directly.  It should only supply a square-budget divisor
whose phase is the target phase.  The finite layer below converts that phase
hit into the already-proved `HitsBalancedPhase` predicate.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace SubsetProductPhase

open ErdosStrausBoxPhase
open ErdosStrausRotationHierarchy

/-- A phase-generating subset-product witness.

The `box` field is the square-budget divisor selected by the prime-phase
generator.  The divisibility conditions say that both the generated divisor
and its complementary divisor land in the target phase `-N` modulo `c`.
-/
structure SubsetProductPhaseHit (n c : ℕ) where
  x : ℕ
  N : ℕ
  box : DivisorExponentBox N
  n_pos : 0 < n
  c_pos : 0 < c
  x_pos : 0 < x
  N_pos : 0 < N
  N_eq : N = n * x
  c_eq : c = 4 * x - n
  divisor_phase : c ∣ N + boxDivisor box
  complement_phase : c ∣ N + boxComplement box

/-- The target phase in the residual quotient. -/
def TargetPhase (N c : ℕ) : ZMod c :=
  -(N : ZMod c)

/-- The generated divisor phase. -/
def generatedDivisorPhase {n c : ℕ} (hit : SubsetProductPhaseHit n c) : ZMod c :=
  (boxDivisor hit.box : ZMod c)

/-- The complementary divisor phase. -/
def generatedComplementPhase {n c : ℕ} (hit : SubsetProductPhaseHit n c) : ZMod c :=
  (boxComplement hit.box : ZMod c)

/-- A generated target phase gives the box-phase predicate used by the
Erdős-Straus closure module. -/
theorem generated_phase_hit_gives_HitsBalancedPhase {n c : ℕ}
    (hit : SubsetProductPhaseHit n c) :
    HitsBalancedPhase n c := by
  refine ⟨hit.x, hit.N, hit.box,
    hit.n_pos, hit.c_pos, hit.x_pos, hit.N_pos,
    hit.N_eq, hit.c_eq, hit.divisor_phase, hit.complement_phase⟩

/-- Hence a generated target phase gives the rational Erdős-Straus
representation. -/
theorem generated_phase_hit_gives_repr {n c : ℕ}
    (hit : SubsetProductPhaseHit n c) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  box_phase_hit_gives_repr (generated_phase_hit_gives_HitsBalancedPhase hit)

/-- Converse: a `HitsBalancedPhase` predicate gives a `SubsetProductPhaseHit`
witness.  The two are isomorphic (Prop existential vs Type structure). -/
theorem subsetProductPhaseHit_of_hitsBalancedPhase {n c : ℕ}
    (h : HitsBalancedPhase n c) :
    Nonempty (SubsetProductPhaseHit n c) := by
  rcases h with ⟨x, N, box, hn, hc, hx, hNpos, hN, hcdef, hdvd, hevd⟩
  refine ⟨SubsetProductPhaseHit.mk x N box hn hc hx hNpos hN hcdef hdvd hevd⟩

/-- The two formulations are equivalent. -/
theorem hitsBalancedPhase_iff_nonempty_subsetProductPhaseHit {n c : ℕ} :
    HitsBalancedPhase n c ↔ Nonempty (SubsetProductPhaseHit n c) :=
  ⟨subsetProductPhaseHit_of_hitsBalancedPhase,
   fun ⟨hit⟩ => generated_phase_hit_gives_HitsBalancedPhase hit⟩

end SubsetProductPhase
end NumberTheory
end IndisputableMonolith
