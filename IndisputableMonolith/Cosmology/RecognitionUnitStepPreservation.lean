import Mathlib
import IndisputableMonolith.Cosmology.GradedRungCost
import IndisputableMonolith.Cosmology.RecognitionEquilibrium

/-!
# Unit-step preservation for active recognition dynamics

Phase 56 proved the graded-rung cost law under the forced minimal-distinction invariant
`UnitStep`: adjacent rungs differ by at most one. Phase 57 wired that law into the runtime
cost meter. The tempting next claim would be that the active mean-move dynamics
(`RecognitionEquilibrium.pairResolve`) preserves this invariant automatically.

That claim is false.

This module records the honest theorem layer:

* `pairResolve_unitStep_of_local`: resolving a pair preserves the real-valued unit-step
  invariant provided every edge touching one of the two resolved endpoints remains
  within one rung after the move. Edges disjoint from the resolved pair are preserved
  for free by `pairResolve_other`.
* `chain3_pairResolve_breaks_unitStep`: a three-site chain with levels `0,1,2` is
  unit-step before the move, but resolving the first edge sends levels to
  `1/2,1/2,2`, so the second edge has gap `3/2` and the invariant fails.

The upshot is precise: the live engine may use the Phase-56 cost law only after auditing
or proving the local unit-step condition for the update being applied. A blind global
"mean-move preserves UnitStep" lemma would be false.

HONEST STATUS: THEOREM, 0 `sorry`, no new axioms beyond Mathlib's standard classical
ones. The counterexample is a theorem, not a numerical observation.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RecognitionUnitStepPreservation

open RecognitionEquilibrium

/-! ## §1. Real-valued unit-step fields on a finite edge list -/

/-- A real-valued version of the Phase-56 unit-step invariant: every listed edge has
level gap at most one. This is the right formulation for `pairResolve`, whose mean move
can create half-rungs even when the input levels are integer rungs. -/
def UnitStepReal {n : ℕ} (x : Fin n → ℝ) (E : List (Fin n × Fin n)) : Prop :=
  ∀ e ∈ E, |x e.1 - x e.2| ≤ 1

/-- An edge touches the pair being resolved if either endpoint is one of the two
resolved vertices. -/
def EdgeTouches {n : ℕ} (i j : Fin n) (e : Fin n × Fin n) : Prop :=
  e.1 = i ∨ e.1 = j ∨ e.2 = i ∨ e.2 = j

/-- **Local preservation criterion.** A `pairResolve` move preserves the unit-step
invariant on the whole edge list if every edge touching the resolved pair remains
unit-step after the move. Disjoint edges are unchanged by `pairResolve_other`, so the
old unit-step invariant carries them automatically.

This is the exact condition the runtime must audit, or a later theorem must prove, before
applying the Phase-56 cost law to an actively updated field. -/
theorem pairResolve_unitStep_of_local {n : ℕ} (x : Fin n → ℝ) (E : List (Fin n × Fin n))
    (i j : Fin n) (hunit : UnitStepReal x E)
    (hlocal : ∀ e ∈ E, EdgeTouches i j e →
      |pairResolve x i j e.1 - pairResolve x i j e.2| ≤ 1) :
    UnitStepReal (pairResolve x i j) E := by
  intro e he
  by_cases ht : EdgeTouches i j e
  · exact hlocal e he ht
  · have h1i : e.1 ≠ i := by
      intro h; exact ht (Or.inl h)
    have h1j : e.1 ≠ j := by
      intro h; exact ht (Or.inr (Or.inl h))
    have h2i : e.2 ≠ i := by
      intro h; exact ht (Or.inr (Or.inr (Or.inl h)))
    have h2j : e.2 ≠ j := by
      intro h; exact ht (Or.inr (Or.inr (Or.inr h)))
    rw [pairResolve_other x h1i h1j, pairResolve_other x h2i h2j]
    exact hunit e he

/-! ## §2. The global preservation claim is false -/

def f0 : Fin 3 := ⟨0, by decide⟩
def f1 : Fin 3 := ⟨1, by decide⟩
def f2 : Fin 3 := ⟨2, by decide⟩

/-- The three-site chain `0 -- 1 -- 2`. -/
def chain3Edges : List (Fin 3 × Fin 3) := [(f0, f1), (f1, f2)]

/-- The initial levels `0, 1, 2`, written by cases over `Fin 3`. -/
def chain3Levels : Fin 3 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2

@[simp] lemma chain3Levels_f0 : chain3Levels f0 = 0 := rfl
@[simp] lemma chain3Levels_f1 : chain3Levels f1 = 1 := rfl
@[simp] lemma chain3Levels_f2 : chain3Levels f2 = 2 := rfl

/-- The chain `0,1,2` is unit-step before any resolution. -/
theorem chain3_unitStep : UnitStepReal chain3Levels chain3Edges := by
  intro e he
  simp [chain3Edges] at he
  rcases he with rfl | he
  · norm_num
  · rcases he with rfl
    norm_num

/-- After resolving the first edge `(0,1)`, the second edge `(1,2)` has gap `3/2`. -/
lemma chain3_resolved_second_gap :
    |pairResolve chain3Levels f0 f1 f1 - pairResolve chain3Levels f0 f1 f2| = (3 / 2 : ℝ) := by
  have hf2_ne_f0 : f2 ≠ f0 := by decide
  have hf2_ne_f1 : f2 ≠ f1 := by decide
  rw [pairResolve_at_j, pairResolve_other chain3Levels hf2_ne_f0 hf2_ne_f1]
  norm_num

/-- **Counterexample.** A unit-step field need not remain unit-step after a mean-move
resolution. The three-site chain `0 -- 1 -- 2` starts with gaps `1` and `1`; resolving
the first edge gives levels `1/2, 1/2, 2`, so the second edge has gap `3/2 > 1`.

This blocks the false global theorem "mean-move preserves UnitStep". The correct theorem
is the local criterion `pairResolve_unitStep_of_local` above. -/
theorem chain3_pairResolve_breaks_unitStep :
    ¬ UnitStepReal (pairResolve chain3Levels f0 f1) chain3Edges := by
  intro h
  have hedge : (f1, f2) ∈ chain3Edges := by
    simp [chain3Edges]
  have hstep := h (f1, f2) hedge
  rw [chain3_resolved_second_gap] at hstep
  norm_num at hstep

/-- Phase-58 headline: active mean-move dynamics does not preserve unit-step globally;
it preserves it exactly under the local post-move edge condition, and the 3-chain
counterexample shows that condition is necessary rather than cosmetic. -/
theorem t58_unitStep_preservation_honest :
    (∀ {n : ℕ} (x : Fin n → ℝ) (E : List (Fin n × Fin n)) (i j : Fin n),
        UnitStepReal x E →
        (∀ e ∈ E, EdgeTouches i j e →
          |pairResolve x i j e.1 - pairResolve x i j e.2| ≤ 1) →
        UnitStepReal (pairResolve x i j) E)
    ∧ ¬ UnitStepReal (pairResolve chain3Levels f0 f1) chain3Edges :=
  ⟨fun {n} x E i j hunit hlocal =>
    pairResolve_unitStep_of_local (n := n) x E i j hunit hlocal,
   chain3_pairResolve_breaks_unitStep⟩

end RecognitionUnitStepPreservation
end Cosmology
end IndisputableMonolith
