import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Foundation.PerfectRecognition
import IndisputableMonolith.Foundation.PublicSpine.BooleanCompletePass
import IndisputableMonolith.LedgerPostingAdjacency

/-!
# BooleanCompletePassNecessity — Lane C hard-half binder (WALL / COND)

Campaign: `plans/PartI_Hard_Half_Closure_Plan_20260723.html`, Lane C.

Already THEOREM under Boolean surjection: `cubePeriodEight_holds`,
`complete_pass_lower_bound`, Gray-8 sharpness (`BooleanCompletePass`).

Hard half asks for a Recognition-native complete-pass predicate that
*implies* surjection without defining completeness as surjection.

## Attempted content

* `ParityClassCoverage`: every D-bit parity class appears as an observation.
  Extensionally equivalent to `Function.Surjective` (packaging risk).
* Atomic ledger posting: `PostingStep` ⇒ one-bit parity change (already
  THEOREM in `LedgerPostingAdjacency`; retained as Recognition dynamics).
* Incomplete countermodel: a period-2 two-vertex walk is not coverage, so
  Anil's incomplete dynamics correctly fail the bound's hypothesis.

## Verdict: WALL on non-packaging discharge

`ParityClassCoverage` forces surjection and the eight-tick bound, but is
packaging-equivalent to surjection. `RecognitionClockIdentificationOpen`
therefore stays uninhabited: inhabiting it with coverage/`Surjective` is
explicitly banned by that declaration's contract. The COND reading is:
*if* Recognition completeness is identified with parity-class coverage, then
the clock bound is THEOREM; that identification is the residual.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open Patterns
open PerfectRecognition
open LedgerPostingAdjacency

/-- Attempted Recognition-native completeness: every parity class of the
D-dimensional ledger has been observed in the pass.

Intension: full distinction coverage. Extension: equivalent to surjection
(packaging; see `parityClassCoverage_iff_surjective`). -/
def ParityClassCoverage {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  ∀ p : Pattern d, ∃ t : Fin T, pass t = p

theorem parityClassCoverage_iff_surjective {d T : ℕ}
    (pass : Fin T → Pattern d) :
    ParityClassCoverage pass ↔ Function.Surjective pass := by
  constructor
  · intro h p
    exact h p
  · intro h p
    exact h p

theorem parityClassCoverage_implies_surjective {d T : ℕ}
    {pass : Fin T → Pattern d} (h : ParityClassCoverage pass) :
    Function.Surjective pass :=
  (parityClassCoverage_iff_surjective pass).mp h

/-- Coverage ⇒ period ≥ `2^D` (compose with the already-proved bound). -/
theorem coverage_forces_period_bound {d T : ℕ}
    (pass : Fin T → Pattern d) (h : ParityClassCoverage pass) :
    2 ^ d ≤ T :=
  complete_pass_lower_bound pass (parityClassCoverage_implies_surjective h)

/-- At D=3, coverage + periodicity ⇒ period ≥ 8. -/
theorem coverage_periodic_forces_eight
    (walk : ℕ → Pattern 3) (p : ℕ) (hp : 0 < p)
    (hper : ∀ n, walk (n + p) = walk n)
    (hcov : ParityClassCoverage (fun t : Fin p => walk t.val)) :
    8 ≤ p := by
  have hsurj : Function.Surjective (fun t : Fin p => walk t.val) :=
    parityClassCoverage_implies_surjective hcov
  -- Lift Fin-surjection to ℕ-surjection on a periodic walk.
  have hsurjN : Function.Surjective walk := by
    intro x
    obtain ⟨t, ht⟩ := hsurj x
    exact ⟨t.val, ht⟩
  exact cubePeriodEightLocal_holds walk p hp hper hsurjN

/-- Atomic posting dynamics: a ledger step changes parity in exactly one bit. -/
theorem atomic_posting_one_bit {d : ℕ} {L L' : LedgerState d}
    (h : PostingStep (d := d) L L') :
    OneBitDiff (parity d L) (parity d L') :=
  postingStep_oneBitDiff h

/-- Incomplete countermodel (Anil): a period-2 alternation of two distinct
patterns is not parity-class coverage for D=3, hence does not trigger the
eight-tick bound. -/
theorem incomplete_period_two_not_coverage :
    ∃ (walk : ℕ → Pattern 3) (p : ℕ),
      0 < p ∧ p < 8 ∧
        (∀ n, walk (n + p) = walk n) ∧
        ¬ ParityClassCoverage (fun t : Fin p => walk t.val) := by
  let a : Pattern 3 := fun _ => false
  let b : Pattern 3 := fun i => decide (i.val = 0)
  let walk : ℕ → Pattern 3 := fun n => if n % 2 = 0 then a else b
  refine ⟨walk, 2, by norm_num, by norm_num, ?_, ?_⟩
  · intro n
    have : (n + 2) % 2 = n % 2 := Nat.add_mod_right n 2
    -- (n+2)%2 = n%2 is true; Nat.add_mod_right says (n+2)%2 = n%2 when 2∣2
    simp only [walk]
    rw [show (n + 2) % 2 = n % 2 by omega]
  · intro hcov
    let c : Pattern 3 := fun i => decide (i.val = 1)
    obtain ⟨t, ht⟩ := hcov c
    have htb : t.val < 2 := t.isLt
    have hcases : t.val = 0 ∨ t.val = 1 := by omega
    have honly : walk t.val = a ∨ walk t.val = b := by
      rcases hcases with h0 | h1
      · left; simp [walk, h0, a]
      · right; simp [walk, h1, b]
    have hc_ne_a : c ≠ a := by
      intro hca
      have := congrFun hca ⟨1, by decide⟩
      simp [c, a] at this
    have hc_ne_b : c ≠ b := by
      intro hcb
      have := congrFun hcb ⟨1, by decide⟩
      simp [c, b] at this
    rcases honly with hwa | hwb
    · exact hc_ne_a (ht.symm.trans hwa)
    · exact hc_ne_b (ht.symm.trans hwb)

/-- Gray is a sharpness witness, not a hypothesis of the coverage bound. -/
theorem gray_not_hypothesis_of_coverage_bound :
    (∀ {d T : ℕ} (pass : Fin T → Pattern d),
      ParityClassCoverage pass → 2 ^ d ≤ T) ∧
      Nonempty (GrayCycle 3) :=
  ⟨fun {_ _} pass h => coverage_forces_period_bound pass h, ⟨grayCycle3⟩⟩

/-! ## WALL binder -/

/-- Lane C WALL / COND binder: coverage ⇒ eight-tick math is THEOREM;
coverage ↔ surjection packaging; incomplete countermodel; atomic one-bit;
Gray not in hyp. Does not inhabit `RecognitionClockIdentificationOpen`. -/
structure BooleanCompletePassNecessity : Prop where
  coverage_iff_surj :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      ParityClassCoverage pass ↔ Function.Surjective pass
  coverage_period :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      ParityClassCoverage pass → 2 ^ d ≤ T
  incomplete_countermodel :
    ∃ (walk : ℕ → Pattern 3) (p : ℕ),
      0 < p ∧ p < 8 ∧
        (∀ n, walk (n + p) = walk n) ∧
        ¬ ParityClassCoverage (fun t : Fin p => walk t.val)
  atomic_one_bit :
    ∀ {d : ℕ} {L L' : LedgerState d},
      PostingStep (d := d) L L' → OneBitDiff (parity d L) (parity d L')
  gray_witness_only :
    (∀ {d T : ℕ} (pass : Fin T → Pattern d),
      ParityClassCoverage pass → 2 ^ d ≤ T) ∧
      Nonempty (GrayCycle 3)
  /-- Packaging wall: coverage is equivalent to surjection. -/
  packaging_wall :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      ParityClassCoverage pass ↔ Function.Surjective pass

theorem booleanCompletePassNecessity_holds : BooleanCompletePassNecessity where
  coverage_iff_surj := fun pass => parityClassCoverage_iff_surjective pass
  coverage_period := fun pass h => coverage_forces_period_bound pass h
  incomplete_countermodel := incomplete_period_two_not_coverage
  atomic_one_bit := fun h => atomic_posting_one_bit h
  gray_witness_only := gray_not_hypothesis_of_coverage_bound
  packaging_wall := fun pass => parityClassCoverage_iff_surjective pass

/-- OPEN: a Recognition-native `P` that forces surjection, admits the
incomplete period-2 countermodel when dropped, and is **not**
packaging-equivalent to `Function.Surjective` / `ParityClassCoverage`.

No `*_holds` theorem. -/
def BooleanCompletePassNecessityOpen : Prop :=
  ∃ (P : ∀ {d T : ℕ}, (Fin T → Pattern d) → Prop),
    (∀ {d T : ℕ} (pass : Fin T → Pattern d), P pass → Function.Surjective pass) ∧
      (∃ (walk : ℕ → Pattern 3) (p : ℕ),
        0 < p ∧
          (∀ n, walk (n + p) = walk n) ∧
          ¬ P (fun t : Fin p => walk t.val)) ∧
      (∀ {d T : ℕ} (pass : Fin T → Pattern d),
        ¬ (P pass ↔ Function.Surjective pass)) ∧
      (∀ {d T : ℕ} (pass : Fin T → Pattern d),
        ¬ (P pass ↔ ParityClassCoverage pass))

end PublicSpine
end Foundation
end IndisputableMonolith
