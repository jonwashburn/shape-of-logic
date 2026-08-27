import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Foundation.PerfectRecognition
import IndisputableMonolith.Foundation.PublicSpine.BooleanCompletePass
import IndisputableMonolith.Foundation.PublicSpine.BooleanCompletePassNecessity
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection
import IndisputableMonolith.LedgerPostingAdjacency

/-!
# ClockDischargeProbe — Lane C deep discovery (Probe C)

Goal: derive Boolean complete-pass / eight-tick clock from a Recognition-native
completeness predicate `P` that **implies** `Function.Surjective` on
`Pattern D` without defining completeness as surjection/coverage
(`RecognitionClockIdentificationOpen`).

Prior wall (`BooleanCompletePassNecessity`): `ParityClassCoverage` ↔ `Surjective`.
This module stress-tests separation and closed one-bit candidates.

## Verdict

**GENUINE-OPEN** on non-packaging discharge. See `clockDischargeProbeCert_holds`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace ClockDischargeProbe

open Patterns
open PerfectRecognition
open PrimitiveRecognitionCalculus.QuotientSelection
open LedgerPostingAdjacency

noncomputable section
open Classical

/-! ## Candidate completeness predicates -/

/-- Bit-resolution: every parity coordinate observed in both polarities. -/
def PassBitResolving {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  ∀ i : Fin d, (∃ t : Fin T, pass t i = false) ∧ (∃ t : Fin T, pass t i = true)

/-- Appearance observable at tick `t`. -/
def appearanceObs {d T : ℕ} (pass : Fin T → Pattern d) (t : Fin T) :
    Pattern d → Bool :=
  fun x => if x = pass t then true else false

def appearanceFamily {d T : ℕ} (pass : Fin T → Pattern d) :
    Set (Pattern d → Bool) :=
  Set.range (appearanceObs pass)

/-- Separation completeness: appearance observables separate `Pattern d`. -/
def PassAppearanceSeparating {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  PostedPerfect (appearanceFamily pass)

/-- Nyquist-injective completeness: period `2^d` and injective. -/
def PassNyquistInjective {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  T = 2 ^ d ∧ Function.Injective pass

/-- GrayCover-shaped predicate (surjection conjunct + one-bit). -/
def PassGrayCover {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d) : Prop :=
  Function.Surjective pass ∧
    ∀ i : Fin T, OneBitDiff (pass i) (pass (i + 1))

/-! ## Route 1a — appearance `PostedPerfect` (independent, too weak) -/

theorem unobserved_appearance_equiv {d T : ℕ}
    (pass : Fin T → Pattern d) {p q : Pattern d}
    (hp : ∀ t : Fin T, pass t ≠ p) (hq : ∀ t : Fin T, pass t ≠ q) :
    ObsEquiv (appearanceFamily pass) p q := by
  intro f hf
  rcases hf with ⟨t, rfl⟩
  have hp' : p ≠ pass t := (hp t).symm
  have hq' : q ≠ pass t := (hq t).symm
  simp only [appearanceObs, if_neg hp', if_neg hq']

theorem appearanceSeparating_at_most_one_missing {d T : ℕ}
    {pass : Fin T → Pattern d} (h : PassAppearanceSeparating pass) :
    ∀ p q : Pattern d,
      (∀ t : Fin T, pass t ≠ p) →
      (∀ t : Fin T, pass t ≠ q) → p = q := by
  intro p q hp hq
  exact h p q (unobserved_appearance_equiv pass hp hq)

def constFalse1 : Pattern 1 := fun _ => false
def constTrue1 : Pattern 1 := fun _ => true
def singleFalsePass : Fin 1 → Pattern 1 := fun _ => constFalse1

private lemma pattern1_dichotomy (p : Pattern 1) :
    p = constFalse1 ∨ p = constTrue1 := by
  cases h : p ⟨0, by decide⟩
  · left; funext i; fin_cases i; exact h
  · right; funext i; fin_cases i; exact h

private lemma constFalse1_ne_constTrue1 : constFalse1 ≠ constTrue1 := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  simp [constFalse1, constTrue1] at this

theorem singleFalsePass_appearanceSeparating :
    PassAppearanceSeparating singleFalsePass := by
  intro x y hxy
  have hx := hxy (appearanceObs singleFalsePass 0) ⟨0, rfl⟩
  simp only [appearanceObs, singleFalsePass] at hx
  by_cases hxF : x = constFalse1
  · by_cases hyF : y = constFalse1
    · exact hxF.trans hyF.symm
    · rw [if_pos hxF, if_neg hyF] at hx
      cases hx
  · by_cases hyF : y = constFalse1
    · rw [if_neg hxF, if_pos hyF] at hx
      cases hx
    · have hxT : x = constTrue1 := (pattern1_dichotomy x).resolve_left hxF
      have hyT : y = constTrue1 := (pattern1_dichotomy y).resolve_left hyF
      exact hxT.trans hyT.symm

theorem singleFalsePass_not_surjective :
    ¬ Function.Surjective singleFalsePass := by
  intro h
  obtain ⟨t, ht⟩ := h constTrue1
  have : constFalse1 = constTrue1 := by simpa [singleFalsePass] using ht
  have hbit := congrFun this ⟨0, by decide⟩
  simp [constFalse1, constTrue1] at hbit

theorem appearanceSeparating_not_force_surjective :
    ∃ (d T : ℕ) (pass : Fin T → Pattern d),
      PassAppearanceSeparating pass ∧ ¬ Function.Surjective pass :=
  ⟨1, 1, singleFalsePass,
    singleFalsePass_appearanceSeparating, singleFalsePass_not_surjective⟩

/-! ## Route 1b — bit-resolution (independent, too weak) -/

def bitResolvePass : Fin 2 → Pattern 3
  | ⟨0, _⟩ => fun _ => false
  | ⟨1, _⟩ => fun _ => true

theorem bitResolvePass_resolving : PassBitResolving bitResolvePass := by
  intro i
  exact ⟨⟨0, by simp [bitResolvePass]⟩, ⟨1, by simp [bitResolvePass]⟩⟩

theorem bitResolvePass_not_surjective :
    ¬ Function.Surjective bitResolvePass := by
  intro h
  let mid : Pattern 3 := fun j => decide (j.val = 0)
  obtain ⟨t, ht⟩ := h mid
  fin_cases t
  · have := congrFun ht ⟨0, by decide⟩; simp [bitResolvePass, mid] at this
  · have := congrFun ht ⟨1, by decide⟩; simp [bitResolvePass, mid] at this

theorem bitResolving_not_force_surjective :
    ∃ (d T : ℕ) (pass : Fin T → Pattern d),
      PassBitResolving pass ∧ ¬ Function.Surjective pass :=
  ⟨3, 2, bitResolvePass, bitResolvePass_resolving, bitResolvePass_not_surjective⟩

/-! ## Route 1c — Nyquist injectivity ⇒ surjection (packaging at threshold) -/

theorem nyquist_injective_surjective {d : ℕ}
    (pass : Fin (2 ^ d) → Pattern d) (hinj : Function.Injective pass) :
    Function.Surjective pass := by
  have hcard : Fintype.card (Pattern d) = Fintype.card (Fin (2 ^ d)) := by
    simp [card_pattern d, Fintype.card_fin]
  exact ((Fintype.bijective_iff_injective_and_card pass).2 ⟨hinj, hcard.symm⟩).2

theorem passNyquistInjective_surjective {d T : ℕ}
    {pass : Fin T → Pattern d} (h : PassNyquistInjective pass) :
    Function.Surjective pass := by
  rcases h with ⟨hT, hinj⟩
  subst hT
  exact nyquist_injective_surjective pass hinj

theorem nyquist_injective_iff_surjective {d : ℕ}
    (pass : Fin (2 ^ d) → Pattern d) :
    Function.Injective pass ↔ Function.Surjective pass := by
  constructor
  · exact nyquist_injective_surjective pass
  · intro hsurj
    have hcard : Fintype.card (Fin (2 ^ d)) = Fintype.card (Pattern d) := by
      simp [card_pattern d, Fintype.card_fin]
    exact ((Fintype.bijective_iff_surjective_and_card pass).2 ⟨hsurj, hcard⟩).1

theorem passNyquistInjective_packaging_at_threshold {d : ℕ}
    (pass : Fin (2 ^ d) → Pattern d) :
    PassNyquistInjective pass ↔ Function.Surjective pass := by
  constructor
  · exact passNyquistInjective_surjective
  · intro hsurj
    exact ⟨rfl, (nyquist_injective_iff_surjective pass).2 hsurj⟩

/-! ## Route 2 — closed one-bit bounce (too weak) -/

def bounceA : Pattern 3 := fun _ => false
def bounceB : Pattern 3 := fun j => decide (j.val = 0)
def bouncePass : Fin 2 → Pattern 3
  | ⟨0, _⟩ => bounceA
  | ⟨1, _⟩ => bounceB

theorem bouncePass_oneBit :
    ∀ i : Fin 2, OneBitDiff (bouncePass i) (bouncePass (i + 1)) := by
  intro i
  fin_cases i
  · -- A → B: differ only at bit 0
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [bouncePass, bounceA, bounceB]
    · intro k hk
      fin_cases k
      · rfl
      · simp [bouncePass, bounceA, bounceB] at hk
      · simp [bouncePass, bounceA, bounceB] at hk
  · -- B → A (wrap): same
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [bouncePass, bounceA, bounceB]
    · intro k hk
      fin_cases k
      · rfl
      · simp [bouncePass, bounceA, bounceB] at hk
      · simp [bouncePass, bounceA, bounceB] at hk

theorem bouncePass_not_surjective :
    ¬ Function.Surjective bouncePass := by
  intro h
  let c : Pattern 3 := fun j => decide (j.val = 1)
  obtain ⟨t, ht⟩ := h c
  fin_cases t
  · have := congrFun ht ⟨1, by decide⟩; simp [bouncePass, bounceA, c] at this
  · have := congrFun ht ⟨0, by decide⟩; simp [bouncePass, bounceB, c] at this

theorem closed_oneBit_not_force_surjective :
    ∃ (pass : Fin 2 → Pattern 3),
      (∀ i : Fin 2, OneBitDiff (pass i) (pass (i + 1))) ∧
        ¬ Function.Surjective pass :=
  ⟨bouncePass, bouncePass_oneBit, bouncePass_not_surjective⟩

/-! ## Route 3 — GrayCover smuggles surjection -/

theorem passGrayCover_implies_surjective {d T : ℕ} [NeZero T]
    {pass : Fin T → Pattern d} (h : PassGrayCover pass) :
    Function.Surjective pass :=
  h.1

/-- Concrete Hamming-distance-2 pair. -/
def pat00 : Pattern 2 := fun _ => false
def pat11 : Pattern 2 := fun _ => true

theorem pat00_pat11_not_oneBit : ¬ OneBitDiff pat00 pat11 := by
  intro h
  rcases h with ⟨k, _, huniq⟩
  have hd0 : pat00 ⟨0, by decide⟩ ≠ pat11 ⟨0, by decide⟩ := by
    simp [pat00, pat11]
  have hd1 : pat00 ⟨1, by decide⟩ ≠ pat11 ⟨1, by decide⟩ := by
    simp [pat00, pat11]
  exact Nat.noConfusion (congrArg Fin.val ((huniq _ hd0).trans (huniq _ hd1).symm))

/-- Surjective pass with an explicit two-bit step `00 → 11`. -/
def jumpCover : Fin 4 → Pattern 2
  | ⟨0, _⟩ => pat00
  | ⟨1, _⟩ => pat11
  | ⟨2, _⟩ => fun j => decide (j.val = 0)
  | ⟨3, _⟩ => fun j => decide (j.val = 1)

theorem jumpCover_surjective : Function.Surjective jumpCover := by
  intro p
  cases h0 : p ⟨0, by decide⟩ <;> cases h1 : p ⟨1, by decide⟩
  · refine ⟨0, funext fun j => ?_⟩
    fin_cases j
    · simpa [jumpCover, pat00] using h0.symm
    · simpa [jumpCover, pat00] using h1.symm
  · refine ⟨3, funext fun j => ?_⟩
    fin_cases j
    · simpa [jumpCover] using h0.symm
    · simpa [jumpCover] using h1.symm
  · refine ⟨2, funext fun j => ?_⟩
    fin_cases j
    · simpa [jumpCover] using h0.symm
    · simpa [jumpCover] using h1.symm
  · refine ⟨1, funext fun j => ?_⟩
    fin_cases j
    · simpa [jumpCover, pat11] using h0.symm
    · simpa [jumpCover, pat11] using h1.symm

theorem jumpCover_not_grayCover : ¬ PassGrayCover jumpCover := by
  intro hG
  have hstep := hG.2 (0 : Fin 4)
  have hnot : ¬ OneBitDiff (jumpCover 0) (jumpCover 1) := by
    simpa [jumpCover] using pat00_pat11_not_oneBit
  exact hnot hstep

theorem passGrayCover_not_iff_surjective :
    ∃ (d T : ℕ) (_ : NeZero T) (pass : Fin T → Pattern d),
      Function.Surjective pass ∧ ¬ PassGrayCover (d := d) (T := T) pass :=
  ⟨2, 4, ⟨by decide⟩, jumpCover, jumpCover_surjective, jumpCover_not_grayCover⟩

/-! ## Route 4 — coverage packaging re-export -/

theorem coverage_is_packaging {d T : ℕ} (pass : Fin T → Pattern d) :
    ParityClassCoverage pass ↔ Function.Surjective pass :=
  parityClassCoverage_iff_surjective pass

/-! ## Route 5 — literal NecessityOpen is unsatisfiable -/

theorem necessityOpen_literal_unsat :
    ¬ BooleanCompletePassNecessityOpen := by
  rintro ⟨P, hPsurj, _, hNotIff, _⟩
  obtain ⟨walk, p, _, _, _, hnotCov⟩ := incomplete_period_two_not_coverage
  let pass : Fin p → Pattern 3 := fun t => walk t.val
  have hnotSurj : ¬ Function.Surjective pass := by
    intro hsurj
    exact hnotCov ((parityClassCoverage_iff_surjective pass).2 hsurj)
  have hnotP : ¬ P pass := fun hP => hnotSurj (hPsurj pass hP)
  have hIff : P pass ↔ Function.Surjective pass :=
    ⟨fun hP => absurd hP hnotP, fun hS => absurd hS hnotSurj⟩
  exact hNotIff pass hIff

/-! ## Atomic posting -/

theorem atomic_posting_one_bit {d : ℕ} {L L' : LedgerState d}
    (h : PostingStep (d := d) L L') :
    OneBitDiff (parity d L) (parity d L') :=
  postingStep_oneBitDiff h

/-! ## Probe binder -/

structure ClockDischargeProbeCert : Prop where
  appearance_gap :
    ∃ (d T : ℕ) (pass : Fin T → Pattern d),
      PassAppearanceSeparating pass ∧ ¬ Function.Surjective pass
  bit_resolve_gap :
    ∃ (d T : ℕ) (pass : Fin T → Pattern d),
      PassBitResolving pass ∧ ¬ Function.Surjective pass
  nyquist_inj_surj :
    ∀ {d : ℕ} (pass : Fin (2 ^ d) → Pattern d),
      Function.Injective pass → Function.Surjective pass
  nyquist_packaging :
    ∀ {d : ℕ} (pass : Fin (2 ^ d) → Pattern d),
      PassNyquistInjective pass ↔ Function.Surjective pass
  closed_oneBit_gap :
    ∃ (pass : Fin 2 → Pattern 3),
      (∀ i : Fin 2, OneBitDiff (pass i) (pass (i + 1))) ∧
        ¬ Function.Surjective pass
  gray_smuggles_surj :
    ∀ {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d),
      PassGrayCover pass → Function.Surjective pass
  gray_strictly_stronger :
    ∃ (d T : ℕ) (_ : NeZero T) (pass : Fin T → Pattern d),
      Function.Surjective pass ∧ ¬ PassGrayCover (d := d) (T := T) pass
  coverage_packaging :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      ParityClassCoverage pass ↔ Function.Surjective pass
  necessityOpen_literal_unsat : ¬ BooleanCompletePassNecessityOpen
  atomic_one_bit :
    ∀ {d : ℕ} {L L' : LedgerState d},
      PostingStep (d := d) L L' → OneBitDiff (parity d L) (parity d L')

theorem clockDischargeProbeCert_holds : ClockDischargeProbeCert where
  appearance_gap := appearanceSeparating_not_force_surjective
  bit_resolve_gap := bitResolving_not_force_surjective
  nyquist_inj_surj := fun pass h => nyquist_injective_surjective pass h
  nyquist_packaging := fun pass => passNyquistInjective_packaging_at_threshold pass
  closed_oneBit_gap := closed_oneBit_not_force_surjective
  gray_smuggles_surj := fun _ h => passGrayCover_implies_surjective h
  gray_strictly_stronger := passGrayCover_not_iff_surjective
  coverage_packaging := fun pass => coverage_is_packaging pass
  necessityOpen_literal_unsat := necessityOpen_literal_unsat
  atomic_one_bit := fun h => atomic_posting_one_bit h

/-- Stronger packaging-test shape: global failure of extensional equivalence.
This repairs the literal inconsistency above, but remains underconstrained:
`P := False` can inhabit it. The semantic clock residual also requires a
Recognition-native predicate that accepts Gray-8. -/
def BooleanCompletePassNecessityOpenCorrected : Prop :=
  ∃ (P : ∀ {d T : ℕ}, (Fin T → Pattern d) → Prop),
    (∀ {d T : ℕ} (pass : Fin T → Pattern d), P pass → Function.Surjective pass) ∧
      (∃ (walk : ℕ → Pattern 3) (p : ℕ),
        0 < p ∧
          (∀ n, walk (n + p) = walk n) ∧
          ¬ P (fun t : Fin p => walk t.val)) ∧
      ¬ (∀ {d T : ℕ} (pass : Fin T → Pattern d),
            P pass ↔ Function.Surjective pass) ∧
      ¬ (∀ {d T : ℕ} (pass : Fin T → Pattern d),
            P pass ↔ ParityClassCoverage pass)

/-- Historical formal residual shape. The semantic residual is stricter than
this proposition; see `ContextualReciprocityComplete.ClockPhase2Wall`. -/
def ClockDischargeResidualOpen : Prop :=
  BooleanCompletePassNecessityOpenCorrected

end
end ClockDischargeProbe
end PublicSpine
end Foundation
end IndisputableMonolith
