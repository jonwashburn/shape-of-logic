import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Cost.Jlog
import IndisputableMonolith.LedgerParityAdjacency

/-!
# Posting-style ledger updates ⇒ parity one-bit adjacency

This file upgrades Workstream B from a “vector lemma” to an explicit **ledger-shaped**
model: a ledger state consists of `(debit, credit)` and a tick posts exactly one unit
to exactly one account (either as debit or credit).

Key theorem (THEOREM level):
- A single post changes `phi = debit-credit` by ±1 at exactly one coordinate, hence the
  induced parity pattern changes in exactly one bit.

Claim hygiene:
- This is still a mathematical model. It is the missing glue between “ledger” language
  and the parity/Gray adjacency lemma in `LedgerParityAdjacency.lean`.
- Deriving why *nature* must use this posting model is a separate MECH/AXIOM/bridge step.
-/

namespace IndisputableMonolith
namespace LedgerPostingAdjacency

open IndisputableMonolith.Recognition
open IndisputableMonolith.Patterns
open IndisputableMonolith.LedgerParityAdjacency
open IndisputableMonolith.Cost
open scoped BigOperators

/-! ## A minimal recognition carrier: accounts = `Fin d` -/

/-- Minimal carrier for a d-account ledger. The recognition relation is irrelevant here. -/
def AccountRS (d : Nat) : RecognitionStructure :=
  { U := Fin d, R := fun _ _ => True }

/-!
### AtomicTick availability (Workstream B tightening)

For the concrete carrier `Fin d` (with `d ≠ 0`), we can construct an `AtomicTick` instance
directly: at tick `t`, the posted account is the canonical `Fin d` coercion of `t`.

Claim hygiene: this is a *model existence* theorem (THEOREM-level within Lean), not an empirical
claim about nature’s tick scheduling.
-/

noncomputable instance accountRS_atomicTick (d : Nat) [NeZero d] : Recognition.AtomicTick (AccountRS d) :=
{ postedAt := fun t u =>
    u = ⟨t % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩
  unique_post := by
    intro t
    refine ⟨⟨t % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩, rfl, ?_⟩
    intro u hu
    simpa [hu]
}

abbrev LedgerState (d : Nat) : Type := Recognition.Ledger (AccountRS d)

abbrev phiVec {d : Nat} (L : LedgerState d) : Fin d → ℤ :=
  Recognition.phi L

abbrev parity (d : Nat) (L : LedgerState d) : Pattern d :=
  parityPattern (phiVec (d := d) L)

/-! ## Posting model -/

inductive Side where
  | debit
  | credit
deriving DecidableEq, Repr

/-- Apply a single unit post (either debit or credit) at account `k`. -/
noncomputable def post {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) : LedgerState d := by
  classical
  exact match side with
  | Side.debit =>
      { debit := fun i => if i = k then L.debit i + 1 else L.debit i
      , credit := L.credit }
  | Side.credit =>
      { debit := L.debit
      , credit := fun i => if i = k then L.credit i + 1 else L.credit i }

@[simp] lemma phiVec_post_debit {d : Nat} (L : LedgerState d) (k : Fin d) (i : Fin d) :
    phiVec (d := d) (post L k Side.debit) i =
      (if i = k then phiVec (d := d) L i + 1 else phiVec (d := d) L i) := by
  by_cases hik : i = k
  · subst hik
    simp [post, phiVec, Recognition.phi]
    ring_nf
  · simp [post, phiVec, Recognition.phi, hik]

@[simp] lemma phiVec_post_credit {d : Nat} (L : LedgerState d) (k : Fin d) (i : Fin d) :
    phiVec (d := d) (post L k Side.credit) i =
      (if i = k then phiVec (d := d) L i - 1 else phiVec (d := d) L i) := by
  by_cases hik : i = k
  · subst hik
    simp [post, phiVec, Recognition.phi]
    ring_nf
  · simp [post, phiVec, Recognition.phi, hik]

/-! ## Bridge: a post induces a coord-atomic step on `phi` -/

lemma phiVec_coordAtomicStep_of_post {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) :
    coordAtomicStep (d := d) (phiVec (d := d) L) (phiVec (d := d) (post L k side)) := by
  classical
  refine ⟨k, ?_, ?_⟩
  · cases side with
    | debit =>
        left
        -- at k, phi increases by 1
        simpa using (by
          have := (phiVec_post_debit (d := d) L k k)
          simpa using this)
    | credit =>
        right
        -- at k, phi decreases by 1
        simpa using (by
          have := (phiVec_post_credit (d := d) L k k)
          simpa using this)
  · intro i hik
    cases side with
    | debit =>
        -- other coordinates unchanged
        have := (phiVec_post_debit (d := d) L k i)
        simpa [hik] using this
    | credit =>
        have := (phiVec_post_credit (d := d) L k i)
        simpa [hik] using this

/-! ## Main theorem: posting ⇒ parity adjacency -/

theorem parity_oneBitDiff_of_post {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) :
    OneBitDiff (parity d L) (parity d (post L k side)) := by
  -- reduce to the coord-atomic step lemma and reuse `coordAtomicStep_oneBitDiff`
  have hstep := phiVec_coordAtomicStep_of_post (d := d) L k side
  simpa [parity] using (coordAtomicStep_oneBitDiff (d := d) (x := phiVec (d := d) L)
    (y := phiVec (d := d) (post L k side)) hstep)

/-! ## Posting-step relation (ledger constraint ⇒ adjacency) -/

/-- One atomic posting step between ledger states. -/
def PostingStep {d : Nat} (L L' : LedgerState d) : Prop :=
  ∃ k : Fin d, ∃ side : Side, L' = post L k side

theorem postingStep_oneBitDiff {d : Nat} {L L' : LedgerState d} (h : PostingStep (d := d) L L') :
    OneBitDiff (parity d L) (parity d L') := by
  rcases h with ⟨k, side, rfl⟩
  simpa using parity_oneBitDiff_of_post (d := d) L k side

/-! ## Optional deepening: a cost/legality predicate that implies `PostingStep` -/

/-- L1 cost of a ledger transition, measured as total absolute change in debit+credit counts. -/
noncomputable def ledgerL1Cost {d : Nat} (L L' : LedgerState d) : Nat :=
  (∑ i : Fin d, Int.natAbs (L'.debit i - L.debit i)) +
  (∑ i : Fin d, Int.natAbs (L'.credit i - L.credit i))

/-- Monotone-posting constraint: debit/credit counts never decrease. -/
def MonotoneLedger {d : Nat} (L L' : LedgerState d) : Prop :=
  (∀ i : Fin d, L.debit i ≤ L'.debit i) ∧ (∀ i : Fin d, L.credit i ≤ L'.credit i)

/-- A small “legality” predicate: monotone ledger counts + unit L1 step. -/
def LegalAtomicTick {d : Nat} (L L' : LedgerState d) : Prop :=
  MonotoneLedger (d := d) L L' ∧ ledgerL1Cost (d := d) L L' = 1

/-! ## Optional deepening: Jlog-cost version (closer to RS cost than L1) -/

/-- A Jlog-based step cost over integer ledger deltas (cast to ℝ). -/
noncomputable def ledgerJlogCost {d : Nat} (L L' : LedgerState d) : ℝ :=
  (∑ i : Fin d, Cost.Jlog ((L'.debit i - L.debit i : ℤ) : ℝ)) +
  (∑ i : Fin d, Cost.Jlog ((L'.credit i - L.credit i : ℤ) : ℝ))

theorem ledgerJlogCost_nonneg {d : Nat} (L L' : LedgerState d) : 0 ≤ ledgerJlogCost (d := d) L L' := by
  classical
  have h₁ : 0 ≤ ∑ i : Fin d, Cost.Jlog ((L'.debit i - L.debit i : ℤ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Cost.Jlog_nonneg _)
  have h₂ : 0 ≤ ∑ i : Fin d, Cost.Jlog ((L'.credit i - L.credit i : ℤ) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Cost.Jlog_nonneg _)
  -- unfold once; avoid `simp` expanding `Jlog` into exponentials.
  dsimp [ledgerJlogCost]
  exact add_nonneg h₁ h₂

private lemma ledgerJlogCost_post {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) :
    ledgerJlogCost (d := d) L (post L k side) = Cost.Jlog (1 : ℝ) := by
  classical
  cases side with
  | debit =>
      -- debit has one +1 delta at k; credit deltas are 0
      have hdeb :
          (∑ i : Fin d, Cost.Jlog (((post L k Side.debit).debit i - L.debit i : ℤ) : ℝ))
            = Cost.Jlog (1 : ℝ) := by
        let f : Fin d → ℝ := fun i => Cost.Jlog (((post L k Side.debit).debit i - L.debit i : ℤ) : ℝ)
        have hsplit :=
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := f) (a := k) (by simp))
        have fk : f k = Cost.Jlog (1 : ℝ) := by
          simp [f, post]
        have hErase : Finset.sum (Finset.univ.erase k : Finset (Fin d)) f = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hik : i ≠ k := by simpa [Finset.mem_erase] using hi
          simp [f, post, hik]
        -- `sum univ = f k + sum (erase k)`
        calc
          (∑ i : Fin d, f i) =
              f k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) f := by
            simpa using hsplit.symm
          _ = Cost.Jlog (1 : ℝ) := by simp [fk, hErase]
      have hcred :
          (∑ i : Fin d, Cost.Jlog (((post L k Side.debit).credit i - L.credit i : ℤ) : ℝ)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        simp [post]
      -- avoid `simp` unfolding `Jlog` into exp-sums (it introduces `-↑d` terms).
      simp only [ledgerJlogCost, hdeb, hcred, add_zero, zero_add]
  | credit =>
      have hdeb :
          (∑ i : Fin d, Cost.Jlog (((post L k Side.credit).debit i - L.debit i : ℤ) : ℝ)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        simp [post]
      have hcred :
          (∑ i : Fin d, Cost.Jlog (((post L k Side.credit).credit i - L.credit i : ℤ) : ℝ))
            = Cost.Jlog (1 : ℝ) := by
        let f : Fin d → ℝ := fun i => Cost.Jlog (((post L k Side.credit).credit i - L.credit i : ℤ) : ℝ)
        have hsplit :=
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := f) (a := k) (by simp))
        have fk : f k = Cost.Jlog (1 : ℝ) := by
          simp [f, post]
        have hErase : Finset.sum (Finset.univ.erase k : Finset (Fin d)) f = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hik : i ≠ k := by simpa [Finset.mem_erase] using hi
          simp [f, post, hik]
        calc
          (∑ i : Fin d, f i) =
              f k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) f := by
            simpa using hsplit.symm
          _ = Cost.Jlog (1 : ℝ) := by simp [fk, hErase]
      simp only [ledgerJlogCost, hdeb, hcred, add_zero, zero_add]

/-! ### Jlog-cost tightening: if a monotone nontrivial tick has Jlog-cost ≤ Jlog(1), it is a posting step. -/

private lemma intCast_ne_zero_of_ne_zero {z : ℤ} (hz : z ≠ 0) : ((z : ℤ) : ℝ) ≠ 0 := by
  exact_mod_cast hz

private lemma jlog_lt_jlog_of_one_lt {x : ℝ} (hx : 1 < x) :
    Cost.Jlog (1 : ℝ) < Cost.Jlog x := by
  -- strict monotone on `Ici 0`, and `1 < x` implies `0 ≤ 1` and `0 ≤ x`
  have hmono := Cost.Jlog_strictMonoOn_Ici0
  have hx0 : (0 : ℝ) ≤ x := le_trans (show (0 : ℝ) ≤ (1 : ℝ) by linarith) (le_of_lt hx)
  exact hmono (by simp) (by simpa [Set.mem_Ici] using hx0) hx

theorem postingStep_of_monotone_and_ledgerJlogCost_le_Jlog1 {d : Nat} {L L' : LedgerState d}
    (hmono : MonotoneLedger (d := d) L L')
    (hneq : L ≠ L')
    (hle : ledgerJlogCost (d := d) L L' ≤ Cost.Jlog (1 : ℝ)) :
    PostingStep (d := d) L L' := by
  classical
  -- helper: deltas
  let dΔ : Fin d → ℤ := fun i => L'.debit i - L.debit i
  let cΔ : Fin d → ℤ := fun i => L'.credit i - L.credit i
  have hdNonneg : ∀ i : Fin d, 0 ≤ dΔ i := by
    intro i
    have : L.debit i ≤ L'.debit i := hmono.1 i
    dsimp [dΔ]
    linarith
  have hcNonneg : ∀ i : Fin d, 0 ≤ cΔ i := by
    intro i
    have : L.credit i ≤ L'.credit i := hmono.2 i
    dsimp [cΔ]
    linarith

  -- show every delta is ≤ 1 (otherwise cost would exceed Jlog 1)
  have hdLeOne : ∀ i : Fin d, dΔ i ≤ 1 := by
    intro i
    by_contra hgt
    have hlt : (1 : ℤ) < dΔ i := lt_of_not_ge hgt
    have h2 : (2 : ℤ) ≤ dΔ i := by
      -- `2 ≤ z ↔ 1 < z`
      exact (Int.add_one_le_iff).2 hlt
    -- strict lower bound on this term
    have hx : (1 : ℝ) < ((dΔ i : ℤ) : ℝ) := by
      -- cast `1 < dΔ i` to ℝ
      exact_mod_cast hlt
    have hterm_lt : Cost.Jlog (1 : ℝ) < Cost.Jlog ((dΔ i : ℤ) : ℝ) :=
      jlog_lt_jlog_of_one_lt (x := ((dΔ i : ℤ) : ℝ)) hx
    -- this term is bounded by total cost (single term ≤ sum) and total cost ≤ Jlog 1: contradiction
    let fD : Fin d → ℝ := fun j => Cost.Jlog ((dΔ j : ℤ) : ℝ)
    have hterm_le_sum : fD i ≤ ∑ j : Fin d, fD j := by
      -- `fD i ≤ sum univ fD` by nonneg
      have hnonneg : ∀ j : Fin d, 0 ≤ fD j := fun _ => Cost.Jlog_nonneg _
      -- use `i` in univ
      -- work directly with `Finset.univ` to avoid rewriting via `Fintype.sum`
      have : fD i ≤ Finset.sum (Finset.univ : Finset (Fin d)) fD :=
        Finset.single_le_sum (by
          intro j hj
          exact hnonneg j) (by simp : i ∈ (Finset.univ : Finset (Fin d)))
      simpa using this
    have hsum_le_cost : (∑ j : Fin d, fD j) ≤ ledgerJlogCost (d := d) L L' := by
      -- debit sum ≤ debit sum + credit sum
      have hcredit_nonneg : 0 ≤ ∑ j : Fin d, Cost.Jlog ((cΔ j : ℤ) : ℝ) :=
        Finset.sum_nonneg (fun _ _ => Cost.Jlog_nonneg _)
      dsimp [ledgerJlogCost, dΔ, cΔ]
      exact le_add_of_nonneg_right hcredit_nonneg
    have hterm_le_cost : Cost.Jlog ((dΔ i : ℤ) : ℝ) ≤ ledgerJlogCost (d := d) L L' := by
      -- rewrite `fD i` and compose inequalities
      have : fD i ≤ ledgerJlogCost (d := d) L L' := le_trans hterm_le_sum hsum_le_cost
      simpa [fD] using this
    have : Cost.Jlog (1 : ℝ) < ledgerJlogCost (d := d) L L' :=
      lt_of_lt_of_le hterm_lt hterm_le_cost
    exact (not_lt_of_ge hle) this

  have hcLeOne : ∀ i : Fin d, cΔ i ≤ 1 := by
    intro i
    by_contra hgt
    have hlt : (1 : ℤ) < cΔ i := lt_of_not_ge hgt
    have hx : (1 : ℝ) < ((cΔ i : ℤ) : ℝ) := by exact_mod_cast hlt
    have hterm_lt : Cost.Jlog (1 : ℝ) < Cost.Jlog ((cΔ i : ℤ) : ℝ) :=
      jlog_lt_jlog_of_one_lt (x := ((cΔ i : ℤ) : ℝ)) hx
    let fC : Fin d → ℝ := fun j => Cost.Jlog ((cΔ j : ℤ) : ℝ)
    have hterm_le_sum : fC i ≤ ∑ j : Fin d, fC j := by
      have hnonneg : ∀ j : Fin d, 0 ≤ fC j := fun _ => Cost.Jlog_nonneg _
      have : fC i ≤ Finset.sum (Finset.univ : Finset (Fin d)) fC :=
        Finset.single_le_sum (by
          intro j hj
          exact hnonneg j) (by simp : i ∈ (Finset.univ : Finset (Fin d)))
      simpa using this
    have hsum_le_cost : (∑ j : Fin d, fC j) ≤ ledgerJlogCost (d := d) L L' := by
      have hdebit_nonneg : 0 ≤ ∑ j : Fin d, Cost.Jlog ((dΔ j : ℤ) : ℝ) :=
        Finset.sum_nonneg (fun _ _ => Cost.Jlog_nonneg _)
      dsimp [ledgerJlogCost, dΔ, cΔ]
      exact le_add_of_nonneg_left hdebit_nonneg
    have hterm_le_cost : Cost.Jlog ((cΔ i : ℤ) : ℝ) ≤ ledgerJlogCost (d := d) L L' := by
      have : fC i ≤ ledgerJlogCost (d := d) L L' := le_trans hterm_le_sum hsum_le_cost
      simpa [fC] using this
    have : Cost.Jlog (1 : ℝ) < ledgerJlogCost (d := d) L L' :=
      lt_of_lt_of_le hterm_lt hterm_le_cost
    exact (not_lt_of_ge hle) this

  -- Convert bounded deltas to `{0,1}` cases.
  have hd01 : ∀ i : Fin d, dΔ i = 0 ∨ dΔ i = 1 := by
    intro i
    have h0 : 0 ≤ dΔ i := hdNonneg i
    have h1 : dΔ i ≤ 1 := hdLeOne i
    cases hdi : dΔ i with
    | ofNat n =>
        have hn : n ≤ 1 := by
          have : (Int.ofNat n) ≤ (1 : ℤ) := by simpa [hdi] using h1
          exact (Int.ofNat_le).1 this
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;> simp [hdi]
    | negSucc n =>
        exfalso
        have : ¬ (0 ≤ (Int.negSucc n)) := by
          have : (Int.negSucc n) < 0 := by simpa using (Int.negSucc_lt_zero n)
          exact not_le_of_gt this
        exact this (by simpa [hdi] using h0)

  have hc01 : ∀ i : Fin d, cΔ i = 0 ∨ cΔ i = 1 := by
    intro i
    have h0 : 0 ≤ cΔ i := hcNonneg i
    have h1 : cΔ i ≤ 1 := hcLeOne i
    cases hci : cΔ i with
    | ofNat n =>
        have hn : n ≤ 1 := by
          have : (Int.ofNat n) ≤ (1 : ℤ) := by simpa [hci] using h1
          exact (Int.ofNat_le).1 this
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;> simp [hci]
    | negSucc n =>
        exfalso
        have : ¬ (0 ≤ (Int.negSucc n)) := by
          have : (Int.negSucc n) < 0 := by simpa using (Int.negSucc_lt_zero n)
          exact not_le_of_gt this
        exact this (by simpa [hci] using h0)

  -- existence of some 1 (since L ≠ L')
  have hex1 : (∃ i : Fin d, dΔ i = 1) ∨ (∃ i : Fin d, cΔ i = 1) := by
    by_contra hnone
    have hnoneD : ∀ i : Fin d, dΔ i = 0 := by
      intro i
      have : ¬ dΔ i = 1 := by
        have : ¬ (∃ i : Fin d, dΔ i = 1) := (not_or.mp hnone).1
        exact fun hi => this ⟨i, hi⟩
      cases hd01 i with
      | inl hz => exact hz
      | inr h1 => exact (this h1).elim
    have hnoneC : ∀ i : Fin d, cΔ i = 0 := by
      intro i
      have : ¬ cΔ i = 1 := by
        have : ¬ (∃ i : Fin d, cΔ i = 1) := (not_or.mp hnone).2
        exact fun hi => this ⟨i, hi⟩
      cases hc01 i with
      | inl hz => exact hz
      | inr h1 => exact (this h1).elim
    -- all deltas are 0 ⇒ ledger equal
    cases L with
    | mk debit credit =>
      cases L' with
      | mk debit' credit' =>
        have hdebitEq : debit' = debit := by
          funext i
          have : debit' i - debit i = 0 := by simpa [dΔ] using hnoneD i
          linarith
        have hcreditEq : credit' = credit := by
          funext i
          have : credit' i - credit i = 0 := by simpa [cΔ] using hnoneC i
          linarith
        exact hneq (by cases hdebitEq; cases hcreditEq; rfl)
  -- uniqueness: cannot have both a debit-1 and a credit-1, and cannot have two debit-1s, etc., else cost > Jlog 1.
  have j1pos : 0 < Cost.Jlog (1 : ℝ) := by
    -- `1 ≠ 0`
    have : (1 : ℝ) ≠ 0 := by norm_num
    exact (Cost.Jlog_pos_iff (1 : ℝ)).2 this
  have not_two_ones :
      ¬((∃ i : Fin d, dΔ i = 1) ∧ (∃ j : Fin d, cΔ j = 1)) := by
    intro hboth
    rcases hboth with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    -- each side contributes at least Jlog 1
    let fD : Fin d → ℝ := fun k => Cost.Jlog ((dΔ k : ℤ) : ℝ)
    let fC : Fin d → ℝ := fun k => Cost.Jlog ((cΔ k : ℤ) : ℝ)
    have hDi : Cost.Jlog (1 : ℝ) ≤ ∑ k : Fin d, fD k := by
      -- `fD i = Jlog 1` and all terms nonneg
      have hnonneg : ∀ k : Fin d, 0 ≤ fD k := fun _ => Cost.Jlog_nonneg _
      have : fD i ≤ ∑ k : Fin d, fD k := by
        have : fD i ≤ Finset.sum (Finset.univ : Finset (Fin d)) fD :=
          Finset.single_le_sum (by
            intro k hk; exact hnonneg k) (by simp : i ∈ (Finset.univ : Finset (Fin d)))
        simpa using this
      have : Cost.Jlog (1 : ℝ) ≤ ∑ k : Fin d, fD k := by
        simpa [fD, hi] using this
      exact this
    have hCj : Cost.Jlog (1 : ℝ) ≤ ∑ k : Fin d, fC k := by
      have hnonneg : ∀ k : Fin d, 0 ≤ fC k := fun _ => Cost.Jlog_nonneg _
      have : fC j ≤ ∑ k : Fin d, fC k := by
        have : fC j ≤ Finset.sum (Finset.univ : Finset (Fin d)) fC :=
          Finset.single_le_sum (by
            intro k hk; exact hnonneg k) (by simp : j ∈ (Finset.univ : Finset (Fin d)))
        simpa using this
      have : Cost.Jlog (1 : ℝ) ≤ ∑ k : Fin d, fC k := by
        simpa [fC, hj] using this
      exact this
    -- so total cost ≥ 2*Jlog1
    have hcost_ge :
        Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) ≤ ledgerJlogCost (d := d) L L' := by
      -- debitSum + creditSum
      dsimp [ledgerJlogCost, dΔ, cΔ]
      exact add_le_add hDi hCj
    have hlt : Cost.Jlog (1 : ℝ) < ledgerJlogCost (d := d) L L' := by
      have : Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) > Cost.Jlog (1 : ℝ) := by linarith
      exact lt_of_lt_of_le this hcost_ge
    exact (not_lt_of_ge hle) hlt

  -- Choose which side has the unique 1.
  cases hex1 with
  | inl hd =>
      rcases hd with ⟨k, hk⟩
      have : ¬ (∃ j : Fin d, cΔ j = 1) := by
        intro hc
        exact not_two_ones ⟨⟨k, hk⟩, hc⟩
      -- all credit deltas are 0
      have hcAll0 : ∀ j : Fin d, cΔ j = 0 := by
        intro j
        have hn1 : ¬ cΔ j = 1 := by
          intro hj
          exact this ⟨j, hj⟩
        cases hc01 j with
        | inl hz => exact hz
        | inr h1 => exact (hn1 h1).elim
      -- all debit deltas are 0 except at k
      have hdAll : ∀ j : Fin d, j ≠ k → dΔ j = 0 := by
        intro j hjk
        have hn1 : ¬ dΔ j = 1 := by
          intro hj1
          -- two debit ones would force cost > Jlog 1 similarly (simpler: use L1 minimality lemma later)
          -- We can derive contradiction by comparing debitSum with two Jlog1 terms.
          let fD : Fin d → ℝ := fun t => Cost.Jlog ((dΔ t : ℤ) : ℝ)
          have hnonneg : ∀ t : Fin d, 0 ≤ fD t := fun _ => Cost.Jlog_nonneg _
          have hi : fD k = Cost.Jlog (1 : ℝ) := by simpa [fD, hk]
          have hj : fD j = Cost.Jlog (1 : ℝ) := by simpa [fD, hj1]
          -- show debitSum ≥ fD k + fD j
          have hsplit :=
            (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := fD) (a := k) (by simp))
          have hjmem : j ∈ (Finset.univ.erase k : Finset (Fin d)) := by simp [hjk]
          have hj_le_rest :
              fD j ≤ Finset.sum (Finset.univ.erase k : Finset (Fin d)) fD := by
            exact Finset.single_le_sum (by
              intro t ht; exact hnonneg t) hjmem
          have hdebit_ge :
              Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) ≤ ∑ t : Fin d, fD t := by
            -- rewrite sum and use `hj_le_rest`
            calc
              Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ)
                  = fD k + fD j := by simp [hi, hj]
              _ ≤ fD k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) fD := by
                    linarith
              _ = ∑ t : Fin d, fD t := by simpa using hsplit.symm
          -- total cost ≥ debitSum
          have hcredit_nonneg : 0 ≤ ∑ t : Fin d, Cost.Jlog ((cΔ t : ℤ) : ℝ) :=
            Finset.sum_nonneg (fun _ _ => Cost.Jlog_nonneg _)
          have hcost_ge : Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) ≤ ledgerJlogCost (d := d) L L' := by
            dsimp [ledgerJlogCost, dΔ, cΔ]
            exact le_trans (le_trans hdebit_ge (le_add_of_nonneg_right hcredit_nonneg)) (le_rfl)
          have : Cost.Jlog (1 : ℝ) < ledgerJlogCost (d := d) L L' := by
            have : Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) > Cost.Jlog (1 : ℝ) := by linarith
            exact lt_of_lt_of_le this hcost_ge
          exact (not_lt_of_ge hle) this
        cases hd01 j with
        | inl hz => exact hz
        | inr h1 => exact (hn1 h1).elim
      -- now show L' = post L k debit
      refine ⟨k, Side.debit, ?_⟩
      cases L with
      | mk debit credit =>
        cases L' with
        | mk debit' credit' =>
          have hdebit' : debit' = fun i => if i = k then debit i + 1 else debit i := by
            funext i
            by_cases hik : i = k
            · subst hik
              have hdiff : debit' i - debit i = 1 := by simpa [dΔ] using hk
              have : debit' i = debit i + 1 := by linarith
              simpa using this
            · have : debit' i - debit i = 0 := by
                have := hdAll i hik
                simpa [dΔ] using this
              simp [hik]
              linarith
          have hcredit' : credit' = credit := by
            funext i
            have : credit' i - credit i = 0 := by simpa [cΔ] using hcAll0 i
            linarith
          subst hdebit' hcredit'
          simp [post]
          ext i <;> by_cases h : i = k <;> simp [h]
  | inr hc =>
      rcases hc with ⟨k, hk⟩
      have : ¬ (∃ j : Fin d, dΔ j = 1) := by
        intro hd
        exact not_two_ones ⟨hd, ⟨k, hk⟩⟩
      -- symmetric to debit case: build post on credit
      have hdAll0 : ∀ j : Fin d, dΔ j = 0 := by
        intro j
        have hn1 : ¬ dΔ j = 1 := by
          intro hj
          exact this ⟨j, hj⟩
        cases hd01 j with
        | inl hz => exact hz
        | inr h1 => exact (hn1 h1).elim
      have hcAll : ∀ j : Fin d, j ≠ k → cΔ j = 0 := by
        intro j hjk
        have hn1 : ¬ cΔ j = 1 := by
          intro hj1
          -- two credit ones would force cost > Jlog 1 (same argument as in debit case)
          let fC : Fin d → ℝ := fun t => Cost.Jlog ((cΔ t : ℤ) : ℝ)
          have hnonneg : ∀ t : Fin d, 0 ≤ fC t := fun _ => Cost.Jlog_nonneg _
          have hi : fC k = Cost.Jlog (1 : ℝ) := by simpa [fC, hk]
          have hj : fC j = Cost.Jlog (1 : ℝ) := by simpa [fC, hj1]
          have hsplit :=
            (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := fC) (a := k) (by simp))
          have hjmem : j ∈ (Finset.univ.erase k : Finset (Fin d)) := by simp [hjk]
          have hj_le_rest :
              fC j ≤ Finset.sum (Finset.univ.erase k : Finset (Fin d)) fC := by
            exact Finset.single_le_sum (by
              intro t ht; exact hnonneg t) hjmem
          have hcredit_ge :
              Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) ≤ ∑ t : Fin d, fC t := by
            calc
              Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ)
                  = fC k + fC j := by simp [hi, hj]
              _ ≤ fC k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) fC := by
                    linarith
              _ = ∑ t : Fin d, fC t := by simpa using hsplit.symm
          have hdebit_nonneg : 0 ≤ ∑ t : Fin d, Cost.Jlog ((dΔ t : ℤ) : ℝ) :=
            Finset.sum_nonneg (fun _ _ => Cost.Jlog_nonneg _)
          have hcost_ge : Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) ≤ ledgerJlogCost (d := d) L L' := by
            dsimp [ledgerJlogCost, dΔ, cΔ]
            exact le_trans (le_trans hcredit_ge (le_add_of_nonneg_left hdebit_nonneg)) (le_rfl)
          have : Cost.Jlog (1 : ℝ) < ledgerJlogCost (d := d) L L' := by
            have : Cost.Jlog (1 : ℝ) + Cost.Jlog (1 : ℝ) > Cost.Jlog (1 : ℝ) := by linarith
            exact lt_of_lt_of_le this hcost_ge
          exact (not_lt_of_ge hle) this
        cases hc01 j with
        | inl hz => exact hz
        | inr h1 => exact (hn1 h1).elim
      refine ⟨k, Side.credit, ?_⟩
      cases L with
      | mk debit credit =>
        cases L' with
        | mk debit' credit' =>
          have hcredit' : credit' = fun i => if i = k then credit i + 1 else credit i := by
            funext i
            by_cases hik : i = k
            · subst hik
              have hdiff : credit' i - credit i = 1 := by simpa [cΔ] using hk
              have : credit' i = credit i + 1 := by linarith
              simpa using this
            · have : credit' i - credit i = 0 := by
                have := hcAll i hik
                simpa [cΔ] using this
              simp [hik]
              linarith
          have hdebit' : debit' = debit := by
            funext i
            have : debit' i - debit i = 0 := by simpa [dΔ] using hdAll0 i
            linarith
          subst hcredit' hdebit'
          simp [post]
          ext i <;> by_cases h : i = k <;> simp [h]

/-! ### Zero-cost characterization -/

theorem ledgerL1Cost_eq_zero_iff {d : Nat} (L L' : LedgerState d) :
    ledgerL1Cost (d := d) L L' = 0 ↔ L' = L := by
  classical
  cases L with
  | mk debit credit =>
    cases L' with
    | mk debit' credit' =>
      constructor
      · intro h0
        -- split into debit/credit sums
        let dSum : Nat := ∑ i : Fin d, Int.natAbs (debit' i - debit i)
        let cSum : Nat := ∑ i : Fin d, Int.natAbs (credit' i - credit i)
        have hsplit : dSum + cSum = 0 := by
          simpa [ledgerL1Cost, dSum, cSum] using h0
        have hd0 : dSum = 0 ∧ cSum = 0 := Nat.add_eq_zero_iff.mp hsplit
        have hdebit0 :
            ∀ i : Fin d, Int.natAbs (debit' i - debit i) = 0 := by
          have h' :
              Finset.sum (Finset.univ : Finset (Fin d)) (fun i => Int.natAbs (debit' i - debit i)) = 0 := by
            simpa [dSum] using hd0.1
          have hall :=
            (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin d)))
              (f := fun i => Int.natAbs (debit' i - debit i))
              (fun _ _ => Nat.zero_le _)).1 h'
          intro i
          exact hall i (by simp)
        have hcredit0 :
            ∀ i : Fin d, Int.natAbs (credit' i - credit i) = 0 := by
          have h' :
              Finset.sum (Finset.univ : Finset (Fin d)) (fun i => Int.natAbs (credit' i - credit i)) = 0 := by
            simpa [cSum] using hd0.2
          have hall :=
            (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin d)))
              (f := fun i => Int.natAbs (credit' i - credit i))
              (fun _ _ => Nat.zero_le _)).1 h'
          intro i
          exact hall i (by simp)
        have hdebitEq : debit' = debit := by
          funext i
          have hz : (debit' i - debit i) = 0 := Int.natAbs_eq_zero.mp (hdebit0 i)
          linarith
        have hcreditEq : credit' = credit := by
          funext i
          have hz : (credit' i - credit i) = 0 := Int.natAbs_eq_zero.mp (hcredit0 i)
          linarith
        subst hdebitEq hcreditEq
        rfl
      · intro hEq
        cases hEq
        simp [ledgerL1Cost]

/-! ### Posting steps satisfy `LegalAtomicTick` (and conversely, by `legalAtomicTick_implies_PostingStep`) -/

private lemma post_monotone {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) :
    MonotoneLedger (d := d) L (post L k side) := by
  classical
  cases side with
  | debit =>
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hik : i = k
        · subst hik
          simp [post]
        · simp [post, hik]
      · intro i
        simp [post]
  | credit =>
      refine ⟨?_, ?_⟩
      · intro i
        simp [post]
      · intro i
        by_cases hik : i = k
        · subst hik
          simp [post]
        · simp [post, hik]

private lemma ledgerL1Cost_post {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) :
    ledgerL1Cost (d := d) L (post L k side) = 1 := by
  classical
  cases side with
  | debit =>
      -- debit changes by +1 at k; credit unchanged
      have hdebit :
          (∑ i : Fin d, Int.natAbs ((post L k Side.debit).debit i - L.debit i)) = 1 := by
        -- isolate `k` and show everything else is 0
        let f : Fin d → Nat := fun i => Int.natAbs ((post L k Side.debit).debit i - L.debit i)
        have hsplit :=
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := f) (a := k) (by simp))
        have fk : f k = 1 := by
          simp [f, post]
        have hErase : Finset.sum (Finset.univ.erase k : Finset (Fin d)) f = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hik : i ≠ k := by
            simpa [Finset.mem_erase] using hi
          simp [f, post, hik]
        -- rewrite `∑ univ` using `hsplit.symm`
        simpa [f] using (by
          calc
            (∑ i : Fin d, f i) = f k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) f := by
              simpa using hsplit.symm
            _ = 1 := by simp [fk, hErase])
      have hcredit :
          (∑ i : Fin d, Int.natAbs ((post L k Side.debit).credit i - L.credit i)) = 0 := by
        -- credit is unchanged everywhere
        refine Finset.sum_eq_zero ?_
        intro i _
        simp [post]
      -- assemble
      simp [ledgerL1Cost, hdebit, hcredit]
  | credit =>
      -- credit changes by +1 at k; debit unchanged
      have hdebit :
          (∑ i : Fin d, Int.natAbs ((post L k Side.credit).debit i - L.debit i)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        simp [post]
      have hcredit :
          (∑ i : Fin d, Int.natAbs ((post L k Side.credit).credit i - L.credit i)) = 1 := by
        let f : Fin d → Nat := fun i => Int.natAbs ((post L k Side.credit).credit i - L.credit i)
        have hsplit :=
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := f) (a := k) (by simp))
        have fk : f k = 1 := by
          simp [f, post]
        have hErase : Finset.sum (Finset.univ.erase k : Finset (Fin d)) f = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hik : i ≠ k := by
            simpa [Finset.mem_erase] using hi
          simp [f, post, hik]
        simpa [f] using (by
          calc
            (∑ i : Fin d, f i) = f k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) f := by
              simpa using hsplit.symm
            _ = 1 := by simp [fk, hErase])
      simp [ledgerL1Cost, hdebit, hcredit]

theorem legalAtomicTick_of_post {d : Nat} (L : LedgerState d) (k : Fin d) (side : Side) :
    LegalAtomicTick (d := d) L (post L k side) := by
  refine ⟨post_monotone (d := d) L k side, ledgerL1Cost_post (d := d) L k side⟩

theorem postingStep_implies_legalAtomicTick {d : Nat} {L L' : LedgerState d}
    (h : PostingStep (d := d) L L') : LegalAtomicTick (d := d) L L' := by
  rcases h with ⟨k, side, rfl⟩
  exact legalAtomicTick_of_post (d := d) L k side

private lemma int_natAbs_eq_one_of_nonneg {z : ℤ} (hz : Int.natAbs z = 1) (hznn : 0 ≤ z) :
    z = 1 := by
  cases z with
  | ofNat n =>
      -- natAbs (ofNat n) = n
      have : n = 1 := by simpa using hz
      simpa [this]
  | negSucc n =>
      -- negative contradiction
      have : ¬ (0 ≤ Int.negSucc n) := by
        -- `negSucc n = -(n+1) < 0`
        have : Int.negSucc n < 0 := by
          simpa using (Int.negSucc_lt_zero n)
        exact not_le_of_gt this
      exact (this hznn).elim

private lemma int_eq_of_natAbs_eq_zero {z : ℤ} (hz : Int.natAbs z = 0) : z = 0 := by
  exact (Int.natAbs_eq_zero.mp hz)

private lemma exists_unique_of_sum_univ_eq_one {d : Nat} (f : Fin d → Nat)
    (hs : (∑ i : Fin d, f i) = 1) :
    ∃ k : Fin d, f k = 1 ∧ ∀ i : Fin d, i ≠ k → f i = 0 := by
  classical
  have hs_ne0 : (∑ i : Fin d, f i) ≠ 0 := by
    simpa [hs] using Nat.one_ne_zero
  obtain ⟨k, _hkMem, hkne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => f i) hs_ne0
  have hdecomp : f k + Finset.sum (Finset.univ.erase k : Finset (Fin d)) f = 1 := by
    -- `f k + sum (erase k) = sum univ`
    have := (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin d))) (f := fun i => f i) (a := k) (by simp))
    simpa [hs] using this
  have hk_cases := Nat.add_eq_one_iff.mp hdecomp
  have hk1 : f k = 1 ∧ Finset.sum (Finset.univ.erase k : Finset (Fin d)) f = 0 := by
    cases hk_cases with
    | inl h0 =>
        -- f k = 0 contradicts hkne0
        exfalso
        exact hkne0 h0.1
    | inr h1 =>
        exact h1
  refine ⟨k, hk1.1, ?_⟩
  intro i hik
  have hi' : i ∈ (Finset.univ.erase k : Finset (Fin d)) := by
    simp [Finset.mem_erase, hik]
  -- sum=0 on erase ⇒ every term on erase is 0
  have hall0 :
      ∀ j : Fin d, j ∈ (Finset.univ.erase k : Finset (Fin d)) → f j = 0 := by
    have :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ.erase k : Finset (Fin d)))
        (f := fun j => f j) (fun _ _ => Nat.zero_le _)).1 hk1.2
    simpa using this
  exact hall0 i hi'

theorem legalAtomicTick_implies_PostingStep {d : Nat} {L L' : LedgerState d}
    (h : LegalAtomicTick (d := d) L L') : PostingStep (d := d) L L' := by
  classical
  rcases h with ⟨hmono, hcost⟩
  rcases hmono with ⟨hmonoD, hmonoC⟩
  -- split the total cost into debit-cost and credit-cost
  let dCost : Nat := ∑ i : Fin d, Int.natAbs (L'.debit i - L.debit i)
  let cCost : Nat := ∑ i : Fin d, Int.natAbs (L'.credit i - L.credit i)
  have hsplit : dCost + cCost = 1 := by
    simpa [ledgerL1Cost, dCost, cCost] using hcost
  have hcases := Nat.add_eq_one_iff.mp hsplit
  cases hcases with
  | inl hc =>
      -- dCost = 0, cCost = 1 → credit posting
      have hd0 : dCost = 0 := hc.1
      have hc1 : cCost = 1 := hc.2
      -- choose the unique changed credit coordinate
      have ⟨k, hk1, hkrest⟩ :=
        exists_unique_of_sum_univ_eq_one (d := d) (f := fun i => Int.natAbs (L'.credit i - L.credit i)) hc1
      -- debit diffs all 0
      have hdAll :
          ∀ i : Fin d, Int.natAbs (L'.debit i - L.debit i) = 0 := by
        have hall0 :
            ∀ i : Fin d, i ∈ (Finset.univ : Finset (Fin d)) → Int.natAbs (L'.debit i - L.debit i) = 0 := by
          have :=
            (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin d)))
              (f := fun i => Int.natAbs (L'.debit i - L.debit i))
              (fun _ _ => Nat.zero_le _)).1 hd0
          simpa [dCost] using this
        intro i; exact hall0 i (by simp)
      -- build PostingStep = post at k on credit side
      refine ⟨k, Side.credit, ?_⟩
      -- prove L' = post L k credit by field ext (no `[ext]` lemma registered)
      cases L with
      | mk debit credit =>
        cases L' with
        | mk debit' credit' =>
          -- show the debit field is unchanged
          have hdebit' : debit' = debit := by
            funext i
            have hz := int_eq_of_natAbs_eq_zero (hdAll i)
            have hz' : (debit' i - debit i) = 0 := by simpa using hz
            linarith
          -- show the credit field matches the `post` update
          have hcredit' :
              credit' = (fun i => if i = k then credit i + 1 else credit i) := by
            funext i
            by_cases hik : i = k
            · subst hik
              -- goal reduces to `credit' i = credit i + 1`
              simp
              have hzabs : Int.natAbs (credit' i - credit i) = 1 := hk1
              have hnn : 0 ≤ (credit' i - credit i) := by
                have : credit i ≤ credit' i := hmonoC i
                linarith
              have hz : (credit' i - credit i) = 1 :=
                int_natAbs_eq_one_of_nonneg (z := (credit' i - credit i)) hzabs hnn
              linarith
            · -- goal reduces to `credit' i = credit i`
              have hzabs : Int.natAbs (credit' i - credit i) = 0 := hkrest i hik
              have hz : (credit' i - credit i) = 0 := int_eq_of_natAbs_eq_zero hzabs
              simp [hik]
              linarith
          -- finish
          subst hdebit' hcredit'
          simp [post]
          ext i <;> by_cases h : i = k <;> simp [h]
  | inr hc =>
      -- dCost = 1, cCost = 0 → debit posting
      have hd1 : dCost = 1 := hc.1
      have hc0 : cCost = 0 := hc.2
      have ⟨k, hk1, hkrest⟩ :=
        exists_unique_of_sum_univ_eq_one (d := d) (f := fun i => Int.natAbs (L'.debit i - L.debit i)) hd1
      have hcAll :
          ∀ i : Fin d, Int.natAbs (L'.credit i - L.credit i) = 0 := by
        have hall0 :
            ∀ i : Fin d, i ∈ (Finset.univ : Finset (Fin d)) → Int.natAbs (L'.credit i - L.credit i) = 0 := by
          have :=
            (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin d)))
              (f := fun i => Int.natAbs (L'.credit i - L.credit i))
              (fun _ _ => Nat.zero_le _)).1 hc0
          simpa [cCost] using this
        intro i; exact hall0 i (by simp)
      refine ⟨k, Side.debit, ?_⟩
      cases L with
      | mk debit credit =>
        cases L' with
        | mk debit' credit' =>
          have hcredit' : credit' = credit := by
            funext i
            have hz := int_eq_of_natAbs_eq_zero (hcAll i)
            have hz' : (credit' i - credit i) = 0 := by simpa using hz
            linarith
          have hdebit' :
              debit' = (fun i => if i = k then debit i + 1 else debit i) := by
            funext i
            by_cases hik : i = k
            · subst hik
              simp
              have hzabs : Int.natAbs (debit' i - debit i) = 1 := hk1
              have hnn : 0 ≤ (debit' i - debit i) := by
                have : debit i ≤ debit' i := hmonoD i
                linarith
              have hz : (debit' i - debit i) = 1 :=
                int_natAbs_eq_one_of_nonneg (z := (debit' i - debit i)) hzabs hnn
              linarith
            · have hzabs : Int.natAbs (debit' i - debit i) = 0 := hkrest i hik
              have hz : (debit' i - debit i) = 0 := int_eq_of_natAbs_eq_zero hzabs
              simp [hik]
              linarith
          subst hcredit' hdebit'
          simp [post]
          ext i <;> by_cases h : i = k <;> simp [h]

theorem postingStep_iff_legalAtomicTick {d : Nat} {L L' : LedgerState d} :
    PostingStep (d := d) L L' ↔ LegalAtomicTick (d := d) L L' :=
  ⟨postingStep_implies_legalAtomicTick (d := d), legalAtomicTick_implies_PostingStep (d := d)⟩

/-! ### Optional B3-style tightening: minimal cost (among monotone, nontrivial steps) ⇒ posting -/

theorem minCost_monotoneStep_implies_postingStep {d : Nat} [NeZero d]
    {L L' : LedgerState d}
    (hmono : MonotoneLedger (d := d) L L')
    (hneq : L ≠ L')
    (hmin : ∀ L'' : LedgerState d, MonotoneLedger (d := d) L L'' → L ≠ L'' →
      ledgerL1Cost (d := d) L L' ≤ ledgerL1Cost (d := d) L L'') :
    PostingStep (d := d) L L' := by
  classical
  -- compare against a concrete single-post candidate (cost = 1)
  let k0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hpostNe : L ≠ post L k0 Side.debit := by
    intro hEq
    have hdeb : L.debit k0 = L.debit k0 + 1 := by
      -- RHS is `L.debit k0 + 1`
      have := congrArg (fun s => s.debit k0) hEq
      simpa [post] using this
    linarith
  have hle1 : ledgerL1Cost (d := d) L L' ≤ 1 := by
    have hmono' : MonotoneLedger (d := d) L (post L k0 Side.debit) :=
      post_monotone (d := d) L k0 Side.debit
    have hcost' : ledgerL1Cost (d := d) L (post L k0 Side.debit) = 1 :=
      ledgerL1Cost_post (d := d) L k0 Side.debit
    have := hmin (post L k0 Side.debit) hmono' hpostNe
    simpa [hcost'] using this
  have hcostNe0 : ledgerL1Cost (d := d) L L' ≠ 0 := by
    intro h0
    have : L' = L := (ledgerL1Cost_eq_zero_iff (d := d) L L').1 h0
    exact hneq (by simpa [this])
  have hcost1 : ledgerL1Cost (d := d) L L' = 1 := by
    have hcases := Nat.le_one_iff_eq_zero_or_eq_one.1 hle1
    cases hcases with
    | inl h0 => exact (hcostNe0 h0).elim
    | inr h1 => exact h1
  -- conclude via the `PostingStep ↔ LegalAtomicTick` equivalence
  have hlegal : LegalAtomicTick (d := d) L L' := ⟨hmono, hcost1⟩
  exact (postingStep_iff_legalAtomicTick (d := d)).2 hlegal

/-! ### Optional B4-style tightening: Jlog-cost minimality (among monotone, nontrivial steps) ⇒ posting -/

theorem minJlogCost_monotoneStep_implies_postingStep {d : Nat} [NeZero d]
    {L L' : LedgerState d}
    (hmono : MonotoneLedger (d := d) L L')
    (hneq : L ≠ L')
    (hmin : ∀ L'' : LedgerState d, MonotoneLedger (d := d) L L'' → L ≠ L'' →
      ledgerJlogCost (d := d) L L' ≤ ledgerJlogCost (d := d) L L'') :
    PostingStep (d := d) L L' := by
  classical
  -- compare against a concrete single-post candidate (Jlog-cost = Jlog 1)
  let k0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hpostNe : L ≠ post L k0 Side.debit := by
    intro hEq
    have hdeb : L.debit k0 = L.debit k0 + 1 := by
      have := congrArg (fun s => s.debit k0) hEq
      simpa [post] using this
    linarith
  have hmono' : MonotoneLedger (d := d) L (post L k0 Side.debit) :=
    post_monotone (d := d) L k0 Side.debit
  have hcost' : ledgerJlogCost (d := d) L (post L k0 Side.debit) = Cost.Jlog (1 : ℝ) :=
    ledgerJlogCost_post (d := d) L k0 Side.debit
  have hleJ1 : ledgerJlogCost (d := d) L L' ≤ Cost.Jlog (1 : ℝ) := by
    have := hmin (post L k0 Side.debit) hmono' hpostNe
    simpa [hcost'] using this
  exact postingStep_of_monotone_and_ledgerJlogCost_le_Jlog1 (d := d) (L := L) (L' := L') hmono hneq hleJ1

theorem legalAtomicTick_oneBitDiff {d : Nat} {L L' : LedgerState d}
    (h : LegalAtomicTick (d := d) L L') :
    OneBitDiff (parity d L) (parity d L') :=
  postingStep_oneBitDiff (legalAtomicTick_implies_PostingStep (d := d) h)

/-! ## Workstream B tightening: RS AtomicTick ⇒ PostingStep (legality predicate) -/

/-- Choose the unique posted account at tick `t` from an RS `AtomicTick` instance. -/
noncomputable def accountAt {d : Nat} [AtomicTick (AccountRS d)] (t : Nat) : Fin d :=
  Classical.choose (ExistsUnique.exists (AtomicTick.unique_post (M := AccountRS d) t))

lemma postedAt_accountAt {d : Nat} [AtomicTick (AccountRS d)] (t : Nat) :
    AtomicTick.postedAt (M := AccountRS d) t (accountAt (d := d) t) := by
  have hex : ∃ u : Fin d, AtomicTick.postedAt (M := AccountRS d) t u :=
    ExistsUnique.exists (AtomicTick.unique_post (M := AccountRS d) t)
  simpa [accountAt] using (Classical.choose_spec hex)

/-- An RS-atomic tick step, parameterized by an explicit debit/credit side schedule. -/
noncomputable def stepAt {d : Nat} [AtomicTick (AccountRS d)] (sideAt : Nat → Side) (t : Nat) (L : LedgerState d) :
    LedgerState d :=
  post L (accountAt (d := d) t) (sideAt t)

lemma stepAt_isPostingStep {d : Nat} [AtomicTick (AccountRS d)] (sideAt : Nat → Side) (t : Nat) (L : LedgerState d) :
    PostingStep (d := d) L (stepAt (d := d) sideAt t L) := by
  refine ⟨accountAt (d := d) t, sideAt t, rfl⟩

theorem stepAt_oneBitDiff {d : Nat} [AtomicTick (AccountRS d)] (sideAt : Nat → Side) (t : Nat) (L : LedgerState d) :
    OneBitDiff (parity d L) (parity d (stepAt (d := d) sideAt t L)) :=
  postingStep_oneBitDiff (stepAt_isPostingStep (d := d) sideAt t L)

/-! ## A per-tick posting schedule induces an adjacent walk in parity space -/

/-- A per-tick posting instruction: (account index, side). -/
abbrev PostInstr (d : Nat) : Type := Fin d × Side

/-- Run a ledger forward under a per-tick posting schedule. -/
noncomputable def run {d : Nat} (L0 : LedgerState d) (sched : Nat → PostInstr d) : Nat → LedgerState d
| 0 => L0
| (t + 1) =>
    let prev := run L0 sched t
    post prev (sched t).1 (sched t).2

theorem run_step_oneBitDiff {d : Nat} (L0 : LedgerState d) (sched : Nat → PostInstr d) (t : Nat) :
    OneBitDiff (parity d (run L0 sched t)) (parity d (run L0 sched (t + 1))) := by
  -- unfold one step of `run` and apply the single-post theorem
  simp [run, parity_oneBitDiff_of_post, parity]

end LedgerPostingAdjacency
end IndisputableMonolith
