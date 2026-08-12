import IndisputableMonolith.Gravity.SevenGaps.Gap2LatticeKindRule
import IndisputableMonolith.LedgerPostingAdjacency

/-!
# Gap 2, fifth arc: does the posting dynamics force the counts-only premise?

The chain of named premises behind Gap 2's measure, as the last three arcs left it: the weight
is size-blind if the cost is kind-only (`Gap2PostingCostDerivation`); the cost is kind-only if
its charge is counts-only (`Gap2KindRule`, the named premise `ChargesCountsOnly`); the charge
is counts-only if the lattice imbalance and magnitude are (`Gap2LatticeKindRule`, the named
premise `LatticeChargesCountsOnly`).  None of those is forced at its own layer, and the fourth
arc flagged the successor as the ledger *dynamics*: the posting rules that produce the states,
not the state type.  This module settles the dynamics, and the answer is the sharpest of the
three.

**The committed answer is no, and for a stronger reason than at the upper layers: the dynamics
excludes nothing.**  A posting step increments one account's debit or credit column by one
quantum (`LedgerPostingAdjacency.post`, `PostingStep`), and a run is a schedule of such steps.
From the balanced zero ledger, *every* ledger with nonnegative columns is reachable
(`postReachable_zero_of_nonneg`: forward reachability; posts only ever raise a column, so
ledgers with a negative column are not reachable and the statement is not ergodicity), so
*every* integer imbalance configuration is the `phi` of a reachable ledger
(`imbalance_realized`), and is reached by an explicit posting schedule
(`imbalance_realized_by_schedule`).  A dynamics that reaches every nonnegative state excludes
no imbalance; in particular it reaches the incidence-reading and index-reading imbalances, the
two families the earlier arcs exhibited non-counts-only members of (the incidence reading on
complexes mixing at least one proper edge with at least one loop, the index reading).

The two conjuncts of the fourth arc's dual premise each fall, for their own reasons:

* **Imbalance.**  The dynamics produces every `phi`, so it produces the countermodel's.  Stated
  at the schedule level, where the premise would have to live: there is an explicitly exhibited
  posting schedule on the two-bridge witness whose imbalance after one tick is not kind-constant
  (`schedule_countermodel_not_countsOnly`), so counts-only is not a theorem about schedules.

* **Magnitude.**  This conjunct falls not to reachability but to silence: the posting step acts
  on the debit and credit columns of a `Recognition.Ledger`, which has no magnitude field, so
  posting says nothing about magnitude at all.  The `DualEntryStrainState` enrichment adds `mag`
  separately, and `DualEntryStrainState.ofLedger` attaches *any* nonnegative magnitude function
  to *any* reachable ledger with unit flux, so every lattice state the fourth arc admitted is
  dynamically generable from balance (`dynamics_produces_incidence_countermodel`).  Whether the
  produced incidence state is itself a countermodel depends on the edge-kind mix: the incidence
  imbalance is `1` on proper edge letters and `0` elsewhere, so it is kind-constant, hence
  counts-only, exactly when the complex's edges are all proper or all loops (`twoBridges` and
  `twoLoops` alike), and it fails counts-only exactly when the complex carries at least one
  proper edge and at least one loop.  The §4 schedule countermodel on `twoBridges` is a
  different witness of a different kind: its imbalance after one tick is `1` on edge letter 0
  and `0` on edge letter 1, which is not the incidence imbalance of any complex.

**The recursion bottoms out at the three layers examined.**  The letter-cost space does not
force counts-only (third arc), the lattice state type does not (fourth arc), and the posting
dynamics does not (this arc); the kernel content is `ledger_forces_countsOnly_at_no_layer`,
the conjunction of those three negative receipts.  Whether some deeper layer than the posting
step could force it is a meta-question the theorems do not address, because the library carries
no layer below the posting step.  What counts-only can still be is a law about the *actual*
schedule nature executes: which account posts, which side, at each tick.  That is a physical
premise about one run, not a theorem about the space of runs, and it is named
`CountsOnlySchedule` in §4.  Whether the universe's schedule satisfies it is the open question
this arc hands to the measure track; it cannot be settled by inspecting the ledger, because
the ledger admits every schedule.

## What this settles for the measure track

Track A of `QG/plans/QG_Full_Theory_Completion_20260729.html` asked (step A1.1): does the
posting dynamics force `LatticeChargesCountsOnly`?  Answer: no, with receipts, and the premise
is now named at the dynamics layer per the plan's hard stop.  Consequence for the next step:
the measure derivation cannot come from any restriction on the charge picture, because no
charge restriction is available at any layer of the ledger.  The remaining route is the
counting structure itself (the canonical pinning and the orbit count), which is Track A1.2's
target.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2DynamicsKindRule

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation Gap2KindRule
open Gap2LatticeKindRule
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-! ## §1. Posting on a generic discrete carrier, and total reachability -/

/-- The balanced zero ledger: every column empty.  This is the state the counted histories are
pinned to by `CanonicalHistory.state_canonical`, seen now as the *initial condition* of the
posting dynamics rather than as a selection among states. -/
def zeroLedger : Recognition.Ledger (discreteCarrier Λ) where
  debit := fun _ => 0
  credit := fun _ => 0

/-- One posting step on the generic carrier: increment one account's debit or credit column by
one quantum.  This is `LedgerPostingAdjacency.post` lifted from `Fin d` to an arbitrary
decidable finite carrier; the step relation it generates is the whole of the dynamics. -/
def postAt (L : Recognition.Ledger (discreteCarrier Λ)) (k : Λ)
    (s : LedgerPostingAdjacency.Side) : Recognition.Ledger (discreteCarrier Λ) :=
  match s with
  | .debit => { debit := fun i => if i = k then L.debit i + 1 else L.debit i
                credit := L.credit }
  | .credit => { debit := L.debit
                 credit := fun i => if i = k then L.credit i + 1 else L.credit i }

/-- **Reachability.**  Ledger `L₂` is reachable from `L₁` by a finite sequence of posting
steps.  Defined as a closure so the reachability statements below are about the step relation
itself, not about any particular scheduling device. -/
inductive PostReachable : Recognition.Ledger (discreteCarrier Λ) →
    Recognition.Ledger (discreteCarrier Λ) → Prop where
  | refl (L : Recognition.Ledger (discreteCarrier Λ)) : PostReachable L L
  | step {L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)} (k : Λ)
      (s : LedgerPostingAdjacency.Side) :
      PostReachable L₁ L₂ → PostReachable L₁ (postAt L₂ k s)

@[simp] theorem phi_zeroLedger (i : Λ) : Recognition.phi zeroLedger i = 0 := rfl

theorem phi_postAt_debit_self (L : Recognition.Ledger (discreteCarrier Λ)) (k : Λ) :
    Recognition.phi (postAt L k .debit) k = Recognition.phi L k + 1 := by
  have h1 : (postAt L k .debit).debit k = L.debit k + 1 := if_pos rfl
  have h2 : (postAt L k .debit).credit k = L.credit k := rfl
  show (postAt L k .debit).debit k - (postAt L k .debit).credit k
      = L.debit k - L.credit k + 1
  rw [h1, h2]
  omega

theorem phi_postAt_credit_self (L : Recognition.Ledger (discreteCarrier Λ)) (k : Λ) :
    Recognition.phi (postAt L k .credit) k = Recognition.phi L k - 1 := by
  have h1 : (postAt L k .credit).debit k = L.debit k := rfl
  have h2 : (postAt L k .credit).credit k = L.credit k + 1 := if_pos rfl
  show (postAt L k .credit).debit k - (postAt L k .credit).credit k
      = L.debit k - L.credit k - 1
  rw [h1, h2]
  omega

theorem phi_postAt_ne (L : Recognition.Ledger (discreteCarrier Λ)) {i k : Λ} (h : i ≠ k)
    (s : LedgerPostingAdjacency.Side) :
    Recognition.phi (postAt L k s) i = Recognition.phi L i := by
  cases s with
  | debit =>
    have h1 : (postAt L k .debit).debit i = L.debit i := if_neg h
    have h2 : (postAt L k .debit).credit i = L.credit i := rfl
    show (postAt L k .debit).debit i - (postAt L k .debit).credit i
        = L.debit i - L.credit i
    rw [h1, h2]
  | credit =>
    have h1 : (postAt L k .credit).debit i = L.debit i := rfl
    have h2 : (postAt L k .credit).credit i = L.credit i := if_neg h
    show (postAt L k .credit).debit i - (postAt L k .credit).credit i
        = L.debit i - L.credit i
    rw [h1, h2]

/-- Ledger extensionality, pointwise. -/
theorem ledger_ext {L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)}
    (hd : ∀ i, L₁.debit i = L₂.debit i) (hc : ∀ i, L₁.credit i = L₂.credit i) :
    L₁ = L₂ := by
  obtain ⟨d₁, c₁⟩ := L₁
  obtain ⟨d₂, c₂⟩ := L₂
  simp only [IndisputableMonolith.Recognition.Ledger.mk.injEq]
  exact ⟨funext fun i => hd i, funext fun i => hc i⟩

/-- The total column mass: sum of absolute column values.  From zero, each posting step raises
mass by exactly one, so mass is the induction measure for reachability. -/
def mass (L : Recognition.Ledger (discreteCarrier Λ)) : ℕ :=
  ∑ i : Λ, (Int.natAbs (L.debit i) + Int.natAbs (L.credit i))

/-- A ledger of zero mass is the zero ledger. -/
theorem eq_zeroLedger_of_mass_zero {L : Recognition.Ledger (discreteCarrier Λ)}
    (hm : mass L = 0) : L = zeroLedger := by
  have hm' : (∑ i : Λ, (Int.natAbs (L.debit i) + Int.natAbs (L.credit i))) = 0 := hm
  have h0 : ∀ i : Λ, Int.natAbs (L.debit i) + Int.natAbs (L.credit i) = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hm'
    exact fun i => hs i (Finset.mem_univ i)
  have hd : ∀ i, L.debit i = 0 := fun i => by have := h0 i; omega
  have hc : ∀ i, L.credit i = 0 := fun i => by have := h0 i; omega
  apply ledger_ext
  · intro i; show L.debit i = 0; exact hd i
  · intro i; show L.credit i = 0; exact hc i

/-- A nonzero nonnegative ledger has a coordinate with a positive column. -/
theorem exists_pos_of_ne_zero {L : Recognition.Ledger (discreteCarrier Λ)}
    (hnn : ∀ i, 0 ≤ L.debit i ∧ 0 ≤ L.credit i) (hne : L ≠ zeroLedger) :
    ∃ i, 0 < L.debit i ∨ 0 < L.credit i := by
  by_contra h
  push_neg at h
  apply hne
  apply ledger_ext
  · intro i
    have hi := (h i).1
    have hj := (hnn i).1
    show L.debit i = 0
    omega
  · intro i
    have hi := (h i).2
    have hj := (hnn i).2
    show L.credit i = 0
    omega

/-- The predecessor of a nonnegative ledger along a positive column: decrement that column at
one coordinate.  The ledger is then the post of its predecessor at that coordinate. -/
def predOf (L : Recognition.Ledger (discreteCarrier Λ)) (k : Λ)
    (s : LedgerPostingAdjacency.Side) : Recognition.Ledger (discreteCarrier Λ) :=
  match s with
  | .debit => { debit := fun i => if i = k then L.debit i - 1 else L.debit i
                credit := L.credit }
  | .credit => { debit := L.debit
                 credit := fun i => if i = k then L.credit i - 1 else L.credit i }

theorem postAt_predOf (L : Recognition.Ledger (discreteCarrier Λ)) (k : Λ)
    (s : LedgerPostingAdjacency.Side)
    (hpos : match s with | .debit => 0 < L.debit k | .credit => 0 < L.credit k) :
    postAt (predOf L k s) k s = L := by
  cases s with
  | debit =>
    apply ledger_ext
    · intro i
      by_cases hik : i = k
      · subst i
        have h1 : (postAt (predOf L k .debit) k .debit).debit k
            = (predOf L k .debit).debit k + 1 := if_pos rfl
        have h2 : (predOf L k .debit).debit k = L.debit k - 1 := if_pos rfl
        have h3 : (postAt (predOf L k .debit) k .debit).credit k
            = (predOf L k .debit).credit k := rfl
        show (postAt (predOf L k .debit) k .debit).debit k = L.debit k
        rw [h1, h2]
        omega
      · have h1 : (postAt (predOf L k .debit) k .debit).debit i
            = (predOf L k .debit).debit i := if_neg hik
        have h2 : (predOf L k .debit).debit i = L.debit i := if_neg hik
        show (postAt (predOf L k .debit) k .debit).debit i = L.debit i
        rw [h1, h2]
    · intro i
      show (postAt (predOf L k .debit) k .debit).credit i = L.credit i
      rfl
  | credit =>
    apply ledger_ext
    · intro i
      show (postAt (predOf L k .credit) k .credit).debit i = L.debit i
      rfl
    · intro i
      by_cases hik : i = k
      · subst i
        have h1 : (postAt (predOf L k .credit) k .credit).credit k
            = (predOf L k .credit).credit k + 1 := if_pos rfl
        have h2 : (predOf L k .credit).credit k = L.credit k - 1 := if_pos rfl
        show (postAt (predOf L k .credit) k .credit).credit k = L.credit k
        rw [h1, h2]
        omega
      · have h1 : (postAt (predOf L k .credit) k .credit).credit i
            = (predOf L k .credit).credit i := if_neg hik
        have h2 : (predOf L k .credit).credit i = L.credit i := if_neg hik
        show (postAt (predOf L k .credit) k .credit).credit i = L.credit i
        rw [h1, h2]

theorem predOf_nonneg {L : Recognition.Ledger (discreteCarrier Λ)}
    (hnn : ∀ i, 0 ≤ L.debit i ∧ 0 ≤ L.credit i) (k : Λ)
    (s : LedgerPostingAdjacency.Side)
    (hpos : match s with | .debit => 0 < L.debit k | .credit => 0 < L.credit k) :
    ∀ i, 0 ≤ (predOf L k s).debit i ∧ 0 ≤ (predOf L k s).credit i := by
  intro i
  cases s with
  | debit =>
    by_cases hik : i = k
    · subst i
      have hd : (predOf L k .debit).debit k = L.debit k - 1 := if_pos rfl
      have hc : (predOf L k .debit).credit k = L.credit k := rfl
      rw [hd, hc]
      have hk := hnn k
      omega
    · have hd : (predOf L k .debit).debit i = L.debit i := if_neg hik
      have hc : (predOf L k .debit).credit i = L.credit i := rfl
      rw [hd, hc]
      exact hnn i
  | credit =>
    by_cases hik : i = k
    · subst i
      have hd : (predOf L k .credit).debit k = L.debit k := rfl
      have hc : (predOf L k .credit).credit k = L.credit k - 1 := if_pos rfl
      rw [hd, hc]
      have hk := hnn k
      omega
    · have hd : (predOf L k .credit).debit i = L.debit i := rfl
      have hc : (predOf L k .credit).credit i = L.credit i := if_neg hik
      rw [hd, hc]
      exact hnn i

/-- The predecessor has strictly smaller mass. -/
theorem mass_predOf_lt {L : Recognition.Ledger (discreteCarrier Λ)}
    (hnn : ∀ i, 0 ≤ L.debit i ∧ 0 ≤ L.credit i) (k : Λ)
    (s : LedgerPostingAdjacency.Side)
    (hpos : match s with | .debit => 0 < L.debit k | .credit => 0 < L.credit k) :
    mass (predOf L k s) < mass L := by
  cases s with
  | debit =>
    have hper : ∀ i ∈ Finset.univ.erase k,
        Int.natAbs ((predOf L k .debit).debit i) + Int.natAbs ((predOf L k .debit).credit i)
          = Int.natAbs (L.debit i) + Int.natAbs (L.credit i) := by
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      have hd : (predOf L k .debit).debit i = L.debit i := if_neg hik
      have hc : (predOf L k .debit).credit i = L.credit i := rfl
      rw [hd, hc]
    have hsplit₁ : mass (predOf L k .debit)
        = (Int.natAbs ((predOf L k .debit).debit k) + Int.natAbs ((predOf L k .debit).credit k))
          + ∑ i ∈ Finset.univ.erase k,
            (Int.natAbs ((predOf L k .debit).debit i) + Int.natAbs ((predOf L k .debit).credit i)) := by
      show (∑ i : Λ, (Int.natAbs ((predOf L k .debit).debit i)
            + Int.natAbs ((predOf L k .debit).credit i))) = _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have hsplit₂ : mass L
        = (Int.natAbs (L.debit k) + Int.natAbs (L.credit k))
          + ∑ i ∈ Finset.univ.erase k, (Int.natAbs (L.debit i) + Int.natAbs (L.credit i)) := by
      show (∑ i : Λ, (Int.natAbs (L.debit i) + Int.natAbs (L.credit i))) = _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have hkk : (predOf L k .debit).debit k = L.debit k - 1 := if_pos rfl
    have hkc : (predOf L k .debit).credit k = L.credit k := rfl
    rw [hsplit₁, Finset.sum_congr rfl hper, hsplit₂, hkk, hkc]
    have hc : 0 < L.debit k := hpos
    have h1 : Int.natAbs (L.debit k - 1) = Int.natAbs (L.debit k) - 1 := by
      omega
    rw [h1]
    omega
  | credit =>
    have hper : ∀ i ∈ Finset.univ.erase k,
        Int.natAbs ((predOf L k .credit).debit i) + Int.natAbs ((predOf L k .credit).credit i)
          = Int.natAbs (L.debit i) + Int.natAbs (L.credit i) := by
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      have hd : (predOf L k .credit).debit i = L.debit i := rfl
      have hc : (predOf L k .credit).credit i = L.credit i := if_neg hik
      rw [hd, hc]
    have hsplit₁ : mass (predOf L k .credit)
        = (Int.natAbs ((predOf L k .credit).debit k) + Int.natAbs ((predOf L k .credit).credit k))
          + ∑ i ∈ Finset.univ.erase k,
            (Int.natAbs ((predOf L k .credit).debit i) + Int.natAbs ((predOf L k .credit).credit i)) := by
      show (∑ i : Λ, (Int.natAbs ((predOf L k .credit).debit i)
            + Int.natAbs ((predOf L k .credit).credit i))) = _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have hsplit₂ : mass L
        = (Int.natAbs (L.debit k) + Int.natAbs (L.credit k))
          + ∑ i ∈ Finset.univ.erase k, (Int.natAbs (L.debit i) + Int.natAbs (L.credit i)) := by
      show (∑ i : Λ, (Int.natAbs (L.debit i) + Int.natAbs (L.credit i))) = _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have hkk : (predOf L k .credit).debit k = L.debit k := rfl
    have hkc : (predOf L k .credit).credit k = L.credit k - 1 := if_pos rfl
    rw [hsplit₁, Finset.sum_congr rfl hper, hsplit₂, hkk, hkc]
    have hc : 0 < L.credit k := hpos
    have h1 : Int.natAbs (L.credit k - 1) = Int.natAbs (L.credit k) - 1 := by
      omega
    rw [h1]
    omega

/-- **THEOREM (the dynamics reaches every nonnegative ledger).**  From the balanced zero
ledger, every ledger with nonnegative columns is reachable by a finite sequence of posting
steps.  Proof: mass induction through the predecessor, which is legal because a nonzero
nonnegative ledger is the post of its predecessor.  Scope: this is forward reachability, not
ergodicity; a posting step only ever raises a column, so there is no return to lower-mass
states and no ledger with a negative column is reachable.  What the theorem supports is that
the dynamics excludes no nonnegative state, and therefore cannot force any restriction on the
imbalances of the states it produces. -/
theorem postReachable_zero_of_nonneg :
    ∀ N : ℕ, ∀ L : Recognition.Ledger (discreteCarrier Λ),
      mass L ≤ N → (∀ i, 0 ≤ L.debit i ∧ 0 ≤ L.credit i) →
      PostReachable zeroLedger L := by
  intro N
  induction N with
  | zero =>
    intro L hm _
    have hz : mass L = 0 := Nat.le_zero.mp hm
    rw [eq_zeroLedger_of_mass_zero hz]
    exact PostReachable.refl _
  | succ N IH =>
    intro L hm hnn
    by_cases hne : L = zeroLedger
    · subst hne
      exact PostReachable.refl _
    · obtain ⟨k, hk⟩ := exists_pos_of_ne_zero hnn hne
      cases hk with
      | inl hpos =>
        have hlt : mass (predOf L k .debit) < mass L := mass_predOf_lt hnn k .debit hpos
        rw [← postAt_predOf L k .debit hpos]
        exact PostReachable.step k .debit
          (IH (predOf L k .debit) (by omega) (predOf_nonneg hnn k .debit hpos))
      | inr hpos =>
        have hlt : mass (predOf L k .credit) < mass L := mass_predOf_lt hnn k .credit hpos
        rw [← postAt_predOf L k .credit hpos]
        exact PostReachable.step k .credit
          (IH (predOf L k .credit) (by omega) (predOf_nonneg hnn k .credit hpos))

/-! ## §2. Every imbalance is realized from balance, by an explicit schedule -/

/-- **THEOREM (every integer imbalance is the phi of a reachable ledger).**  Given any integer
configuration `φ`, the ledger with `debit = max φ 0`, `credit = max (-φ) 0` is nonnegative, has
`phi = φ`, and is reachable from balance by `postReachable_zero_of_nonneg`.  The dynamics
produces every imbalance pattern, the incidence-reading and index-reading ones included. -/
theorem imbalance_realized (φ : Λ → ℤ) :
    ∃ L : Recognition.Ledger (discreteCarrier Λ),
      (∀ i, 0 ≤ L.debit i ∧ 0 ≤ L.credit i) ∧
      PostReachable zeroLedger L ∧ Recognition.phi L = φ := by
  refine ⟨{ debit := fun i => max (φ i) 0, credit := fun i => max (-(φ i)) 0 }, ?_, ?_, ?_⟩
  · intro i
    exact ⟨le_max_right _ _, le_max_right _ _⟩
  · exact postReachable_zero_of_nonneg (mass _) _ (Nat.le_refl _)
      (fun i => ⟨le_max_right _ _, le_max_right _ _⟩)
  · funext i
    show max (φ i) 0 - max (-(φ i)) 0 = φ i
    by_cases h : 0 ≤ φ i
    · rw [max_eq_left h, max_eq_right (by omega : -(φ i) ≤ 0)]
      omega
    · rw [max_eq_right (by omega : φ i ≤ 0), max_eq_left (by omega : 0 ≤ -(φ i))]
      omega

/-- A posting schedule on the carrier: at each tick, either an idle tick or a named account
posting on a named side.  This is the free variable of the dynamics, the one thing the ledger
structure does not constrain. -/
abbrev Schedule (Λ : Type) := ℕ → Option (Λ × LedgerPostingAdjacency.Side)

/-- Run a schedule forward from an initial ledger; idle ticks leave the state unchanged. -/
def runSchedule (L₀ : Recognition.Ledger (discreteCarrier Λ)) (sched : Schedule Λ) :
    ℕ → Recognition.Ledger (discreteCarrier Λ)
  | 0 => L₀
  | (t + 1) => match sched t with
    | none => runSchedule L₀ sched t
    | some (k, s) => postAt (runSchedule L₀ sched t) k s

/-- The imbalance after `t` ticks of a schedule from balance. -/
def phiAfter (sched : Schedule Λ) (t : ℕ) : Λ → ℤ :=
  Recognition.phi (runSchedule zeroLedger sched t)

/-- Runs agree while their schedules agree: only ticks below `t` matter at tick `t`. -/
theorem runSchedule_eq_of_agree_below (L₀ : Recognition.Ledger (discreteCarrier Λ))
    {sched₁ sched₂ : Schedule Λ} {t : ℕ}
    (h : ∀ u, u < t → sched₁ u = sched₂ u) :
    runSchedule L₀ sched₁ t = runSchedule L₀ sched₂ t := by
  induction t with
  | zero => rfl
  | succ u IH =>
    have hu : sched₁ u = sched₂ u := h u (Nat.lt_succ_self u)
    have hpre : runSchedule L₀ sched₁ u = runSchedule L₀ sched₂ u :=
      IH (fun w hw => h w (Nat.lt_trans hw (Nat.lt_succ_self u)))
    simp only [runSchedule, hu, hpre]

/-- Every run state is reachable: the run is one presentation of reachability. -/
theorem postReachable_run (sched : Schedule Λ) (t : ℕ) :
    PostReachable zeroLedger (runSchedule zeroLedger sched t) := by
  induction t with
  | zero => exact PostReachable.refl _
  | succ u IH =>
    simp only [runSchedule]
    cases hs : sched u with
    | none => exact IH
    | some instr =>
      obtain ⟨k, s⟩ := instr
      exact PostReachable.step k s IH

/-- Every reachable state is reached by some schedule at some tick. -/
theorem exists_schedule_of_reachable {L : Recognition.Ledger (discreteCarrier Λ)}
    (h : PostReachable zeroLedger L) :
    ∃ (sched : Schedule Λ) (t : ℕ), runSchedule zeroLedger sched t = L := by
  induction h with
  | refl => exact ⟨fun _ => none, 0, rfl⟩
  | step k s _ IH =>
    obtain ⟨sched, t, ht⟩ := IH
    refine ⟨Function.update sched t (some (k, s)), t + 1, ?_⟩
    have hagree : ∀ u, u < t → Function.update sched t (some (k, s)) u = sched u :=
      fun u hu => Function.update_of_ne (Nat.ne_of_lt hu) _ _
    have hpre := runSchedule_eq_of_agree_below zeroLedger hagree
    simp only [runSchedule, Function.update_self, hpre, ht]

/-- **THEOREM (every imbalance is realized by an explicit schedule).**  The schedule form of
`imbalance_realized`: there is a schedule and a tick at which the run's imbalance from balance
is exactly `φ`. -/
theorem imbalance_realized_by_schedule (φ : Λ → ℤ) :
    ∃ (sched : Schedule Λ) (t : ℕ), phiAfter sched t = φ := by
  obtain ⟨L, _, hreach, hphi⟩ := imbalance_realized φ
  obtain ⟨sched, t, ht⟩ := exists_schedule_of_reachable hreach
  exact ⟨sched, t, by
    show Recognition.phi (runSchedule zeroLedger sched t) = φ
    rw [ht]
    exact hphi⟩

/-! ## §3. The dynamics produces the countermodel, on the actual posting alphabet -/

/-- The incidence imbalance on a complex's posting alphabet: one quantum on every proper edge
letter, nothing elsewhere.  This is the `phi` of the fourth arc's countermodel
`incidencePhiLattice`, exhibited as a target configuration for the dynamics. -/
def incidenceImbalance {B : ℕ} (K : BoundedComplex B) : PostingAlphabet K → ℤ
  | Sum.inr (Sum.inl e) => if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then 1 else 0
  | _ => 0

/-- **THEOREM (the dynamics produces the incidence-reading countermodel).**  On every complex's
posting alphabet there is a ledger, reachable from balance, whose imbalance is exactly the
incidence imbalance; and that ledger lifts, with any nonnegative magnitude function whatever,
to a `DualEntryStrainState` with that imbalance and that magnitude.  The countermodel state the
counts-only premise exists to exclude is not an edge case the dynamics fails to generate: the
dynamics generates it from balance, one posting at a time, and the magnitude factor rides
along for free because the posting step never touches it.  Scope, stated exactly: the
incidence imbalance is `1` on proper edge letters and `0` on every other letter, so the
produced state is counts-only exactly when the complex's edges are all proper or all loops,
and is a countermodel exactly when the complex carries at least one proper edge and at least
one loop.  The `∀ K` statement holds on every complex; "countermodel" describes the mixed
edge-kind case.  §4's failing schedule on `twoBridges` is a witness of a different family: its
imbalance is `1` on one edge letter and `0` on the other, not the incidence imbalance. -/
theorem dynamics_produces_incidence_countermodel {B : ℕ} (K : BoundedComplex B)
    (magv : PostingAlphabet K → ℝ) (hnn : ∀ a, 0 ≤ magv a) :
    ∃ (L : Recognition.Ledger (discreteCarrier (PostingAlphabet K))),
      PostReachable zeroLedger L ∧
      ∃ S : DualEntryStrainState (PostingAlphabet K),
        S.phi = incidenceImbalance K ∧ S.mag = magv := by
  obtain ⟨L, _, hreach, hphi⟩ := imbalance_realized (incidenceImbalance K)
  refine ⟨L, hreach, ?_⟩
  have hflux : ∀ i, |Recognition.phi L i| ≤ 1 := by
    intro i
    have hi := congrFun hphi i
    rw [hi]
    cases i with
    | inl v => simp [incidenceImbalance]
    | inr rest =>
      cases rest with
      | inl e =>
        by_cases h : (K.edgeVerts e).1 ≠ (K.edgeVerts e).2
        · simp [incidenceImbalance, h]
        · simp [incidenceImbalance, h]
      | inr t => simp [incidenceImbalance]
  refine ⟨DualEntryStrainState.ofLedger L magv hnn hflux, ?_, rfl⟩
  show (DualEntryStrainState.ofLedger L magv hnn hflux).phi = incidenceImbalance K
  rw [DualEntryStrainState.phi_ofLedger L magv hnn hflux]
  exact hphi

/-! ## §4. The premise, named at the only layer where it can live: the schedule -/

/-- An imbalance configuration is counts-only (kind-constant) on a complex's posting alphabet:
constant on vertex letters, constant on edge letters, constant on tetrahedron letters.  This is
the imbalance-level content of the third arc's `ChargesCountsOnly`, stated directly on the
charge the dynamics produces. -/
def CountsOnlyImbalance {B : ℕ} (K : BoundedComplex B) (χ : PostingAlphabet K → ℤ) : Prop :=
  ∃ cV cE cT : ℤ,
    (∀ v : Fin K.nV, χ (Sum.inl v) = cV) ∧
    (∀ e : Fin K.nE, χ (Sum.inr (Sum.inl e)) = cE) ∧
    (∀ t : Fin K.nT, χ (Sum.inr (Sum.inr t)) = cT)

/-- **The named premise, at the dynamics layer.**  A posting schedule is counts-only if the
imbalance it produces from balance is kind-constant at every tick.  Three arcs have now shown
that nothing below this premise forces it: not the cost-function space, not the lattice state
type, and not the dynamics, which reaches every imbalance.  What remains is exactly this: a law
about the actual schedule the universe executes.  It is a physical premise about one run, not
a theorem about the space of runs, and the countermodel below shows it is not forced. -/
def CountsOnlySchedule {B : ℕ} (K : BoundedComplex B) (sched : Schedule (PostingAlphabet K)) :
    Prop :=
  ∀ t : ℕ, CountsOnlyImbalance K (phiAfter sched t)

/-- The posted letter of the countermodel schedule: edge 0 of the two-bridge witness. -/
def cmEdge0 : PostingAlphabet twoBridges := Sum.inr (Sum.inl ⟨0, by decide⟩)

/-- The other edge letter of the two-bridge witness. -/
def cmEdge1 : PostingAlphabet twoBridges := Sum.inr (Sum.inl ⟨1, by decide⟩)

theorem cmEdge1_ne_cmEdge0 : cmEdge1 ≠ cmEdge0 := by
  intro hh
  have h2 := Sum.inr.inj hh
  have h3 := Sum.inl.inj h2
  exact absurd h3 (by decide)

/-- The one-post countermodel schedule on the two-bridge witness: a single debit on edge
letter 0 at tick 0, idle forever after.  It is a legal run of the posting dynamics. -/
def countermodelSchedule : Schedule (PostingAlphabet twoBridges)
  | 0 => some (cmEdge0, .debit)
  | _ => none

/-- **THEOREM (the premise is not forced by the dynamics).**  The countermodel schedule's
imbalance after one tick is `1` on edge letter 0 and `0` on edge letter 1, two letters of the
same kind.  So a legal run of the posting dynamics produces a not-counts-only charge: no
counts-only law about schedules is derivable from the dynamics. -/
theorem schedule_countermodel_not_countsOnly :
    ¬ CountsOnlySchedule twoBridges countermodelSchedule := by
  intro h
  obtain ⟨_, cE, _, _, hE, _⟩ := h 1
  have hr : runSchedule zeroLedger countermodelSchedule 1
      = postAt zeroLedger cmEdge0 .debit := by
    simp only [runSchedule, countermodelSchedule]
  have h0 : phiAfter countermodelSchedule 1 cmEdge0 = 1 := by
    show Recognition.phi (runSchedule zeroLedger countermodelSchedule 1) cmEdge0 = 1
    rw [hr, phi_postAt_debit_self, phi_zeroLedger]
    omega
  have h1 : phiAfter countermodelSchedule 1 cmEdge1 = 0 := by
    show Recognition.phi (runSchedule zeroLedger countermodelSchedule 1) cmEdge1 = 0
    rw [hr, phi_postAt_ne zeroLedger cmEdge1_ne_cmEdge0 .debit, phi_zeroLedger]
  have hcontra : (1 : ℤ) = 0 := by
    calc (1 : ℤ) = phiAfter countermodelSchedule 1 cmEdge0 := h0.symm
      _ = cE := hE ⟨0, by decide⟩
      _ = phiAfter countermodelSchedule 1 cmEdge1 := (hE ⟨1, by decide⟩).symm
      _ = 0 := h1
  exact one_ne_zero hcontra

/-! ## §5. The three-layer verdict, the index, and what the measure track gets -/

/-- **THEOREM (the ledger forces counts-only at no layer examined).**  The conjunction of the
three arcs' negative results: the letter-cost space admits a not-counts-only charge (third
arc), the lattice state type admits a not-counts-only induced charge (fourth arc), and the
posting dynamics runs to a not-counts-only imbalance from balance (this arc).  Counts-only is
therefore not forced at any of these three named layers.  Whether a deeper layer than the
posting step exists and could force it is outside what this theorem says: the library carries
no such layer, and the remaining live form of the premise is a law about the actual schedule,
`CountsOnlySchedule`, whose satisfaction by nature's run is a physical premise rather than a
theorem about the space of runs. -/
theorem ledger_forces_countsOnly_at_no_layer :
    (¬ ChargesCountsOnly (incidenceCost 1)) ∧
    (¬ ChargesCountsOnly (incidencePhiLattice.toLetterCost)) ∧
    (∃ (sched : Schedule (PostingAlphabet twoBridges)),
      ¬ CountsOnlySchedule twoBridges sched) :=
  ⟨chargesCountsOnly_excludes_incidence 1 one_ne_zero,
   incidencePhiLattice_not_countsOnly,
   ⟨countermodelSchedule, schedule_countermodel_not_countsOnly⟩⟩

/-- The index of the fifth arc.  Each flag is the Prop form of the corresponding theorem, so
`index_audit` pins them together.  The fourth flag is the premise in its strongest schedule
form: "every posting schedule on the two-bridge witness is counts-only."  The audit refutes
that Prop with the exhibited countermodel schedule, so the negative in the index is a real
theorem, not a constant. -/
structure Index where
  dynamics_reaches_every_nonneg_ledger : Prop
  every_imbalance_realized_by_schedule : Prop
  dynamics_produces_incidence_countermodel : Prop
  dynamics_forces_countsOnly_schedule : Prop
  premise_named_at : String

def index : Index where
  dynamics_reaches_every_nonneg_ledger :=
    ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ] (L : Recognition.Ledger (discreteCarrier Λ)),
      (∀ i, 0 ≤ L.debit i ∧ 0 ≤ L.credit i) → PostReachable zeroLedger L
  every_imbalance_realized_by_schedule :=
    ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ] (φ : Λ → ℤ),
      ∃ (sched : Schedule Λ) (t : ℕ), phiAfter sched t = φ
  dynamics_produces_incidence_countermodel :=
    ∀ {B : ℕ} (K : BoundedComplex B) (magv : PostingAlphabet K → ℝ) (hnn : ∀ a, 0 ≤ magv a),
      ∃ (L : Recognition.Ledger (discreteCarrier (PostingAlphabet K))),
        PostReachable zeroLedger L ∧
        ∃ S : DualEntryStrainState (PostingAlphabet K),
          S.phi = incidenceImbalance K ∧ S.mag = magv
  dynamics_forces_countsOnly_schedule :=
    ∀ sched : Schedule (PostingAlphabet twoBridges), CountsOnlySchedule twoBridges sched
  premise_named_at := "CountsOnlySchedule: a law about the actual posting run, not derivable"

/-- The audit pinning the index flags to their theorems.  The fourth conjunct refutes the
universal schedule law using the one-post countermodel of §4. -/
theorem index_audit : index.dynamics_reaches_every_nonneg_ledger ∧
    index.every_imbalance_realized_by_schedule ∧
    index.dynamics_produces_incidence_countermodel ∧
    ¬ index.dynamics_forces_countsOnly_schedule := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Λ _ _ L hnn
    exact postReachable_zero_of_nonneg (mass L) L (Nat.le_refl _) hnn
  · intro Λ _ _ φ
    exact imbalance_realized_by_schedule φ
  · intro B K magv hnn
    exact dynamics_produces_incidence_countermodel K magv hnn
  · intro h
    exact schedule_countermodel_not_countsOnly (h countermodelSchedule)

end

#print axioms postReachable_zero_of_nonneg
#print axioms imbalance_realized
#print axioms imbalance_realized_by_schedule
#print axioms dynamics_produces_incidence_countermodel
#print axioms schedule_countermodel_not_countsOnly
#print axioms ledger_forces_countsOnly_at_no_layer
#print axioms index_audit

end Gap2DynamicsKindRule
end SevenGaps
end Gravity
end IndisputableMonolith
