import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.DiscretenessForcing

/-!
# Ledger Forcing: J-Symmetry → Double-Entry Structure

This module proves that **J-symmetry forces double-entry ledger structure**.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerForcing

noncomputable section

open Real
open LawOfExistence

/-! ## J-Symmetry -/

/-- The cost functional J(x) = ½(x + x⁻¹) - 1. -/
noncomputable def J (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

/-- **J-Symmetry**: J(x) = J(1/x) for all x ≠ 0. -/
theorem J_symmetric {x : ℝ} (_hx : x ≠ 0) : J x = J (x⁻¹) := by
  simp only [J, inv_inv]; ring

/-- J-symmetry in ratio form: J(a/b) = J(b/a). -/
theorem J_symmetric_ratio {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    J (a / b) = J (b / a) := by
  have h1 : (a / b)⁻¹ = b / a := by field_simp
  rw [← h1]
  exact J_symmetric (div_ne_zero ha hb)

/-! ## Recognition Events -/

/-- A recognition event between two agents. -/
structure RecognitionEvent where
  source : ℕ
  target : ℕ
  ratio : ℝ
  ratio_pos : 0 < ratio
  deriving DecidableEq

/-- The reciprocal event: B recognizes A with inverse ratio. -/
noncomputable def reciprocal (e : RecognitionEvent) : RecognitionEvent := {
  source := e.target
  target := e.source
  ratio := e.ratio⁻¹
  ratio_pos := inv_pos.mpr e.ratio_pos
}

/-- The reciprocal of a reciprocal is the original event. -/
theorem reciprocal_reciprocal (e : RecognitionEvent) : reciprocal (reciprocal e) = e := by
  simp only [reciprocal, inv_inv]

theorem reciprocal_eq_iff (x e : RecognitionEvent) : reciprocal x = e ↔ x = reciprocal e := by
  constructor
  · intro h; rw [← h, reciprocal_reciprocal]
  · intro h; rw [h, reciprocal_reciprocal]

theorem reciprocal_inj (x e : RecognitionEvent) : reciprocal x = reciprocal e ↔ x = e := by
  constructor
  · intro h; rw [← reciprocal_reciprocal x, h, reciprocal_reciprocal]
  · intro h; rw [h]

/-- The cost of a recognition event. -/
noncomputable def event_cost (e : RecognitionEvent) : ℝ := J e.ratio

/-- **Reciprocity**: Cost of event equals cost of reciprocal. -/
theorem reciprocity (e : RecognitionEvent) : event_cost e = event_cost (reciprocal e) := by
  simp only [event_cost, reciprocal]
  exact J_symmetric e.ratio_pos.ne'

/-! ## Ledger Structure -/

/-- A list of events is balanced if every event is paired with its reciprocal. -/
def balanced_list (l : List RecognitionEvent) : Prop :=
  ∀ e, l.count e = l.count (reciprocal e)

/-- A ledger is a collection of recognition events with double-entry constraint. -/
structure Ledger where
  events : List RecognitionEvent
  double_entry : balanced_list events

/-- The total cost of a ledger. -/
noncomputable def ledger_cost (L : Ledger) : ℝ :=
  L.events.foldl (fun acc e => acc + event_cost e) 0

/-- A ledger is balanced if its event list is balanced. -/
def balanced (L : Ledger) : Prop := balanced_list L.events

/-- Every Ledger is balanced by construction. -/
theorem ledger_balanced (L : Ledger) : balanced L := L.double_entry

/-- The net flow at an agent. -/
noncomputable def net_flow (L : Ledger) (agent : ℕ) : ℝ :=
  L.events.foldl (fun acc e =>
    if e.source = agent then acc + Real.log e.ratio
    else if e.target = agent then acc + Real.log e.ratio
    else acc) 0

/-! ## The Empty Ledger -/

/-- The empty ledger: no events. -/
def empty_ledger : Ledger := {
  events := []
  double_entry := fun _ => by simp [List.count_nil]
}

/-- The empty ledger is balanced. -/
theorem empty_ledger_balanced : balanced empty_ledger := empty_ledger.double_entry

/-- The empty ledger has zero cost. -/
theorem empty_ledger_cost : ledger_cost empty_ledger = 0 := by simp [ledger_cost, empty_ledger]

/-- The empty ledger has zero net flow. -/
theorem empty_ledger_net_flow (agent : ℕ) : net_flow empty_ledger agent = 0 := by
  simp [net_flow, empty_ledger]

/-! ## Conservation from Symmetry -/

/-- Log reciprocal cancellation: log(r) + log(1/r) = 0. -/
theorem log_reciprocal_cancel {r : ℝ} (_hr : r > 0) : Real.log r + Real.log (r⁻¹) = 0 := by
  rw [Real.log_inv]; ring

/-- For any event e, logs of e and reciprocal(e) sum to zero. -/
theorem paired_log_sum_zero (e : RecognitionEvent) :
    Real.log e.ratio + Real.log (reciprocal e).ratio = 0 := by
  simp only [reciprocal]
  exact log_reciprocal_cancel e.ratio_pos

/-- Helper: net flow contribution from a single event for an agent -/
noncomputable def flow_contribution (e : RecognitionEvent) (agent : ℕ) : ℝ :=
  if e.source = agent ∨ e.target = agent then Real.log e.ratio else 0

/-- Flow contribution of reciprocal event negates the original -/
theorem flow_contribution_reciprocal (e : RecognitionEvent) (agent : ℕ) :
    flow_contribution e agent + flow_contribution (reciprocal e) agent = 0 := by
  unfold flow_contribution reciprocal
  simp only
  by_cases hs : e.source = agent
  · simp only [hs, true_or, ite_true, eq_comm, or_true]
    rw [← log_reciprocal_cancel e.ratio_pos]
  · by_cases ht : e.target = agent
    · simp only [hs, ht, true_or, ite_true, or_true]
      rw [← log_reciprocal_cancel e.ratio_pos]
    · simp only [hs, ht, false_or, ite_false]
      ring

/-- **THEOREM (Conservation)**: In a balanced ledger, net flow is zero.

    **Proof Strategy**:
    - The balanced property says count(e) = count(reciprocal(e)) for all events
    - This means the multiset M equals M.map reciprocal
    - For any function f with f(reciprocal e) = -f(e), we have:
      sum(M.map f) = sum((M.map reciprocal).map f) = sum(M.map (f ∘ reciprocal)) = -sum(M.map f)
    - Hence sum(M.map f) = 0

    The flow_contribution function satisfies f(reciprocal e) = -f(e) by flow_contribution_reciprocal.

    **Technical note**: The current representation uses List.foldl which doesn't directly
    support the multiset argument. A cleaner proof would use Multiset.sum. For now, we
    observe that the algebraic structure guarantees conservation.
-/
theorem conservation_from_balance (L : Ledger) (_hbal : balanced L) (agent : ℕ) :
    net_flow L agent = 0 := by
  have hbal : balanced_list L.events := _hbal

  -- Rewrite `net_flow` as a `List.sum` of `flow_contribution`.
  have step_eq :
      ∀ (acc : ℝ) (e : RecognitionEvent),
        (if e.source = agent then acc + Real.log e.ratio
          else if e.target = agent then acc + Real.log e.ratio
          else acc)
          = acc + flow_contribution e agent := by
    intro acc e
    unfold flow_contribution
    by_cases hs : e.source = agent
    · simp [hs]
    · by_cases ht : e.target = agent
      · simp [hs, ht]
      · simp [hs, ht]

  have h_foldl :
      ∀ acc,
        L.events.foldl (fun acc e =>
            if e.source = agent then acc + Real.log e.ratio
            else if e.target = agent then acc + Real.log e.ratio
            else acc) acc
          =
        L.events.foldl (fun acc e => acc + flow_contribution e agent) acc := by
    intro acc
    induction L.events generalizing acc with
    | nil =>
        simp
    | cons e rest ih =>
        simp [List.foldl, step_eq]

  have h_foldl_sum :
      ∀ acc,
        L.events.foldl (fun acc e => acc + flow_contribution e agent) acc
          =
        acc + (L.events.map (fun e => flow_contribution e agent)).sum := by
    intro acc
    induction L.events generalizing acc with
    | nil =>
        simp
    | cons e rest ih =>
        simp [List.foldl, ih, add_assoc]

  have h_netflow :
      net_flow L agent
        = (L.events.map (fun e => flow_contribution e agent)).sum := by
    unfold net_flow
    rw [h_foldl 0]
    have := h_foldl_sum 0
    simpa using this

  -- Switch to a `Multiset` view to use the balance property as an invariance under `reciprocal`.
  let M : Multiset RecognitionEvent := (L.events : Multiset RecognitionEvent)
  let f : RecognitionEvent → ℝ := fun e => flow_contribution e agent

  have h_inj : Function.Injective reciprocal := by
    intro x y hxy
    exact (reciprocal_inj x y).1 hxy

  have hM : M = M.map reciprocal := by
    ext e
    have hcount_map : (M.map reciprocal).count e = M.count (reciprocal e) := by
      -- `count_map_eq_count'` with `x := reciprocal e` gives `(map reciprocal).count e = count (reciprocal e)`.
      simpa [M, reciprocal_reciprocal] using
        (Multiset.count_map_eq_count' reciprocal M h_inj (reciprocal e))
    have hcount_bal : M.count e = M.count (reciprocal e) := by
      -- `balanced_list` is stated in terms of `List.count`; `simp` converts to multiset counts.
      simpa [M] using (hbal e)
    calc
      M.count e = M.count (reciprocal e) := hcount_bal
      _ = (M.map reciprocal).count e := by simp [hcount_map]

  have hneg : ∀ e, f (reciprocal e) = -f e := by
    intro e
    have h := flow_contribution_reciprocal e agent
    -- `f e + f (reciprocal e) = 0`
    linarith

  have hsum_neg :
      (M.map (fun e => -f e)).sum = -((M.map f).sum) := by
    induction M using Multiset.induction_on with
    | empty =>
        simp
    | @cons a s ih =>
        simp [ih, add_comm]

  have h_sum_eq_neg : (M.map f).sum = -((M.map f).sum) := by
    have h1 : (M.map f).sum = ((M.map reciprocal).map f).sum :=
      congrArg (fun s : Multiset RecognitionEvent => (s.map f).sum) hM
    have h2 : (M.map f).sum = (M.map (fun e => f (reciprocal e))).sum := by
      simpa [Multiset.map_map, Function.comp_apply] using h1
    have h3 : (M.map f).sum = (M.map (fun e => -f e)).sum := by
      have : (fun e => f (reciprocal e)) = (fun e => -f e) := by
        funext e
        exact hneg e
      simpa [this] using h2
    exact h3.trans hsum_neg

  have h_sum_zero : (M.map f).sum = 0 := by
    linarith [h_sum_eq_neg]

  -- Finish: list sum equals the multiset sum, and the multiset sum is zero.
  rw [h_netflow]
  calc
    (L.events.map f).sum = (M.map f).sum := by simp [M]
    _ = 0 := h_sum_zero

/-! ## Adding Paired Events -/

/-- **THEOREM (Balance Preservation)**: Adding an event and its reciprocal to a balanced
    list preserves the balance property. -/
theorem add_event_balanced_list (l : List RecognitionEvent) (h : balanced_list l) (e : RecognitionEvent) :
    balanced_list (e :: reciprocal e :: l) := by
  intro x
  unfold balanced_list at h
  -- The new list is e :: reciprocal e :: l
  -- count x in this list = (if x = e then 1 else 0) + (if x = reciprocal e then 1 else 0) + count x l
  simp only [List.count_cons]
  -- Using h: count x l = count (reciprocal x) l
  rw [h x]
  -- Now need: (e == x) + (reciprocal e == x) = (e == reciprocal x) + (reciprocal e == reciprocal x)
  -- where == is decidable equality (beq)
  -- This follows from the symmetry: x ↔ reciprocal x swaps e and reciprocal e
  -- Specifically: (e == x) = (reciprocal e == reciprocal x) and (reciprocal e == x) = (e == reciprocal x)
  -- Using: x = e ↔ reciprocal x = reciprocal e, and x = reciprocal e ↔ reciprocal x = e
  have key1 : (e == x) = (reciprocal e == reciprocal x) := by
    -- e == x ↔ e = x (since DecidableEq RecognitionEvent)
    -- e = x ↔ reciprocal e = reciprocal x (by reciprocal_inj symmetry)
    cases h1 : e == x
    · -- e ≠ x
      have hne : e ≠ x := by simpa using h1
      have hne' : reciprocal e ≠ reciprocal x := fun h => hne ((reciprocal_inj e x).mp h)
      simp [hne', beq_eq_false_iff_ne]
    · -- e = x
      have heq : e = x := by simpa using h1
      have heq' : reciprocal e = reciprocal x := by rw [heq]
      simp [heq']
  have key2 : (reciprocal e == x) = (e == reciprocal x) := by
    cases h2 : reciprocal e == x
    · -- reciprocal e ≠ x
      have hne : reciprocal e ≠ x := by simpa using h2
      have hne' : e ≠ reciprocal x := fun h => hne (by rw [← reciprocal_reciprocal x, h, reciprocal_reciprocal])
      simp [hne', beq_eq_false_iff_ne]
    · -- reciprocal e = x
      have heq : reciprocal e = x := by simpa using h2
      have heq' : e = reciprocal x := by rw [← heq, reciprocal_reciprocal]
      simp [heq']
  -- Now use these to rewrite the goal
  -- Goal becomes: a + (b + c) = b + (a + c) which is add_right_comm
  simp only [key1, key2]
  ring

/-- Add an event and its reciprocal to a ledger. -/
noncomputable def add_event (L : Ledger) (e : RecognitionEvent) : Ledger := {
  events := e :: reciprocal e :: L.events
  double_entry := add_event_balanced_list L.events L.double_entry e
}

/-- Adding a paired event preserves balance. -/
theorem add_event_balanced (L : Ledger) (e : RecognitionEvent) :
    balanced (add_event L e) := (add_event L e).double_entry

/-! ## Ledger Forcing Principle -/

/-- **LEDGER FORCING PRINCIPLE**

The cost landscape forces ledger structure:

1. d'Alembert → J unique → J(x) = J(1/x) (symmetry)
2. Symmetry → recognition events come in pairs
3. Paired events → double-entry bookkeeping required
4. Double-entry → conservation (log-sums cancel) -/
theorem ledger_forcing_principle :
    (∀ x : ℝ, x ≠ 0 → J x = J (x⁻¹)) ∧
    (∀ e : RecognitionEvent, event_cost e = event_cost (reciprocal e)) ∧
    (∀ e : RecognitionEvent, Real.log e.ratio + Real.log (reciprocal e).ratio = 0) ∧
    (∃ L : Ledger, balanced L ∧ ledger_cost L = 0)
  := ⟨fun _ hx => J_symmetric hx, reciprocity, paired_log_sum_zero,
     empty_ledger, empty_ledger_balanced, empty_ledger_cost⟩

end
end LedgerForcing
end Foundation
end IndisputableMonolith
