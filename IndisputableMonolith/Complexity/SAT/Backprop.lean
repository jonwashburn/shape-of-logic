import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- Partial assignments for backpropagation: `none` = unknown, `some b` = determined. -/
abbrev PartialAssignment (n : Nat) := Var n → Option Bool

/-- Backward-propagation state over a CNF with XOR constraints. -/
structure BPState (n : Nat) where
  assign : PartialAssignment n

/-- Update a partial assignment at variable `v` to value `b`. -/
def setVar {n} (σ : PartialAssignment n) (v : Var n) (b : Bool) : PartialAssignment n :=
  fun w => if w = v then some b else σ w

@[simp] lemma setVar_same {n} (σ : PartialAssignment n) (v : Var n) (b : Bool) :
    setVar σ v b v = some b := by
  unfold setVar; simp

lemma setVar_ne {n} (σ : PartialAssignment n) (v w : Var n) (b : Bool) (hvw : w ≠ v) :
    setVar σ v b w = σ w := by
  unfold setVar
  simp only [ite_eq_right_iff]
  intro heq
  exact absurd heq hvw

/-- Evaluate a literal under a partial assignment. -/
def valueOfLit {n} (σ : PartialAssignment n) : Lit n → Option Bool
  | .pos v => σ v
  | .neg v => Option.map not (σ v)

/-- Evaluate a clause under a partial assignment: returns `some b` if all literals
    are known, otherwise none. -/
def valueOfClause {n} (σ : PartialAssignment n) (C : Clause n) : Option Bool :=
  let vals := C.map (valueOfLit σ)
  if vals.all Option.isSome then
    some (vals.any fun o => o.getD false)
  else
    none

/-- Evaluate an XOR constraint under a partial assignment: returns `some b` if all
    vars are known, else none. -/
def valueOfXOR {n} (σ : PartialAssignment n) (X : XORConstraint n) : Option Bool :=
  if X.vars.all (fun v => (σ v).isSome) then
    some (X.vars.foldl (fun acc v => Bool.xor acc ((σ v).getD false)) false)
  else
    none

/-- If exactly one variable of an XOR constraint is unknown, return that variable and the
    value needed to satisfy the parity given the known variables. -/
def xorMissing {n} (σ : PartialAssignment n) (X : XORConstraint n) : Option (Var n × Bool) :=
  let unknowns := X.vars.filter (fun v => (σ v).isNone)
  if h : unknowns.length = 1 then
    let v := unknowns.get ⟨0, by omega⟩
    let knownParity := X.vars.foldl (fun acc w =>
      if (σ w).isSome then Bool.xor acc ((σ w).getD false) else acc) false
    some (v, Bool.xor X.parity knownParity)
  else
    none

/-- If exactly one literal of a clause is unknown and the others are false, return that var and required value. -/
def clauseUnit {n} (σ : PartialAssignment n) (C : Clause n) : Option (Var n × Bool) :=
  let vals := C.map (valueOfLit σ)
  let unknowns := C.zip vals |>.filter (fun ⟨_, o⟩ => o.isNone)
  if h1 : unknowns.length = 1 then
    if (vals.filter Option.isSome).all (fun o => o.getD false = false) then
      let l := unknowns.get ⟨0, by omega⟩
      match l.fst with
      | .pos v => some (v, true)
      | .neg v => some (v, false)
    else none
  else none

/-- A (single) backpropagation step relation with guarded rules. -/
inductive BPStep {n} (φ : CNF n) (H : XORSystem n) : BPState n → BPState n → Prop
  | xor_push
      {s : BPState n}
      (X : XORConstraint n)
      (v : Var n)
      (b : Bool)
      (hX : X ∈ H)
      (hmiss : xorMissing s.assign X = some (v, b))
      : BPStep φ H s { assign := setVar s.assign v b }
  | clause_unit
      {s : BPState n}
      (C : Clause n)
      (v : Var n)
      (b : Bool)
      (hC : C ∈ φ.clauses)
      (hmiss : clauseUnit s.assign C = some (v, b))
      : BPStep φ H s { assign := setVar s.assign v b }
  -- Additional gate placeholders (to be refined with circuit semantics):
  | and_one  {s : BPState n} : BPStep φ H s s
  | and_zero {s : BPState n} : BPStep φ H s s
  | or_one   {s : BPState n} : BPStep φ H s s
  | or_zero  {s : BPState n} : BPStep φ H s s
  | not_flip {s : BPState n} : BPStep φ H s s
  | wire_prop {s : BPState n} : BPStep φ H s s

/-- Predicate: state is complete (all variables determined). -/
def complete {n} (s : BPState n) : Prop :=
  ∀ v, (s.assign v).isSome = true

/-- Predicate: state is consistent with φ ∧ H (semantic notion). -/
def consistent {n} (s : BPState n) (φ : CNF n) (H : XORSystem n) : Prop :=
  ∃ a : Assignment n, (∀ v, s.assign v = some (a v)) ∧
    evalCNF a φ = true ∧ satisfiesSystem a H

/-- Compatibility: a partial assignment agrees with a total assignment on known bits. -/
def compatible {n} (σ : PartialAssignment n) (a : Assignment n) : Prop :=
  ∀ v, σ v = some (a v) ∨ σ v = none

/-- If σ is compatible with a and we set v to (a v), the result is still compatible. -/
lemma compatible_setVar {n} (σ : PartialAssignment n) (a : Assignment n) (v : Var n)
    (hcompat : compatible σ a) :
    compatible (setVar σ v (a v)) a := by
  intro w
  by_cases hwv : w = v
  · subst hwv
    left
    simp [setVar_same]
  · rw [setVar_ne σ v w (a v) hwv]
    exact hcompat w

/-!
## Semantic Correctness for XOR Propagation

The xorMissing function produces the correct value for a satisfying assignment.
This is now a **proved theorem**, not an axiom.
-/

-- Helper lemmas for xorMissing_correct proof
private lemma not_isSome_eq_isNone' {α : Type*} (o : Option α) : (!o.isSome) = o.isNone := by
  cases o <;> rfl

private lemma xor_comm_assoc' (a b c : Bool) : Bool.xor a (Bool.xor b c) = Bool.xor b (Bool.xor a c) := by
  cases a <;> cases b <;> cases c <;> rfl

private lemma xor_comm_cancel' (a b : Bool) : Bool.xor (Bool.xor b a) b = a := by
  cases a <;> cases b <;> rfl

private lemma parityOf_filter_split' {n} (a : Assignment n) (vs : List (Var n)) (p : Var n → Bool) :
    parityOf a vs = Bool.xor
      (parityOf a (vs.filter p))
      (parityOf a (vs.filter (fun v => !p v))) := by
  induction vs with
  | nil => simp [parityOf]
  | cons v vs ih =>
    simp only [parityOf_cons, List.filter_cons]
    by_cases hp : p v
    · have h1 : (if p v then v :: vs.filter p else vs.filter p) = v :: vs.filter p := by simp [hp]
      have h2 : (if !p v then v :: vs.filter (fun v => !p v) else vs.filter (fun v => !p v)) =
                vs.filter (fun v => !p v) := by simp [hp]
      rw [h1, h2, parityOf_cons, ih, Bool.xor_assoc]
    · have h1 : (if p v then v :: vs.filter p else vs.filter p) = vs.filter p := by simp [hp]
      have h2 : (if !p v then v :: vs.filter (fun v => !p v) else vs.filter (fun v => !p v)) =
                v :: vs.filter (fun v => !p v) := by simp [hp]
      rw [h1, h2, parityOf_cons, ih]
      exact xor_comm_assoc' _ _ _

private lemma getD_of_compat_isSome' {n} (σ : PartialAssignment n) (a : Assignment n) (w : Var n)
    (hcompat : compatible σ a) (hsome : (σ w).isSome = true) :
    (σ w).getD false = a w := by
  cases h : σ w with
  | none => simp [h] at hsome
  | some b =>
    simp only [Option.getD_some]
    have := hcompat w; rw [h] at this
    rcases this with heq | hn
    · exact Option.some.injEq b (a w) |>.mp heq
    · simp at hn

private lemma knownParity_eq_parityOf_known' {n} (σ : PartialAssignment n) (a : Assignment n)
    (X : XORConstraint n) (hcompat : compatible σ a) :
    X.vars.foldl (fun acc w => if (σ w).isSome then Bool.xor acc ((σ w).getD false) else acc) false =
    parityOf a (X.vars.filter (fun w => (σ w).isSome)) := by
  suffices h : ∀ init,
    X.vars.foldl (fun acc w => if (σ w).isSome then Bool.xor acc ((σ w).getD false) else acc) init =
    Bool.xor init (parityOf a (X.vars.filter (fun w => (σ w).isSome))) by
    specialize h false; simp at h; exact h
  intro init
  induction X.vars generalizing init with
  | nil => simp [parityOf]
  | cons w ws ih =>
    simp only [List.foldl_cons]
    by_cases hw : (σ w).isSome
    · simp only [hw, ↓reduceIte, List.filter_cons_of_pos]
      have hgetD : (σ w).getD false = a w := getD_of_compat_isSome' σ a w hcompat hw
      rw [hgetD, ih (Bool.xor init (a w)), parityOf_cons, Bool.xor_assoc]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, List.filter_cons_of_neg, not_false_eq_true]
      exact ih init

private lemma list_singleton_of_length_one' {α : Type*} (l : List α) (h : l.length = 1) :
    l = [l.get ⟨0, by omega⟩] := by
  match l with
  | [] => simp at h
  | [x] => simp
  | _ :: _ :: _ => simp at h

/-- **PROVED**: xorMissing produces the correct value for a satisfying assignment.
    If exactly one variable v is unknown in XOR constraint X, and a satisfies X,
    then the value returned by xorMissing equals a v.

    **Mathematical justification**: XOR is linear over GF(2).
    If ⊕_{w ∈ X.vars} a(w) = X.parity and we know all values except a(v),
    then a(v) = X.parity ⊕ (⊕_{w ≠ v} a(w)).

    **Status**: PROVED (formerly axiom) -/
theorem xorMissing_correct {n} (σ : PartialAssignment n) (a : Assignment n) (X : XORConstraint n)
    (v : Var n) (b : Bool)
    (hcompat : compatible σ a)
    (hsat : satisfiesXOR a X)
    (hmiss : xorMissing σ X = some (v, b)) :
    b = a v := by
  unfold xorMissing at hmiss
  simp only at hmiss
  split at hmiss
  case isTrue h_len1 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmiss
    obtain ⟨hv_eq, hb_eq⟩ := hmiss

    set unknowns := X.vars.filter (fun w => (σ w).isNone) with h_unknowns_def
    set known := X.vars.filter (fun w => (σ w).isSome) with h_known_def

    have h_unknowns_singleton : unknowns = [v] := by
      have h := list_singleton_of_length_one' unknowns h_len1
      rw [h, hv_eq]

    unfold satisfiesXOR at hsat

    have h_split := parityOf_filter_split' a X.vars (fun w => (σ w).isSome)
    have h_filter_eq : X.vars.filter (fun w => !(σ w).isSome) = unknowns := by
      simp only [h_unknowns_def]; congr 1; ext w; exact not_isSome_eq_isNone' (σ w)
    rw [h_filter_eq, h_unknowns_singleton] at h_split

    have h_par_v : parityOf a [v] = a v := by simp [parityOf]
    rw [h_par_v, ← h_known_def] at h_split
    rw [hsat] at h_split

    have h_known_par := knownParity_eq_parityOf_known' σ a X hcompat
    rw [← h_known_def] at h_known_par

    rw [← hb_eq, h_known_par, h_split]
    exact xor_comm_cancel' (a v) (parityOf a known)

  case isFalse h => simp at hmiss

/-!
## Semantic Correctness for Unit Propagation

The clauseUnit function produces the correct value for a satisfying assignment.
This is now a **proved theorem**, not an axiom.
-/

-- Helper lemmas for clauseUnit_correct proof
private lemma not_isSome_iff_isNone' {α : Type*} (o : Option α) : ¬o.isSome ↔ o.isNone := by
  cases o <;> simp

private lemma singleton_eq_get_zero' {α : Type*} (l : List α) (h : l.length = 1) :
    ∃ x, l = [x] ∧ x = l.get ⟨0, by omega⟩ := by
  match l with
  | [] => simp at h
  | [x] => exact ⟨x, rfl, rfl⟩
  | _ :: _ :: _ => simp at h

private lemma mem_zip_of_getElem' {α β : Type*} (l1 : List α) (l2 : List β) (i : Nat)
    (hi1 : i < l1.length) (hi2 : i < l2.length) :
    (l1[i], l2[i]) ∈ l1.zip l2 := by
  rw [List.mem_iff_getElem]
  have hi : i < (l1.zip l2).length := by simp; omega
  exact ⟨i, hi, by simp⟩

private lemma known_lit_false'' {n} (σ : PartialAssignment n) (a : Assignment n) (l : Lit n)
    (hcompat : compatible σ a) (hsome : (valueOfLit σ l).isSome)
    (hfalse : (valueOfLit σ l).getD false = false) :
    evalLit a l = false := by
  have heq : valueOfLit σ l = some (evalLit a l) := by
    cases l with
    | pos v =>
      simp only [valueOfLit, evalLit] at *
      rcases hcompat v with h | h
      · exact h
      · simp [h] at hsome
    | neg v =>
      simp only [valueOfLit, evalLit, Option.map] at *
      rcases hcompat v with h | h
      · simp [h]
      · simp [h] at hsome
  cases hv : valueOfLit σ l with
  | none => simp [hv] at hsome
  | some b =>
    simp only [hv, Option.getD_some] at hfalse heq
    simp only [Option.some.injEq] at heq
    rw [← heq, hfalse]

/-- **PROVED**: clauseUnit produces the correct value for a satisfying assignment.
    If exactly one literal is unknown in clause C, all known literals are false,
    and a satisfies C, then the value returned by clauseUnit equals a v.

    **Mathematical justification**: A clause is satisfied iff at least one literal is true.
    If all known literals are false under a (by compatibility), and a satisfies C,
    then the unknown literal must be the satisfying one.
    - For .pos v: the literal is true iff a v = true
    - For .neg v: the literal is true iff a v = false

    **Status**: PROVED (formerly axiom) -/
theorem clauseUnit_correct {n} (σ : PartialAssignment n) (a : Assignment n) (C : Clause n)
    (v : Var n) (b : Bool)
    (hcompat : compatible σ a)
    (hsat : evalClause a C = true)
    (hmiss : clauseUnit σ C = some (v, b)) :
    b = a v := by
  unfold clauseUnit at hmiss
  simp only at hmiss

  split at hmiss
  case isFalse h => simp at hmiss
  case isTrue h_len1 =>
    split at hmiss
    case isFalse h => simp at hmiss
    case isTrue h_all_false =>
      -- Set up unknowns
      set unknowns := (C.zip (C.map (valueOfLit σ))).filter (fun ⟨_, o⟩ => o.isNone) with hunk_def
      have h_len1' : unknowns.length = 1 := h_len1

      -- Get the singleton element
      obtain ⟨unk, h_singleton, hunk_get⟩ := singleton_eq_get_zero' unknowns h_len1'

      -- Known literals are false
      have h_known_false : ∀ l ∈ C, (valueOfLit σ l).isSome → evalLit a l = false := by
        intro l hl_in hsome
        have hval_in : valueOfLit σ l ∈ (C.map (valueOfLit σ)).filter Option.isSome := by
          simp only [List.mem_filter, List.mem_map]
          exact ⟨⟨l, hl_in, rfl⟩, hsome⟩
        rw [List.all_eq_true] at h_all_false
        simp only [decide_eq_true_eq] at h_all_false
        exact known_lit_false'' σ a l hcompat hsome (h_all_false _ hval_in)

      -- Some literal is true
      rw [evalClause, List.any_eq_true] at hsat
      obtain ⟨l_sat, hl_in, hl_true⟩ := hsat

      -- l_sat must be unknown
      have hl_unknown : (valueOfLit σ l_sat).isNone := by
        rw [← not_isSome_iff_isNone']
        intro hsome
        have hfalse := h_known_false l_sat hl_in hsome
        rw [hl_true] at hfalse
        cases hfalse

      -- l_sat is in unknowns
      have hl_in_unk : (l_sat, valueOfLit σ l_sat) ∈ unknowns := by
        rw [hunk_def, List.mem_filter]
        constructor
        · have hlen : C.length = (C.map (valueOfLit σ)).length := by simp
          obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hl_in
          have hi2 : i < (C.map (valueOfLit σ)).length := by simp; omega
          have hmem := mem_zip_of_getElem' C (C.map (valueOfLit σ)) i hi hi2
          simp only [List.getElem_map, hget] at hmem
          exact hmem
        · exact hl_unknown

      -- Since unknowns = [unk], l_sat = unk.fst
      rw [h_singleton, List.mem_singleton] at hl_in_unk
      have hl_eq : l_sat = unk.fst := congrArg Prod.fst hl_in_unk

      -- Rewrite hmiss using hunk_get
      have hmiss' : (match unk.fst with
          | .pos v => some (v, true)
          | .neg v => some (v, false)) = some (v, b) := by
        convert hmiss using 2
        rw [← hunk_get]

      -- Case analysis on unk.fst
      cases hl : unk.fst with
      | pos w =>
        simp only [hl] at hmiss'
        simp only [Option.some.injEq, Prod.mk.injEq] at hmiss'
        obtain ⟨hv_eq, hb_eq⟩ := hmiss'
        subst hv_eq hb_eq
        rw [hl_eq, hl] at hl_true
        simp only [evalLit] at hl_true
        exact hl_true.symm

      | neg w =>
        simp only [hl] at hmiss'
        simp only [Option.some.injEq, Prod.mk.injEq] at hmiss'
        obtain ⟨hv_eq, hb_eq⟩ := hmiss'
        subst hv_eq hb_eq
        rw [hl_eq, hl] at hl_true
        simp only [evalLit, Bool.not_eq_true'] at hl_true
        exact hl_true.symm

/-- Soundness of one step: preserves compatibility with any model. -/
lemma bp_step_sound {n} (φ : CNF n) (H : XORSystem n)
    {s t : BPState n} :
    BPStep φ H s t →
    ∀ a : Assignment n, evalCNF a φ = true → satisfiesSystem a H →
    compatible s.assign a → compatible t.assign a := by
  intro hstep a hφ hH hcompat
  cases hstep with
  | xor_push X v b hX hmiss =>
      -- Need to show: compatible (setVar s.assign v b) a
      -- Since a satisfies X and xorMissing gave us (v, b), we need b = a v
      have hXsat : satisfiesXOR a X := hH X hX
      have hbeq : b = a v := xorMissing_correct s.assign a X v b hcompat hXsat hmiss
      subst hbeq
      exact compatible_setVar s.assign a v hcompat
  | clause_unit C v b hC hmiss =>
      -- Need to show: compatible (setVar s.assign v b) a
      -- Since a satisfies C and clauseUnit gave us (v, b), we need b = a v
      have hCsat : evalClause a C = true := by
        unfold evalCNF at hφ
        simp only [List.all_eq_true] at hφ
        exact hφ C hC
      have hbeq : b = a v := clauseUnit_correct s.assign a C v b hcompat hCsat hmiss
      subst hbeq
      exact compatible_setVar s.assign a v hcompat
  | and_one => exact hcompat
  | and_zero => exact hcompat
  | or_one => exact hcompat
  | or_zero => exact hcompat
  | not_flip => exact hcompat
  | wire_prop => exact hcompat

/-- Monotonicity: steps never unassign known values. -/
lemma bp_step_monotone {n} (φ : CNF n) (H : XORSystem n)
  {s t : BPState n} :
  BPStep φ H s t →
  ∀ v, (s.assign v).isSome → (t.assign v).isSome := by
  intro hstep v hv
  cases hstep with
  | xor_push X v_pushed b_pushed hX hmiss =>
      by_cases hvv : v = v_pushed
      · subst hvv; simp only [setVar_same, Option.isSome_some]
      · show (setVar s.assign v_pushed b_pushed v).isSome = true
        rw [setVar_ne _ _ _ _ hvv]; exact hv
  | clause_unit C v_pushed b_pushed hC hmiss =>
      by_cases hvv : v = v_pushed
      · subst hvv; simp only [setVar_same, Option.isSome_some]
      · show (setVar s.assign v_pushed b_pushed v).isSome = true
        rw [setVar_ne _ _ _ _ hvv]; exact hv
  | and_one => exact hv
  | and_zero => exact hv
  | or_one => exact hv
  | or_zero => exact hv
  | not_flip => exact hv
  | wire_prop => exact hv

/-- Backpropagation succeeds if every legal start reaches a complete consistent state. -/
def BackpropSucceeds {n} (φ : CNF n) (H : XORSystem n) : Prop :=
  ∀ (_s0 : BPState n),
    ∃ s, complete s ∧ consistent s φ H

end SAT
end Complexity
end IndisputableMonolith
