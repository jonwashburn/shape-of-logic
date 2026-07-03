import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- Constraints are either CNF-clauses or XOR-checks. -/
inductive Constraint (n : Nat) where
  | cnf (C : Clause n)
  | xor (X : XORConstraint n)
deriving Repr

/-- Whether a variable is mentioned in a literal. -/
def mentionsVarLit {n} (l : Lit n) (v : Var n) : Bool :=
  match l with
  | .pos u => decide (u = v)
  | .neg u => decide (u = v)

/-- Whether a variable is mentioned in a clause. -/
def mentionsVarClause {n} (C : Clause n) (v : Var n) : Bool :=
  C.any (fun l => mentionsVarLit l v)

/-- Whether a variable is mentioned in an XOR constraint. -/
def mentionsVarXOR {n} (X : XORConstraint n) (v : Var n) : Bool :=
  X.vars.any (fun u => decide (u = v))

/-- Whether a variable is mentioned in a mixed constraint. -/
def mentionsVar {n} (K : Constraint n) (v : Var n) : Bool :=
  match K with
  | .cnf C => mentionsVarClause C v
  | .xor X => mentionsVarXOR X v

/-- Satisfaction semantics for mixed constraints. -/
def satisfiesConstraint {n} (a : Assignment n) (K : Constraint n) : Prop :=
  match K with
  | .cnf C => evalClause a C = true
  | .xor X => parityOf a X.vars = X.parity

/-- The constraint K determines variable v w.r.t. reference assignment `aRef`:
    fixing all non-v variables to `aRef` and requiring `K` forces `v = aRef v`. -/
def determinesVar {n}
  (aRef : Assignment n) (K : Constraint n) (v : Var n) : Prop :=
  ∀ (a' : Assignment n),
    (∀ w : Var n, w ≠ v → a' w = aRef w) →
    satisfiesConstraint a' K →
    a' v = aRef v

/-- Collect all constraints arising from a CNF+XOR instance. -/
def constraintsOf {n} (φ : CNF n) (H : XORSystem n) : List (Constraint n) :=
  (φ.clauses.map Constraint.cnf) ++ (H.map Constraint.xor)

/-- Set of input variables (as a finset) for PC property articulation. -/
abbrev InputSet (n : Nat) := Finset (Var n)

/-- Propagation-Completeness condition (PC):
    For every nonempty U ⊆ inputs, there exists a constraint K and v ∈ U such that
    (i) K mentions v, (ii) K mentions no other element of U, and (iii) K determines v
    with respect to the unique reference assignment `aRef`. -/
def PC {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) : Prop :=
  ∀ (U : Finset (Var n)),
    U ⊆ inputs →
    U.Nonempty →
    ∃ (K : Constraint n),
      K ∈ constraintsOf φ H ∧
      ∃ v ∈ U,
        mentionsVar K v = true ∧
        (∀ w ∈ U, w ≠ v → mentionsVar K w = false) ∧
        determinesVar aRef K v

/-- Peeling witness structure: a list of variables and constraints meeting the peeling conditions. -/
structure PeelingData {n : Nat} (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) where
  vars : List (Var n)
  constrs : List (Constraint n)
  nodup : vars.Nodup
  len_eq : vars.length = constrs.length
  cover : ∀ v : Var n, v ∈ inputs ↔ v ∈ vars
  step : ∀ k (hk : k < vars.length),
    let v := vars.get ⟨k, hk⟩
    let K := constrs.get ⟨k, by omega⟩
    mentionsVar K v = true ∧
    (∀ w, w ∈ vars.drop k.succ → mentionsVar K w = false) ∧
    determinesVar aRef K v

/-- Peeling witness (Prop-level): there exists a peeling structure. -/
def PeelingWitness {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) : Prop :=
  Nonempty (PeelingData inputs aRef φ H)

/-- Forced-implication reachability (abstract): there is a directed arborescence
    of locally-determining constraints from OUTPUT to every input.

    **Definition**: We define ForcedArborescence as equivalent to PeelingWitness.
    The peeling order (v₁, v₂, ..., vₙ) with determining constraints (K₁, K₂, ..., Kₙ)
    implicitly defines an arborescence where each variable's parent is determined
    by the constraint that determines it.

    **Graph interpretation**: The arborescence edges are:
    - v → K_i for each variable v mentioned in K_i's "known" portion
    - K_i → v_i for the variable determined by K_i

    This forms a directed tree rooted at OUTPUT reaching all input variables. -/
def ForcedArborescence {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) : Prop :=
  PeelingWitness inputs aRef φ H  -- Arborescence IS the peeling structure

/-- Forced arborescence witness: for this development we take it to be the same data
    as a peeling witness (a spanning, duplicate-free list of vars with matching constraints). -/
abbrev ForcedArborescenceWitness {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) : Prop :=
  PeelingWitness inputs aRef φ H

/-- Program goal (graph-theoretic equivalence to target):
    PC ↔ existence of a forced-implication arborescence (to be proven). -/
def programGoal_pc_iff_arborescence {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) : Prop :=
  (PC inputs aRef φ H) ↔ (ForcedArborescence inputs aRef φ H)

/-- Helper to extract one (K, v) pair from PC condition. -/
noncomputable def extractFromPC {n : Nat} (inputs : InputSet n) (aRef : Assignment n)
    (φ : CNF n) (H : XORSystem n) (hPC : PC inputs aRef φ H)
    (U : Finset (Var n)) (hU : U ⊆ inputs) (hne : U.Nonempty) :
    { p : Constraint n × Var n //
      p.1 ∈ constraintsOf φ H ∧
      p.2 ∈ U ∧
      mentionsVar p.1 p.2 = true ∧
      (∀ w ∈ U, w ≠ p.2 → mentionsVar p.1 w = false) ∧
      determinesVar aRef p.1 p.2 } := by
  have h := hPC U hU hne
  choose K hK using h
  choose v hv using hK.2
  exact ⟨(K, v), hK.1, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩

/-- Bundled result type for peeling construction. -/
structure PeelingResult {n : Nat} (inputs : InputSet n) (aRef : Assignment n)
    (φ : CNF n) (H : XORSystem n) (U : Finset (Var n)) where
  vars : List (Var n)
  constrs : List (Constraint n)
  len_eq : vars.length = constrs.length
  nodup : vars.Nodup
  cover : ∀ v, v ∈ vars ↔ v ∈ U
  step : ∀ k (hk : k < vars.length),
    let v := vars.get ⟨k, hk⟩
    let K := constrs.get ⟨k, by omega⟩
    mentionsVar K v = true ∧
    (∀ w ∈ vars.drop k.succ, mentionsVar K w = false) ∧
    determinesVar aRef K v

/-- **PROVED**: Build the peeling order via Finset induction.
    At each step, PC gives constraint K and variable v ∈ U that K uniquely determines.
    Recursively peel U \ {v} to get (vs, cs), then return (v :: vs, K :: cs). -/
noncomputable def buildPeelingResult {n : Nat} (inputs : InputSet n) (aRef : Assignment n)
    (φ : CNF n) (H : XORSystem n) (hPC : PC inputs aRef φ H)
    (U : Finset (Var n)) (hU : U ⊆ inputs) :
    PeelingResult inputs aRef φ H U := by
  induction' hcard : U.card with k ih generalizing U
  · -- Base case: U is empty
    exact {
      vars := []
      constrs := []
      len_eq := rfl
      nodup := List.nodup_nil
      cover := by intro v; simp; rw [Finset.card_eq_zero.mp hcard]; exact Finset.not_mem_empty v
      step := by intro k hk; simp at hk
    }
  · -- Inductive case: U is nonempty
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    let ⟨⟨K, v⟩, _, hvmem, hment, honly, hdet⟩ := extractFromPC inputs aRef φ H hPC U hU hne
    let U' := U.erase v
    have hU' : U' ⊆ inputs := fun w hw => hU (Finset.mem_erase.mp hw).2
    have hcard' : U'.card = k := by rw [Finset.card_erase_of_mem hvmem]; omega
    let rec_result := ih U' hU' hcard'
    exact {
      vars := v :: rec_result.vars
      constrs := K :: rec_result.constrs
      len_eq := by simp only [List.length_cons, rec_result.len_eq]
      nodup := by
        refine List.Nodup.cons ?_ rec_result.nodup
        intro hv_in_vs
        have hv_in_U' := (rec_result.cover v).mp hv_in_vs
        exact (Finset.not_mem_erase v U) hv_in_U'
      cover := by
        intro w
        simp only [List.mem_cons]
        constructor
        · intro hw
          rcases hw with rfl | hw'
          · exact hvmem
          · exact Finset.mem_of_mem_erase ((rec_result.cover w).mp hw')
        · intro hw
          by_cases hwv : w = v
          · left; exact hwv
          · right; exact (rec_result.cover w).mpr (Finset.mem_erase.mpr ⟨hwv, hw⟩)
      step := by
        intro idx hidx
        simp only [List.length_cons] at hidx
        cases idx with
        | zero =>
          simp only [List.drop_succ_cons, List.drop_zero]
          constructor
          · exact hment
          constructor
          · intro w hw
            have hw_in_U' := (rec_result.cover w).mp hw
            have hw_in_U := Finset.mem_of_mem_erase hw_in_U'
            have hw_ne_v : w ≠ v := fun heq => by
              rw [heq] at hw_in_U'
              exact (Finset.not_mem_erase v U) hw_in_U'
            exact honly w hw_in_U hw_ne_v
          · exact hdet
        | succ idx' =>
          simp only [List.drop_succ_cons]
          have hidx' : idx' < rec_result.vars.length := by simp at hidx; omega
          exact rec_result.step idx' hidx'
    }

/-- **PROVED**: PC ⇒ peeling.
    If the PC condition holds for inputs, we can construct a peeling witness.

    **Proof**: Classical Finset induction via `buildPeelingResult`. At each step:
    1. Given nonempty U ⊆ inputs, PC gives constraint K and variable v ∈ U
    2. K mentions only v from U, and determines v
    3. Recursively peel U \ {v} to get (vs, cs)
    4. Return (v :: vs, K :: cs)

    Base case: empty U gives ([], []). -/
theorem pc_implies_peeling {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) :
  PC inputs aRef φ H → PeelingWitness inputs aRef φ H := by
  intro hPC
  let result := buildPeelingResult inputs aRef φ H hPC inputs (fun _ h => h)
  exact ⟨{
    vars := result.vars
    constrs := result.constrs
    nodup := result.nodup
    len_eq := result.len_eq
    cover := fun v => (result.cover v).symm
    step := result.step
  }⟩

/-- Peeling ⇒ forced arborescence (Prop-level).
    Trivial since ForcedArborescence is defined as PeelingWitness. -/
theorem peeling_implies_arborescence {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) :
  PeelingWitness inputs aRef φ H → ForcedArborescence inputs aRef φ H := by
  unfold ForcedArborescence
  exact id

/-- Arborescence ⇒ peeling (Prop-level).
    Trivial since ForcedArborescence is defined as PeelingWitness. -/
theorem arborescence_implies_peeling {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) :
  ForcedArborescence inputs aRef φ H → PeelingWitness inputs aRef φ H := by
  unfold ForcedArborescence
  exact id

/-- Peeling ↔ Arborescence equivalence. -/
theorem peeling_iff_arborescence {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) :
  PeelingWitness inputs aRef φ H ↔ ForcedArborescence inputs aRef φ H := by
  unfold ForcedArborescence
  exact Iff.rfl

/-- PC ⇒ ForcedArborescence. -/
theorem pc_implies_forcedArborescence {n}
  (inputs : InputSet n) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n) :
  PC inputs aRef φ H → ForcedArborescence inputs aRef φ H := by
  unfold ForcedArborescence
  exact pc_implies_peeling inputs aRef φ H

end SAT
end Complexity
end IndisputableMonolith
