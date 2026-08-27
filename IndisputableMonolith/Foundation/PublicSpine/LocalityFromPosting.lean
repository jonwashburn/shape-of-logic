import IndisputableMonolith.Foundation.CostFromDistinction
import IndisputableMonolith.Foundation.HierarchyDynamics
import IndisputableMonolith.Foundation.HierarchyEmergence
import IndisputableMonolith.Foundation.HierarchyForcing
import IndisputableMonolith.Foundation.PublicSpine.SelectedScaleClosure
import IndisputableMonolith.Foundation.UnifiedForcingChain
import IndisputableMonolith.Constants

/-!
# LocalityFromPosting — φ-spine gap 2 (binary recurrence from Recognition)

Target (from `ClosureDischargeProbe`): prove the recurrence is binary (not
higher-order) from Recognition structure, so `LocalBinaryRecurrence` is
derived rather than disclosed in `P_closure`.

## What is THEOREM here

1. **Binary arity of posting.** `ConfigSpace.join` is a binary operation.
   One independent join of two seed events induces a **two-term** size law
   (`binary_join_induces_two_term_size`), never a three-term sum from that
   single act.
2. **Higher-order needs more parents.** Nested joins of three independent
   events induce a three-term size law (`ternary_nested_join_induces_three_term_size`).
   So order > 2 is available only by using more than one binary seed post
   (or an n-ary posting primitive, which Recognition does not supply).
3. **Plastic independence.** The alternate short closure `r³ = r + 1` has a
   positive root ≠ φ (`exists_plastic_root_ne_phi`). Selecting the binary
   Fibonacci short closure over that cubic alternative is therefore contentful.

## WALL

Binary *arity* of recognition-work posting forces that a single seed post is
a binary size relation. It does **not** by itself force the hierarchy's
generating recurrence / short-closure choice to be that single adjacent-seed
post (versus a plastic skip `L0+L1=L3`, or a disclosed higher-order local
recurrence). The missing lemma is `BinarySeedClosureSelectionOpen`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace LocalityFromPosting

open CostFromDistinction
open CostFromDistinction.CostFunction
open HierarchyDynamics
open HierarchyEmergence
open HierarchyForcing
open Constants
open SelectedScaleClosure

/-! ## Binary posting arity ⇒ two-term size law -/

/-- One independent binary join produces exactly a two-term additive size. -/
theorem binary_join_induces_two_term_size
    {Event : Type} [ConfigSpace Event]
    (κ : CostFunction Event)
    (e0 e1 : Event)
    (hindep : ConfigSpace.Independent e0 e1) :
    κ.C (ConfigSpace.join e0 e1) = κ.C e0 + κ.C e1 :=
  κ.additivity e0 e1 hindep

/-- Specialization: if level 2 is the binary join of seeds 0 and 1, and levels
read recognition-work costs, the induced recurrence is binary additive. -/
theorem seed_binary_post_forces_binary_recurrence
    (M : HierarchyForcing.NontrivialMultilevelComposition)
    {Event : Type} [ConfigSpace Event]
    (κ : CostFunction Event)
    (levelEvent : ℕ → Event)
    (level_size_eq : ∀ k, M.levels k = κ.C (levelEvent k))
    (seed_is_join :
      levelEvent 2 =
        ConfigSpace.join (levelEvent 0) (levelEvent 1))
    (seed_independent :
      ConfigSpace.Independent (levelEvent 0) (levelEvent 1)) :
    M.levels 2 = M.levels 1 + M.levels 0 := by
  have hsz :=
    binary_join_induces_two_term_size κ (levelEvent 0) (levelEvent 1)
      seed_independent
  calc
    M.levels 2 = κ.C (levelEvent 2) := level_size_eq 2
    _ = κ.C (ConfigSpace.join (levelEvent 0) (levelEvent 1)) := by rw [seed_is_join]
    _ = κ.C (levelEvent 0) + κ.C (levelEvent 1) := hsz
    _ = M.levels 0 + M.levels 1 := by rw [← level_size_eq 0, ← level_size_eq 1]
    _ = M.levels 1 + M.levels 0 := by ring

/-- Package form: binary seed join + cost reading ⇒ `LocalBinaryRecurrence`
with unit coefficients (hence Fibonacci). -/
noncomputable def localBinaryRecurrence_of_binary_seed_post
    (L : UniformScaleLadder)
    {Event : Type} [ConfigSpace Event]
    (κ : CostFunction Event)
    (levelEvent : ℕ → Event)
    (level_size_eq : ∀ k, L.levels k = κ.C (levelEvent k))
    (seed_is_join :
      levelEvent 2 =
        ConfigSpace.join (levelEvent 0) (levelEvent 1))
    (seed_independent :
      ConfigSpace.Independent (levelEvent 0) (levelEvent 1)) :
    LocalBinaryRecurrence where
  ladder := L
  coeff_a := 1
  coeff_b := 1
  coeff_a_pos := by norm_num
  coeff_b_pos := by norm_num
  local_recurrence := by
    have h :
        L.levels 2 = L.levels 1 + L.levels 0 := by
      -- Rebuild via a temporary multilevel wrapper is heavy; prove directly.
      have hsz :=
        binary_join_induces_two_term_size κ (levelEvent 0) (levelEvent 1)
          seed_independent
      calc
        L.levels 2 = κ.C (levelEvent 2) := level_size_eq 2
        _ = κ.C (ConfigSpace.join (levelEvent 0) (levelEvent 1)) := by
              rw [seed_is_join]
        _ = κ.C (levelEvent 0) + κ.C (levelEvent 1) := hsz
        _ = L.levels 0 + L.levels 1 := by rw [← level_size_eq 0, ← level_size_eq 1]
        _ = L.levels 1 + L.levels 0 := by ring
    simpa [one_mul] using h

/-! ## Higher-order size laws require more than one binary seed post -/

/-- Nested join of three independent events yields a three-term size law. -/
theorem ternary_nested_join_induces_three_term_size
    {Event : Type} [ConfigSpace Event]
    (κ : CostFunction Event)
    (e0 e1 e2 : Event)
    (h01 : ConfigSpace.Independent e0 e1)
    (h02 : ConfigSpace.Independent e0 e2)
    (h12 : ConfigSpace.Independent e1 e2)
    (h0_join : ConfigSpace.Independent e0 (ConfigSpace.join e1 e2)) :
    κ.C (ConfigSpace.join e0 (ConfigSpace.join e1 e2)) =
      κ.C e0 + κ.C e1 + κ.C e2 :=
  additive_three κ e0 e1 e2 h01 h02 h12 h0_join

/-- Clean arithmetic form: a two-term sum of positives cannot equal the
same sum plus a third positive. -/
theorem two_term_ne_three_term_of_positive
    (x y z : ℝ) (_hx : 0 < x) (_hy : 0 < y) (hz : 0 < z) :
    ¬ (x + y = x + y + z) := by
  linarith

/-- Therefore a three-parent additive size cannot arise as the size of one
binary join of two of the three positive-cost parents. -/
theorem binary_join_of_two_parents_misses_third
    {Event : Type} [ConfigSpace Event]
    (κ : CostFunction Event)
    (e0 e1 e2 : Event)
    (h01 : ConfigSpace.Independent e0 e1)
    (h0 : 0 < κ.C e0) (h1 : 0 < κ.C e1) (h2 : 0 < κ.C e2) :
    κ.C (ConfigSpace.join e0 e1) ≠ κ.C e0 + κ.C e1 + κ.C e2 := by
  intro h
  have h2term : κ.C (ConfigSpace.join e0 e1) = κ.C e0 + κ.C e1 :=
    binary_join_induces_two_term_size κ e0 e1 h01
  have : κ.C e0 + κ.C e1 = κ.C e0 + κ.C e1 + κ.C e2 := by
    linarith [h, h2term]
  exact (two_term_ne_three_term_of_positive (κ.C e0) (κ.C e1) (κ.C e2) h0 h1 h2) this

/-! ## Plastic / higher short-closure independence -/

/-- Re-export: cubic short closure admits a positive root ≠ φ. -/
theorem plastic_short_closure_independent :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1 :=
  exists_plastic_root_ne_phi

/-- On a uniform ladder, the plastic relation `L3 = L1 + L0` is compatible
with ratio `r` satisfying `r³ = r + 1`, hence is a real higher-index
alternative to binary Fibonacci `L2 = L1 + L0`. -/
theorem plastic_relation_on_uniform_ladder
    (L : UniformScaleLadder)
    (hr : L.ratio ^ 3 = L.ratio + 1) :
    L.levels 3 = L.levels 1 + L.levels 0 := by
  have h0 : L.levels 0 ≠ 0 := ne_of_gt (L.levels_pos 0)
  have h1 : L.levels 1 = L.ratio * L.levels 0 := L.uniform_scaling 0
  have h2 : L.levels 2 = L.ratio * L.levels 1 := L.uniform_scaling 1
  have h3 : L.levels 3 = L.ratio * L.levels 2 := L.uniform_scaling 2
  have h3' : L.levels 3 = L.ratio ^ 3 * L.levels 0 := by
    rw [h3, h2, h1]; ring
  have hrhs : L.levels 1 + L.levels 0 = (L.ratio + 1) * L.levels 0 := by
    rw [h1]; ring
  calc
    L.levels 3 = L.ratio ^ 3 * L.levels 0 := h3'
    _ = (L.ratio + 1) * L.levels 0 := by rw [hr]
    _ = L.levels 1 + L.levels 0 := by rw [← hrhs]

/-! ## Typed WALL -/

/-- **Missing lemma (precise).**

Binary posting arity proves that *one* seed post of two independent events is
a binary size law. What is still OPEN is a Recognition-native selection that
the hierarchy's short closure / generating recurrence *is* that single
adjacent-seed binary post at index 2 (rather than a plastic skip to index 3,
a nested three-seed post, or a disclosed `LocalBinaryRecurrence` field).

Zero-parameter minimality among coefficient pairs of a *fixed* binary family
is already THEOREM (`ClosureDischargeProbe`); it does not select the family
order. -/
structure BinarySeedClosureSelectionOpen : Prop where
  stated : True := trivial

/-- Wall binder for gap 2. -/
structure LocalityFromPostingWall : Prop where
  /-- One binary join ⇒ two-term size. -/
  binary_arity :
    ∀ {Event : Type} [ConfigSpace Event] (κ : CostFunction Event)
      (e0 e1 : Event),
      ConfigSpace.Independent e0 e1 →
      κ.C (ConfigSpace.join e0 e1) = κ.C e0 + κ.C e1
  /-- Two parents miss a third positive cost. -/
  misses_third :
    ∀ {Event : Type} [ConfigSpace Event] (κ : CostFunction Event)
      (e0 e1 e2 : Event),
      ConfigSpace.Independent e0 e1 →
      0 < κ.C e0 → 0 < κ.C e1 → 0 < κ.C e2 →
      κ.C (ConfigSpace.join e0 e1) ≠ κ.C e0 + κ.C e1 + κ.C e2
  /-- Plastic short closure is a real alternative ≠ φ. -/
  plastic_independent :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1
  /-- Named OPEN: select binary adjacent-seed closure as the hierarchy law. -/
  selection_open : BinarySeedClosureSelectionOpen

theorem localityFromPostingWall_holds : LocalityFromPostingWall where
  binary_arity := binary_join_induces_two_term_size
  misses_third := binary_join_of_two_parents_misses_third
  plastic_independent := plastic_short_closure_independent
  selection_open := {}

/-- Status tag for the parent session. -/
def localityStatus : String := "WALL"

end LocalityFromPosting
end PublicSpine
end Foundation
end IndisputableMonolith
