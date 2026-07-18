import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure

/-!
# Seven Gaps, Lane D1: invariance alone does not determine the path-sum measure

## What this module proves (KILL + WITNESS)

**Status: THEOREM (kernel no-go with explicit witnesses).**  The killed
prior attempt "mu-from-invariance" claimed that relabeling invariance
(plus the obvious positivity and normalization requirements) singles out
the symmetry-factor measure `mu = 1/|Aut|` on the scoped path-sum
configuration class.  That positive claim stays dead.  This module proves
the corresponding NO-GO as a kernel fact:

* `InvarianceAxioms` names the invariance-type properties used here, each
  stateable against the existing Lean machinery: relabeling invariance
  (the measure is a class function for `relabelSetoid`),
  strict positivity, per-configuration normalization `w K <= 1`, and the
  unit normalization `w(empty) = 1` on the canonical empty configuration.
  The no-go is scoped to THIS named set; a strictly richer axiom set
  (gluing/factorization, orbit-stabilizer, substrate structure) could in
  principle restore uniqueness, and that possibility is exactly the OPEN
  substrate-derivation frontier.
* THREE genuinely different weight functions satisfy ALL of the named
  axioms: the symmetry-factor measure `mu = 1/|Aut|` (`muMeasure`), the
  uniform weight `1` (`uniformMeasure`), and the squared symmetry factor
  `1/|Aut|^2` (`muSqMeasure`).  In fact a countably infinite injective
  family does (`muPowMeasure`, `invariance_admits_infinite_measure_family`).
* The separation is witnessed concretely, not abstractly: the two-vertex
  edgeless configuration `twoPointComplex` has automorphism group of
  cardinality exactly 2 (`autCard_twoPointComplex`, via the explicit
  equivalence `twoPointAutEquiv` with the permutation triple), so
  `mu = 1/2 < 1` there (`mu_twoPointComplex`) while the uniform weight
  is `1`.
* **Headline:** `mu_not_determined_by_invariance`.  Both candidate
  measures satisfy the named axioms and they are unequal, with the
  pointwise strict inequality exhibited.  Invariance alone underdetermines
  the path-sum measure.

## What this module does NOT prove (binding honesty disclosures)

* It does NOT resurrect the positive claim that invariance fixes
  `1/|Aut|`; it refutes exactly that determination claim.
* It does NOT derive the `1/|Aut|` measure from recognition-ledger
  substrate axioms.  `substrate_measure_derived` stays RED (OPEN): no
  named substrate axiom set in the existing Lean forces a unique measure,
  and this module shows the invariance-type axioms stateable against the
  existing `PathSumMeasure` machinery cannot.  A future derivation would
  need strictly richer named substrate structure.
* A disjoint-union / gluing factorization axiom is NOT included in
  `InvarianceAxioms`, because the existing `BoundedComplex` machinery
  carries no disjoint-union operation to state it against.  The no-go is
  scoped to the axioms actually named; this scope is disclosed here and
  in `measureInvarianceNoGoStatus`.
* Nothing here concerns the continuum limit (`Z_RS_continuum_limit`
  stays RED / OPEN), and no `FullTheoryLedger` flag is touched.

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms, no `native_decide`):**
`autCard_emptyComplex`, `mu_emptyComplex`, `autCard_twoPointComplex`,
`mu_twoPointComplex`, `muMeasure_satisfies`, `uniformMeasure_satisfies`,
`muSqMeasure_satisfies`, `muPowMeasure_satisfies`,
`mu_not_determined_by_invariance`, `invariance_underdetermines_measure`,
`invariance_admits_infinite_measure_family`.

**MODEL (definitional, inherited):** the scoped configuration class
`BoundedComplex` and the `1/|Aut|` convention itself, from
`PathSumMeasure`.

**OPEN (recorded, never claimed):** a substrate-DERIVED unique measure;
the continuum limit.

Expected axiom footprint: standard trio
`[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MeasureInvarianceNoGo

open PathSumMeasure

/-! ## §1. The named invariance axioms

The invariance-type requirements on a candidate path-sum weight used by
this no-go: class-function invariance under `relabelSetoid`, strict
positivity, per-configuration normalization, and unit weight on the
canonical empty configuration.  A disjoint-union factorization axiom is
NOT stateable against the existing `BoundedComplex` inventory (no gluing
operation exists there); that scope limit is disclosed in the module
docstring, and the no-go is scoped to the axioms named here. -/

/-- The named invariance axioms for a candidate path-sum weight `w` on the
scoped configuration class at cap `B`.  The no-go below is scoped to
exactly this axiom set. -/
structure InvarianceAxioms (B : ℕ) (w : BoundedComplex B → ℝ) : Prop where
  /-- The weight is a relabeling class function. -/
  relabel_invariant : ∀ K K' : BoundedComplex B, Equivalent K K' → w K = w K'
  /-- The weight is strictly positive. -/
  positive : ∀ K : BoundedComplex B, 0 < w K
  /-- Per-configuration normalization: no configuration outweighs the
  reference weight 1. -/
  normalized_le_one : ∀ K : BoundedComplex B, w K ≤ 1
  /-- Unit normalization on the canonical empty configuration. -/
  unital_on_empty : w (emptyComplex B) = 1

/-- **THEOREM (normalizability on the finite scoped family).**  Any weight
satisfying the named axioms has finite total mass bounded by the proved
configuration count: the axioms already contain normalizability. -/
theorem InvarianceAxioms.totalMass_le_card {B : ℕ} {w : BoundedComplex B → ℝ}
    (h : InvarianceAxioms B w) :
    ∑ K : BoundedComplex B, w K ≤ (Fintype.card (BoundedComplex B) : ℝ) := by
  calc ∑ K : BoundedComplex B, w K
      ≤ ∑ _K : BoundedComplex B, (1 : ℝ) :=
        Finset.sum_le_sum fun K _ => h.normalized_le_one K
    _ = (Fintype.card (BoundedComplex B) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-! ## §2. The symmetry factor on the empty configuration -/

/-- The automorphism group of the empty configuration is trivial: all
three index types are empty, so all three index bijections are forced. -/
instance instSubsingletonAutEmpty (B : ℕ) :
    Subsingleton (Aut (emptyComplex B)) :=
  ⟨fun _a _b => Relabel.ext
    (Equiv.ext fun x => x.elim0)
    (Equiv.ext fun x => x.elim0)
    (Equiv.ext fun x => x.elim0)⟩

/-- **THEOREM.**  `|Aut(empty)| = 1`. -/
theorem autCard_emptyComplex (B : ℕ) :
    Nat.card (Aut (emptyComplex B)) = 1 :=
  Nat.card_unique

/-- **THEOREM.**  The symmetry-factor measure is 1 on the empty
configuration, so `mu` satisfies the unit-normalization axiom. -/
theorem mu_emptyComplex (B : ℕ) : mu (emptyComplex B) = 1 := by
  unfold mu
  rw [autCard_emptyComplex]
  norm_num

/-! ## §3. The separating witness: two vertices, no incidence

The two-vertex edgeless configuration has a nontrivial automorphism (the
vertex swap), and its automorphism group is EXACTLY the permutation
triple `S_2 x S_0 x S_0` because the incidence commutation constraints
are vacuous.  So `mu = 1/2` there while the uniform weight is 1. -/

/-- The two-vertex edgeless configuration at any cap `B >= 2`.  (`abbrev`
so the size fields reduce during elaboration.) -/
abbrev twoPointComplex (B : ℕ) (hB : 2 ≤ B) : BoundedComplex B where
  nV := 2
  nE := 0
  nT := 0
  hV := hB
  hE := Nat.zero_le B
  hT := Nat.zero_le B
  edgeVerts := fun e => e.elim0
  tetVerts := fun t => t.elim0

/-- With no edges and no tetrahedra the commutation constraints are
vacuous: the automorphism group of the two-point configuration IS the
full triple of index permutations. -/
def twoPointAutEquiv (B : ℕ) (hB : 2 ≤ B) :
    Aut (twoPointComplex B hB) ≃
      ((Fin 2 ≃ Fin 2) × (Fin 0 ≃ Fin 0) × (Fin 0 ≃ Fin 0)) where
  toFun a := ⟨a.vEquiv, a.eEquiv, a.tEquiv⟩
  invFun p :=
    { vEquiv := p.1
      eEquiv := p.2.1
      tEquiv := p.2.2
      edge_comm := fun e => e.elim0
      tet_comm := fun t _ => t.elim0 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **THEOREM.**  `|Aut(twoPoint)| = 2` exactly (the identity and the
vertex swap). -/
theorem autCard_twoPointComplex (B : ℕ) (hB : 2 ≤ B) :
    Nat.card (Aut (twoPointComplex B hB)) = 2 := by
  rw [Nat.card_congr (twoPointAutEquiv B hB), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_prod,
    Fintype.card_equiv (Equiv.refl (Fin 2)),
    Fintype.card_equiv (Equiv.refl (Fin 0)),
    Fintype.card_fin 2, Fintype.card_fin 0]
  norm_num [Nat.factorial]

/-- **THEOREM.**  The symmetry-factor measure of the two-point witness is
exactly `1/2`. -/
theorem mu_twoPointComplex (B : ℕ) (hB : 2 ≤ B) :
    mu (twoPointComplex B hB) = 1 / 2 := by
  unfold mu
  rw [autCard_twoPointComplex B hB]
  norm_num

/-! ## §4. The candidate measures and their axiom certificates -/

/-- Candidate 1: the standing symmetry-factor measure `1/|Aut|`. -/
noncomputable def muMeasure (B : ℕ) : BoundedComplex B → ℝ := fun K => mu K

/-- Candidate 2: the uniform weight 1. -/
def uniformMeasure (B : ℕ) : BoundedComplex B → ℝ := fun _ => 1

/-- Candidate 3: the squared symmetry factor `1/|Aut|^2`. -/
noncomputable def muSqMeasure (B : ℕ) : BoundedComplex B → ℝ :=
  fun K => mu K ^ 2

/-- A countable family of candidates: `1/|Aut|^(n+1)` for every `n`. -/
noncomputable def muPowMeasure (B : ℕ) (n : ℕ) : BoundedComplex B → ℝ :=
  fun K => mu K ^ (n + 1)

/-- **THEOREM.**  `1/|Aut|` satisfies every named invariance axiom. -/
theorem muMeasure_satisfies (B : ℕ) : InvarianceAxioms B (muMeasure B) :=
  ⟨fun _ _ h => mu_congr h, fun K => mu_pos K, fun K => mu_le_one K,
    mu_emptyComplex B⟩

/-- **THEOREM.**  The uniform weight 1 satisfies every named invariance
axiom. -/
theorem uniformMeasure_satisfies (B : ℕ) :
    InvarianceAxioms B (uniformMeasure B) :=
  ⟨fun _ _ _ => rfl, fun _ => one_pos, fun _ => le_refl 1, rfl⟩

/-- **THEOREM.**  `1/|Aut|^2` satisfies every named invariance axiom. -/
theorem muSqMeasure_satisfies (B : ℕ) : InvarianceAxioms B (muSqMeasure B) :=
  ⟨fun K K' h => by
      show mu K ^ 2 = mu K' ^ 2
      rw [mu_congr h],
    fun K => pow_pos (mu_pos K) 2,
    fun K => pow_le_one₀ (mu_pos K).le (mu_le_one K),
    by
      show mu (emptyComplex B) ^ 2 = 1
      rw [mu_emptyComplex B]
      norm_num⟩

/-- **THEOREM.**  Every member of the countable family satisfies every
named invariance axiom. -/
theorem muPowMeasure_satisfies (B n : ℕ) :
    InvarianceAxioms B (muPowMeasure B n) :=
  ⟨fun K K' h => by
      show mu K ^ (n + 1) = mu K' ^ (n + 1)
      rw [mu_congr h],
    fun K => pow_pos (mu_pos K) (n + 1),
    fun K => pow_le_one₀ (mu_pos K).le (mu_le_one K),
    by
      show mu (emptyComplex B) ^ (n + 1) = 1
      rw [mu_emptyComplex B]
      norm_num⟩

/-! ## §5. The separation: the candidates are genuinely different -/

/-- **Pointwise strict separation.**  At the two-point witness the
symmetry-factor measure is strictly below the uniform weight:
`1/2 < 1`. -/
theorem muMeasure_lt_uniform_at_witness (B : ℕ) (hB : 2 ≤ B) :
    muMeasure B (twoPointComplex B hB) <
      uniformMeasure B (twoPointComplex B hB) := by
  show mu (twoPointComplex B hB) < 1
  rw [mu_twoPointComplex B hB]
  norm_num

/-- The two candidate measures are unequal as functions. -/
theorem muMeasure_ne_uniformMeasure (B : ℕ) (hB : 2 ≤ B) :
    muMeasure B ≠ uniformMeasure B := fun h =>
  absurd (congrFun h (twoPointComplex B hB))
    (ne_of_lt (muMeasure_lt_uniform_at_witness B hB))

/-- The squared candidate also separates from both. -/
theorem muSqMeasure_separations (B : ℕ) (hB : 2 ≤ B) :
    muSqMeasure B ≠ uniformMeasure B ∧ muSqMeasure B ≠ muMeasure B := by
  constructor
  · intro h
    have hval := congrFun h (twoPointComplex B hB)
    have hmu : muSqMeasure B (twoPointComplex B hB) = 1 / 4 := by
      show mu (twoPointComplex B hB) ^ 2 = 1 / 4
      rw [mu_twoPointComplex B hB]
      norm_num
    rw [hmu] at hval
    have huni : uniformMeasure B (twoPointComplex B hB) = 1 := rfl
    rw [huni] at hval
    norm_num at hval
  · intro h
    have hval := congrFun h (twoPointComplex B hB)
    have hmu2 : muSqMeasure B (twoPointComplex B hB) = 1 / 4 := by
      show mu (twoPointComplex B hB) ^ 2 = 1 / 4
      rw [mu_twoPointComplex B hB]
      norm_num
    have hmu1 : muMeasure B (twoPointComplex B hB) = 1 / 2 :=
      mu_twoPointComplex B hB
    rw [hmu2, hmu1] at hval
    norm_num at hval

/-! ## §6. Headline no-go theorems -/

/-- **HEADLINE (KILL + WITNESS).**  The named invariance axioms do NOT
determine the path-sum measure: the symmetry-factor measure `1/|Aut|`
and the uniform weight 1 BOTH satisfy every named axiom, yet they are
unequal, with the pointwise strict inequality exhibited at the concrete
two-point witness (where `|Aut| = 2`).  This is the kernel refutation of
the killed "mu-from-invariance" determination claim; the substrate
derivation of a unique measure remains OPEN. -/
theorem mu_not_determined_by_invariance (B : ℕ) (hB : 2 ≤ B) :
    InvarianceAxioms B (muMeasure B) ∧
    InvarianceAxioms B (uniformMeasure B) ∧
    muMeasure B ≠ uniformMeasure B ∧
    muMeasure B (twoPointComplex B hB) <
      uniformMeasure B (twoPointComplex B hB) :=
  ⟨muMeasure_satisfies B, uniformMeasure_satisfies B,
    muMeasure_ne_uniformMeasure B hB,
    muMeasure_lt_uniform_at_witness B hB⟩

/-- **Existential packaging of the headline.**  There exist two distinct
weight functions satisfying all the named invariance axioms. -/
theorem invariance_underdetermines_measure (B : ℕ) (hB : 2 ≤ B) :
    ∃ w₁ w₂ : BoundedComplex B → ℝ,
      InvarianceAxioms B w₁ ∧ InvarianceAxioms B w₂ ∧ w₁ ≠ w₂ :=
  ⟨muMeasure B, uniformMeasure B, muMeasure_satisfies B,
    uniformMeasure_satisfies B, muMeasure_ne_uniformMeasure B hB⟩

/-- The countable family is injective: distinct exponents give distinct
measures (separated at the two-point witness where `mu = 1/2`). -/
theorem muPowMeasure_injective (B : ℕ) (hB : 2 ≤ B) :
    Function.Injective (muPowMeasure B) := by
  have hval : ∀ n : ℕ,
      muPowMeasure B n (twoPointComplex B hB) = (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    show mu (twoPointComplex B hB) ^ (n + 1) = (1 / 2 : ℝ) ^ (n + 1)
    rw [mu_twoPointComplex B hB]
  have hanti : StrictAnti (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) := by
    intro a b hab
    exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
      (Nat.succ_lt_succ hab)
  intro n m h
  have h2 : ((1 : ℝ) / 2) ^ (n + 1) = ((1 : ℝ) / 2) ^ (m + 1) := by
    rw [← hval n, ← hval m, h]
  exact hanti.injective h2

/-- **HEADLINE (strengthened form).**  The named invariance axioms admit a
countably INFINITE injective family of measures `1/|Aut|^(n+1)`: the
underdetermination is not a two-point accident. -/
theorem invariance_admits_infinite_measure_family (B : ℕ) (hB : 2 ≤ B) :
    (∀ n : ℕ, InvarianceAxioms B (muPowMeasure B n)) ∧
      Function.Injective (muPowMeasure B) :=
  ⟨muPowMeasure_satisfies B, muPowMeasure_injective B hB⟩

/-! ## §7. Status record (honest boundary; RED flags stay RED) -/

/-- Status record for the measure-invariance no-go.  Every `true` flag is
tied to its kernel theorem by the grounding theorem below; the RED flags
stay false. -/
structure MeasureInvarianceNoGoStatus where
  /-- §1: `InvarianceAxioms` names the stateable invariance properties. -/
  named_axioms_stated : Bool
  /-- §4: `muMeasure_satisfies`. -/
  mu_satisfies_axioms : Bool
  /-- §4: `uniformMeasure_satisfies`. -/
  uniform_satisfies_axioms : Bool
  /-- §6: `mu_not_determined_by_invariance`. -/
  measures_separated : Bool
  /-- §6: `invariance_admits_infinite_measure_family`. -/
  infinite_family_exhibited : Bool
  /-- Disclosed scope limit: no disjoint-union factorization axiom is
  stateable against the existing `BoundedComplex` machinery. -/
  factorization_axiom_stateable : Bool
  /-- RED (OPEN): no substrate derivation of a unique measure exists;
  this module proves the named invariance axioms cannot supply one. -/
  substrate_measure_derived : Bool
  /-- RED (OPEN). -/
  Z_RS_continuum_limit : Bool

/-- The canonical status record. -/
def measureInvarianceNoGoStatus : MeasureInvarianceNoGoStatus where
  named_axioms_stated := true
  mu_satisfies_axioms := true
  uniform_satisfies_axioms := true
  measures_separated := true
  infinite_family_exhibited := true
  factorization_axiom_stateable := false
  substrate_measure_derived := false
  Z_RS_continuum_limit := false

/-- **Grounding theorem.**  Every `true` status flag is tied to a kernel
statement; the RED flags remain false. -/
theorem measureInvarianceNoGoStatus_grounded :
    (measureInvarianceNoGoStatus.named_axioms_stated = true ∧
      ∀ B : ℕ, ∃ w : BoundedComplex B → ℝ, InvarianceAxioms B w) ∧
    (measureInvarianceNoGoStatus.mu_satisfies_axioms = true ∧
      ∀ B : ℕ, InvarianceAxioms B (muMeasure B)) ∧
    (measureInvarianceNoGoStatus.uniform_satisfies_axioms = true ∧
      ∀ B : ℕ, InvarianceAxioms B (uniformMeasure B)) ∧
    (measureInvarianceNoGoStatus.measures_separated = true ∧
      ∀ B : ℕ, 2 ≤ B → muMeasure B ≠ uniformMeasure B) ∧
    (measureInvarianceNoGoStatus.infinite_family_exhibited = true ∧
      (∀ B n : ℕ, InvarianceAxioms B (muPowMeasure B n)) ∧
      ∀ B : ℕ, 2 ≤ B → Function.Injective (muPowMeasure B)) ∧
    measureInvarianceNoGoStatus.factorization_axiom_stateable = false ∧
    measureInvarianceNoGoStatus.substrate_measure_derived = false ∧
    measureInvarianceNoGoStatus.Z_RS_continuum_limit = false :=
  ⟨⟨rfl, fun B => ⟨uniformMeasure B, uniformMeasure_satisfies B⟩⟩,
    ⟨rfl, muMeasure_satisfies⟩,
    ⟨rfl, uniformMeasure_satisfies⟩,
    ⟨rfl, muMeasure_ne_uniformMeasure⟩,
    ⟨rfl, fun B n => muPowMeasure_satisfies B n, muPowMeasure_injective⟩,
    rfl, rfl, rfl⟩

#print axioms mu_not_determined_by_invariance
#print axioms invariance_underdetermines_measure
#print axioms invariance_admits_infinite_measure_family
#print axioms measureInvarianceNoGoStatus_grounded

end MeasureInvarianceNoGo
end SevenGaps
end Gravity
end IndisputableMonolith
