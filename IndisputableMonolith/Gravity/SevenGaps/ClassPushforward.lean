import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure

/-!
# Seven Gaps, Crux-2 (pillar 2, path-sum): the class pushforward of Z

## Protocol: QUOTIENT_BOOKKEEPING (panel-locked).

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms):**
* `FiniteQuotient.sum_fiberwise_quotient` and
  `FiniteQuotient.sum_eq_quotient_sum_classMass`: for a `Fintype α`, a
  `Setoid α`, and any `AddCommMonoid`-valued function, the finite sum over
  `α` decomposes over the fibers of the quotient map; when the function is
  constant on classes the fiber sum collapses to
  `fiberCard q • f (rep q)`.  Generic; no group action anywhere.
  Decidability of the quotient is supplied classically (this is
  noncomputable measure bookkeeping, not computation).
* `PathSum.classMass`: for `q : TriangulationClass B`,
  `classMass q = Σ_{K : ⟦K⟧ = q} μ(K)`, and
  `PathSum.Z_eq_classPushforward`: for any weight `w` constant on classes
  (explicit hypothesis `hw`), `Z B w = Σ_q classMass(q) · w(rep q)`.
  NOTE (what `classMass` IS and IS NOT): by
  `PathSum.classMass_eq_fiberCard_mul_mu`,
  `classMass q = |fiber(q)| · (1/|Aut(rep q)|)`.  It is NOT `1/|Aut|` per
  class: the labeled fiber cardinality multiplies the symmetry factor.
* **FORK VERDICT (C1 landmine DETONATED as a kernel fact):**
  `PathSum.exists_nonSingleton_fiber` exhibits, at `B = 2`, two DISTINCT
  labeled complexes (`edgeAB` with edge `(0,1)`, `edgeBA` with edge
  `(1,0)`) related by an explicit vertex-swap relabeling
  (`edgeSwapRelabel`), and `PathSum.one_lt_fiberCard_edgeClass` shows the
  corresponding quotient fiber has cardinality `> 1`.  The numeric
  separation is itself a THEOREM: `PathSum.mu_lt_classMass_edgeClass`
  proves `μ(edgeAB) < classMass(⟦edgeAB⟧)`, so (kernel fact, not prose)
  the class decomposition of the standing `Z` of `PathSumMeasure` carries
  the weight `|fiber| · (1/|Aut|)` per class and differs from the
  inequivalent-class sum with weights `1/|Aut|` already at `B = 2`.
  SCOPE OF THE DETONATION: this concerns `PathSum.Z`, the LABELED sum of
  `PathSumMeasure`, ONLY.  It does not apply to the exact-shell
  `Z_RS_uv` of the `ExactShellGaugeUV` wave, which is defined in the
  quotient-sum convention per its own header; the two are different
  conventions, not a contradiction.

**MODEL / NEXT WAVE (recorded, not claimed):**
* The quotient-first object (a path sum defined directly on
  `TriangulationClass B` with per-class `1/|Aut|` weights, and its
  relation to the labeled `Z` via orbit counting) is PROMOTED to the next
  wave; it is not constructed here.

**OPEN (flags stay RED; nothing here changes them):**
* `Z_RS_continuum_limit` : RED.  No continuum-limit or "prepares
  convergence" claim is made anywhere in this module.
* `substrate_measure_derived` : RED.  The `1/|Aut|` convention is a MODEL
  input; no derivation from invariance + normalization is attempted.
* `gap1_bridge_derived` : RED.

## Proof notes
* Classical decidability instances are used for quotient `Finset`s
  (noncomputable, honest); no `decide` / `native_decide` anywhere in this
  module; no numerical cardinality evaluation, only structure.
* All undischarged premises are explicit hypothesis parameters (`hw`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

open PathSumMeasure

/-! ## §1. Generic finite-quotient fiber decomposition (T1)

No `MulAction`, no group anywhere: a `Fintype`, a `Setoid`, and finite-sum
bookkeeping over the fibers of the quotient map. -/

namespace FiniteQuotient

/-- A quotient of a finite type is a finite type (noncomputable via
classical choice; fine for measure bookkeeping).  SCOPED so downstream
files do not silently pick it up; activate with `open FiniteQuotient`. -/
noncomputable scoped instance instFintypeQuotient {α : Type*} [Fintype α]
    (s : Setoid α) : Fintype (Quotient s) :=
  Fintype.ofFinite _

/-- Classical decidability of quotient equality (low priority so any real
decidable instance wins; honest noncomputable bookkeeping, never used for
computation).  SCOPED so downstream files do not silently pick it up;
activate with `open FiniteQuotient`. -/
noncomputable scoped instance (priority := 10) instDecEqQuotient {α : Type*}
    (s : Setoid α) : DecidableEq (Quotient s) :=
  Classical.decEq _

/-- The labeled fiber of a quotient class: all elements of `α` mapping to
`q` under the quotient map.  Decidability is classical (noncomputable
bookkeeping). -/
noncomputable def classFiber {α : Type*} [Fintype α] (s : Setoid α)
    (q : Quotient s) : Finset α :=
  Finset.univ.filter (fun a => Quotient.mk s a = q)

/-- Membership in the fiber is exactly quotient-map equality. -/
theorem mem_classFiber {α : Type*} [Fintype α] (s : Setoid α)
    (q : Quotient s) (a : α) :
    a ∈ classFiber s q ↔ Quotient.mk s a = q := by
  unfold classFiber
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The labeled cardinality of a quotient fiber. -/
noncomputable def fiberCard {α : Type*} [Fintype α] (s : Setoid α)
    (q : Quotient s) : ℕ :=
  (classFiber s q).card

/-- **THEOREM (T1, fiber decomposition).**  A finite sum over a `Fintype`
decomposes over the fibers of any quotient map:
`Σ_{a : α} g a = Σ_{q : Quotient s} Σ_{a ∈ fiber q} g a`.
Generic (`AddCommMonoid` values); proved via `Finset.sum_fiberwise`. -/
theorem sum_fiberwise_quotient {α : Type*} [Fintype α] (s : Setoid α)
    {M : Type*} [AddCommMonoid M] (g : α → M) :
    ∑ a : α, g a = ∑ q : Quotient s, ∑ a ∈ classFiber s q, g a := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (Quotient.mk s) g]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr ?_ fun a _ => rfl
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_classFiber]

/-- **THEOREM (T1, class-constant collapse).**  If `f` is constant on
classes (mk-equality hypothesis), the fiber sum collapses:
`Σ_{a : α} f a = Σ_{q} fiberCard(q) • f (rep q)` where `rep q = q.out`. -/
theorem sum_eq_quotient_sum_classMass {α : Type*} [Fintype α] (s : Setoid α)
    {M : Type*} [AddCommMonoid M] (f : α → M)
    (hf : ∀ a b, Quotient.mk s a = Quotient.mk s b → f a = f b) :
    ∑ a : α, f a = ∑ q : Quotient s, fiberCard s q • f (Quotient.out q) := by
  rw [sum_fiberwise_quotient s f]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hconst : ∀ a ∈ classFiber s q, f a = f (Quotient.out q) := by
    intro a ha
    exact hf a (Quotient.out q)
      (((mem_classFiber s q a).mp ha).trans (Quotient.out_eq q).symm)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  rfl

end FiniteQuotient

/-! ## §2. The class pushforward of the labeled path sum (T2, T3) -/

namespace PathSum

open FiniteQuotient

/-- Bridge: quotient-map equality yields a relabeling equivalence
(`Quotient.exact` specialized to `relabelSetoid`). -/
theorem equivalent_of_mk_eq {B : ℕ} {K K' : BoundedComplex B}
    (h : Quotient.mk (relabelSetoid B) K = Quotient.mk (relabelSetoid B) K') :
    Equivalent K K' :=
  Quotient.exact h

/-- **T2 (definition).**  The pushforward mass of a triangulation class:
the sum of the labeled measure `μ` over the labeled fiber of the class.
WHAT THIS IS: `classMass q = |fiber(q)| · (1/|Aut(rep q)|)`
(`classMass_eq_fiberCard_mul_mu` below).  WHAT THIS IS NOT: it is NOT the
per-class weight `1/|Aut|`; the labeled fiber cardinality multiplies in. -/
noncomputable def classMass {B : ℕ} (q : TriangulationClass B) : ℝ :=
  ∑ K ∈ classFiber (relabelSetoid B) q, mu K

/-- **T3 (the fork detector, identity form).**  The pushforward class mass
is the labeled fiber cardinality times the symmetry factor of the class
representative: `classMass q = |fiber(q)| · μ(rep q)`.  Kernel-checked on
the actual carrier; uses `mu_congr` (μ is a class function). -/
theorem classMass_eq_fiberCard_mul_mu {B : ℕ} (q : TriangulationClass B) :
    classMass q = (fiberCard (relabelSetoid B) q : ℝ) * mu (Quotient.out q) := by
  unfold classMass
  have hconst : ∀ K ∈ classFiber (relabelSetoid B) q, mu K = mu (Quotient.out q) := by
    intro K hK
    exact mu_congr (equivalent_of_mk_eq
      (((mem_classFiber (relabelSetoid B) q K).mp hK).trans (Quotient.out_eq q).symm))
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- **T2 (headline).**  For any weight `w` constant on classes (explicit
hypothesis `hw`; note `unitaryWeight S` is class-constant only when `S`
is), the labeled path sum `Z` equals its class pushforward:
`Z B w = Σ_{q : TriangulationClass B} classMass(q) · w(rep q)`.
HONEST SCOPE: `classMass q = |fiber(q)| · (1/|Aut(rep q)|)`
(see `classMass_eq_fiberCard_mul_mu`), NOT `1/|Aut|` per class; this
theorem does NOT equate `Z` with the inequivalent-class sum with weights
`1/|Aut|` (the two weights are separated as a kernel fact by
`mu_lt_classMass_edgeClass`, built on `exists_nonSingleton_fiber`). -/
theorem Z_eq_classPushforward (B : ℕ) (w : BoundedComplex B → ℂ)
    (hw : ∀ K K', Equivalent K K' → w K = w K') :
    Z B w = ∑ q : TriangulationClass B,
      (classMass q : ℂ) * w (Quotient.out q) := by
  unfold Z
  rw [FiniteQuotient.sum_fiberwise_quotient (relabelSetoid B)
    (fun K => (mu K : ℂ) * w K)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmem : ∀ K ∈ classFiber (relabelSetoid B) q, Equivalent K (Quotient.out q) := by
    intro K hK
    exact equivalent_of_mk_eq
      (((mem_classFiber (relabelSetoid B) q K).mp hK).trans (Quotient.out_eq q).symm)
  calc ∑ K ∈ classFiber (relabelSetoid B) q, (mu K : ℂ) * w K
      = ∑ K ∈ classFiber (relabelSetoid B) q, (mu K : ℂ) * w (Quotient.out q) := by
        refine Finset.sum_congr rfl fun K hK => ?_
        rw [hw K (Quotient.out q) (hmem K hK)]
    _ = (∑ K ∈ classFiber (relabelSetoid B) q, (mu K : ℂ)) * w (Quotient.out q) := by
        rw [← Finset.sum_mul]
    _ = (classMass q : ℂ) * w (Quotient.out q) := by
        unfold classMass
        rw [Complex.ofReal_sum]

/-- The unitary instance: for a class-constant action `S`, the unitary
path sum equals its class pushforward.  Same honest scope as
`Z_eq_classPushforward`. -/
theorem zRS_eq_classPushforward (B : ℕ) (S : BoundedComplex B → ℝ)
    (hS : ∀ K K', Equivalent K K' → S K = S K') :
    Z B (unitaryWeight S) = ∑ q : TriangulationClass B,
      (classMass q : ℂ) * unitaryWeight S (Quotient.out q) := by
  refine Z_eq_classPushforward B (unitaryWeight S) ?_
  intro K K' h
  unfold unitaryWeight
  rw [hS K K' h]

/-! ## §3. T3 fork evaluation: a fiber of cardinality > 1 exists

The `edgeVerts` field is an ORDERED pair, so swapping the two vertex
labels of a one-edge complex produces a DIFFERENT labeled complex that is
`Equivalent` to the original via the explicit vertex-swap relabeling.
Witness at `B = 2`: `nV = 2`, `nE = 1`, `nT = 0`. -/

/-- Labeled complex at `B = 2`: one edge, ordered `(0, 1)`.  (`abbrev` so
the size fields reduce during numeral elaboration.) -/
abbrev edgeAB : BoundedComplex 2 where
  nV := 2
  nE := 1
  nT := 0
  hV := le_refl 2
  hE := one_le_two
  hT := Nat.zero_le 2
  edgeVerts := fun _ => (0, 1)
  tetVerts := fun t => t.elim0

/-- Labeled complex at `B = 2`: one edge, ordered `(1, 0)` (the vertex
labels of `edgeAB` swapped).  (`abbrev` so the size fields reduce during
numeral elaboration.) -/
abbrev edgeBA : BoundedComplex 2 where
  nV := 2
  nE := 1
  nT := 0
  hV := le_refl 2
  hE := one_le_two
  hT := Nat.zero_le 2
  edgeVerts := fun _ => (1, 0)
  tetVerts := fun t => t.elim0

/-- The explicit vertex-swap relabeling `edgeAB ≃ edgeBA`. -/
def edgeSwapRelabel : Relabel edgeAB edgeBA where
  vEquiv := Equiv.swap 0 1
  eEquiv := Equiv.refl _
  tEquiv := Equiv.refl _
  edge_comm := fun _ => by
    show ((1 : Fin 2), (0 : Fin 2)) =
      (Equiv.swap (0 : Fin 2) 1 (0 : Fin 2), Equiv.swap (0 : Fin 2) 1 (1 : Fin 2))
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  tet_comm := fun t _ => t.elim0

/-- Labeled observable separating the two witnesses: the numeric value of
the first endpoint of edge `0` (or `0` if there is no edge). -/
def firstEndpointVal {B : ℕ} (K : BoundedComplex B) : ℕ :=
  if h : 0 < K.nE then ((K.edgeVerts ⟨0, h⟩).1 : ℕ) else 0

theorem firstEndpointVal_edgeAB : firstEndpointVal edgeAB = 0 := rfl

theorem firstEndpointVal_edgeBA : firstEndpointVal edgeBA = 1 := rfl

/-- The two witnesses are DISTINCT labeled complexes (they differ on the
labeled observable `firstEndpointVal`). -/
theorem edgeAB_ne_edgeBA : edgeAB ≠ edgeBA := by
  intro h
  have h0 := congrArg firstEndpointVal h
  rw [firstEndpointVal_edgeAB, firstEndpointVal_edgeBA] at h0
  exact absurd h0 (by norm_num)

/-- **T3 FORK VERDICT (non-singleton fiber; C1 landmine detonated).**
There exist two distinct labeled complexes that are equivalent: the
quotient fibers of `TriangulationClass` are NOT all singletons, so the
labeled pushforward mass `classMass = |fiber| · (1/|Aut|)` genuinely
differs from the per-class `1/|Aut|` weight.  Explicit witness at
`B = 2`. -/
theorem exists_nonSingleton_fiber :
    ∃ K K' : BoundedComplex 2, K ≠ K' ∧ Equivalent K K' :=
  ⟨edgeAB, edgeBA, edgeAB_ne_edgeBA, ⟨edgeSwapRelabel⟩⟩

/-- **T3 FORK VERDICT (count form).**  The fiber of the one-edge class at
`B = 2` has labeled cardinality strictly greater than 1: both `edgeAB`
and `edgeBA` lie in it. -/
theorem one_lt_fiberCard_edgeClass :
    1 < fiberCard (relabelSetoid 2) (Quotient.mk (relabelSetoid 2) edgeAB) := by
  have hmemAB : edgeAB ∈ classFiber (relabelSetoid 2)
      (Quotient.mk (relabelSetoid 2) edgeAB) :=
    (mem_classFiber (relabelSetoid 2) _ edgeAB).mpr rfl
  have hmemBA : edgeBA ∈ classFiber (relabelSetoid 2)
      (Quotient.mk (relabelSetoid 2) edgeAB) :=
    (mem_classFiber (relabelSetoid 2) _ edgeBA).mpr
      (Quotient.sound ⟨edgeSwapRelabel.symm⟩)
  exact Finset.one_lt_card.mpr
    ⟨edgeBA, hmemBA, edgeAB, hmemAB, fun h => edgeAB_ne_edgeBA h.symm⟩

/-- **T3 FORK VERDICT (numeric witness; the formalized detonation).**
At the `B = 2` edge class the labeled measure of a single representative
is STRICTLY BELOW the pushforward class mass:
`μ(edgeAB) < classMass(⟦edgeAB⟧)`.  Hence a path sum carrying weight
`classMass` per class is NOT the per-class `1/|Aut|` sum, as a kernel
fact (via `classMass_eq_fiberCard_mul_mu`, `one_lt_fiberCard_edgeClass`,
`mu_congr`, and `mu_pos`).  This concerns the LABELED `PathSum.Z` object
only. -/
theorem mu_lt_classMass_edgeClass :
    mu edgeAB < classMass (Quotient.mk (relabelSetoid 2) edgeAB) := by
  have hrep : mu (Quotient.out (Quotient.mk (relabelSetoid 2) edgeAB)) =
      mu edgeAB :=
    mu_congr (equivalent_of_mk_eq (Quotient.out_eq _))
  rw [classMass_eq_fiberCard_mul_mu, hrep]
  have hcard : (1 : ℝ) < (fiberCard (relabelSetoid 2)
      (Quotient.mk (relabelSetoid 2) edgeAB) : ℝ) := by
    exact_mod_cast one_lt_fiberCard_edgeClass
  calc mu edgeAB = 1 * mu edgeAB := (one_mul _).symm
    _ < _ * mu edgeAB := mul_lt_mul_of_pos_right hcard (mu_pos edgeAB)

end PathSum

/-! ## §4. Status ledger (rfl-forced; RED flags stay RED) -/

/-- Status record for the class-pushforward wave.  No `True` shells; every
flag is forced by `rfl` below. -/
structure ClassPushforwardStatus where
  generic_fiber_decomposition_proved : Bool
  classMass_defined : Bool
  Z_eq_classPushforward_proved : Bool
  classMass_is_fiberCard_mul_mu : Bool
  nonSingleton_fiber_exhibited : Bool
  /-- FALSE (C1 detonated): the standing labeled `PathSum.Z` is NOT the
  inequivalent-class sum with per-class `1/|Aut|` weights; the kernel
  witness is `PathSum.mu_lt_classMass_edgeClass`.  (Says nothing about
  the separate quotient-sum convention of the exact-shell `Z_RS_uv`.) -/
  Z_is_invAut_class_sum : Bool
  /-- FALSE: the quotient-first path-sum object is promoted to the next
  wave, not constructed here. -/
  quotient_first_object_constructed : Bool
  /-- RED. -/
  Z_RS_continuum_limit : Bool
  /-- RED. -/
  substrate_measure_derived : Bool
  /-- RED. -/
  gap1_bridge_derived : Bool

/-- The class-pushforward status after this module. -/
def classPushforwardStatus : ClassPushforwardStatus where
  generic_fiber_decomposition_proved := true
  classMass_defined := true
  Z_eq_classPushforward_proved := true
  classMass_is_fiberCard_mul_mu := true
  nonSingleton_fiber_exhibited := true
  Z_is_invAut_class_sum := false
  quotient_first_object_constructed := false
  Z_RS_continuum_limit := false
  substrate_measure_derived := false
  gap1_bridge_derived := false

theorem classPushforwardStatus_flags :
    classPushforwardStatus.generic_fiber_decomposition_proved = true ∧
    classPushforwardStatus.classMass_defined = true ∧
    classPushforwardStatus.Z_eq_classPushforward_proved = true ∧
    classPushforwardStatus.classMass_is_fiberCard_mul_mu = true ∧
    classPushforwardStatus.nonSingleton_fiber_exhibited = true ∧
    classPushforwardStatus.Z_is_invAut_class_sum = false ∧
    classPushforwardStatus.quotient_first_object_constructed = false ∧
    classPushforwardStatus.Z_RS_continuum_limit = false ∧
    classPushforwardStatus.substrate_measure_derived = false ∧
    classPushforwardStatus.gap1_bridge_derived = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SevenGaps
end Gravity
end IndisputableMonolith
