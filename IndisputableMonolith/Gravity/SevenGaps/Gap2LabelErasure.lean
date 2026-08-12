import IndisputableMonolith.Gravity.SevenGaps.Gap2NonEquivariantPosting
import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingDerivation

/-!
# Gap 2 / A18: label erasure Jacobian (lane C4)

## Scoped headline (exact shape; flag 8 unmoved)

mu is the pushforward of a local relabeling-invariant labeled weight; 1/|Aut| is the
erasure Jacobian; the surviving freedom is the local numerator and three fugacities.

This module does **not** assert flag 8 closed.  Flag 8 moves only on G1∧G2 PASS plus later
fugacity elimination plus numerator triviality.  `FullTheoryLedger` is not imported.
`measure_flag_moved = false` is rfl-forced below.

## What is proved

**D1 (statability gate G1).**  On serially named (labeled) bounded complexes, a
`labeledWeight` carries no `gibbsWeight` factor.  `RelabelInvariant` is stated
letterwise: invariance under the serial-name permutation action (`Gap2GaugeVolume.push`).
Its hypothesis side names neither `Aut`, nor orbit, nor stabilizer, nor gauge class, nor
canonical representative.  For the erasure map `q = Quotient.mk (relabelSetoid B)`,

  `(q_* w)(K) = w(L_K) · (nV! · nE! · nT!) / |Aut K|`

by orbit-stabilizer (`Gap2GaugeVolume.orbitCard_mul_autCard`).  Corollary:
`gibbsWeight` is the size-only factor of that Jacobian (not a substrate hypothesis).

**D2 (discrimination gate G2).**  Locality `h(A ⊔ B) = h(A) + h(B)` is an explicit
hypothesis (the raw `LetterCost` API admits ambient-dependent charges).  On the
admissible witness `A = dust 1` with `A ⊔ A` admissible, `|Aut(A ⊔ A)| = 2 · |Aut A|²`
by the S₂ wreath factor, so `log|Aut|` is not disjoint-additive.  Hence no locally
additive cost realizes `log|Aut|`.  Fugacity-robust corollary: no
disjoint-multiplicative numerator `Q` times count fugacities converts the gauge weight
into uniform-on-iso-classes, because the S₂ factor cannot be absorbed.

## Pre-flight Aut note (directed carrier)

Library `Aut K := Relabel K K` is the group of incidence-preserving index bijections on
the directed/ordered carrier.  Permuting isomorphic connected components is included
(component swap is an automorphism).  Reversing a directed edge with distinct endpoints
is **not** included.  Panel undirected witnesses `|Aut|=8` vs `|Aut|=2` at count vector
`(4,2,0)` therefore do **not** hold as stated; the directed recomputation is `|Aut|=2`
(two disjoint directed edges) vs `|Aut|=1` (directed 2-path plus isolated vertex), so
the predicted class-mass ratio is `1/2`, not `1/4`.  The D2 wreath identity used below
is unaffected: it needs only the S₂ factor on identical components, which the directed
carrier still supplies (witness: dust).

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LabelErasure

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume
open Gap2GluingDerivation Gap2PostingCostDerivation Gap2NonEquivariantPosting

variable {B : ℕ}

/-! ## §1. Letterwise relabeling invariance (G1 hypothesis side)

The invariance predicate below is the entire load of gate G1.  Its binders mention
serial-name permutations and the rename action only. -/

/-- A **labeled weight**: a real function of serially named bounded complexes.
Definitionally no `gibbsWeight` factor appears. -/
abbrev labeledWeight (B : ℕ) : Type := BoundedComplex B → ℝ

/-- Rename a labeled complex by independently permuting its vertex, edge, and
tetrahedron serial names (the carrier's incidence is transported).  This is
`Gap2GaugeVolume.push` under a letterwise name. -/
def rename (K : BoundedComplex B)
    (σv : Equiv.Perm (Fin K.nV)) (σe : Equiv.Perm (Fin K.nE))
    (σt : Equiv.Perm (Fin K.nT)) : BoundedComplex B :=
  Gap2GaugeVolume.push K (σv, σe, σt)

/-- **Letterwise relabeling invariance.**  The weight is unchanged when serial names
are permuted.  No Aut, orbit, stabilizer, gauge class, or canonical representative
appears in this definition. -/
def RelabelInvariant {B : ℕ} (w : labeledWeight B) : Prop :=
  ∀ (K : BoundedComplex B) (σv : Equiv.Perm (Fin K.nV))
    (σe : Equiv.Perm (Fin K.nE)) (σt : Equiv.Perm (Fin K.nT)),
    w (rename K σv σe σt) = w K

/-- Erasure: forget serial names down to the isomorphism class. -/
def erase (B : ℕ) : BoundedComplex B → TriangulationClass B :=
  Quotient.mk (relabelSetoid B)

/-- Pushforward of a labeled weight along erasure: sum the weight over the fibre. -/
noncomputable def erasePush {B : ℕ} (w : labeledWeight B)
    (c : TriangulationClass B) : ℝ :=
  classMass w c

/-! ## §2. Letterwise invariance implies class-function invariance -/

theorem rename_eq_push (K : BoundedComplex B)
    (σv : Equiv.Perm (Fin K.nV)) (σe : Equiv.Perm (Fin K.nE))
    (σt : Equiv.Perm (Fin K.nT)) :
    rename K σv σe σt = Gap2GaugeVolume.push K (σv, σe, σt) := rfl

/-- Letterwise invariance upgrades to invariance under any relabeling equivalence. -/
theorem relabelInvariant_implies_classFun {w : labeledWeight B}
    (hw : RelabelInvariant w) {K K' : BoundedComplex B} (h : Equivalent K K') :
    w K = w K' := by
  obtain ⟨r⟩ := h
  let g : Gap2GaugeVolume.SectorGroup K := Gap2GaugeVolume.toSector ⟨K', r⟩
  have hpair : Gap2GaugeVolume.ofSector K g = ⟨K', r⟩ :=
    Gap2GaugeVolume.ofSector_toSector K ⟨K', r⟩
  have hpush : Gap2GaugeVolume.push K g = K' := congrArg Sigma.fst hpair
  have hw' : w (Gap2GaugeVolume.push K g) = w K := hw K g.1 g.2.1 g.2.2
  rw [← hpush, hw']

/-- The constant weight `1` is letterwise relabeling-invariant. -/
theorem relabelInvariant_one : RelabelInvariant (fun _ : BoundedComplex B => (1 : ℝ)) := by
  intro K σv σe σt; rfl

/-- An equivariant letter cost has a letterwise-invariant Boltzmann numerator. -/
theorem relabelInvariant_exp_neg_history {c : LetterCost} (hc : Equivariant c) :
    RelabelInvariant (fun K : BoundedComplex B => Real.exp (-(historyCost c B K))) := by
  intro K σv σe σt
  have hEq : Equivalent K (rename K σv σe σt) :=
    Gap2GaugeVolume.equivalent_push K (σv, σe, σt)
  obtain ⟨r⟩ := hEq
  simp only [historyCost_invariant hc r]

/-! ## §3. D1: pushforward equals labeled weight times the gauge divisor -/

/-- **D1.**  For any letterwise relabeling-invariant labeled weight, the erasure
pushforward on the class of `K` equals the weight at `K` times the gauge divisor
`(nV! nE! nT!) / |Aut K|`.  `|Aut|` appears only in the conclusion. -/
theorem pushforward_labeledWeight_eq_gauge_divisor
    (w : labeledWeight B) (hw : RelabelInvariant w) (K : BoundedComplex B) :
    erasePush w (erase B K)
      = w K * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
          / (Nat.card (Aut K) : ℝ) := by
  have hinv : ∀ K₁ K₂ : BoundedComplex B, Equivalent K₁ K₂ → w K₁ = w K₂ :=
    fun _ _ h => relabelInvariant_implies_classFun hw h
  have hpos : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by exact_mod_cast autCard_pos K
  have hmass :
      erasePush w (erase B K)
        = (gaugeOrbitCard K : ℝ) * w (Quotient.out (erase B K)) := by
    unfold erasePush erase
    rw [classMass_of_invariant w hinv, orbitCardClass_mk]
  have hout : w (Quotient.out (erase B K)) = w K :=
    hinv _ _ (equivalent_out K)
  have hOS :
      (gaugeOrbitCard K : ℝ) * (Nat.card (Aut K) : ℝ)
        = ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
    exact_mod_cast orbitCard_mul_autCard K
  rw [hmass, hout]
  have hdiv :
      (gaugeOrbitCard K : ℝ)
        = ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
            / (Nat.card (Aut K) : ℝ) :=
    (eq_div_iff hpos.ne').2 hOS
  rw [hdiv, mul_div_assoc, mul_comm]

/-- Uniform labeled weight pushes forward to the orbit count; times `gibbsWeight` is `mu`. -/
theorem mu_eq_gibbs_mul_erasePush_one (K : BoundedComplex B) :
    mu K
      = gibbsWeight K
          * erasePush (fun _ : BoundedComplex B => (1 : ℝ)) (erase B K) := by
  have h1 := pushforward_labeledWeight_eq_gauge_divisor
    (fun _ : BoundedComplex B => (1 : ℝ)) relabelInvariant_one K
  have hpos : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by exact_mod_cast autCard_pos K
  unfold gibbsWeight mu
  rw [h1]
  field_simp [hpos.ne']

/-- **Corollary.**  The posted weight factors as Boltzmann numerator times
`gibbsWeight`; under letterwise invariance of the numerator, D1 identifies
`gibbsWeight` as the size-only factor of the erasure Jacobian
`(nV! nE! nT!) / |Aut|`, not as an independent substrate hypothesis. -/
theorem gibbsWeight_is_the_erasure_jacobian
    {c : LetterCost} (hc : Equivariant c) (K : BoundedComplex B) :
    erasePush (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K'))) (erase B K)
      = Real.exp (-(historyCost c B K))
          * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
          / (Nat.card (Aut K) : ℝ)
      ∧ postedWeight c B K
          = Real.exp (-(historyCost c B K)) * gibbsWeight K
      ∧ mu K
          = gibbsWeight K
              * erasePush (fun _ : BoundedComplex B => (1 : ℝ)) (erase B K) :=
  ⟨pushforward_labeledWeight_eq_gauge_divisor _
      (relabelInvariant_exp_neg_history hc) K,
    rfl,
    mu_eq_gibbs_mul_erasePush_one K⟩

/-! ## §4. G2 witness: admissible A with A ⊔ A admissible -/

/-- **G2(a).**  The singleton dust complex is admissible at cap 1, and its
disjoint union with itself is admissible at cap 2 (equivalent to `dust 2`). -/
theorem dust_twin_admissible :
    (dust 1 : BoundedComplex 1).nV = 1 ∧ (dust 1).nE = 0 ∧ (dust 1).nT = 0
      ∧ Equivalent (dunion (dust 1) (dust 1)) (dust 2) :=
  ⟨rfl, rfl, rfl, dunion_dust_equivalent 1 1⟩

/-- **Wreath factor on the dust twin.**  `|Aut(A ⊔ A)| = 2 · |Aut A|²` for
`A = dust 1`. -/
theorem autCard_dust_twin :
    Nat.card (Aut (dunion (dust 1) (dust 1)))
      = 2 * (Nat.card (Aut (dust 1))) ^ 2 := by
  rw [autCard_congr (dunion_dust_equivalent 1 1), autCard_dust, autCard_dust]
  decide

/-- The wreath factor is strictly larger than the naive product of Aut counts. -/
theorem autCard_dust_twin_ne_square :
    Nat.card (Aut (dunion (dust 1) (dust 1)))
      ≠ Nat.card (Aut (dust 1)) * Nat.card (Aut (dust 1)) := by
  rw [autCard_dust_twin, autCard_dust]
  decide

/-! ## §5. D2: no local additive cost realizes log|Aut| -/

/-- Explicit locality hypothesis for a size-indexed real cost: additive under
disjoint union.  Required because the raw `LetterCost` API admits
ambient-dependent charges, so additivity is not free. -/
def LocallyAdditive (h : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ (B B' : ℕ) (A : BoundedComplex B) (C : BoundedComplex B'),
    h (B + B') (dunion A C) = h B A + h B' C

/-- **D2.**  No locally additive real cost on bounded complexes can realize
`log|Aut|` at every complex.  Witness: `A = dust 1` forces
`log|Aut(A ⊔ A)| = log 2` against `2 · log|Aut A| = 0`. -/
theorem no_local_additive_cost_realizes_log_aut :
    ¬ ∃ h : ∀ B : ℕ, BoundedComplex B → ℝ,
        LocallyAdditive h
          ∧ (∀ (B : ℕ) (K : BoundedComplex B),
              h B K = Real.log (Nat.card (Aut K) : ℝ)) := by
  intro ⟨h, hloc, hlog⟩
  have hEq := hloc 1 1 (dust 1) (dust 1)
  have hEq' :
      Real.log (Nat.card (Aut (dunion (dust 1) (dust 1))) : ℝ)
        = Real.log (Nat.card (Aut (dust 1)) : ℝ)
            + Real.log (Nat.card (Aut (dust 1)) : ℝ) := by
    simpa [hlog] using hEq
  have hL : Nat.card (Aut (dunion (dust 1) (dust 1))) = 2 := by
    rw [autCard_congr (dunion_dust_equivalent 1 1), autCard_dust]; decide
  have hR : Nat.card (Aut (dust 1)) = 1 := by rw [autCard_dust]; decide
  have h2 : Real.log (2 : ℝ) = Real.log (1 : ℝ) + Real.log (1 : ℝ) := by
    simpa [hL, hR] using hEq'
  have h0 : Real.log (1 : ℝ) = 0 := Real.log_one
  have hbad : Real.log (2 : ℝ) = 0 := by simpa [h0] using h2
  exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))) hbad

/-- **Fugacity-robust corollary.**  No disjoint-multiplicative numerator `Q`
together with three count fugacities can convert the gauge weight into
uniform-on-iso-classes: the identity `Q · z^counts = |Aut|` fails at the dust
twin because the left side squares while the right side carries the S₂ factor. -/
theorem uniform_is_not_a_local_pushforward :
    ¬ ∃ (Q : ∀ B : ℕ, BoundedComplex B → ℝ) (zV zE zT : ℝ),
        (∀ (B B' : ℕ) (A : BoundedComplex B) (C : BoundedComplex B'),
          Q (B + B') (dunion A C) = Q B A * Q B' C)
          ∧ (∀ (B : ℕ) (K : BoundedComplex B),
              Q B K * zV ^ K.nV * zE ^ K.nE * zT ^ K.nT
                = (Nat.card (Aut K) : ℝ)) := by
  intro ⟨Q, zV, zE, zT, hQ, hAut⟩
  have h1 := hAut 1 (dust 1)
  have h2 := hAut (1 + 1) (dunion (dust 1) (dust 1))
  have hQd := hQ 1 1 (dust 1) (dust 1)
  have hR : Nat.card (Aut (dust 1)) = 1 := by rw [autCard_dust]; decide
  have hL : Nat.card (Aut (dunion (dust 1) (dust 1))) = 2 := by
    rw [autCard_congr (dunion_dust_equivalent 1 1), autCard_dust]; decide
  -- At dust 1: Q * zV = 1.
  have hone : Q 1 (dust 1) * zV = (1 : ℝ) := by
    simpa [dust_nV, dust_nE, dust_nT, hR, pow_one, pow_zero, mul_one] using h1
  -- At the twin: Q(A⊔A) * zV^2 = 2, and Q(A⊔A) = Q(A)^2.
  have hsq : Q 1 (dust 1) * Q 1 (dust 1) * zV ^ 2 = (2 : ℝ) := by
    have h2' :
        Q (1 + 1) (dunion (dust 1) (dust 1))
            * zV ^ ((dust 1).nV + (dust 1).nV)
            * zE ^ ((dust 1).nE + (dust 1).nE)
            * zT ^ ((dust 1).nT + (dust 1).nT)
          = (2 : ℝ) := by
      simpa [dunion_nV, dunion_nE, dunion_nT, hL] using h2
    simpa [hQd, dust_nV, dust_nE, dust_nT, pow_zero, mul_one] using h2'
  have hpow : (Q 1 (dust 1) * zV) ^ 2 = (2 : ℝ) := by
    calc (Q 1 (dust 1) * zV) ^ 2
        = Q 1 (dust 1) * Q 1 (dust 1) * zV ^ 2 := by ring
      _ = 2 := hsq
  rw [hone] at hpow
  norm_num at hpow

/-! ## §6. Certificate: flag unmoved -/

structure LabelErasureIndex : Type where
  /-- D1 is stated with letterwise RelabelInvariant (G1). -/
  d1_stated_letterwise : Bool
  /-- D2 landed with locality explicit and the dust twin witness (G2). -/
  d2_wreath_witness : Bool
  /-- NOT claimed: flag 8 / gap2_measure_derived. -/
  measure_flag_moved : Bool

def labelErasureIndex : LabelErasureIndex where
  d1_stated_letterwise := true
  d2_wreath_witness := true
  measure_flag_moved := false

theorem index_d1 : labelErasureIndex.d1_stated_letterwise = true := rfl
theorem index_d2 : labelErasureIndex.d2_wreath_witness = true := rfl
/-- NOT moved.  Flag 8 stays false; this module derives the Jacobian reading, not
the full measure. -/
theorem index_flag_unmoved : labelErasureIndex.measure_flag_moved = false := rfl

/-! ## Axiom audit -/

#print axioms relabelInvariant_implies_classFun
#print axioms pushforward_labeledWeight_eq_gauge_divisor
#print axioms gibbsWeight_is_the_erasure_jacobian
#print axioms mu_eq_gibbs_mul_erasePush_one
#print axioms dust_twin_admissible
#print axioms autCard_dust_twin
#print axioms autCard_dust_twin_ne_square
#print axioms no_local_additive_cost_realizes_log_aut
#print axioms uniform_is_not_a_local_pushforward
#print axioms index_flag_unmoved

end Gap2LabelErasure
end SevenGaps
end Gravity
end IndisputableMonolith
