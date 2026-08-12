import IndisputableMonolith.Gravity.SevenGaps.Gap2FugacityPostingGluing
import IndisputableMonolith.Gravity.SevenGaps.Gap2LabelErasure
import IndisputableMonolith.Gravity.SevenGaps.Gap2LetterCostDichotomy

/-!
# Gap 2 / A19 (lane C17): fugacity elimination after the erasure Jacobian

## Scoped headline (exact shape; flag 8 unmoved)

After the C4 erasure Jacobian, any letter cost whose posted class mass equals `mu`
at the three atoms and is representable there by a size-blind weight `sizeWeight f`
forces `UnitFugacity f`, so the three sector fugacities collapse.  On the
gluing-residue family `characterSize z_V z_E z_T` this is exactly
`z_V = z_E = z_T = 1`.  Composed with the erasure Jacobian, the posted class mass
equals `mu` with no fugacity freedom on that class.

This module does **not** assert flag 8 closed.  Flag 8 still needs numerator
triviality for physical costs (the local Boltzmann factor).  `FullTheoryLedger`
is not imported.  `measure_flag_moved = false` is rfl-forced below.

## What is proved

**D1 (elimination, A1.4 class).**  `unit_fugacity_forced_after_erasure`: any letter
cost that posts `mu` at the three atoms, with class mass represented there by
`sizeWeight f`, forces `UnitFugacity f`.  This is A1.4's
`no_posting_countermodel_with_nonunit_fugacity`, named as the mandatory second half
after C4's divisor emergence.  Specialization
`three_fugacities_collapse_on_posting_mu`: on the gluing closed-form residue
`characterSize z_V z_E z_T`, posting `mu` at the atoms forces
`z_V = z_E = z_T = 1`.

**D2 (widening past atom-named `mu`, A1.7 class).**
`unit_fugacity_forced_by_surface_and_kindTotals`: on any census dilate family, a
letter cost with fixed kind totals whose dilate history is a pure surface term
forces the posted weight to equal `sizeWeight gibbsSize` everywhere, forces
`UnitFugacity gibbsSize`, and posts `mu` at every complex.  The atom values of
`mu` are derived, not assumed (`atom_normalizations_are_derived`).

**D3 (composition).**  `erasure_and_unit_fugacity_compose_to_mu`: for an
equivariant letter cost whose posted class mass at the atoms is represented by
`sizeWeight f` and equals `mu` there, the erasure Jacobian holds, `UnitFugacity f`
holds, and (when the representation extends to every complex and posts `mu`
everywhere) the size function is exactly `gibbsSize`, so the posted class mass
equals `mu` with no fugacity freedom.

## What blocks further widening (deliverable, not a failure)

1. **Non-`sizeWeight` posting.**  `tiltedCost` posts `mu` everywhere with a
   non-unit labeled numerator; its posted weight is not any `sizeWeight`
   (`postedWeight_tiltedCost_not_sizeWeight`).  At class-mass level the
   representing size function is still `gibbsSize` (unit).  So `UnitFugacity`
   as a predicate on a size function does not apply to the labeled weight, and
   the local numerator remains free for non-equivariant costs (A1.3).
2. **Structural conditions without naming `mu`.**  `characterCost` with any
   positive non-unit triple is kind-only, equivariant, size-blind, and glues,
   yet has non-unit fugacity (`gluing_and_posting_do_not_force_unit_fugacity`).
   Posting-layer structure plus gluing cannot supply the elimination; the
   load-bearing hypothesis names `mu` at the atoms.
3. **Costs without fixed kind totals.**  A1.7's escape `surfaceCost t` is
   equivariant, bulk-cancelling, and nonzero, with no fixed kind totals.  The
   A1.7 widening does not bind that class; the local numerator for physical
   costs without kind totals remains open.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2FugacityElimination

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume
open Gap2GluingDerivation Gap2PostingCostDerivation Gap2NonEquivariantPosting
open Gap2SizeBlindnessReach Gap2FugacityPostingGluing Gap2LabelErasure
open Gap2LetterCostDichotomy

noncomputable section

variable {B : ℕ}

/-! ## §1. Elimination on the A1.4 class (after erasure)

The panel's locked protocol: once the divisor genuinely emerges (C4), use A1.4
to eliminate `z_V, z_E, z_T`.  The content is A1.4's atom-only theorem; the
work here is naming it as the second half and specializing to the three-fugacity
residue. -/

/-- **C17 elimination (A1.4 class).**  After the erasure Jacobian, any letter cost
that posts the derived base measure `mu` at the three atoms, and whose posted
class mass there is represented by a size-blind weight `sizeWeight f`, forces
unit sector fugacity on `f`.  Equivariant or not, kind-only or not, gluing or
not.  The class on the theorem's face: atom-only posting of `mu`, plus
`sizeWeight`-representability of the class mass at those atoms. -/
theorem unit_fugacity_forced_after_erasure (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
    (hrep : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K)) :
    UnitFugacity f :=
  no_posting_countermodel_with_nonunit_fugacity c f hpost hrep

/-- **Specialization to the three fugacities.**  The gluing derivation's closed-form
residue is `characterSize z_V z_E z_T`.  Posting `mu` at the three atoms forces
`z_V = z_E = z_T = 1`.  This is the literal elimination of the three fugacities
named in the C4 surviving-freedom headline. -/
theorem three_fugacities_collapse_on_posting_mu {zV zE zT : ℝ}
    (_hzV : 0 < zV) (_hzE : 0 < zE) (_hzT : 0 < zT)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (sizeWeight (characterSize zV zE zT))
        (Quotient.mk (relabelSetoid B') K) = mu K) :
    zV = 1 ∧ zE = 1 ∧ zT = 1 := by
  have hUF : UnitFugacity (characterSize zV zE zT) :=
    posts_mu_at_atoms_forces_unit_fugacity (characterSize zV zE zT) hpost
  exact unitFugacity_characterSize_iff.mp hUF

/-- Same elimination, transported through the character cost's posted weight. -/
theorem three_fugacities_collapse_via_characterCost {zV zE zT : ℝ}
    (hzV : 0 < zV) (hzE : 0 < zE) (hzT : 0 < zT)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight (characterCost zV zE zT) B')
        (Quotient.mk (relabelSetoid B') K) = mu K) :
    zV = 1 ∧ zE = 1 ∧ zT = 1 := by
  have hrep : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (postedWeight (characterCost zV zE zT) B')
          (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight (characterSize zV zE zT))
          (Quotient.mk (relabelSetoid B') K) := by
    intro B' K
    rw [postedWeight_characterCost_eq hzV hzE hzT B']
  have hUF : UnitFugacity (characterSize zV zE zT) :=
    unit_fugacity_forced_after_erasure (characterCost zV zE zT) (characterSize zV zE zT)
      (fun B' K hv hi => hpost B' K hv hi)
      (fun B' K hv hi => hrep B' K)
  exact unitFugacity_characterSize_iff.mp hUF

/-! ## §2. Widening: A1.7 forces unit fugacity without naming `mu` at the atoms -/

/-- **Widening past A1.4's atom-named `mu` hypothesis.**  On any census dilate
family, fixed kind totals plus surface-pure dilate history force the posted weight
to equal `sizeWeight gibbsSize` at every complex, force `UnitFugacity gibbsSize`,
and post `mu` everywhere.  Strength, exactly: the `UnitFugacity gibbsSize` conjunct
is free once the posted weight is forced to `sizeWeight gibbsSize`
(`gibbsSize_unitFugacity` uses no binders); what the binders buy is A1.7's
posted-weight and class-mass forcing.  The three atom values of `mu` are derived
(`atom_normalizations_are_derived`), not assumed.  Class on the face:
`FixedKindTotals` + `SurfaceTotal` on a `CensusDilateFamily`. -/
theorem unit_fugacity_forced_by_surface_and_kindTotals
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (h : FixedKindTotals c) (hs : SurfaceTotal F c a e) :
    UnitFugacity gibbsSize
      ∧ (∀ (B' : ℕ) (K : BoundedComplex B'),
          postedWeight c B' K = sizeWeight gibbsSize K)
      ∧ (∀ (B' : ℕ) (K : BoundedComplex B'),
          classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K) := by
  refine ⟨gibbsSize_unitFugacity, ?_, ?_⟩
  · intro B' K
    have hgib := (the_measure_is_exactly_the_gauge_divisor F h hs B' K).2.1
    rw [hgib, gibbsWeight_eq_gibbsSize]
    rfl
  · intro B' K
    exact (the_measure_is_exactly_the_gauge_divisor F h hs B' K).2.2.2

/-- Corollary: the A1.7 class lands inside the A1.4 elimination hypothesis, with
representing size function `gibbsSize`. -/
theorem a17_lands_in_a14_elimination
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (h : FixedKindTotals c) (hs : SurfaceTotal F c a e) :
    UnitFugacity gibbsSize :=
  (unit_fugacity_forced_by_surface_and_kindTotals F h hs).1

/-! ## §3. Composition: erasure Jacobian + unit fugacity ⇒ `mu` with no fugacity freedom -/

/-- **Composition (atom class).**  For an equivariant letter cost that posts `mu`
at the three atoms with class mass represented there by `sizeWeight f`:

1. the erasure Jacobian holds (C4 / D1);
2. `UnitFugacity f` holds (C17 / D1);
3. at every atom, the posted class mass equals `mu`.

Class on the face: `Equivariant` + atom-only posting of `mu` +
`sizeWeight`-representability at the atoms.  This is the full current position of
the base/no-tilt split on that class: the divisor is the erasure Jacobian, and the
fugacity freedom has collapsed. -/
theorem erasure_and_unit_fugacity_compose_to_mu
    {c : LetterCost} (hc : Equivariant c) (f : ℕ → ℕ → ℕ → ℝ)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
    (hrep : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K)) :
    (∀ (K : BoundedComplex B),
        erasePush (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K')))
            (erase B K)
          = Real.exp (-(historyCost c B K))
              * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
              / (Nat.card (Aut K) : ℝ)
          ∧ postedWeight c B K = Real.exp (-(historyCost c B K)) * gibbsWeight K
          ∧ mu K
              = gibbsWeight K
                  * erasePush (fun _ : BoundedComplex B => (1 : ℝ)) (erase B K))
      ∧ UnitFugacity f
      ∧ (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
          classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K) :=
  ⟨fun K => gibbsWeight_is_the_erasure_jacobian hc K,
    unit_fugacity_forced_after_erasure c f hpost hrep,
    hpost⟩

/-- **Composition at full strength on the size-blind class.**  If the
`sizeWeight` representation and the posting of `mu` extend to every complex (not
only the atoms), the size function is exactly `gibbsSize` at every size triple
any complex realizes, so the posted class mass equals `mu` with the fugacity
character forced to the unit point. -/
theorem erasure_and_full_posting_force_gibbsSize
    {c : LetterCost} (hc : Equivariant c) (f : ℕ → ℕ → ℕ → ℝ)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
    (hrep : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K))
    (K : BoundedComplex B) :
    f K.nV K.nE K.nT = gibbsSize K.nV K.nE K.nT
      ∧ UnitFugacity f
      ∧ erasePush (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K')))
          (erase B K)
        = Real.exp (-(historyCost c B K))
            * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
            / (Nat.card (Aut K) : ℝ) := by
  have hUF : UnitFugacity f :=
    unit_fugacity_forced_after_erasure c f
      (fun B' K' hv hi => hpost B' K')
      (fun B' K' hv hi => hrep B' K')
  have hgs : f K.nV K.nE K.nT = gibbsSize K.nV K.nE K.nT := by
    have hmu : classMass (sizeWeight f) (Quotient.mk (relabelSetoid B) K) = mu K := by
      rw [← hrep B K]
      exact hpost B K
    exact (classMass_sizeWeight_eq_mu_iff f K).mp hmu
  refine ⟨hgs, hUF, ?_⟩
  exact (gibbsWeight_is_the_erasure_jacobian hc K).1

/-- **Composition on the A1.7 class.**  Erasure Jacobian plus the A1.7 forcing:
posted weight equals the Gibbs size-blind weight, unit fugacity holds, class mass
equals `mu`, and the three fugacities of the closed-form residue are gone. -/
theorem erasure_and_a17_compose_to_mu_no_fugacity
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (hc : Equivariant c) (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (K : BoundedComplex B) :
    erasePush (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K')))
        (erase B K)
      = Real.exp (-(historyCost c B K))
          * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
          / (Nat.card (Aut K) : ℝ)
      ∧ postedWeight c B K = sizeWeight gibbsSize K
      ∧ UnitFugacity gibbsSize
      ∧ classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K := by
  obtain ⟨hUF, hsw, hmu⟩ := unit_fugacity_forced_by_surface_and_kindTotals F h hs
  refine ⟨(gibbsWeight_is_the_erasure_jacobian hc K).1, hsw B K, hUF, hmu B K⟩

/-! ## §4. Obstruction witnesses: what blocks further widening -/

/-- **Obstruction 1 (labeled level).**  There exist costs that post `mu` everywhere
whose posted weight is not any `sizeWeight`, so the A1.4 elimination predicate
(`UnitFugacity` on a representing size function) does not apply to the labeled
weight.  At class-mass level the representing size function is still `gibbsSize`
(unit).  Witness: `tiltedCost (1/2)`. -/
theorem widening_blocked_by_non_sizeWeight_posting :
    ∃ (c : LetterCost),
      (∀ (B' : ℕ) (K : BoundedComplex B'),
          classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
        ∧ (¬ ∃ f : ℕ → ℕ → ℕ → ℝ,
              ∀ K : BoundedComplex 3, postedWeight c 3 K = sizeWeight f K)
        ∧ UnitFugacity gibbsSize := by
  have ht : |(1 / 2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have ht0 : (1 / 2 : ℝ) ≠ 0 := by norm_num
  refine ⟨tiltedCost (1 / 2), fun B' K => tiltedCost_posts_mu ht B' K,
    postedWeight_tiltedCost_not_sizeWeight ht ht0, gibbsSize_unitFugacity⟩

/-- **Obstruction 2 (no-`mu` structural class).**  Kind-only + equivariant +
size-blind + gluing leaves the fugacity free: for every positive non-unit triple
there is a countermodel.  So elimination cannot drop the hypothesis that names
`mu` at the atoms. -/
theorem widening_blocked_without_naming_mu {zV zE zT : ℝ}
    (hzV : 0 < zV) (hzE : 0 < zE) (hzT : 0 < zT)
    (hne : ¬ (zV = 1 ∧ zE = 1 ∧ zT = 1)) :
    ∃ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
      KindOnly c ∧ Equivariant c ∧ SizeBlind (postedWeight c)
        ∧ (∀ (B' : ℕ) (K : BoundedComplex B'), postedWeight c B' K = sizeWeight f K)
        ∧ CarrierShuffle f
        ∧ ¬ UnitFugacity f :=
  gluing_and_posting_do_not_force_unit_fugacity hzV hzE hzT hne

/-- **Obstruction 3 (A1.7 escape).**  Fixed kind totals is load-bearing for the
A1.7 widening: `surfaceCost t` is equivariant, bulk-cancelling, and nonzero, with
no fixed kind totals.  Costs without kind totals are outside the widened class. -/
theorem widening_blocked_without_kindTotals (F : CensusDilateFamily) {t : ℝ}
    (ht : t ≠ 0) :
    Equivariant (surfaceCost t)
      ∧ SurfaceTotal F (surfaceCost t) t 0
      ∧ ¬ FixedKindTotals (surfaceCost t)
      ∧ historyCost (surfaceCost t) 16 (dust 16) ≠ 0 :=
  fixed_kind_totals_is_load_bearing F ht

/-! ## §5. Verdict package and flag certificate -/

/-- **THE VERDICT.**  Four parts, composing C4 with C17 on the classes that
genuinely reach.

1.  Atom-only posting of `mu` plus `sizeWeight` representation forces unit
    fugacity (`unit_fugacity_forced_after_erasure`).
2.  On the three-fugacity residue, that is exactly `z_V = z_E = z_T = 1`.
3.  A1.7 widens past naming `mu`: surface purity plus kind totals derive unit
    fugacity and `mu` posting.
4.  Composed with the erasure Jacobian, the posted class mass equals `mu` with
    no fugacity freedom on those classes.

Flag 8 stays false: the local numerator for physical costs remains open, and
costs outside the `sizeWeight` / A1.7 classes are not bound. -/
theorem fugacity_elimination_verdict :
    (∀ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
        (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
            classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K) →
          (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
              classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
                = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K)) →
            UnitFugacity f)
      ∧ (∀ zV zE zT : ℝ, 0 < zV → 0 < zE → 0 < zT →
          (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
              classMass (sizeWeight (characterSize zV zE zT))
                (Quotient.mk (relabelSetoid B') K) = mu K) →
            zV = 1 ∧ zE = 1 ∧ zT = 1)
      ∧ (∀ (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ),
          FixedKindTotals c → SurfaceTotal F c a e → UnitFugacity gibbsSize)
      ∧ UnitFugacity gibbsSize :=
  ⟨fun c f hpost hrep => unit_fugacity_forced_after_erasure c f hpost hrep,
    fun _zV _zE _zT hzV hzE hzT h => three_fugacities_collapse_on_posting_mu hzV hzE hzT h,
    fun F _c _ _ h hs => a17_lands_in_a14_elimination F h hs,
    gibbsSize_unitFugacity⟩

structure FugacityEliminationIndex : Type where
  /-- C17 elimination lands on the A1.4 atom/`sizeWeight` class. -/
  elimination_on_sizeWeight_atoms : Bool
  /-- The three fugacities of `characterSize` collapse on posting `mu`. -/
  three_fugacities_collapse : Bool
  /-- A1.7 widens past naming `mu` at the atoms. -/
  a17_widening : Bool
  /-- Composition with the erasure Jacobian is stated. -/
  erasure_composition : Bool
  /-- NOT claimed: flag 8 / gap2_measure_derived. -/
  measure_flag_moved : Bool

def fugacityEliminationIndex : FugacityEliminationIndex where
  elimination_on_sizeWeight_atoms := true
  three_fugacities_collapse := true
  a17_widening := true
  erasure_composition := true
  measure_flag_moved := false

theorem index_elimination : fugacityEliminationIndex.elimination_on_sizeWeight_atoms = true := rfl
theorem index_three_fugacities : fugacityEliminationIndex.three_fugacities_collapse = true := rfl
theorem index_a17_widening : fugacityEliminationIndex.a17_widening = true := rfl
theorem index_composition : fugacityEliminationIndex.erasure_composition = true := rfl
/-- NOT moved.  Flag 8 stays false; this module eliminates the three fugacities
on the named classes, not the local numerator for physical costs. -/
theorem index_flag_unmoved : fugacityEliminationIndex.measure_flag_moved = false := rfl

/-! ## Axiom audit -/

#print axioms unit_fugacity_forced_after_erasure
#print axioms three_fugacities_collapse_on_posting_mu
#print axioms three_fugacities_collapse_via_characterCost
#print axioms unit_fugacity_forced_by_surface_and_kindTotals
#print axioms a17_lands_in_a14_elimination
#print axioms erasure_and_unit_fugacity_compose_to_mu
#print axioms erasure_and_full_posting_force_gibbsSize
#print axioms erasure_and_a17_compose_to_mu_no_fugacity
#print axioms widening_blocked_by_non_sizeWeight_posting
#print axioms widening_blocked_without_naming_mu
#print axioms widening_blocked_without_kindTotals
#print axioms fugacity_elimination_verdict
#print axioms index_flag_unmoved

end

end Gap2FugacityElimination
end SevenGaps
end Gravity
end IndisputableMonolith
