import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.ClassPushforward

/-!
# Seven Gaps, Pillar 2: quotient-first path-sum object

## What is proved here

This module constructs the quotient-first path-sum object promoted by the
P2c panel lock:

* `Zq B wq = Σ q : TriangulationClass B, (1 / |Aut(out q)|) · wq q`.
  The quotient is finite by the scoped `FiniteQuotient` instances imported
  from `ClassPushforward`; those classical instances are opened locally.
* `labeledZ_eq_sum_fiberCard_mul_mu`: the standing LABELED path sum
  `PathSumMeasure.Z` with a class-constant weight is exactly the quotient
  sum with the mandatory labeled-fiber factor:
  `Σ q, |fiber q| · μ(out q) · wq q`.
* `labeledZ_eq_Zq_plus_fiberExcess` and
  `Zq_eq_labeledZ_iff_fiberExcess_vanishes`: the exact relation between
  `Zq` and the labeled `Z` is not an unconditional equality.  Their
  difference is the explicit excess
  `Σ q, (|fiber q| - 1) · μ(out q) · wq q`.

## Honesty boundary

The P2c panel killed the unconditional claim that the standing labeled
`PathSumMeasure.Z` equals the per-class `1/|Aut|` quotient sum.  This file
does not resurrect it by convention.  The non-singleton fiber fact is
inherited from `ClassPushforward` (`PathSum.one_lt_fiberCard_edgeClass`),
so the fiber factor remains part of the bridge.

No orbit-stabilizer theorem for the full bounded `TriangulationClass B`
setoid is derived here.  Unlike the fixed-signature exact-shell machinery,
the scoped bounded carrier ranges over varying signatures, so a single
global relabeling group action is not supplied in this wave.  Any future
orbit-stabilizer statement must be a theorem with its signature/gauge
volume hypotheses explicit.

Expected axiom footprint: standard trio
`[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace QuotientFirstZ

open PathSumMeasure
open FiniteQuotient

/-- The quotient-first path sum over triangulation classes, with the
per-class symmetry-factor measure evaluated on the chosen representative.
This is the quotient convention, not the standing labeled `PathSumMeasure.Z`.
-/
noncomputable def Zq (B : ℕ) (wq : TriangulationClass B → ℂ) : ℂ :=
  ∑ q : TriangulationClass B, (mu (Quotient.out q) : ℂ) * wq q

/-- The representative symmetry factor is independent of the chosen
representative of a triangulation class. -/
theorem mu_out_eq_of_mk_eq {B : ℕ} {K : BoundedComplex B}
    (q : TriangulationClass B) (hK : Quotient.mk (relabelSetoid B) K = q) :
    mu (Quotient.out q) = mu K := by
  exact mu_congr (PathSum.equivalent_of_mk_eq ((Quotient.out_eq q).trans hK.symm))

/-- **Bridge to the labeled sum, with the mandatory fiber factor.**  For a
class weight `wq`, the standing labeled path sum with pulled-back weight is
the quotient sum weighted by the pushforward class mass
`|fiber q| · μ(out q)`. -/
theorem labeledZ_eq_sum_fiberCard_mul_mu (B : ℕ)
    (wq : TriangulationClass B → ℂ) :
    Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) =
      ∑ q : TriangulationClass B,
        (((fiberCard (relabelSetoid B) q : ℂ) * (mu (Quotient.out q) : ℂ))
          * wq q) := by
  classical
  have hw : ∀ K K' : BoundedComplex B, Equivalent K K' →
      wq (Quotient.mk (relabelSetoid B) K) =
        wq (Quotient.mk (relabelSetoid B) K') := by
    intro K K' h
    exact congrArg wq (Quotient.sound h)
  calc
    Z B (fun K => wq (Quotient.mk (relabelSetoid B) K))
        = ∑ q : TriangulationClass B,
            (PathSum.classMass q : ℂ) *
              wq (Quotient.mk (relabelSetoid B) (Quotient.out q)) := by
          simpa using PathSum.Z_eq_classPushforward B
            (fun K => wq (Quotient.mk (relabelSetoid B) K)) hw
    _ = ∑ q : TriangulationClass B,
        (((fiberCard (relabelSetoid B) q : ℂ) * (mu (Quotient.out q) : ℂ))
          * wq q) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [PathSum.classMass_eq_fiberCard_mul_mu]
          rw [show wq (Quotient.mk (relabelSetoid B) (Quotient.out q)) = wq q
            from congrArg wq (Quotient.out_eq q)]
          simp only [Complex.ofReal_mul]
          norm_num

/-- The explicit excess by which the labeled class pushforward differs
from the quotient-first object.  It is zero only under additional
fiber/weight cancellation hypotheses; no such cancellation is assumed. -/
noncomputable def fiberExcess (B : ℕ) (wq : TriangulationClass B → ℂ) : ℂ :=
  ∑ q : TriangulationClass B,
    ((((fiberCard (relabelSetoid B) q : ℂ) - 1) * (mu (Quotient.out q) : ℂ))
      * wq q)

/-- **Exact relation.**  The labeled class-constant path sum is the
quotient-first path sum plus the labeled-fiber excess.  This is the honest
replacement for the killed unconditional claim `Z = Σ_q wq/|Aut q|`. -/
theorem labeledZ_eq_Zq_plus_fiberExcess (B : ℕ)
    (wq : TriangulationClass B → ℂ) :
    Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) =
      Zq B wq + fiberExcess B wq := by
  classical
  rw [labeledZ_eq_sum_fiberCard_mul_mu, Zq, fiberExcess, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  let f : ℂ := fiberCard (relabelSetoid B) q
  let m : ℂ := mu (Quotient.out q)
  let z : ℂ := wq q
  calc
    (((fiberCard (relabelSetoid B) q : ℂ) * (mu (Quotient.out q) : ℂ)) * wq q)
        = (f * m) * z := rfl
    _ = m * z + ((f - 1) * m) * z := by ring
    _ = (mu (Quotient.out q) : ℂ) * wq q +
        ((((fiberCard (relabelSetoid B) q : ℂ) - 1) *
          (mu (Quotient.out q) : ℂ)) * wq q) := rfl

/-- **IFF form of the exact relation.**  The quotient-first object equals
the standing labeled sum for a pulled-back class weight exactly when the
explicit fiber excess vanishes. -/
theorem Zq_eq_labeledZ_iff_fiberExcess_vanishes (B : ℕ)
    (wq : TriangulationClass B → ℂ) :
    Zq B wq = Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) ↔
      fiberExcess B wq = 0 := by
  rw [labeledZ_eq_Zq_plus_fiberExcess]
  constructor
  · intro h
    have h' : Zq B wq + fiberExcess B wq = Zq B wq + 0 := by
      simpa using h.symm
    exact add_left_cancel h'
  · intro h
    rw [h, add_zero]

/-- A sufficient singleton-fiber condition under which the quotient-first
object agrees with the labeled sum.  `ClassPushforward` proves this
condition is false in general (`PathSum.one_lt_fiberCard_edgeClass`). -/
theorem Zq_eq_labeledZ_of_singleton_fibers (B : ℕ)
    (wq : TriangulationClass B → ℂ)
    (hfiber : ∀ q : TriangulationClass B,
      fiberCard (relabelSetoid B) q = 1) :
    Zq B wq = Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) := by
  rw [Zq_eq_labeledZ_iff_fiberExcess_vanishes]
  unfold fiberExcess
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [hfiber q]
  norm_num

/-! ## Status record (honest boundary; RED flags stay RED) -/

/-- Status record for the quotient-first path-sum wave.  No `True` shells:
the grounding theorem below ties the green flags to kernel statements and
keeps the requested RED flags false. -/
structure QuotientFirstStatus where
  quotient_first_object_constructed : Bool
  labeled_bridge_has_fiber_factor : Bool
  exact_excess_relation_proved : Bool
  nonSingleton_fiber_inherited : Bool
  /-- FALSE in this wave: no full bounded-setoid orbit-stabilizer theorem
  is derived here. -/
  bounded_orbit_stabilizer_derived : Bool
  /-- RED. -/
  Z_RS_continuum_limit : Bool
  /-- RED: the `1/|Aut|` measure remains a MODEL input. -/
  substrate_measure_derived : Bool
  /-- RED. -/
  gap1_bridge_derived : Bool

/-- The canonical status record for this quotient-first module. -/
def quotientFirstStatus : QuotientFirstStatus where
  quotient_first_object_constructed := true
  labeled_bridge_has_fiber_factor := true
  exact_excess_relation_proved := true
  nonSingleton_fiber_inherited := true
  bounded_orbit_stabilizer_derived := false
  Z_RS_continuum_limit := false
  substrate_measure_derived := false
  gap1_bridge_derived := false

/-- **Grounding theorem.**  The status flags are tied to the constructed
object and kernel bridges.  The RED flags remain false, and the inherited
non-singleton fiber theorem records why the unconditional labeled/quotient
equality is not available. -/
theorem quotientFirstStatus_grounded :
    (quotientFirstStatus.quotient_first_object_constructed = true ∧
      ∀ B : ℕ, ∀ wq : TriangulationClass B → ℂ,
        Zq B wq = ∑ q : TriangulationClass B,
          (mu (Quotient.out q) : ℂ) * wq q) ∧
    (quotientFirstStatus.labeled_bridge_has_fiber_factor = true ∧
      ∀ B : ℕ, ∀ wq : TriangulationClass B → ℂ,
        Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) =
          ∑ q : TriangulationClass B,
            (((fiberCard (relabelSetoid B) q : ℂ) * (mu (Quotient.out q) : ℂ))
              * wq q)) ∧
    (quotientFirstStatus.exact_excess_relation_proved = true ∧
      ∀ B : ℕ, ∀ wq : TriangulationClass B → ℂ,
        Zq B wq = Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) ↔
          fiberExcess B wq = 0) ∧
    (quotientFirstStatus.nonSingleton_fiber_inherited = true ∧
      1 < fiberCard (relabelSetoid 2)
        (Quotient.mk (relabelSetoid 2) PathSum.edgeAB)) ∧
    quotientFirstStatus.bounded_orbit_stabilizer_derived = false ∧
    quotientFirstStatus.Z_RS_continuum_limit = false ∧
    quotientFirstStatus.substrate_measure_derived = false ∧
    quotientFirstStatus.gap1_bridge_derived = false :=
  ⟨⟨rfl, fun _ _ => rfl⟩,
    ⟨rfl, labeledZ_eq_sum_fiberCard_mul_mu⟩,
    ⟨rfl, Zq_eq_labeledZ_iff_fiberExcess_vanishes⟩,
    ⟨rfl, PathSum.one_lt_fiberCard_edgeClass⟩,
    rfl, rfl, rfl, rfl⟩

end QuotientFirstZ
end SevenGaps
end Gravity
end IndisputableMonolith
