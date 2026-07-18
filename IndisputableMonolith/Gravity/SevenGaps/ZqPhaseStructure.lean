import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.QuotientFirstZ
import IndisputableMonolith.Gravity.SevenGaps.MeasureInvarianceNoGo

/-!
# Seven Gaps, Lane D3: phase structure on the quotient-first path sum

## What this module proves

**Status: THEOREM (structure theorems at fixed complexity cap; the
continuum limit stays OPEN).**  On the quotient-first object
`QuotientFirstZ.Zq` this module adds an explicit oscillatory phase model
and proves:

* `PhaseModel`: an explicit phase structure, a real phase function on
  LABELED configurations together with the stated relabeling-invariance
  property, which therefore descends to `TriangulationClass`
  (`classPhase`).  The phased weight `exp(i*phase)` has unit modulus
  (`phasedWeight_norm`).
* **Boundedness / well-definedness at fixed cap** (`Zq_norm_le_totalClassMass`,
  `Zq_phased_wellDefined`): for every phase model the phased `Zq` is a
  finite sum with the proved modulus bound `‖Zq‖ <= totalClassMass B <=
  card(TriangulationClass B)`.
* **Conditional cancellation** (`Zq_pairing_decomposition`,
  `Zq_pairing_bound`, `Zq_pairing_beats_triangle`): under a STATED
  pairing hypothesis (an injection `j` from a subfamily `s` of classes to
  classes outside `s` whose measured summands are exactly opposite), the
  paired contributions cancel EXACTLY and the modulus bound improves to
  `totalClassMass - pairedMass`, STRICTLY better than the triangle
  inequality whenever the paired family is nonempty.  These general
  theorems are finite-sum arithmetic under the exact-opposite hypothesis;
  the cancellation MECHANISM is not derived here, it is supplied by the
  hypothesis and discharged concretely by the `B = 2` witness below.
* **Two-term phase-pairing arithmetic** (`opposite_phase_pair_cancels`,
  `opposite_phase_pair_strict`): equal masses at phases `θ` and `θ + π`
  cancel exactly; the triangle inequality is strict there.
* **Non-vacuity witness at `B = 2`** (`phased_Zq_pairing_witness`,
  `phased_Zq_beats_triangle_witness`): an EXPLICIT phase model (phase 0
  on the vertex-free class, phase π elsewhere) whose pairing hypotheses
  are DISCHARGED concretely on the empty-complex class and the one-point
  class (both of unit symmetry factor, proved), giving the kernel chain
  `‖Zq 2 (phasedWeight witnessPhaseModel)‖ <= totalClassMass 2 - 2 <
  totalClassMass 2` (single theorem `phased_Zq_witness_chain`), with
  `2 <= totalClassMass 2` proved (`two_le_totalClassMass_two`) so the
  improved bound is nonnegative and meaningful.  The pairing hypotheses
  are therefore satisfiable, not vacuous.

## What this module does NOT prove (binding honesty disclosures)

* These are STRUCTURE theorems at a FIXED complexity cap `B`.  They are
  NOT `Z_RS_continuum_limit`; the continuum limit stays OPEN, and the
  complexity cutoff is NOT mesh refinement (standing constraint).
* The zero-phase route to regulator removal is DEAD
  (`RegulatorRemovalNoGo.not_hasZRSRegulatorRemoval_zeroPhase`, on the
  exact-shell quotient object): any well-defined removal needs phase
  cancellation.  This module supplies proved cancellation mechanisms at
  fixed cap only; it does NOT prove regulator removal or any limit for
  any phase.
* `Zq` is the QUOTIENT-first convention.  It is never silently equated
  with the LABELED `PathSumMeasure.Z`: the exact bridge carries the
  labeled fiber factor (`QuotientFirstZ.labeledZ_eq_Zq_plus_fiberExcess`),
  and nothing here bypasses it.
* The general pairing theorems carry their pairing hypotheses explicitly;
  the `B = 2` witness discharges them in one concrete instance and makes
  no claim that pairings exist for every phase model or every cap.

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms, no `native_decide`):**
`Zq_norm_le_totalClassMass`, `Zq_phased_wellDefined`,
`Zq_pairing_decomposition`, `Zq_pairing_bound`,
`Zq_pairing_beats_triangle`, `opposite_phase_pair_cancels`,
`opposite_phase_pair_strict`, `mu_onePointComplex`,
`phased_Zq_pairing_witness`, `phased_Zq_beats_triangle_witness`,
`two_le_totalClassMass_two`, `phased_Zq_witness_chain`.

**MODEL (definitional):** the `PhaseModel` shape itself (a real phase
function with relabeling invariance) and the `1/|Aut|` measure inherited
from `PathSumMeasure`.

**OPEN (recorded, never claimed):** the continuum limit of the phased
`Zq`; regulator removal at any oscillatory phase; a substrate-derived
phase function.

Expected axiom footprint: standard trio
`[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ZqPhaseStructure

open PathSumMeasure
open FiniteQuotient
open QuotientFirstZ

/-! ## §1. The explicit phase model -/

/-- An explicit oscillatory phase model on the scoped configuration
class: a real phase on LABELED configurations with the STATED property of
relabeling invariance.  MODEL: the phase function itself is an input; a
substrate-derived phase is OPEN. -/
structure PhaseModel (B : ℕ) where
  phase : BoundedComplex B → ℝ
  invariant : ∀ K K' : BoundedComplex B, Equivalent K K' → phase K = phase K'

/-- The phase descends to the quotient: a well-defined phase on
triangulation classes (this is where the stated invariance is used). -/
def classPhase {B : ℕ} (P : PhaseModel B) : TriangulationClass B → ℝ :=
  Quotient.lift P.phase (fun K K' h => P.invariant K K' h)

/-- Descent computes on representatives. -/
theorem classPhase_mk {B : ℕ} (P : PhaseModel B) (K : BoundedComplex B) :
    classPhase P (Quotient.mk (relabelSetoid B) K) = P.phase K := rfl

/-- The unitary class weight of a phase model. -/
noncomputable def phasedWeight {B : ℕ} (P : PhaseModel B) :
    TriangulationClass B → ℂ :=
  fun q => Complex.exp (Complex.I * (classPhase P q : ℂ))

/-- **THEOREM.**  The phased weight has modulus exactly 1. -/
theorem phasedWeight_norm {B : ℕ} (P : PhaseModel B)
    (q : TriangulationClass B) : ‖phasedWeight P q‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

/-! ## §2. Boundedness of the phased Zq at fixed complexity cap -/

/-- The total per-class mass at cap `B`: the quotient-side triangle bound
for unit-modulus weights. -/
noncomputable def totalClassMass (B : ℕ) : ℝ :=
  ∑ q : TriangulationClass B, mu (Quotient.out q)

/-- The total class mass is strictly positive (the empty-complex class is
always present). -/
theorem totalClassMass_pos (B : ℕ) : 0 < totalClassMass B := by
  unfold totalClassMass
  refine Finset.sum_pos (fun q _ => mu_pos _) ?_
  exact ⟨Quotient.mk (relabelSetoid B) (emptyComplex B), Finset.mem_univ _⟩

/-- The total class mass is bounded by the class count. -/
theorem totalClassMass_le_card (B : ℕ) :
    totalClassMass B ≤ (Fintype.card (TriangulationClass B) : ℝ) := by
  unfold totalClassMass
  calc ∑ q : TriangulationClass B, mu (Quotient.out q)
      ≤ ∑ _q : TriangulationClass B, (1 : ℝ) :=
        Finset.sum_le_sum fun q _ => mu_le_one _
    _ = (Fintype.card (TriangulationClass B) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **THEOREM (triangle bound for Zq).**  For any weight of modulus at
most 1, the quotient-first path sum is bounded by the total class mass. -/
theorem Zq_norm_le_totalClassMass (B : ℕ) (wq : TriangulationClass B → ℂ)
    (hw : ∀ q, ‖wq q‖ ≤ 1) :
    ‖Zq B wq‖ ≤ totalClassMass B := by
  show ‖∑ q : TriangulationClass B, (mu (Quotient.out q) : ℂ) * wq q‖ ≤ _
  calc ‖∑ q : TriangulationClass B, (mu (Quotient.out q) : ℂ) * wq q‖
      ≤ ∑ q : TriangulationClass B, ‖(mu (Quotient.out q) : ℂ) * wq q‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q : TriangulationClass B, mu (Quotient.out q) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (mu_pos _)]
        exact mul_le_of_le_one_right (mu_pos _).le (hw q)
    _ = totalClassMass B := rfl

/-- **THEOREM (well-definedness of the phased Zq at fixed cap).**  For
every phase model, the phased quotient-first path sum has unit-modulus
weights and satisfies the proved finiteness bounds.  This is a structure
theorem at fixed complexity cap, NOT a continuum-limit statement. -/
theorem Zq_phased_wellDefined (B : ℕ) (P : PhaseModel B) :
    (∀ q, ‖phasedWeight P q‖ = 1) ∧
    ‖Zq B (phasedWeight P)‖ ≤ totalClassMass B ∧
    ‖Zq B (phasedWeight P)‖ ≤ (Fintype.card (TriangulationClass B) : ℝ) := by
  have hb := Zq_norm_le_totalClassMass B (phasedWeight P)
    (fun q => le_of_eq (phasedWeight_norm P q))
  exact ⟨phasedWeight_norm P, hb, le_trans hb (totalClassMass_le_card B)⟩

/-! ## §3. The pairing cancellation theorems

A pairing is an injection `j` from a subfamily `s` of classes to classes
OUTSIDE `s` whose measured summands are exactly opposite.  Under this
STATED hypothesis the paired contributions cancel exactly, and the
modulus bound strictly beats the triangle inequality.  These are
finite-sum arithmetic theorems conditional on the exact-opposite
hypothesis; they do not derive a pairing, and §5 discharges the
hypothesis in one concrete instance. -/

/-- **THEOREM (exact pairing cancellation).**  Under the pairing
hypothesis, `Zq` equals the sum over the UNPAIRED classes only: the
paired contributions cancel exactly. -/
theorem Zq_pairing_decomposition (B : ℕ) (wq : TriangulationClass B → ℂ)
    (s : Finset (TriangulationClass B))
    (j : TriangulationClass B → TriangulationClass B)
    (hinj : ∀ q ∈ s, ∀ q' ∈ s, j q = j q' → q = q')
    (hdisj : ∀ q ∈ s, j q ∉ s)
    (hcancel : ∀ q ∈ s,
      (mu (Quotient.out (j q)) : ℂ) * wq (j q)
        = -((mu (Quotient.out q) : ℂ) * wq q)) :
    Zq B wq = ∑ q ∈ Finset.univ \ (s ∪ s.image j),
      (mu (Quotient.out q) : ℂ) * wq q := by
  have hdisjoint : Disjoint s (s.image j) := by
    rw [Finset.disjoint_right]
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact hdisj q hq
  have hpair : ∑ q ∈ s ∪ s.image j,
      (mu (Quotient.out q) : ℂ) * wq q = 0 := by
    rw [Finset.sum_union hdisjoint, Finset.sum_image hinj,
      Finset.sum_congr rfl hcancel, Finset.sum_neg_distrib, add_neg_cancel]
  have hsplit := Finset.sum_sdiff
    (f := fun q => (mu (Quotient.out q) : ℂ) * wq q)
    (Finset.subset_univ (s ∪ s.image j))
  calc Zq B wq
      = ∑ q ∈ Finset.univ, (mu (Quotient.out q) : ℂ) * wq q := rfl
    _ = ∑ q ∈ Finset.univ \ (s ∪ s.image j),
          (mu (Quotient.out q) : ℂ) * wq q
        + ∑ q ∈ s ∪ s.image j, (mu (Quotient.out q) : ℂ) * wq q :=
        hsplit.symm
    _ = ∑ q ∈ Finset.univ \ (s ∪ s.image j),
          (mu (Quotient.out q) : ℂ) * wq q := by
        rw [hpair, add_zero]

/-- **THEOREM (pairing bound).**  Under the pairing hypothesis, the
modulus bound improves from the triangle bound `totalClassMass` to
`totalClassMass - pairedMass`. -/
theorem Zq_pairing_bound (B : ℕ) (wq : TriangulationClass B → ℂ)
    (hw : ∀ q, ‖wq q‖ ≤ 1)
    (s : Finset (TriangulationClass B))
    (j : TriangulationClass B → TriangulationClass B)
    (hinj : ∀ q ∈ s, ∀ q' ∈ s, j q = j q' → q = q')
    (hdisj : ∀ q ∈ s, j q ∉ s)
    (hcancel : ∀ q ∈ s,
      (mu (Quotient.out (j q)) : ℂ) * wq (j q)
        = -((mu (Quotient.out q) : ℂ) * wq q)) :
    ‖Zq B wq‖ ≤ totalClassMass B
      - ∑ q ∈ s ∪ s.image j, mu (Quotient.out q) := by
  rw [Zq_pairing_decomposition B wq s j hinj hdisj hcancel]
  have hrest : ∑ q ∈ Finset.univ \ (s ∪ s.image j), mu (Quotient.out q)
      = totalClassMass B - ∑ q ∈ s ∪ s.image j, mu (Quotient.out q) :=
    eq_sub_of_add_eq (Finset.sum_sdiff (Finset.subset_univ _))
  calc ‖∑ q ∈ Finset.univ \ (s ∪ s.image j),
        (mu (Quotient.out q) : ℂ) * wq q‖
      ≤ ∑ q ∈ Finset.univ \ (s ∪ s.image j),
          ‖(mu (Quotient.out q) : ℂ) * wq q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.univ \ (s ∪ s.image j), mu (Quotient.out q) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (mu_pos _)]
        exact mul_le_of_le_one_right (mu_pos _).le (hw q)
    _ = totalClassMass B - ∑ q ∈ s ∪ s.image j, mu (Quotient.out q) :=
        hrest

/-- **THEOREM (strictly better than the triangle inequality).**  Under the
pairing hypothesis with a NONEMPTY paired family, the phased `Zq` is
STRICTLY below the triangle bound `totalClassMass`. -/
theorem Zq_pairing_beats_triangle (B : ℕ) (wq : TriangulationClass B → ℂ)
    (hw : ∀ q, ‖wq q‖ ≤ 1)
    (s : Finset (TriangulationClass B))
    (j : TriangulationClass B → TriangulationClass B)
    (hinj : ∀ q ∈ s, ∀ q' ∈ s, j q = j q' → q = q')
    (hdisj : ∀ q ∈ s, j q ∉ s)
    (hcancel : ∀ q ∈ s,
      (mu (Quotient.out (j q)) : ℂ) * wq (j q)
        = -((mu (Quotient.out q) : ℂ) * wq q))
    (hne : s.Nonempty) :
    ‖Zq B wq‖ < totalClassMass B := by
  have hb := Zq_pairing_bound B wq hw s j hinj hdisj hcancel
  have hpos : 0 < ∑ q ∈ s ∪ s.image j, mu (Quotient.out q) := by
    obtain ⟨q0, hq0⟩ := hne
    exact Finset.sum_pos (fun q _ => mu_pos _)
      ⟨q0, Finset.mem_union_left _ hq0⟩
  linarith

/-! ## §4. Two-term phase-pairing arithmetic -/

/-- Advancing a phase by π negates the unitary weight. -/
theorem opposite_phase_exp (θ : ℝ) :
    Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ))
      = -Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [Complex.ofReal_add, mul_add, Complex.exp_add,
    mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I, mul_neg_one]

/-- **THEOREM (two-term exact cancellation).**  Equal masses at phases
`θ` and `θ + π` cancel exactly. -/
theorem opposite_phase_pair_cancels (m θ : ℝ) :
    (m : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
      + (m : ℂ) * Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ)) = 0 := by
  rw [opposite_phase_exp, mul_neg, add_neg_cancel]

/-- **THEOREM (two-term strict improvement).**  For positive mass the
paired two-term sum is STRICTLY below its triangle bound. -/
theorem opposite_phase_pair_strict (m θ : ℝ) (hm : 0 < m) :
    ‖(m : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        + (m : ℂ) * Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ))‖
      < ‖(m : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖
        + ‖(m : ℂ) * Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ))‖ := by
  rw [opposite_phase_pair_cancels, norm_zero]
  have h1 : ‖(m : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = m := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      Complex.norm_exp_I_mul_ofReal, mul_one]
  have h2 : ‖(m : ℂ) * Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ))‖
      = m := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      Complex.norm_exp_I_mul_ofReal, mul_one]
  rw [h1, h2]
  linarith

/-! ## §5. The non-vacuity witness at B = 2

The pairing hypotheses of §3 are satisfiable: an explicit phase model at
`B = 2` pairs the empty-complex class (phase 0) with the one-point class
(phase π).  Both classes carry unit symmetry factor (proved), so the
measured summands are exactly opposite and the paired mass is exactly 2. -/

/-- The one-point configuration at cap 2 (one vertex, no incidence).
(`abbrev` so the size fields reduce during elaboration.) -/
abbrev onePointComplex : BoundedComplex 2 where
  nV := 1
  nE := 0
  nT := 0
  hV := one_le_two
  hE := Nat.zero_le 2
  hT := Nat.zero_le 2
  edgeVerts := fun e => e.elim0
  tetVerts := fun t => t.elim0

/-- The automorphism group of the one-point configuration is trivial:
the vertex index type `Fin 1` is a subsingleton and the other index types
are empty. -/
instance instSubsingletonAutOnePoint : Subsingleton (Aut onePointComplex) :=
  ⟨fun _a _b => Relabel.ext
    (Equiv.ext fun _x => Subsingleton.elim _ _)
    (Equiv.ext fun x => x.elim0)
    (Equiv.ext fun x => x.elim0)⟩

/-- **THEOREM.**  The one-point configuration has unit symmetry factor. -/
theorem mu_onePointComplex : mu onePointComplex = 1 := by
  unfold mu
  rw [Nat.card_unique]
  norm_num

/-- The empty-complex class at cap 2. -/
def emptyClass : TriangulationClass 2 :=
  Quotient.mk (relabelSetoid 2) (emptyComplex 2)

/-- The one-point class at cap 2. -/
def pointClass : TriangulationClass 2 :=
  Quotient.mk (relabelSetoid 2) onePointComplex

/-- The two witness classes are distinct (no bijection `Fin 0 ≃ Fin 1`). -/
theorem emptyClass_ne_pointClass : emptyClass ≠ pointClass := by
  intro h
  have hequiv : Equivalent (emptyComplex 2) onePointComplex :=
    Quotient.exact h
  obtain ⟨r⟩ := hequiv
  exact Fin.elim0 (r.vEquiv.symm ⟨0, Nat.succ_pos 0⟩)

/-- The representative symmetry factor of the empty-complex class is 1. -/
theorem mu_out_emptyClass : mu (Quotient.out emptyClass) = 1 := by
  rw [mu_out_eq_of_mk_eq (K := emptyComplex 2) emptyClass rfl]
  exact MeasureInvarianceNoGo.mu_emptyComplex 2

/-- The representative symmetry factor of the one-point class is 1. -/
theorem mu_out_pointClass : mu (Quotient.out pointClass) = 1 := by
  rw [mu_out_eq_of_mk_eq (K := onePointComplex) pointClass rfl]
  exact mu_onePointComplex

/-- The explicit witness phase model at `B = 2`: phase 0 on vertex-free
configurations, phase π otherwise.  The vertex count is a relabeling
invariant, so the stated invariance property holds. -/
noncomputable def witnessPhaseModel : PhaseModel 2 where
  phase K := if K.nV = 0 then 0 else Real.pi
  invariant K K' h := by
    obtain ⟨r⟩ := h
    have hnV : K.nV = K'.nV := Fin.equiv_iff_eq.mp ⟨r.vEquiv⟩
    rw [hnV]

/-- The witness weight on the empty-complex class is `+1`. -/
theorem phasedWeight_emptyClass :
    phasedWeight witnessPhaseModel emptyClass = 1 := by
  have hph : classPhase witnessPhaseModel emptyClass = 0 := by
    show (if (emptyComplex 2).nV = 0 then (0 : ℝ) else Real.pi) = 0
    rw [if_pos (show (emptyComplex 2).nV = 0 from rfl)]
  show Complex.exp (Complex.I * (classPhase witnessPhaseModel emptyClass : ℂ))
      = 1
  rw [hph, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- The witness weight on the one-point class is `-1`. -/
theorem phasedWeight_pointClass :
    phasedWeight witnessPhaseModel pointClass = -1 := by
  have hph : classPhase witnessPhaseModel pointClass = Real.pi := by
    show (if onePointComplex.nV = 0 then (0 : ℝ) else Real.pi) = Real.pi
    rw [if_neg Nat.one_ne_zero]
  show Complex.exp (Complex.I * (classPhase witnessPhaseModel pointClass : ℂ))
      = -1
  rw [hph, mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I]

/-- The witness pairing family: the empty-complex class alone. -/
def witnessPaired : Finset (TriangulationClass 2) := {emptyClass}

/-- The witness pairing map: everything to the one-point class. -/
def witnessPairing : TriangulationClass 2 → TriangulationClass 2 :=
  fun _ => pointClass

/-- The witness pairing is injective on the paired family. -/
theorem witnessPairing_injOn : ∀ q ∈ witnessPaired, ∀ q' ∈ witnessPaired,
    witnessPairing q = witnessPairing q' → q = q' := by
  intro q hq q' hq' _
  rw [witnessPaired, Finset.mem_singleton] at hq hq'
  rw [hq, hq']

/-- The witness pairing lands outside the paired family. -/
theorem witnessPairing_disj : ∀ q ∈ witnessPaired,
    witnessPairing q ∉ witnessPaired := by
  intro q _ hmem
  rw [witnessPaired, Finset.mem_singleton] at hmem
  exact emptyClass_ne_pointClass hmem.symm

/-- The witness pairing cancels exactly: unit mass at phase π against
unit mass at phase 0. -/
theorem witnessPairing_cancel : ∀ q ∈ witnessPaired,
    (mu (Quotient.out (witnessPairing q)) : ℂ)
        * phasedWeight witnessPhaseModel (witnessPairing q)
      = -((mu (Quotient.out q) : ℂ) * phasedWeight witnessPhaseModel q) := by
  intro q hq
  rw [witnessPaired, Finset.mem_singleton] at hq
  subst hq
  show (mu (Quotient.out pointClass) : ℂ)
      * phasedWeight witnessPhaseModel pointClass
    = -((mu (Quotient.out emptyClass) : ℂ)
      * phasedWeight witnessPhaseModel emptyClass)
  rw [mu_out_emptyClass, mu_out_pointClass, phasedWeight_emptyClass,
    phasedWeight_pointClass]
  norm_num

/-- The paired mass of the witness pairing is exactly 2. -/
theorem witnessPaired_mass :
    ∑ q ∈ witnessPaired ∪ witnessPaired.image witnessPairing,
      mu (Quotient.out q) = 2 := by
  have himg : witnessPaired.image witnessPairing = {pointClass} := by
    rw [witnessPaired]
    exact Finset.image_singleton _ _
  rw [himg, witnessPaired, ← Finset.insert_eq,
    Finset.sum_insert (by
      rw [Finset.mem_singleton]
      exact emptyClass_ne_pointClass),
    Finset.sum_singleton, mu_out_emptyClass, mu_out_pointClass]
  norm_num

/-- **HEADLINE (non-vacuous quantitative cancellation witness).**  The
explicit phase model at `B = 2` beats the triangle bound by EXACTLY the
paired mass 2: `‖Zq‖ <= totalClassMass 2 - 2`.  This discharges the
pairing hypotheses of the general theorems in one concrete instance. -/
theorem phased_Zq_pairing_witness :
    ‖Zq 2 (phasedWeight witnessPhaseModel)‖ ≤ totalClassMass 2 - 2 := by
  have hb := Zq_pairing_bound 2 (phasedWeight witnessPhaseModel)
    (fun q => le_of_eq (phasedWeight_norm witnessPhaseModel q))
    witnessPaired witnessPairing witnessPairing_injOn witnessPairing_disj
    witnessPairing_cancel
  rw [witnessPaired_mass] at hb
  exact hb

/-- **HEADLINE (strict improvement, witnessed).**  The phased `Zq` of the
explicit witness model is STRICTLY below the triangle bound.  Genuine
cancellation, not an inequality-shuffling tautology: the bound drop is
the exact paired mass. -/
theorem phased_Zq_beats_triangle_witness :
    ‖Zq 2 (phasedWeight witnessPhaseModel)‖ < totalClassMass 2 :=
  Zq_pairing_beats_triangle 2 (phasedWeight witnessPhaseModel)
    (fun q => le_of_eq (phasedWeight_norm witnessPhaseModel q))
    witnessPaired witnessPairing witnessPairing_injOn witnessPairing_disj
    witnessPairing_cancel ⟨emptyClass, Finset.mem_singleton_self _⟩

/-- **THEOREM (non-vacuity of the improved bound).**  The total class mass
at cap 2 is at least 2 (the two distinct unit-mass witness classes alone
contribute 2), so `totalClassMass 2 - 2` is nonnegative and the improved
bound is meaningful. -/
theorem two_le_totalClassMass_two : (2 : ℝ) ≤ totalClassMass 2 := by
  have hsum : ∑ q ∈ ({emptyClass, pointClass} : Finset (TriangulationClass 2)),
      mu (Quotient.out q) = 2 := by
    rw [Finset.sum_insert (by
        rw [Finset.mem_singleton]
        exact emptyClass_ne_pointClass),
      Finset.sum_singleton, mu_out_emptyClass, mu_out_pointClass]
    norm_num
  calc (2 : ℝ)
      = ∑ q ∈ ({emptyClass, pointClass} : Finset (TriangulationClass 2)),
          mu (Quotient.out q) := hsum.symm
    _ ≤ ∑ q : TriangulationClass 2, mu (Quotient.out q) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun q _ _ => (mu_pos _).le)
    _ = totalClassMass 2 := rfl

/-- **HEADLINE (single-theorem chain).**  The full advertised chain in one
kernel statement: the witness `Zq` is bounded by `totalClassMass 2 - 2`,
that improved bound is strictly below the triangle bound, and it is
nonnegative. -/
theorem phased_Zq_witness_chain :
    ‖Zq 2 (phasedWeight witnessPhaseModel)‖ ≤ totalClassMass 2 - 2 ∧
    totalClassMass 2 - 2 < totalClassMass 2 ∧
    (0 : ℝ) ≤ totalClassMass 2 - 2 :=
  ⟨phased_Zq_pairing_witness, by linarith,
    by linarith [two_le_totalClassMass_two]⟩

/-! ## §6. Status record (honest boundary; RED flags stay RED) -/

/-- Status record for the Zq phase-structure wave.  Every `true` flag is
tied to its kernel theorem by the grounding theorem below; the RED flags
stay false. -/
structure ZqPhaseStructureStatus where
  /-- §1: `PhaseModel` with stated invariance, descending to classes. -/
  phase_model_defined : Bool
  /-- §2: `Zq_phased_wellDefined`. -/
  phased_Zq_bounded_at_fixed_cap : Bool
  /-- §3: `Zq_pairing_decomposition` and `Zq_pairing_beats_triangle`. -/
  pairing_cancellation_proved : Bool
  /-- §5: `phased_Zq_pairing_witness` (hypotheses discharged at B = 2). -/
  pairing_nonvacuity_witnessed : Bool
  /-- RED (OPEN): no continuum limit is proved or claimed for any phase;
  the complexity cutoff is NOT mesh refinement. -/
  Z_RS_continuum_limit : Bool
  /-- RED (OPEN): regulator removal at oscillatory phase is not decided
  here (the zero-phase route is refuted in `RegulatorRemovalNoGo`). -/
  oscillatory_regulator_removal_derived : Bool
  /-- RED (OPEN): the phase function is a MODEL input, not derived. -/
  substrate_phase_derived : Bool

/-- The canonical status record. -/
def zqPhaseStructureStatus : ZqPhaseStructureStatus where
  phase_model_defined := true
  phased_Zq_bounded_at_fixed_cap := true
  pairing_cancellation_proved := true
  pairing_nonvacuity_witnessed := true
  Z_RS_continuum_limit := false
  oscillatory_regulator_removal_derived := false
  substrate_phase_derived := false

/-- **Grounding theorem.**  Every `true` status flag is tied to a kernel
statement (the general pairing flag to the GENERAL conditional theorem,
not merely the witness); the RED flags remain false. -/
theorem zqPhaseStructureStatus_grounded :
    (zqPhaseStructureStatus.phase_model_defined = true ∧
      ∀ B : ℕ, ∀ P : PhaseModel B,
        (∀ K, classPhase P (Quotient.mk (relabelSetoid B) K) = P.phase K) ∧
        ∀ q, ‖phasedWeight P q‖ = 1) ∧
    (zqPhaseStructureStatus.phased_Zq_bounded_at_fixed_cap = true ∧
      ∀ B : ℕ, ∀ P : PhaseModel B,
        ‖Zq B (phasedWeight P)‖ ≤ totalClassMass B) ∧
    (zqPhaseStructureStatus.pairing_cancellation_proved = true ∧
      ∀ (B : ℕ) (wq : TriangulationClass B → ℂ)
        (s : Finset (TriangulationClass B))
        (j : TriangulationClass B → TriangulationClass B),
        (∀ q ∈ s, ∀ q' ∈ s, j q = j q' → q = q') →
        (∀ q ∈ s, j q ∉ s) →
        (∀ q ∈ s, (mu (Quotient.out (j q)) : ℂ) * wq (j q)
            = -((mu (Quotient.out q) : ℂ) * wq q)) →
        Zq B wq = ∑ q ∈ Finset.univ \ (s ∪ s.image j),
          (mu (Quotient.out q) : ℂ) * wq q) ∧
    (zqPhaseStructureStatus.pairing_nonvacuity_witnessed = true ∧
      ‖Zq 2 (phasedWeight witnessPhaseModel)‖ ≤ totalClassMass 2 - 2 ∧
      ‖Zq 2 (phasedWeight witnessPhaseModel)‖ < totalClassMass 2 ∧
      (2 : ℝ) ≤ totalClassMass 2) ∧
    zqPhaseStructureStatus.Z_RS_continuum_limit = false ∧
    zqPhaseStructureStatus.oscillatory_regulator_removal_derived = false ∧
    zqPhaseStructureStatus.substrate_phase_derived = false :=
  ⟨⟨rfl, fun _B P => ⟨classPhase_mk P, phasedWeight_norm P⟩⟩,
    ⟨rfl, fun B P => (Zq_phased_wellDefined B P).2.1⟩,
    ⟨rfl, Zq_pairing_decomposition⟩,
    ⟨rfl, phased_Zq_pairing_witness, phased_Zq_beats_triangle_witness,
      two_le_totalClassMass_two⟩,
    rfl, rfl, rfl⟩

#print axioms Zq_norm_le_totalClassMass
#print axioms Zq_phased_wellDefined
#print axioms Zq_pairing_decomposition
#print axioms Zq_pairing_bound
#print axioms Zq_pairing_beats_triangle
#print axioms opposite_phase_pair_cancels
#print axioms opposite_phase_pair_strict
#print axioms phased_Zq_pairing_witness
#print axioms phased_Zq_beats_triangle_witness
#print axioms two_le_totalClassMass_two
#print axioms phased_Zq_witness_chain
#print axioms zqPhaseStructureStatus_grounded

end ZqPhaseStructure
end SevenGaps
end Gravity
end IndisputableMonolith
