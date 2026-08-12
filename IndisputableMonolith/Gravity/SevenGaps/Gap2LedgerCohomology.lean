import IndisputableMonolith.Gravity.SevenGaps.Gap2LetterCostDichotomy

/-!
# Gap 2 / C18: ledger cohomology of natural local posting costs

The panel's repaired form of incidence silence (C18): compute
`H¹_natural(PostingLedger; ℝ)`, the space of relabeling-natural, local,
path-independent additive costs on the posting ledger, modulo ledger
coboundaries, and ask whether it equals `span{dn_V, dn_E, dn_T}`.

## Verdict (MEASURED at caps 1–3, kernel-certified)

It does **not**.  On the incidence-local feature basis
`(f_V, f_E_loop, f_E_proper, f_T)` the history space has dimension

| cap | dim H¹ (histories) | dim span{nV,nE,nT} | incidence class |
|----:|-------------------:|-------------------:|-----------------|
|   1 |                  3 |                  3 | coboundary (no proper edges exist) |
|   2 |                  4 |                  3 | **genuine class** |
|   3 |                  4 |                  3 | **genuine class** |

Receipt: `scripts/qg/out/ledger_cohomology_20260730.json`
(runner `scripts/qg/qg_ledger_cohomology_20260730.py`, Bigbird 2026-07-30).

The obstruction is exhibited, not asserted: `incidenceCost t` is
gauge-equivariant, incidence-local, path-independent (its step cost at an
edge post depends only on whether the two endpoints differ, data available
at posting time), has history `t · properEdgeCount`, and that history is
not a function of the three sort counts (`twoLoops` vs `twoBridges` at
size `(2,2,0)`).  It is therefore a concrete new referent in H¹ outside
the count span.  The A1.7 escape witness `kindRateCost 1 0 (-1/24)` is by
contrast a count combination (rates `(1,0,-1/24)`), not a coboundary and
not a new class.

## What this closes, and what it does not

On the ledger-generated class the numerator question for flag 8 asked
whether every natural local path-independent cost is history-zero after
atom normalizations.  The count span alone would have forced that (A1.7 /
`fixedKindTotals_and_atoms_force_zero_historyCost`).  The obstruction
shows the premise "natural + local + path-independent" does **not** force
count-linearity, so it does not force history-zero.  The centered fibre
(`centeredIncidenceCost`) remains a coboundary in the history sense
(history identically zero) and is not the obstruction.  No flag moves.

## Cochain complex (definitions)

* **0-cochains.** Natural potentials on complexes: relabeling-invariant
  real functions of a `BoundedComplex`.
* **1-cochains.** Additive costs on legal single-letter posts.  Realized
  here as `LetterCost`s; the history is the path integral empty → K.
* **Coboundary.** `dφ` has history `φ(K) - φ(∅)`.  A cost is a *ledger
  coboundary* in the C18 sense when its history vanishes identically
  (invisible to the Boltzmann weight); `centeredIncidenceCost` lives here.
* **Path-independence.** The path integral depends only on the final
  complex.  Automatic for every `LetterCost`; for step costs, the
  incidence basis satisfies the diamond cocycle by inspection (each
  feature is a finished-complex letter count).
* **Locality / naturality.** A letter's cost depends only on
  relabeling-invariant local incidence data of that letter.  The
  incidence basis is the spanning set measured above.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LedgerCohomology

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Gap2LetterCostDichotomy

noncomputable section

variable {B : ℕ}

/-! ## §1. The cochain complex -/

/-- A **natural potential**: a relabeling-invariant real function of a complex. -/
def NaturalPotential : Type :=
  { φ : ∀ (B : ℕ), BoundedComplex B → ℝ //
      ∀ (B : ℕ) (K K' : BoundedComplex B), Equivalent K K' → φ B K = φ B K' }

/-- The **coboundary** of a natural potential, as a letter cost that charges
the whole complex's potential change onto no particular letter: its history
is `φ(K) - φ(∅)`.  Used only to name the comparison; the C18 quotient is by
history-zero costs below. -/
def historyOfPotential (φ : NaturalPotential) (B : ℕ) (K : BoundedComplex B) : ℝ :=
  φ.1 B K - φ.1 B (emptyComplex B)

/-- **Ledger coboundary** (C18): a letter cost whose history vanishes at every
complex.  These are invisible to `postedWeight` and form the subspace the
panel called the centered-incidence fibre. -/
def IsLedgerCoboundary (c : LetterCost) : Prop :=
  ∀ (B : ℕ) (K : BoundedComplex B), historyCost c B K = 0

/-- **Count-linear**: the history is a fixed linear combination of the three
sort counts.  Equivalent to `FixedKindTotals`. -/
def IsCountLinear (c : LetterCost) : Prop := FixedKindTotals c

/-- The three **count differentials**: charge one unit per letter of the
named kind.  These are `dn_V`, `dn_E`, `dn_T` as letter costs. -/
def dnV : LetterCost := kindRateCost 1 0 0
def dnE : LetterCost := kindRateCost 0 1 0
def dnT : LetterCost := kindRateCost 0 0 1

theorem dnV_kindRates : KindRates dnV 1 0 0 := kindRateCost_kindRates 1 0 0
theorem dnE_kindRates : KindRates dnE 0 1 0 := kindRateCost_kindRates 0 1 0
theorem dnT_kindRates : KindRates dnT 0 0 1 := kindRateCost_kindRates 0 0 1

theorem dnV_countLinear : IsCountLinear dnV := kindRateCost_fixedKindTotals 1 0 0
theorem dnE_countLinear : IsCountLinear dnE := kindRateCost_fixedKindTotals 0 1 0
theorem dnT_countLinear : IsCountLinear dnT := kindRateCost_fixedKindTotals 0 0 1

theorem dnV_equivariant : Equivariant dnV := kindRateCost_equivariant 1 0 0
theorem dnE_equivariant : Equivariant dnE := kindRateCost_equivariant 0 1 0
theorem dnT_equivariant : Equivariant dnT := kindRateCost_equivariant 0 0 1

/-- **History of a count differential.** -/
theorem historyCost_dnV (B : ℕ) (K : BoundedComplex B) :
    historyCost dnV B K = (K.nV : ℝ) := by
  simpa using historyCost_of_kindRates dnV_kindRates B K

theorem historyCost_dnE (B : ℕ) (K : BoundedComplex B) :
    historyCost dnE B K = (K.nE : ℝ) := by
  simpa using historyCost_of_kindRates dnE_kindRates B K

theorem historyCost_dnT (B : ℕ) (K : BoundedComplex B) :
    historyCost dnT B K = (K.nT : ℝ) := by
  simpa using historyCost_of_kindRates dnT_kindRates B K

/-! ## §2. Incidence locality -/

/-- **Incidence locality**: there exist reals `cV`, `cLoop`, `cProper`, `cT`
such that every edge letter is charged exactly by the loop/proper dichotomy,
and vertex/tet letters are charged by fixed kind rates.  This is the feature
basis measured in the C18 enumeration. -/
def IncidenceLocal (c : LetterCost) (cV cLoop cProper cT : ℝ) : Prop :=
  (∀ (B : ℕ) (K : BoundedComplex B) (v : Fin K.nV), c B K (Sum.inl v) = cV)
    ∧ (∀ (B : ℕ) (K : BoundedComplex B) (e : Fin K.nE),
        c B K (Sum.inr (Sum.inl e))
          = if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then cProper else cLoop)
    ∧ (∀ (B : ℕ) (K : BoundedComplex B) (τ : Fin K.nT),
        c B K (Sum.inr (Sum.inr τ)) = cT)

/-- The cost with the four incidence-local rates. -/
def incidenceLocalCost (cV cLoop cProper cT : ℝ) : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => cV
  | Sum.inr (Sum.inl e) =>
      if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then cProper else cLoop
  | Sum.inr (Sum.inr _) => cT

theorem incidenceLocalCost_is (cV cLoop cProper cT : ℝ) :
    IncidenceLocal (incidenceLocalCost cV cLoop cProper cT) cV cLoop cProper cT := by
  refine ⟨fun _ _ _ => rfl, ?_, fun _ _ _ => rfl⟩
  intro B K e
  rfl

/-- **History of an incidence-local cost**, in loop/proper form. -/
theorem historyCost_incidenceLocal (cV cLoop cProper cT : ℝ)
    (B : ℕ) (K : BoundedComplex B) :
    historyCost (incidenceLocalCost cV cLoop cProper cT) B K
      = cV * (K.nV : ℝ)
          + cLoop * (K.nE : ℝ)
          + (cProper - cLoop) * (properEdgeCount K : ℝ)
          + cT * (K.nT : ℝ) := by
  classical
  unfold historyCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hV : ∑ v : Fin K.nV, incidenceLocalCost cV cLoop cProper cT B K (Sum.inl v)
      = cV * (K.nV : ℝ) := by
    simp only [incidenceLocalCost, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hT : ∑ τ : Fin K.nT, incidenceLocalCost cV cLoop cProper cT B K (Sum.inr (Sum.inr τ))
      = cT * (K.nT : ℝ) := by
    simp only [incidenceLocalCost, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hE :
      (∑ e : Fin K.nE, incidenceLocalCost cV cLoop cProper cT B K (Sum.inr (Sum.inl e)))
        = cLoop * (K.nE : ℝ) + (cProper - cLoop) * (properEdgeCount K : ℝ) := by
    have hterm : ∀ e : Fin K.nE,
        incidenceLocalCost cV cLoop cProper cT B K (Sum.inr (Sum.inl e))
          = cLoop + (if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then cProper - cLoop else 0) := by
      intro e
      simp only [incidenceLocalCost]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun e _ => hterm e), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hP : (∑ e : Fin K.nE,
          if (K.edgeVerts e).1 ≠ (K.edgeVerts e).2 then cProper - cLoop else (0 : ℝ))
        = (cProper - cLoop) * (properEdgeCount K : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      unfold properEdgeCount
      ring
    rw [hP]
    ring
  rw [hV, hE, hT]
  ring

/-- Count-linear costs are incidence-local with `cLoop = cProper`. -/
theorem kindRateCost_incidenceLocal (cV cE cT : ℝ) :
    IncidenceLocal (kindRateCost cV cE cT) cV cE cE cT := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => by split_ifs <;> rfl, fun _ _ _ => rfl⟩

/-- `incidenceCost t` is incidence-local with rates `(0, 0, t, 0)`. -/
theorem incidenceCost_incidenceLocal (t : ℝ) :
    IncidenceLocal (incidenceCost t) 0 0 t 0 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Equivariance of an incidence-local cost. -/
theorem incidenceLocalCost_equivariant (cV cLoop cProper cT : ℝ) :
    Equivariant (incidenceLocalCost cV cLoop cProper cT) := by
  intro B K K' r a
  rcases a with x | (y | z)
  · rfl
  · rw [show postingAlphEquiv r.vEquiv r.eEquiv r.tEquiv (Sum.inr (Sum.inl y))
        = Sum.inr (Sum.inl (r.eEquiv y)) from rfl]
    simp only [incidenceLocalCost]
    exact if_congr (not_congr (loop_iff_of_relabel r y).symm) rfl rfl
  · rfl

/-! ## §3. Cap-1 collapse: H¹ equals the count span when proper edges cannot exist -/

/-- **MEASURED / kernel-certified at cap 1.**  On every complex with `nV ≤ 1`,
an incidence-local history reduces to a count-linear combination, because
`properEdgeCount = 0` and therefore `n_loop = nE`. -/
theorem incidenceLocal_history_countLinear_of_nV_le_one
    (cV cLoop cProper cT : ℝ) (B : ℕ) (K : BoundedComplex B) (h : K.nV ≤ 1) :
    historyCost (incidenceLocalCost cV cLoop cProper cT) B K
      = cV * (K.nV : ℝ) + cLoop * (K.nE : ℝ) + cT * (K.nT : ℝ) := by
  rw [historyCost_incidenceLocal, properEdgeCount_eq_zero_of_nV_le_one K h]
  ring

/-- At `nV ≤ 1` the proper-edge feature is history-invisible: charging proper
edges anything is a ledger coboundary relative to charging them nothing. -/
theorem properFeature_invisible_at_nV_le_one (t : ℝ) (B : ℕ)
    (K : BoundedComplex B) (h : K.nV ≤ 1) :
    historyCost (incidenceCost t) B K = 0 := by
  rw [historyCost_incidenceCost, properEdgeCount_eq_zero_of_nV_le_one K h]
  simp

/-! ## §4. The obstruction: incidence is a genuine H¹ class -/

/-- **Not a ledger coboundary.**  At `twoBridges`, `incidenceCost 1` has history 2. -/
theorem incidenceCost_not_coboundary :
    ¬ IsLedgerCoboundary (incidenceCost (1 : ℝ)) := by
  intro h
  have h2 := h 2 twoBridges
  rw [historyCost_incidenceCost, properEdgeCount_twoBridges] at h2
  norm_num at h2

/-- **Not count-linear.**  `twoLoops` and `twoBridges` share the count triple
`(2,2,0)` but carry histories `0` and `2` under `incidenceCost 1`. -/
theorem incidenceCost_history_not_a_function_of_counts :
    twoLoops.nV = twoBridges.nV ∧ twoLoops.nE = twoBridges.nE ∧ twoLoops.nT = twoBridges.nT
      ∧ historyCost (incidenceCost (1 : ℝ)) 2 twoLoops
          ≠ historyCost (incidenceCost (1 : ℝ)) 2 twoBridges := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [historyCost_incidenceCost, historyCost_incidenceCost,
    properEdgeCount_twoLoops, properEdgeCount_twoBridges]
  norm_num

theorem incidenceCost_not_countLinear :
    ¬ IsCountLinear (incidenceCost (1 : ℝ)) := by
  rintro ⟨cV, cE, cT, hc⟩
  have hL := historyCost_of_kindTotalRates hc 2 twoLoops
  have hB := historyCost_of_kindTotalRates hc 2 twoBridges
  have hEq : historyCost (incidenceCost (1 : ℝ)) 2 twoLoops
      = historyCost (incidenceCost (1 : ℝ)) 2 twoBridges := by
    rw [hL, hB]; simp [twoLoops, twoBridges]
  exact (incidenceCost_history_not_a_function_of_counts).2.2.2 hEq

/-- **THEOREM (the C18 obstruction).**  `incidenceCost 1` is gauge-equivariant,
incidence-local, not a ledger coboundary, and not count-linear.  It is the
exhibited generator of H¹ outside `span{dn_V, dn_E, dn_T}`. -/
theorem incidence_is_genuine_H1_class :
    Equivariant (incidenceCost (1 : ℝ))
      ∧ IncidenceLocal (incidenceCost (1 : ℝ)) 0 0 1 0
      ∧ ¬ IsLedgerCoboundary (incidenceCost (1 : ℝ))
      ∧ ¬ IsCountLinear (incidenceCost (1 : ℝ))
      ∧ historyCost (incidenceCost (1 : ℝ)) 2 twoLoops = 0
      ∧ historyCost (incidenceCost (1 : ℝ)) 2 twoBridges = 2
      ∧ twoLoops.nV = twoBridges.nV
      ∧ twoLoops.nE = twoBridges.nE
      ∧ twoLoops.nT = twoBridges.nT := by
  refine ⟨incidenceCost_equivariant 1, incidenceCost_incidenceLocal 1,
    incidenceCost_not_coboundary, incidenceCost_not_countLinear, ?_, ?_, rfl, rfl, rfl⟩
  · rw [historyCost_incidenceCost, properEdgeCount_twoLoops]; norm_num
  · rw [historyCost_incidenceCost, properEdgeCount_twoBridges]; norm_num

/-! ## §5. The A1.7 escape is a count combination -/

/-- **Classification of A1.7's escape witness.**  `kindRateCost 1 0 (-1/24)` is
count-linear with rates `(1, 0, -1/24)`, gauge-equivariant, and not a ledger
coboundary (its history at the vertex atom is 1).  It is not a new H¹ class. -/
theorem a17_escape_history_at_dust :
    historyCost (kindRateCost 1 0 (-(1 / 24))) 1 (dust 1) = 1 :=
  historyCost_kindRateCost_dust_one 1 0 (-(1 / 24))

theorem a17_escape_not_coboundary :
    ¬ IsLedgerCoboundary (kindRateCost 1 0 (-(1 / 24))) := by
  intro h
  have h1 := h 1 (dust 1)
  rw [a17_escape_history_at_dust] at h1
  exact (by norm_num : (1 : ℝ) ≠ 0) h1

theorem a17_escape_is_count_combination :
    IsCountLinear (kindRateCost 1 0 (-(1 / 24)))
      ∧ Equivariant (kindRateCost 1 0 (-(1 / 24)))
      ∧ ¬ IsLedgerCoboundary (kindRateCost 1 0 (-(1 / 24)))
      ∧ historyCost (kindRateCost 1 0 (-(1 / 24))) 1 (dust 1) = 1
      ∧ KindRates (kindRateCost 1 0 (-(1 / 24))) 1 0 (-(1 / 24)) :=
  ⟨kindRateCost_fixedKindTotals 1 0 (-(1 / 24)),
    kindRateCost_equivariant 1 0 (-(1 / 24)),
    a17_escape_not_coboundary,
    a17_escape_history_at_dust,
    kindRateCost_kindRates 1 0 (-(1 / 24))⟩

/-- The same witness's census history is the measured A1.7 polynomial
`4N³ + 6N² + 4N + 1` (imported from the dichotomy module). -/
theorem a17_escape_census_history (F : CensusDilateFamily) (N : ℕ) :
    historyCost (kindRateCost 1 0 (-(1 / 24))) (F.cap N) (F.K N)
      = 4 * (N : ℝ) ^ 3 + 6 * (N : ℝ) ^ 2 + 4 * (N : ℝ) + 1 :=
  (purity_of_the_surface_term_is_load_bearing F).2.2.2 N

/-! ## §6. The count span is three-dimensional -/

/-- The three count histories are independent as class functions: there is no
nontrivial rate triple giving history zero at the three atoms
`dust 1` (1,0,0), `bouquet 1 0` (1,1,0), `bouquet 0 1` (1,0,1). -/
theorem count_span_rank_three :
    ∀ cV cE cT : ℝ,
      historyCost (kindRateCost cV cE cT) 1 (dust 1) = 0 →
      historyCost (kindRateCost cV cE cT) 2 (bouquet 1 0) = 0 →
      historyCost (kindRateCost cV cE cT) 2 (bouquet 0 1) = 0 →
      cV = 0 ∧ cE = 0 ∧ cT = 0 := by
  intro cV cE cT hV hE hT
  rw [historyCost_of_kindRates (kindRateCost_kindRates cV cE cT)] at hV hE hT
  simp only [dust_nV, dust_nE, dust_nT, bouquet_nV, bouquet_nE, bouquet_nT,
    Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero] at hV hE hT
  exact ⟨hV, by linarith, by linarith⟩

/-- **Linear independence of the three count differentials.**  No nontrivial
linear combination is a ledger coboundary. -/
theorem count_differentials_independent {cV cE cT : ℝ}
    (h : IsLedgerCoboundary (kindRateCost cV cE cT)) :
    cV = 0 ∧ cE = 0 ∧ cT = 0 :=
  count_span_rank_three cV cE cT (h 1 (dust 1)) (h 2 (bouquet 1 0)) (h 2 (bouquet 0 1))

/-! ## §7. Measured dimensions (cap-restricted, kernel-mirrored) -/

/-- Cap-by-cap H¹ dimensions from the Bigbird enumeration
(`scripts/qg/out/ledger_cohomology_20260730.json`).  Scoped as MEASURED data
mirrored into the kernel; the obstruction theorems of §4 are the
kernel-certified content. -/
def measuredH1Dim : ℕ → ℕ
  | 1 => 3
  | 2 => 4
  | 3 => 4
  | _ => 0

def measuredCountSpanDim : ℕ → ℕ
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | _ => 0

theorem measured_H1_cap1 : measuredH1Dim 1 = 3 := rfl
theorem measured_H1_cap2 : measuredH1Dim 2 = 4 := rfl
theorem measured_H1_cap3 : measuredH1Dim 3 = 4 := rfl
theorem measured_count_cap1 : measuredCountSpanDim 1 = 3 := rfl
theorem measured_count_cap2 : measuredCountSpanDim 2 = 3 := rfl
theorem measured_count_cap3 : measuredCountSpanDim 3 = 3 := rfl

theorem measured_H1_exceeds_count_at_cap2 :
    measuredCountSpanDim 2 < measuredH1Dim 2 := by decide

theorem measured_H1_exceeds_count_at_cap3 :
    measuredCountSpanDim 3 < measuredH1Dim 3 := by decide

theorem measured_H1_equals_count_at_cap1 :
    measuredH1Dim 1 = measuredCountSpanDim 1 := rfl

/-! ## §8. Centered incidence is a ledger coboundary (not the obstruction) -/

theorem centeredIncidence_is_coboundary (t : ℝ) :
    IsLedgerCoboundary (centeredIncidenceCost t) :=
  fun B K => historyCost_centeredIncidenceCost t B K

/-! ## §9. Verdict package -/

/-- **C18 verdict.**  The target equality
`H¹_natural = span{dn_V, dn_E, dn_T}` fails on the incidence-local class:
the obstruction `incidenceCost 1` is exhibited.  The A1.7 escape is a count
combination.  Cap 1 collapses to the count span because proper edges cannot
exist.  Flag unmoved. -/
structure LedgerCohomologyVerdict where
  obstruction : Equivariant (incidenceCost (1 : ℝ))
    ∧ ¬ IsLedgerCoboundary (incidenceCost (1 : ℝ))
    ∧ ¬ IsCountLinear (incidenceCost (1 : ℝ))
  a17_escape_count : IsCountLinear (kindRateCost 1 0 (-(1 / 24)))
    ∧ ¬ IsLedgerCoboundary (kindRateCost 1 0 (-(1 / 24)))
  count_span_rank : ∀ cV cE cT : ℝ,
    historyCost (kindRateCost cV cE cT) 1 (dust 1) = 0 →
    historyCost (kindRateCost cV cE cT) 2 (bouquet 1 0) = 0 →
    historyCost (kindRateCost cV cE cT) 2 (bouquet 0 1) = 0 →
    cV = 0 ∧ cE = 0 ∧ cT = 0
  cap1_collapse : ∀ (cV cLoop cProper cT : ℝ) (B : ℕ) (K : BoundedComplex B),
    K.nV ≤ 1 →
      historyCost (incidenceLocalCost cV cLoop cProper cT) B K
        = cV * (K.nV : ℝ) + cLoop * (K.nE : ℝ) + cT * (K.nT : ℝ)
  measured_dims : measuredH1Dim 1 = 3 ∧ measuredH1Dim 2 = 4 ∧ measuredH1Dim 3 = 4
    ∧ measuredCountSpanDim 2 = 3 ∧ measuredCountSpanDim 2 < measuredH1Dim 2
  centered_is_coboundary : ∀ t : ℝ, IsLedgerCoboundary (centeredIncidenceCost t)
  measure_flag_moved : Bool := false

def ledgerCohomologyVerdict : LedgerCohomologyVerdict where
  obstruction := ⟨(incidence_is_genuine_H1_class).1,
    (incidence_is_genuine_H1_class).2.2.1,
    (incidence_is_genuine_H1_class).2.2.2.1⟩
  a17_escape_count := ⟨(a17_escape_is_count_combination).1,
    (a17_escape_is_count_combination).2.2.1⟩
  count_span_rank := count_span_rank_three
  cap1_collapse := fun cV cLoop cProper cT B K h =>
    incidenceLocal_history_countLinear_of_nV_le_one cV cLoop cProper cT B K h
  measured_dims := ⟨rfl, rfl, rfl, rfl, measured_H1_exceeds_count_at_cap2⟩
  centered_is_coboundary := centeredIncidence_is_coboundary
  measure_flag_moved := false

theorem index_flag_unmoved : ledgerCohomologyVerdict.measure_flag_moved = false := rfl

end

/-! ## Axiom audit -/

#print axioms historyCost_dnV
#print axioms historyCost_dnE
#print axioms historyCost_dnT
#print axioms historyCost_incidenceLocal
#print axioms incidenceLocalCost_equivariant
#print axioms incidenceCost_incidenceLocal
#print axioms incidenceLocal_history_countLinear_of_nV_le_one
#print axioms properFeature_invisible_at_nV_le_one
#print axioms incidenceCost_not_coboundary
#print axioms incidenceCost_history_not_a_function_of_counts
#print axioms incidenceCost_not_countLinear
#print axioms incidence_is_genuine_H1_class
#print axioms a17_escape_history_at_dust
#print axioms a17_escape_not_coboundary
#print axioms a17_escape_is_count_combination
#print axioms a17_escape_census_history
#print axioms count_differentials_independent
#print axioms count_span_rank_three
#print axioms centeredIncidence_is_coboundary
#print axioms measured_H1_exceeds_count_at_cap2
#print axioms ledgerCohomologyVerdict

end Gap2LedgerCohomology
end SevenGaps
end Gravity
end IndisputableMonolith
