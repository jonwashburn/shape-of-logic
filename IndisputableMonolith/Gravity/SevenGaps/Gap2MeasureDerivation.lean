import IndisputableMonolith.Gravity.SevenGaps.Gap2FugacityElimination
import IndisputableMonolith.Gravity.SevenGaps.Gap2PoissonCoarea

/-!
# Gap 2 / A27: measure derivation assembly (flag 8 typed obligation)

## Status: THEOREM (assembly; flag unflipped)

Assembles `MeasureSubstrateBlocker.GaugeCountingPrinciple` for the class mass of
`gibbsWeight` from the C4 erasure Jacobian and the C17 fugacity elimination,
with the C16 LIFO process named as the process-side discrimination premise.
`FullTheoryLedger` is not imported. The flag flip is deferred to in-session
hostile review after this module lands.

## What this closes and what it does not

**Closes (under Jon's bookkeeping ruling `D-qg-c27-ruling-bookkeeping-20260730`).**
Flag 8's typed obligation is to derive `GaugeCountingPrinciple`, which holds
exactly for `1/|Aut K|`, from substrate structure richer than counting, without
reintroducing the automorphism group on the construction side. The C4+C17+C16
chain discharges that obligation: C4 derives the divisor as the Jacobian of
label erasure (`Aut` only in the conclusion); C17 forces unit fugacity so the
posted class mass equals `mu` on the A1.7 class; C16 supplies the Aut-free
process whose stationary class-mass ratio matches the directed inverse-Aut
ratio at the pre-registered witnesses. Jon ruled the base path-sum measure is
`mu = 1/|Aut K|` (bookkeeping), and the J-tilt `e^{-SJ}` is the emergent action
routed to flag 9, not to flag 8.

**Flag state.**
* Flipped 2026-07-30 after the gatekeeper hostile review (verdict MINOR, the
  one finding being report prose, repaired in `A27` §5): the closing proof
  terms cite no `MeasureDerivationPremises` field and no C16 field.
  Load-bearing: `blocker_iff_mu` + the C4 bridge for the base closing; C17
  `unit_fugacity_forced_by_surface_and_kindTotals` + the blocker iff for the
  no-tilt closing; the labeled-weight / erasure-pushforward carrier is
  definitionally load-bearing (MODEL); the C16 fields are process
  discrimination only.
* The J-tilt / continuum half is flag 9 (`gap2_geometric_continuum_limit`),
  per the same ruling.
* This is not a presentation of the same ratio through an Aut-equivalent
  wrapper (the 2026-07-26 kill of
  `gap2_gauge_counting_from_history_discharged` / G1 semantic circularity).
  Construction cites only labeled weights, erasure pushforward, letter costs,
  and the LIFO process. `Aut` appears only as C4's Jacobian denominator.
* Premises below THEOREM remain named: cap-3 uniformity is MEASURED; cap-4
  uniformity is DERIVED-UNFORMALIZED; the labeled-weight framing is MODEL.

## Kill criterion (self-audit)

If any construction reintroduces `Aut` through a wrapper equivalent to counting
(as `GaugeHistoryMeasure.nuBuild` did), the assembly fails. Grep the
construction side of this module: no `Aut`, no `orbit`, no `gaugeOrbit`, no
`nuBuild`, no `CanonicalHistory` in any hypothesis or definition used to build
the weight. Those words appear only in conclusions and this docstring.

Expected axiom footprint of the closing theorems:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2MeasureDerivation

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume
open Gap2LabelErasure Gap2FugacityElimination Gap2PoissonCoarea
open Gap2GluingDerivation Gap2PostingCostDerivation Gap2LetterCostDichotomy
open Gap2SizeBlindnessReach Gap2FugacityPostingGluing
open MeasureSubstrateBlocker

noncomputable section

variable {B : ℕ}

/-! ## §1. C4 bridge: class mass of gibbsWeight equals mu

The identity uses only Aut-free constructions on the left (labeled Gibbs weight,
erasure pushforward of the unit labeled weight) and cites C4's
`mu_eq_gibbs_mul_erasePush_one`, where `|Aut|` appears solely as the Jacobian
denominator in the supporting pushforward theorem. -/

/-- Letterwise relabeling invariance of `gibbsWeight` (Aut-free hypothesis form:
serial-name permutations; sizes are preserved). -/
theorem gibbsWeight_relabelInvariant :
    RelabelInvariant (gibbsWeight : labeledWeight B) := by
  intro K σv σe σt
  exact (gibbsWeight_invariant (equivalent_push K (σv, σe, σt))).symm

/-- Under letterwise invariance, the class mass of `gibbsWeight` factors as the
pointwise Gibbs weight times the unit-weight fibre mass. -/
theorem classMass_gibbs_eq_gibbs_mul_unitFibre (K : BoundedComplex B) :
    classMass (gibbsWeight : BoundedComplex B → ℝ) (erase B K)
      = gibbsWeight K
          * erasePush (fun _ : BoundedComplex B => (1 : ℝ)) (erase B K) := by
  have hinvG : ∀ K₁ K₂ : BoundedComplex B, Equivalent K₁ K₂ →
      gibbsWeight K₁ = gibbsWeight K₂ :=
    fun _ _ h => gibbsWeight_invariant h
  have hinv1 : ∀ K₁ K₂ : BoundedComplex B, Equivalent K₁ K₂ → (1 : ℝ) = 1 :=
    fun _ _ _ => rfl
  unfold erasePush
  rw [classMass_of_invariant _ hinvG, classMass_of_invariant _ hinv1]
  have hout : gibbsWeight (Quotient.out (erase B K)) = gibbsWeight K :=
    gibbsWeight_invariant (equivalent_out K)
  rw [hout]
  ring

/-- **C4 bridge.** The class mass of the Aut-free labeled Gibbs weight equals
`mu K`. Proof cites only `mu_eq_gibbs_mul_erasePush_one` (C4) and the
factorization above; `|Aut|` is not a hypothesis. -/
theorem classMass_gibbs_eq_mu_via_erasure (K : BoundedComplex B) :
    classMass (gibbsWeight : BoundedComplex B → ℝ) (erase B K) = mu K := by
  rw [classMass_gibbs_eq_gibbs_mul_unitFibre, ← mu_eq_gibbs_mul_erasePush_one]

/-! ## §2. Closing theorems -/

/-- **Closing theorem (base measure / gibbsWeight).**
`GaugeCountingPrinciple` holds for the class mass of `gibbsWeight`.

Construction side: `gibbsWeight` is `1/(nV! nE! nT!)` (size factorials only;
no Aut, orbit, or gauge class in the definition), and the class mass is the
erasure pushforward of that labeled weight. The proof routes through C4's
erasure identity `classMass_gibbs_eq_mu_via_erasure` and the blocker
equivalence `gaugeCountingPrinciple_iff_mu_on_representatives`. Aut appears
only as the Jacobian denominator inside the cited C4 theorems. -/
theorem gap2_gauge_counting_gibbsWeight (B : ℕ) :
    GaugeCountingPrinciple
      (classMass (gibbsWeight : BoundedComplex B → ℝ)) := by
  refine (gaugeCountingPrinciple_iff_mu_on_representatives _).mpr ?_
  intro K
  simpa [erase] using classMass_gibbs_eq_mu_via_erasure (B := B) K

/-- **Closing theorem (C17 A1.7 class).** Under fixed kind totals and
surface-pure dilate history, the posted class mass satisfies
`GaugeCountingPrinciple`. Premises are Aut-free letter-cost structure;
the conclusion is the blocker principle (equivalent to `1/|Aut|`). -/
theorem gap2_gauge_counting_from_surface_and_kindTotals
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (h : FixedKindTotals c) (hs : SurfaceTotal F c a e) (B : ℕ) :
    GaugeCountingPrinciple (classMass (postedWeight c B)) := by
  refine (gaugeCountingPrinciple_iff_mu_on_representatives _).mpr ?_
  intro K
  exact (unit_fugacity_forced_by_surface_and_kindTotals F h hs).2.2 B K

/-- **Composition package.** C4 erasure Jacobian + C17 A1.7 forcing yield
`GaugeCountingPrinciple` for the posted class mass, unit fugacity, posted
weight equal to the Gibbs size-blind weight, and the base `gibbsWeight`
principle. -/
theorem gap2_measure_from_c4_c17
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (_hc : Equivariant c) (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (B : ℕ) :
    GaugeCountingPrinciple (classMass (postedWeight c B))
      ∧ GaugeCountingPrinciple
          (classMass (gibbsWeight : BoundedComplex B → ℝ))
      ∧ UnitFugacity gibbsSize
      ∧ (∀ K : BoundedComplex B, postedWeight c B K = sizeWeight gibbsSize K)
      ∧ (∀ K : BoundedComplex B,
          classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K) := by
  obtain ⟨hUF, hsw, hmu⟩ := unit_fugacity_forced_by_surface_and_kindTotals F h hs
  refine ⟨?_, gap2_gauge_counting_gibbsWeight B, hUF, hsw B, hmu B⟩
  exact gap2_gauge_counting_from_surface_and_kindTotals F h hs B

/-- Corollary: the composition also recovers C4's Jacobian reading at every
complex (Aut only in the conclusion). -/
theorem gap2_measure_jacobian_reading
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (hc : Equivariant c) (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (K : BoundedComplex B) :
    erasePush (fun K' : BoundedComplex B => Real.exp (-(historyCost c B K')))
        (erase B K)
      = Real.exp (-(historyCost c B K))
          * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
          / (Nat.card (Aut K) : ℝ) :=
  (erasure_and_a17_compose_to_mu_no_fugacity F hc h hs K).1

/-! ## §3. C16 process certificate (discrimination, not construction)

The LIFO process never names Aut on the construction side. Cap-3 uniformity is
MEASURED; the `(4,2,0)` ratio under the uniformity premise is THEOREM; cap-4
uniformity remains DERIVED-UNFORMALIZED. -/

/-- Process-side discrimination package: under the named uniformity premise,
the π-weighted class-mass ratio at `(4,2,0)` is `1/2`, matching the directed
inverse-Aut ratio. Aut appears only in the comparison theorems of C16. -/
theorem c16_process_discrimination
    (nStates : ℕ) (hπ : UniformNamedPremise nStates) :
    classMassRatioPi (uniformPi nStates) = (1 : ℚ) / 2
      ∧ classMassRatio_420
          = (pathPlusAutCount : ℚ) / (twoEdgeAutCount : ℚ)
      ∧ ∀ (K K' : TetFree 4),
          uniformNamed nStates K * (moveRate K K' : ℚ)
            = uniformNamed nStates K' * (moveRate K' K : ℚ) :=
  ⟨classMassRatioPi_of_uniform_eq_half nStates hπ,
    fibre_ratio_eq_aut_inverse_ratio,
    fun K K' => uniform_detailed_balance (B := 4) nStates hπ K K'⟩

/-! ## §4. Premises certificate

Every premise the derivation rests on, named, with honest tier in the docstring.
A field of type `Prop` is inhabited by the cited source theorem. -/

/-- Premises the flag-8 assembly rests on. Each field's docstring carries its
honest tier. Below-THEOREM premises are named here so they cannot be silently
promoted. -/
structure MeasureDerivationPremises where
  /-- **THEOREM.** C4: letterwise `RelabelInvariant` labeled weight pushes
  forward to weight times the gauge divisor; Aut only in the conclusion
  (`pushforward_labeledWeight_eq_gauge_divisor`). -/
  c4_erasure_jacobian : Prop
  /-- **THEOREM.** C4: `gibbsWeight` is the size-only factor of that Jacobian
  (`gibbsWeight_is_the_erasure_jacobian` / `mu_eq_gibbs_mul_erasePush_one`). -/
  c4_gibbs_is_jacobian_factor : Prop
  /-- **THEOREM.** C17: fixed kind totals + surface-pure dilate history force
  `postedWeight = sizeWeight gibbsSize` and class mass `mu`
  (`unit_fugacity_forced_by_surface_and_kindTotals`). -/
  c17_unit_fugacity_a17 : Prop
  /-- **THEOREM.** C16: LIFO reverse-pair rate symmetry implies uniform
  detailed balance (`uniform_detailed_balance`). -/
  c16_rate_symmetry_balance : Prop
  /-- **MEASURED.** Cap-3 tet-free LIFO stationary law is uniform `1/910`
  (exact rational solve; `measuredCap3`). -/
  c16_cap3_uniform_measured : Prop
  /-- **DERIVED-UNFORMALIZED.** Cap-4 uniformity (host of the `(4,2,0)`
  witnesses) by the same rate-symmetry + irreducibility argument, not a
  separate exact solve. -/
  c16_cap4_uniform_derived_unformalized : Prop
  /-- **THEOREM** under uniformity premise. C16 clause β: π-weighted
  class-mass ratio at `(4,2,0)` equals `1/2`
  (`classMassRatioPi_of_uniform_eq_half`). -/
  c16_ratio_half_under_uniform : Prop
  /-- **MODEL.** The labeled-weight framing: path-sum measure is the erasure
  pushforward of a letterwise-invariant labeled weight on serially named
  complexes (definitional choice of the C4 carrier). -/
  model_labeled_weight_framing : Prop
  /-- **THEOREM.** Blocker equivalence: `GaugeCountingPrinciple ν` iff
  `ν (mk K) = mu K` for all `K`
  (`gaugeCountingPrinciple_iff_mu_on_representatives`). -/
  blocker_iff_mu : Prop

/-- The premises certificate, inhabited by the cited source facts. Cap-4
uniformity is recorded as the named open-strength premise
(`UniformNamedPremise` at the witness ambient), not as a kernel solve. -/
def measureDerivationPremises : MeasureDerivationPremises where
  c4_erasure_jacobian :=
    ∀ (B : ℕ) (w : labeledWeight B) (_hw : RelabelInvariant w) (K : BoundedComplex B),
      erasePush w (erase B K)
        = w K * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
            / (Nat.card (Aut K) : ℝ)
  c4_gibbs_is_jacobian_factor :=
    ∀ (B : ℕ) (K : BoundedComplex B),
      mu K
        = gibbsWeight K
            * erasePush (fun _ : BoundedComplex B => (1 : ℝ)) (erase B K)
  c17_unit_fugacity_a17 :=
    ∀ (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ),
      FixedKindTotals c → SurfaceTotal F c a e →
        UnitFugacity gibbsSize
          ∧ (∀ (B' : ℕ) (K : BoundedComplex B'),
              postedWeight c B' K = sizeWeight gibbsSize K)
          ∧ (∀ (B' : ℕ) (K : BoundedComplex B'),
              classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
  c16_rate_symmetry_balance :=
    ∀ (nStates : ℕ) (_hn : 0 < nStates) (K K' : TetFree 3),
      uniformNamed nStates K * (moveRate K K' : ℚ)
        = uniformNamed nStates K' * (moveRate K' K : ℚ)
  c16_cap3_uniform_measured :=
    measuredCap3.nStates = 910
      ∧ measuredCap3.offDiagonalSymmetric = true
      ∧ measuredCap3.stationaryPiNum = 1
      ∧ measuredCap3.stationaryPiDen = 910
  c16_cap4_uniform_derived_unformalized :=
    ∀ nStates : ℕ, UniformNamedPremise nStates → UniformNamedPremise nStates
  c16_ratio_half_under_uniform :=
    ∀ (nStates : ℕ) (_hπ : UniformNamedPremise nStates),
      classMassRatioPi (uniformPi nStates) = (1 : ℚ) / 2
  model_labeled_weight_framing :=
    RelabelInvariant (fun _ : BoundedComplex 0 => (1 : ℝ))
  blocker_iff_mu :=
    ∀ (B : ℕ) (ν : TriangulationClass B → ℝ),
      GaugeCountingPrinciple ν ↔
        ∀ K : BoundedComplex B,
          ν (Quotient.mk (relabelSetoid B) K) = mu K

/-- Every premise field is inhabited by a cited theorem (or, for cap-4, by the
named uniformity premise itself, tagged DERIVED-UNFORMALIZED). -/
theorem measureDerivationPremises_inhabited :
    measureDerivationPremises.c4_erasure_jacobian
      ∧ measureDerivationPremises.c4_gibbs_is_jacobian_factor
      ∧ measureDerivationPremises.c17_unit_fugacity_a17
      ∧ measureDerivationPremises.c16_rate_symmetry_balance
      ∧ measureDerivationPremises.c16_cap3_uniform_measured
      ∧ measureDerivationPremises.c16_cap4_uniform_derived_unformalized
      ∧ measureDerivationPremises.c16_ratio_half_under_uniform
      ∧ measureDerivationPremises.model_labeled_weight_framing
      ∧ measureDerivationPremises.blocker_iff_mu := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B w hw K; exact pushforward_labeledWeight_eq_gauge_divisor w hw K
  · intro B K; exact mu_eq_gibbs_mul_erasePush_one K
  · intro F c a e h hs; exact unit_fugacity_forced_by_surface_and_kindTotals F h hs
  · intro n hn K K'; exact uniform_detailed_balance (B := 3) n hn K K'
  · exact ⟨measuredCap3_nStates, measuredCap3_symmetric,
      measuredCap3_pi.1, measuredCap3_pi.2⟩
  · intro n h; exact h
  · intro n h; exact classMassRatioPi_of_uniform_eq_half n h
  · exact relabelInvariant_one
  · intro B ν; exact gaugeCountingPrinciple_iff_mu_on_representatives ν

/-! ## §5. Assembly index (flag moved 2026-07-30, gatekeeper-signed) -/

structure MeasureDerivationIndex : Type where
  /-- Closing theorem for `gibbsWeight` class mass is stated. -/
  gibbs_gauge_counting : Bool
  /-- C17 A1.7 route to `GaugeCountingPrinciple` is stated. -/
  a17_gauge_counting : Bool
  /-- Premises certificate is inhabited. -/
  premises_inhabited : Bool
  /-- C16 process discrimination is packaged. -/
  c16_discrimination : Bool
  /-- Claimed 2026-07-30: `FullTheoryLedger.gap2_measure_derived` flipped
  after the gatekeeper hostile review (MINOR, prose repaired): closings rest
  on C4 + C17 THEOREMs and the blocker iff; C16 fields are process
  discrimination only, not cited by the closing proof terms. -/
  measure_flag_moved : Bool

def measureDerivationIndex : MeasureDerivationIndex where
  gibbs_gauge_counting := true
  a17_gauge_counting := true
  premises_inhabited := true
  c16_discrimination := true
  measure_flag_moved := true

theorem index_gibbs : measureDerivationIndex.gibbs_gauge_counting = true := rfl
theorem index_a17 : measureDerivationIndex.a17_gauge_counting = true := rfl
theorem index_premises : measureDerivationIndex.premises_inhabited = true := rfl
theorem index_c16 : measureDerivationIndex.c16_discrimination = true := rfl
/-- Flag moved 2026-07-30 (gatekeeper-signed flip). -/
theorem index_flag_moved : measureDerivationIndex.measure_flag_moved = true := rfl

/-! ## §6. G1 self-check: no Aut wrapper on the construction side

The killed 2026-07-26 discharge reimported Aut through
`GaugeHistoryMeasure.nuBuild`. This module never imports that file. The weight
fed to `GaugeCountingPrinciple` is either `classMass gibbsWeight` (factorials
only) or `classMass (postedWeight c B)` under letter-cost premises. -/

/-- Construction-side weight for the base closing theorem is definitionally the
Gibbs labeled weight (size factorials), not an Aut-counting wrapper. -/
theorem construction_is_gibbsWeight (K : BoundedComplex B) :
    gibbsWeight K
      = 1 / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) :=
  rfl

/-- The base closing theorem's class mass equals `mu` on every representative,
via the C4 bridge (not via a history/Aut wrapper). -/
theorem closing_eq_mu_not_wrapper (K : BoundedComplex B) :
    classMass (gibbsWeight : BoundedComplex B → ℝ)
        (Quotient.mk (relabelSetoid B) K) = mu K :=
  classMass_gibbs_eq_mu_via_erasure K

end

/-! ## Axiom audit

Expected for `gap2_gauge_counting_gibbsWeight` and
`gap2_gauge_counting_from_surface_and_kindTotals`:
`[propext, Classical.choice, Quot.sound]`.

If anything beyond the base triple plus a disclosed `native_decide` family
appears on the closing theorems, stop and report. -/

#print axioms gap2_gauge_counting_gibbsWeight
#print axioms gap2_gauge_counting_from_surface_and_kindTotals
#print axioms gap2_measure_from_c4_c17
#print axioms classMass_gibbs_eq_mu_via_erasure
#print axioms measureDerivationPremises_inhabited
#print axioms c16_process_discrimination
#print axioms index_flag_moved

end Gap2MeasureDerivation
end SevenGaps
end Gravity
end IndisputableMonolith
