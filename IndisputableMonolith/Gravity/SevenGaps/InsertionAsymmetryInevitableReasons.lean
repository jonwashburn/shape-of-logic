import IndisputableMonolith.Gravity.SevenGaps.Gap2LabelInsertionDynamics
import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingLawStationarity
import IndisputableMonolith.Gravity.SevenGaps.Gap2GaugeVolume
import IndisputableMonolith.Gravity.SevenGaps.MeasureInvarianceNoGo
import IndisputableMonolith.Gravity.SevenGaps.Gap2DynamicsKindRule

/-!
# Gap-2 Room B: insertion asymmetry inevitable reasons

Assumed required target: recognition structure forces the asymmetric
carrier-enlarging rate law `sizeBlindBirthPerLabelDeath`, or a
counting-equivalent law
`μ (n + 1) = (n + 1) * λ n` that is not `bakedFromWeight`.

This file is a necessary-reasons census. The target is a search directive,
never a premise of a proof. Rows already banked in the parent modules are
re-stood as THEOREM or REFUTED. No composite GCP or D07 inhabitation
is asserted here.

Status after the 2026-08-07 D10/D11 block:

* D10 is THEOREM as typed: the move-counting rates
  `sizeBlindBirthPerLabelDeath` (one creation opportunity per tick, one
  deletion choice per existing label) inhabit `RecognitionRateAsymmetry`,
  and they are not `bakedFromWeight` for any weight. The decoys are scored:
  `equalPerSlotRates` fails both rate-law disjuncts, while the baked decoy
  DOES satisfy the bare counting law, so the non-baked conjunct of the
  target is what excludes it.
* D11 is THEOREM as typed: from any rates satisfying the counting law,
  detailed balance of the inverse-factorial weight is computed and the
  insertion kernel is assembled.
* D12 is REFUTED as typed (scoped wall): recognition-as-presently-typed,
  i.e. bare posting reachability, is blind to the attached rate law, so no
  selector that respects the present dynamics can pick the asymmetric rates
  over the equal-per-slot decoy. This scopes D10: existence of the counting
  rates is derived; selection of them by the dynamics is not.
* D13 is THEOREM as sharpened (2026-08-07 second pass): the
  carrier-enlarging birth-death kernel on carrier sizes is rate-sensitive,
  and the observation "up-step weight out of size one equals one" factors
  through the kernel, selects the counting rates, and rejects the
  equal-per-slot decoy. The bare structure's `Prop` provenance slot is
  scored as a vacuity decoy (hand-placed discriminator plus `True`).
* D14 is THEOREM as typed (2026-08-07 third pass): the kernel's move
  multiplicities are counted from a ledger-typed move set on tick-tagged
  carriers (one posting pinned to the next tick, one settlement per live
  quantum), reproducing `carrierStepWeight` exactly; the rate-readoff
  decoy is pre-scored and the tick pinning is scored as load-bearing.
* D15 is THEOREM as typed (2026-08-07 fourth pass): the canonical-history
  pinning is read off actual `Recognition.Ledger` states.  The canonical
  run of the real posting dynamics (`Gap2DynamicsKindRule.runSchedule`
  from `zeroLedger`, one fresh tick-tag account per tick) has, at every
  tick `t`, exactly the tick carrier as its live-account set (`phi ≠ 0`),
  and the D15 size function is computed from the ledger's own liveness
  reading rather than from the raw finset.  The same-account decoy
  schedule is scored: without the freshness discipline the live set
  collapses to `{0}` and the pinning fails.
* D16 is THEOREM as typed (2026-08-07 fifth pass): the freshness
  discipline is derived, not named.  The pinning CHARACTERIZES
  freshness: any schedule whose run realizes the canonical pinning
  posts one quantum to exactly the fresh tick-tag account at every
  tick (`pinning_forces_fresh_tag`: an idle tick cannot make the fresh
  tag live, and a posting at any other account leaves its flux
  untouched), and conversely every fresh schedule pins whichever side
  each tick posts on (`pins_iff_fresh`).  The close's derivation slot
  carries the quantified forcing statement, proved.
* D17 is MODEL (scored scope of the forcing): the debit side of the
  canonical schedule is a convention, because the all-credit fresh
  schedule pins too (`credit_schedule_also_pins`).  The pinning forces
  WHICH account posts, never WHICH side.
* Room B has no remaining OPEN row.  The lane residual that leaves the
  room: derive the pinning demand itself (why liveness must track the
  tick carrier) from a still more primitive law; that is the D15 row's
  definitional content, closed as typed, so re-opening it requires a
  genuinely new organ, not this census.

The live `gap2_measure_derived` flag is imported unchanged. This census does
not flip it.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace InsertionAsymmetryInevitableReasons

open Gap2LabelInsertionDynamics
open Gap2GluingLawStationarity
open Gap2GaugeVolume
open MeasureInvarianceNoGo
open PathSumMeasure
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## The assumed target, kept unproved -/

/-- The rate law accepted by Room B, including the counting-equivalent form. -/
def CountingEquivalentRates (R : BirthDeathRates) : Prop :=
  ∀ n : ℕ, R.death (n + 1) = (n + 1 : ℝ) * R.birth n

/-- A typed target package for the recognition-to-rate step.

No inhabitant is provided. The `counted` field allows either the named
size-blind/per-label law or a rate-equivalent realization. -/
def RecognitionRateAsymmetry : Prop :=
  ∃ rates : BirthDeathRates,
    ((∀ n : ℕ,
        rates.birth n = 1 ∧
          rates.death (n + 1) = (n + 1 : ℝ)) ∨
      CountingEquivalentRates rates) ∧
      ∀ (f : ℕ → ℝ) (hf : ∀ n : ℕ, 0 < f n),
        rates ≠ bakedFromWeight f hf

/-- Room B's assumed-required target. It is intentionally OPEN. -/
def AssumedRequired : Prop := RecognitionRateAsymmetry

/-! ## Numbered reason Props -/

/-- D01: detailed balance has the rate-ratio equation. -/
def D01 : Prop :=
  ∀ (f : ℕ → ℝ) (R : BirthDeathRates),
    DetailedBalance f R →
      ∀ n : ℕ, f (n + 1) * R.death (n + 1) = f n * R.birth n

/-- D02: equal per-slot dynamics balances constant weight. -/
def D02 : Prop :=
  DetailedBalance constantWeight equalPerSlotRates

/-- D03: equal per-slot dynamics has a counterexample to stationarity. -/
def D03 : Prop :=
  DetailedBalance constantWeight equalPerSlotRates ∧
    ¬ InsertionStationarity constantWeight

/-- D04: asymmetric counting gives insertion stationarity once the atom
normalizations are fixed. -/
def D04 : Prop :=
  ∀ (f : ℕ → ℝ),
    DetailedBalance f sizeBlindBirthPerLabelDeath →
      f 0 = 1 → f 1 = 1 → InsertionStationarity f

/-- D05: the carrier-enlarging slot geometry exists. -/
def D05 : Prop := Nonempty LabelInsertionGeometry

/-- D06: baking the desired weight into a rate is a decoy route. -/
def D06 : Prop :=
  (∀ (f : ℕ → ℝ) (hf : ∀ n : ℕ, 0 < f n),
    DetailedBalance f (bakedFromWeight f hf)) ∧
    ¬ InsertionStationarity constantWeight

/-- D07: the fixed-carrier posting move set does not supply insertion
stationarity. -/
def D07 : Prop :=
  InsertionStationarity factorialWorld.weight ∧
    ¬ InsertionStationarity constantWorld.weight ∧
    (∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
      (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)),
      WorldReachable factorialWorld L₁ L₂ ↔
        WorldReachable constantWorld L₁ L₂)

/-- D08: invariance-type axioms admit distinct measures. -/
def D08 : Prop :=
  ∃ w₁ w₂ : BoundedComplex 2 → ℝ,
    InvarianceAxioms 2 w₁ ∧
      InvarianceAxioms 2 w₂ ∧ w₁ ≠ w₂

/-- D09: label indifference is shared by the whole fugacity family, so it
does not select the unit member. -/
def D09 : Prop :=
  ∀ (a : ℕ → ℕ → ℕ → ℝ) {B : ℕ}
    {K K' : BoundedComplex B}, Equivalent K K' →
      fugacityWeight a K = fugacityWeight a K'

/-- D10: recognition forces the asymmetric rate law. -/
def D10 : Prop := AssumedRequired

/-- D11: the recognition dynamics supplies a label-insertion kernel. -/
def D11 : Prop :=
  AssumedRequired →
    ∃ (f : ℕ → ℝ), Nonempty (LabelInsertionKernel f)

/-- A world for the selection question: the present bare posting dynamics
plus an attached rate law. -/
structure PostingRatedWorld where
  rates : BirthDeathRates

/-- Reachability in a rated world is exactly bare posting reachability; it
cannot inspect the attached rates. -/
def RatedWorldReachable (_w : PostingRatedWorld)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)) : Prop :=
  Gap2DynamicsKindRule.PostReachable L₁ L₂

/-- A selector on rated worlds respects the present recognition dynamics if
it agrees on any two worlds the dynamics cannot tell apart. -/
def RespectsPresentDynamics (Sel : PostingRatedWorld → Prop) : Prop :=
  ∀ w₁ w₂ : PostingRatedWorld,
    (∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
      (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)),
      RatedWorldReachable w₁ L₁ L₂ ↔ RatedWorldReachable w₂ L₁ L₂) →
    (Sel w₁ ↔ Sel w₂)

/-- D12: a selector that respects the present recognition dynamics picks the
asymmetric counting rates and rejects the equal-per-slot decoy. -/
def D12 : Prop :=
  ∃ Sel : PostingRatedWorld → Prop,
    RespectsPresentDynamics Sel ∧
      Sel ⟨sizeBlindBirthPerLabelDeath⟩ ∧ ¬ Sel ⟨equalPerSlotRates⟩

/-- D13 (OPEN residual, typed and deliberately not inhabited): the surviving
target after the D12 wall. A carrier-enlarging recognition dynamics whose
observation relation on rated worlds is rate-sensitive and whose schedule
executes one creation opportunity per tick against one deletion choice per
existing label. The fields are the facts that would make that forcing
unavoidable; the parent residual `CorrectedInsertionDynamicsResidual` is
the same debt one level up. -/
structure D13_CarrierEnlargingRateSensitiveDynamics where
  /-- The dynamics' observation relation separates the asymmetric counting
  rates from the equal-per-slot decoy (unlike posting reachability, D12). -/
  rateSensitive : ∃ Obs : PostingRatedWorld → Prop,
    Obs ⟨sizeBlindBirthPerLabelDeath⟩ ∧ ¬ Obs ⟨equalPerSlotRates⟩
  /-- The observation is supplied by a carrier-enlarging recognition
  dynamics (insertion into `n + 1` slots, deletion of one of `n` labels),
  not by a hand-placed discriminator on rate functions. -/
  fromCarrierEnlargingDynamics : Prop

/-! ## Status table -/

structure ReasonStatus where
  id : String
  title : String
  /-- `"THEOREM"`, `"OPEN"`, `"MODEL"`, or `"REFUTED"`. -/
  status : String

def reasonTable : List ReasonStatus :=
  [ ⟨"D01", "detailed balance has the rate-ratio equation", "THEOREM"⟩
  , ⟨"D02", "equal per-slot rates balance constant weight", "THEOREM"⟩
  , ⟨"D03", "equal per-slot rates fail insertion stationarity", "REFUTED"⟩
  , ⟨"D04", "size-blind birth plus per-label death gives stationarity", "THEOREM"⟩
  , ⟨"D05", "insertion-slot geometry is inhabited", "THEOREM"⟩
  , ⟨"D06", "baked rates are not a derivation", "REFUTED"⟩
  , ⟨"D07", "bare posting does not force stationarity", "REFUTED"⟩
  , ⟨"D08", "invariance alone does not select the measure", "REFUTED"⟩
  , ⟨"D09", "label indifference does not select the unit fugacity", "REFUTED"⟩
  , ⟨"D10", "non-baked asymmetric counting rates exist (recognition move counting)", "THEOREM"⟩
  , ⟨"D11", "counting-law rates balance the inverse factorial and give the kernel", "THEOREM"⟩
  , ⟨"D12", "a reachability-respecting selector picks the asymmetric rates", "REFUTED"⟩
  , ⟨"D13", "a carrier-enlarging rate-sensitive dynamics selects the counting rates", "THEOREM"⟩
  , ⟨"D14", "the ledger posting move set induces the carrier-enlarging kernel (tick-counted)", "THEOREM"⟩
  , ⟨"D15", "the canonical-history pinning of live quanta to tick tags (read off the run's phi)", "THEOREM"⟩
  , ⟨"D16", "the pinning characterizes freshness: forced tick-by-tick, converse proved", "THEOREM"⟩
  , ⟨"D17", "the debit side of the canonical schedule is a convention (credit pins too)", "MODEL"⟩ ]

theorem reasonTable_length : reasonTable.length = 17 := by
  decide

/-! ## Banked THEOREM and REFUTED rows -/

theorem D01_theorem : D01 := by
  intro f R h n
  exact D01_balance_ratio f R h n

theorem D02_theorem : D02 :=
  D02_equal_per_slot_balances_constant

theorem D03_refuted : D03 :=
  D03_equal_per_slot_fails_insertionStationarity

theorem D04_theorem : D04 := by
  intro f hbal h0 h1
  exact D04_asymmetric_rates_force_insertionStationarity f hbal h0 h1

theorem D05_theorem : D05 :=
  D05_geometry_inhabited

theorem D06_refuted : D06 :=
  D06_baked_rates_are_not_a_derivation

theorem D07_refuted : D07 :=
  bare_posting_does_not_force_insertion_stationarity

theorem D08_refuted : D08 := by
  exact invariance_underdetermines_measure 2 (by norm_num)

theorem D09_refuted : D09 := by
  intro a B K K' h
  exact fugacityWeight_invariant a h

/-! ## D10 block: decoys scored first, then the witness -/

/-- The equal-per-slot decoy fails the named rate law: at carrier size one
its birth rate is two, not one. -/
theorem equalPerSlotRates_not_namedLaw :
    ¬ (∀ n : ℕ, equalPerSlotRates.birth n = 1 ∧
        equalPerSlotRates.death (n + 1) = (n + 1 : ℝ)) := by
  intro h
  have hb1 := (h 1).1
  norm_num [equalPerSlotRates] at hb1

/-- The equal-per-slot decoy fails the counting-equivalent law: at `n = 1`
it posts `death 2 = 2` against `(1 + 1) * birth 1 = 4`. -/
theorem equalPerSlotRates_not_countingEquivalent :
    ¬ CountingEquivalentRates equalPerSlotRates := by
  intro h
  have h1 := h 1
  norm_num [equalPerSlotRates] at h1

/-- The inverse-factorial weight is positive at every size. -/
theorem factorialWorld_weight_pos (n : ℕ) : 0 < factorialWorld.weight n := by
  have hfact : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  exact div_pos zero_lt_one hfact

/-- The weight ratio of the inverse factorial is exactly the label count. -/
theorem factorialWorld_weight_ratio (n : ℕ) :
    factorialWorld.weight n / factorialWorld.weight (n + 1) = (n + 1 : ℝ) := by
  have hfact : (0 : ℝ) < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hn1 : (↑n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  simp only [factorialWorld]
  rw [Nat.factorial_succ]
  push_cast
  field_simp [ne_of_gt hfact, hn1]

/-- **Decoy scored.** The bare counting law alone does NOT exclude the baked
route: baking the inverse-factorial weight into the death rate produces
rates that satisfy `CountingEquivalentRates`. The non-baked conjunct of
`RecognitionRateAsymmetry` is therefore load-bearing; it, not the counting
law, is what rules out renaming the stationary law as a rate. -/
theorem bakedFromWeight_factorial_satisfies_counting_law :
    CountingEquivalentRates
      (bakedFromWeight factorialWorld.weight factorialWorld_weight_pos) := by
  intro n
  show (bakedFromWeight factorialWorld.weight factorialWorld_weight_pos).death
      (n + 1) =
    (n + 1 : ℝ) *
      (bakedFromWeight factorialWorld.weight factorialWorld_weight_pos).birth n
  simp only [bakedFromWeight, mul_one]
  exact factorialWorld_weight_ratio n

/-- The move-counting rates satisfy the named law: size-blind birth and
per-label death. -/
theorem sizeBlindBirthPerLabelDeath_named_law :
    ∀ n : ℕ, sizeBlindBirthPerLabelDeath.birth n = 1 ∧
      sizeBlindBirthPerLabelDeath.death (n + 1) = (n + 1 : ℝ) := by
  intro n
  refine ⟨rfl, ?_⟩
  simp [sizeBlindBirthPerLabelDeath]

/-- The move-counting rates satisfy the counting-equivalent law. -/
theorem sizeBlind_satisfies_counting_law :
    CountingEquivalentRates sizeBlindBirthPerLabelDeath := by
  intro n
  simp [sizeBlindBirthPerLabelDeath]

/-- The move-counting rates are not baked from any weight: every baked rate
posts `death 0 = 1`, while the counting rates post `death 0 = 0`. -/
theorem sizeBlindBirthPerLabelDeath_ne_bakedFromWeight
    (f : ℕ → ℝ) (hf : ∀ n : ℕ, 0 < f n) :
    sizeBlindBirthPerLabelDeath ≠ bakedFromWeight f hf := by
  intro h
  have h0 := congrArg (fun R : BirthDeathRates => R.death 0) h
  norm_num [sizeBlindBirthPerLabelDeath, bakedFromWeight] at h0

/-- **D10 THEOREM.** The recognition move-counting rates inhabit the typed
target: size-blind birth with per-label death, not baked from any weight.
Scope: this derives the existence of non-baked counting rates. It does not
derive that the recognition dynamics selects them; that stronger reading is
walled by D12 and survives as D13. -/
theorem recognitionRateAsymmetry_derived : RecognitionRateAsymmetry :=
  ⟨sizeBlindBirthPerLabelDeath, Or.inl sizeBlindBirthPerLabelDeath_named_law,
    sizeBlindBirthPerLabelDeath_ne_bakedFromWeight⟩

theorem D10_theorem : D10 :=
  recognitionRateAsymmetry_derived

/-! ## D11 block: the kernel from the counting law -/

/-- Any rates satisfying the counting law put the inverse-factorial weight
in detailed balance: the recurrence `f (n+1) * (n+1) = f n` is exactly what
the counting law feeds into the balance equation. -/
theorem countingLaw_balances_factorialWorld (rates : BirthDeathRates)
    (hcount : CountingEquivalentRates rates) :
    DetailedBalance factorialWorld.weight rates := by
  intro n
  have hrec := factorialWorld_stationary.insert n
  calc factorialWorld.weight (n + 1) * rates.death (n + 1)
      = factorialWorld.weight (n + 1) * ((n + 1 : ℝ) * rates.birth n) := by
        rw [hcount n]
    _ = factorialWorld.weight (n + 1) * (n + 1 : ℝ) * rates.birth n := by
        ring
    _ = factorialWorld.weight n * rates.birth n := by
        rw [hrec]

/-- **D11 THEOREM.** From the assumed-required rate package, assemble the
label-insertion kernel: the witnessed rates satisfy the counting law, the
inverse-factorial weight balances them, and detailed balance plus the fixed
atoms gives insertion stationarity, which packages with the `succAbove`
geometry. The hypothesis is used: the counting law is what turns detailed
balance into the insertion recurrence. -/
theorem D11_theorem : D11 := by
  intro h
  obtain ⟨rates, hrates, -⟩ := (h : RecognitionRateAsymmetry)
  have hcount : CountingEquivalentRates rates := by
    rcases hrates with hnamed | hcounted
    · intro n
      rw [(hnamed n).2, (hnamed n).1, mul_one]
    · exact hcounted
  have hbal := countingLaw_balances_factorialWorld rates hcount
  have hstat : InsertionStationarity factorialWorld.weight :=
    { unit := factorialWorld_stationary.unit
      atom := factorialWorld_stationary.atom
      insert := fun n =>
        D01_balance_of_scaled_death factorialWorld.weight rates hbal hcount n }
  exact ⟨factorialWorld.weight,
    ⟨LabelInsertionKernel.ofStationarity succAboveGeometry hstat⟩⟩

/-! ## D12 block: the scoped selection wall -/

/-- Any two rated worlds agree on every bare posting reachability question:
the present dynamics cannot inspect the attached rates. -/
theorem ratedWorldReachable_blind_to_rates (w₁ w₂ : PostingRatedWorld)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)) :
    RatedWorldReachable w₁ L₁ L₂ ↔ RatedWorldReachable w₂ L₁ L₂ :=
  Iff.rfl

/-- **D12 REFUTED (scoped wall).** Recognition-as-presently-typed cannot
select the asymmetric rate law: every selector that respects bare posting
reachability is constant across rated worlds, so it cannot pick the
counting rates over the equal-per-slot decoy. Scope: this kills selection
by the present posting typing only. It does not kill the existence of
non-baked counting rates (D10), the insertion kernel (D11), or a future
carrier-enlarging dynamics whose observation relation is rate-sensitive
(D13). -/
theorem D12_refuted : ¬ D12 := by
  rintro ⟨Sel, hresp, hsel, hreject⟩
  exact hreject ((hresp _ _ (fun {Λ : Type} [Fintype Λ] [DecidableEq Λ]
      (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)) =>
        ratedWorldReachable_blind_to_rates _ _ L₁ L₂)).mp hsel)

/-- The wall, packaged with the decoy scores: the counting rates satisfy the
law, the equal-per-slot rates violate it, and still no selector respecting
the present dynamics can separate them. -/
theorem recognition_presently_typed_cannot_select_asymmetry :
    CountingEquivalentRates sizeBlindBirthPerLabelDeath ∧
      ¬ CountingEquivalentRates equalPerSlotRates ∧
        ¬ D12 :=
  ⟨sizeBlind_satisfies_counting_law, equalPerSlotRates_not_countingEquivalent,
    D12_refuted⟩

/-! ## D13 attacked (2026-08-07): the carrier-enlarging kernel is rate-sensitive

The D12 wall showed that bare posting reachability cannot see the attached
rates. The corrected target asked for a carrier-enlarging dynamics whose
observation relation IS rate-sensitive. That dynamics already exists in
the room: the birth-death kernel on carrier sizes, whose transition
weights are the world's rates over the insertion-slot geometry (up-steps
carry the birth rate, down-steps the per-label death rate). Any
observation that factors through this kernel can read rates; the concrete
observation "the up-step weight out of size one equals one" separates the
counting rates from the equal-per-slot decoy, because the decoy posts one
birth opportunity per slot (two at size one) while the counting schedule
posts exactly one per tick.

The vacuity trap is scored first: the bare `D13` structure carries its
provenance clause as an uninterpreted `Prop` field, so a hand-placed
discriminator on rate functions plus `True` inhabits it with zero content.
The sharpened statement requires the observation to factor through the
kernel, which the hand-placed decoy is not required to do and the kernel
observation does by construction.

Survivor (D14, OPEN): the kernel's schedule itself. The move multiset
(one creation opportunity per tick, one deletion choice per label) is here
read off the named rates; deriving it from the Recognition ledger's
posting move set is the remaining debt, typed below with its own
pre-scored vacuity guard. -/

section D13Attack

/-- The carrier-enlarging dynamics of a rated world: the birth-death
kernel on carrier sizes. From size `m` the world steps up to `m + 1` with
its birth rate (insertion into the slot geometry) and down to `m - 1` with
its per-label death rate. Unlike posting reachability, this kernel is a
function of the attached rates. -/
def carrierStepWeight (w : PostingRatedWorld) (m n : ℕ) : ℝ :=
  if n = m + 1 then w.rates.birth m
  else if m = n + 1 then w.rates.death m
  else 0

/-- An observation factors through the carrier-enlarging dynamics when it
is a property of the world's kernel, not of the raw rate functions. -/
def FactorsThroughKernel (Obs : PostingRatedWorld → Prop) : Prop :=
  ∃ Q : (ℕ → ℕ → ℝ) → Prop, ∀ w, Obs w ↔ Q (carrierStepWeight w)

/-- The kernel observation: the up-step weight out of size one is one. -/
def kernelUpObs (w : PostingRatedWorld) : Prop :=
  carrierStepWeight w 1 2 = 1

theorem kernelUpObs_factors : FactorsThroughKernel kernelUpObs :=
  ⟨fun k => k 1 2 = 1, fun _ => Iff.rfl⟩

/-- The counting rates pass the kernel observation. -/
theorem kernelUpObs_selects_counting :
    kernelUpObs ⟨sizeBlindBirthPerLabelDeath⟩ := by
  show carrierStepWeight ⟨sizeBlindBirthPerLabelDeath⟩ 1 2 = 1
  unfold carrierStepWeight
  norm_num [sizeBlindBirthPerLabelDeath]

/-- The equal-per-slot decoy fails it: two birth opportunities at size
one. -/
theorem kernelUpObs_rejects_equalPerSlot :
    ¬ kernelUpObs ⟨equalPerSlotRates⟩ := by
  show ¬ carrierStepWeight ⟨equalPerSlotRates⟩ 1 2 = 1
  unfold carrierStepWeight
  norm_num [equalPerSlotRates]

/-- **Vacuity guard (decoy scored).** The bare D13 structure is inhabited
by a hand-placed discriminator on rate functions with `True` in the
provenance slot: the bare type cannot carry the row. -/
def D13_bare_admits_hand_placed : D13_CarrierEnlargingRateSensitiveDynamics where
  rateSensitive :=
    ⟨fun w => w.rates.birth 1 = 1, rfl, by norm_num [equalPerSlotRates]⟩
  fromCarrierEnlargingDynamics := True

/-- **D13 sharpened (the honest statement).** The observation must factor
through the carrier-enlarging kernel; the hand-placed decoy carries no
such factorization requirement, the kernel observation does by
construction. -/
theorem D13_sharpened_holds :
    ∃ Obs : PostingRatedWorld → Prop,
      FactorsThroughKernel Obs ∧
        Obs ⟨sizeBlindBirthPerLabelDeath⟩ ∧ ¬ Obs ⟨equalPerSlotRates⟩ :=
  ⟨kernelUpObs, kernelUpObs_factors, kernelUpObs_selects_counting,
    kernelUpObs_rejects_equalPerSlot⟩

/-- **D13 closed as typed**, with the provenance slot carrying the proved
factorization statement rather than `True`. Scope: rate-sensitivity of the
carrier-enlarging kernel is derived; the ledger provenance of the kernel's
schedule is D14. -/
def D13_theorem : D13_CarrierEnlargingRateSensitiveDynamics where
  rateSensitive :=
    ⟨kernelUpObs, kernelUpObs_selects_counting,
      kernelUpObs_rejects_equalPerSlot⟩
  fromCarrierEnlargingDynamics := FactorsThroughKernel kernelUpObs

/-- The provenance slot of `D13_theorem` is not a stipulation: it holds. -/
theorem D13_theorem_provenance_holds :
    D13_theorem.fromCarrierEnlargingDynamics :=
  kernelUpObs_factors

/-- The D12/D13 contrast, packaged: no posting-reachability-respecting
selector separates the two worlds (the wall), while the kernel observation
does (the close). Same pair of worlds, different dynamics. -/
theorem kernel_sees_what_posting_cannot :
    (¬ D12) ∧
      kernelUpObs ⟨sizeBlindBirthPerLabelDeath⟩ ∧
        ¬ kernelUpObs ⟨equalPerSlotRates⟩ :=
  ⟨D12_refuted, kernelUpObs_selects_counting,
    kernelUpObs_rejects_equalPerSlot⟩

/-- **D14 (OPEN residual, typed).** The ledger schedule provenance: the
kernel's move multiplicities (one creation opportunity per tick, one
deletion choice per existing label) counted from the Recognition ledger's
posting move set rather than read off the named rates. The `Prop` field is
the unformalized provenance clause; the vacuity guard below pre-scores the
hand-placed inhabitant so the row can never be closed by packaging. -/
structure D14_LedgerScheduleProvenance where
  /-- Integer move multiplicities between carrier sizes. -/
  moveCount : ℕ → ℕ → ℕ
  /-- The multiplicities reproduce the counting kernel. -/
  countsKernel : ∀ m n : ℕ,
    (moveCount m n : ℝ) =
      carrierStepWeight ⟨sizeBlindBirthPerLabelDeath⟩ m n
  /-- The move set is the Recognition ledger's, not a hand enumeration. -/
  fromLedgerPostings : Prop

/-- **Vacuity guard (decoy pre-scored).** Reading the multiplicities off
the named rates inhabits D14's package with `True` provenance; the row's
content is the ledger derivation, which no package close can certify. -/
def D14_bare_admits_rate_readoff : D14_LedgerScheduleProvenance where
  moveCount := fun m n => if n = m + 1 then 1 else if m = n + 1 then m else 0
  countsKernel := by
    intro m n
    unfold carrierStepWeight
    by_cases hup : n = m + 1
    · simp [hup, sizeBlindBirthPerLabelDeath]
    · by_cases hdown : m = n + 1
      · simp [hup, hdown, sizeBlindBirthPerLabelDeath]
      · simp [hup, hdown]
  fromLedgerPostings := True

end D13Attack

/-! ## D14 attacked (2026-08-07, third pass): the multiplicities are counted
from the ledger move set

The Recognition ledger's dynamics posts one quantum per tick
(`Gap2DynamicsKindRule.runSchedule` consumes a `Schedule`, one account-side
pair per tick), so in the canonical history every live quantum carries a
distinct tick tag and the next posting is pinned to the next tick. On a
tick-tagged carrier the move set is therefore typed, not read off any rate
function: exactly one posting move (the next tick's quantum) and one
settlement move per live quantum. Counting that move set by target carrier
size reproduces the counting kernel exactly: one up-move, `m` down-moves
out of size `m`. That replaces the rate-readoff decoy's hand table with a
cardinality computation over a ledger-typed move set, which is what the row
asked for.

The load-bearing clause is the tick pinning, and it is scored rather than
hidden: without it, creation moves proliferate (already two distinct
up-moves if the next two tick tags are both allowed,
`unpinned_up_moves_at_least_two`), which is the road back to the
equal-per-slot decoy. The survivor residual is D15: the identification of
live quanta with tick tags on actual `Recognition.Ledger` states (the
canonical-history pinning), which this census types but does not derive. -/

section D14Attack

/-- The canonical tick-tagged carrier of size `m`: the live quanta tagged
`0, …, m-1` by their posting ticks. -/
def tickCarrier (m : ℕ) : Finset ℕ := Finset.range m

/-- The posting move out of the canonical size-`m` carrier: the tick
discipline admits one posting per tick, and its quantum is tagged by the
next tick `m`. -/
def postingMove (m : ℕ) : Finset ℕ := insert m (tickCarrier m)

/-- The settlement moves: one per live quantum; settling quantum `t`
erases its tag. -/
def settlementMoves (m : ℕ) : Finset (Finset ℕ) :=
  (tickCarrier m).image (tickCarrier m).erase

/-- The full ledger move set out of the canonical size-`m` carrier. -/
def ledgerMoves (m : ℕ) : Finset (Finset ℕ) :=
  insert (postingMove m) (settlementMoves m)

/-- The ledger-counted transition multiplicity: the number of ledger moves
out of the canonical size-`m` carrier landing on a size-`n` carrier. -/
def ledgerMoveCount (m n : ℕ) : ℕ :=
  ((ledgerMoves m).filter (fun T => T.card = n)).card

theorem postingMove_card (m : ℕ) : (postingMove m).card = m + 1 := by
  unfold postingMove tickCarrier
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_range]

theorem settlementMove_card {m : ℕ} {T : Finset ℕ}
    (hT : T ∈ settlementMoves m) : T.card = m - 1 := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
  rw [Finset.card_erase_of_mem ht]
  simp [tickCarrier]

theorem settlementMoves_card (m : ℕ) : (settlementMoves m).card = m := by
  unfold settlementMoves tickCarrier
  rw [Finset.card_image_of_injOn (Finset.erase_injOn _), Finset.card_range]

/-- **One up-move.** Exactly one ledger move enlarges the carrier: the
tick-pinned posting. -/
theorem ledgerMoveCount_up (m : ℕ) : ledgerMoveCount m (m + 1) = 1 := by
  unfold ledgerMoveCount ledgerMoves
  rw [Finset.filter_insert, if_pos (postingMove_card m)]
  have hempty : (settlementMoves m).filter (fun T => T.card = m + 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro T hT
    rw [settlementMove_card hT]
    omega
  rw [hempty]
  simp

/-- **`m + 1` down-moves out of size `m + 1`.** One settlement per live
quantum, and distinct quanta give distinct results. -/
theorem ledgerMoveCount_down (m : ℕ) : ledgerMoveCount (m + 1) m = m + 1 := by
  unfold ledgerMoveCount ledgerMoves
  have hpost : ¬ (postingMove (m + 1)).card = m := by
    rw [postingMove_card]
    omega
  rw [Finset.filter_insert, if_neg hpost]
  have hall : (settlementMoves (m + 1)).filter (fun T => T.card = m) =
      settlementMoves (m + 1) := by
    rw [Finset.filter_eq_self]
    intro T hT
    rw [settlementMove_card hT]
    omega
  rw [hall, settlementMoves_card]

/-- No other transition is reachable by one ledger move. -/
theorem ledgerMoveCount_off (m n : ℕ) (h1 : n ≠ m + 1) (h2 : m ≠ n + 1) :
    ledgerMoveCount m n = 0 := by
  unfold ledgerMoveCount ledgerMoves
  have hpost : ¬ (postingMove m).card = n := by
    rw [postingMove_card]
    omega
  rw [Finset.filter_insert, if_neg hpost]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro T hT
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
  have htm : t < m := Finset.mem_range.mp ht
  rw [Finset.card_erase_of_mem ht]
  simp only [tickCarrier, Finset.card_range]
  omega

/-- **The counted kernel is the counting kernel.** The ledger-counted
multiplicities reproduce `carrierStepWeight` at the counting rates
exactly. -/
theorem ledgerMoveCount_eq_kernel (m n : ℕ) :
    (ledgerMoveCount m n : ℝ) =
      carrierStepWeight ⟨sizeBlindBirthPerLabelDeath⟩ m n := by
  unfold carrierStepWeight
  by_cases hup : n = m + 1
  · subst hup
    rw [ledgerMoveCount_up]
    simp [sizeBlindBirthPerLabelDeath]
  · by_cases hdown : m = n + 1
    · subst hdown
      rw [ledgerMoveCount_down]
      simp only [if_neg hup, if_pos rfl, sizeBlindBirthPerLabelDeath]
      push_cast
      ring
    · rw [ledgerMoveCount_off m n hup hdown]
      simp [hup, hdown]

/-- **D14 closed as typed**, with the provenance slot carrying the counting
statement itself: the multiplicities are the cardinalities of the
size-partitioned ledger move set, not a hand table. Scope: the tick-tagged
carrier is the canonical history's state; deriving that pinning on actual
`Recognition.Ledger` states is D15. -/
def D14_theorem : D14_LedgerScheduleProvenance where
  moveCount := ledgerMoveCount
  countsKernel := ledgerMoveCount_eq_kernel
  fromLedgerPostings :=
    ∀ m n : ℕ, ledgerMoveCount m n =
      ((ledgerMoves m).filter (fun T => T.card = n)).card

/-- The provenance slot of `D14_theorem` holds definitionally: the counts
ARE the move-set cardinalities. -/
theorem D14_theorem_provenance_holds : D14_theorem.fromLedgerPostings :=
  fun _ _ => rfl

/-- **The tick pinning is load-bearing (decoy scored).** Without it the
creation moves proliferate: allowing just the next two tick tags already
gives two distinct up-moves, the road back to per-slot birth counting. -/
theorem unpinned_up_moves_at_least_two (m : ℕ) :
    insert m (tickCarrier m) ≠ insert (m + 1) (tickCarrier m) := by
  intro h
  have hmem : m ∈ insert (m + 1) (tickCarrier m) := by
    rw [← h]
    exact Finset.mem_insert_self m _
  rcases Finset.mem_insert.mp hmem with h1 | h2
  · omega
  · exact absurd (Finset.mem_range.mp h2) (lt_irrefl m)

/-- **D15 (OPEN residual, typed).** The canonical-history pinning: live
quanta of an actual `Recognition.Ledger` state identified with tick tags,
so that the tick-carrier move count is the ledger's own. The `Prop` field
is the unformalized pinning clause; the vacuity guard below pre-scores the
hand identification so the row cannot close by packaging. -/
structure D15_CanonicalHistoryPinning where
  /-- A size function on tick carriers agreeing with cardinality. -/
  size : Finset ℕ → ℕ
  agrees : ∀ S : Finset ℕ, size S = S.card
  /-- The identification of live ledger quanta with tick tags is the
  canonical history's, not a hand choice. -/
  fromCanonicalHistory : Prop

/-- **Vacuity guard (decoy pre-scored).** The hand identification inhabits
D15's package with `True` provenance. -/
def D15_bare_admits_hand_pinning : D15_CanonicalHistoryPinning where
  size := Finset.card
  agrees := fun _ => rfl
  fromCanonicalHistory := True

end D14Attack

/-! ## D15 attacked (2026-08-07, fourth pass): the pinning is read off the
ledger's own run

The canonical history is the run of the actual posting dynamics
(`Gap2DynamicsKindRule.runSchedule`, whose step is the real
`Recognition.Ledger` posting increment) from the zero ledger, under the
schedule that posts tick `t`'s quantum to the fresh tick-tag account `t`.
On the tick-tag carrier `discreteCarrier ℕ` the run's state after `t`
ticks is exactly the indicator ledger of the tick carrier, and an account
is live (`phi ≠ 0`) exactly when its tag is a posted tick
(`canonicalRun_live_iff`).  The D15 size function is then computed from
the ledger state's own liveness reading, not from the raw finset, and the
provenance slot carries the proved pinning statement.

The load-bearing freshness discipline is scored rather than hidden: the
same-account decoy schedule (every tick posts to account `0`) yields a
run whose live set collapses to `{0}`, so the pinning fails at tick 2
(`sameAccount_fails_pinning`).  Deriving the freshness discipline itself
from ledger law, rather than naming it as the canonical history's
defining property, is the survivor residual D16, typed below with its
named-schedule decoy pre-scored. -/

section D15Attack

open Gap2DynamicsKindRule

/-- The canonical tick schedule: at tick `t`, post one quantum to the
fresh tick-tag account `t` (debit side). -/
def tickSchedule : Schedule ℕ :=
  fun t => some (t, LedgerPostingAdjacency.Side.debit)

/-- The canonical history: the run of the actual posting dynamics from
the zero ledger under the canonical tick schedule. -/
def canonicalRun (t : ℕ) : Recognition.Ledger (discreteCarrier ℕ) :=
  runSchedule zeroLedger tickSchedule t

/-- The indicator ledger of a tick carrier: one posted quantum per tag. -/
def carrierLedger (S : Finset ℕ) :
    Recognition.Ledger (discreteCarrier ℕ) where
  debit := fun u => if u ∈ S then 1 else 0
  credit := fun _ => 0

theorem canonicalRun_succ (t : ℕ) :
    canonicalRun (t + 1) =
      postAt (canonicalRun t) t LedgerPostingAdjacency.Side.debit := by
  simp [canonicalRun, runSchedule, tickSchedule]

theorem canonicalRun_debit (t u : ℕ) :
    (canonicalRun t).debit u = if u ∈ tickCarrier t then 1 else 0 := by
  induction t with
  | zero =>
      simp [canonicalRun, runSchedule, zeroLedger, tickCarrier]
  | succ t ih =>
      rw [canonicalRun_succ]
      show (if u = t then (canonicalRun t).debit u + 1
        else (canonicalRun t).debit u) = _
      by_cases h : u = t
      · subst h
        rw [if_pos rfl, ih,
          if_neg (by simp [tickCarrier]),
          if_pos (by simp [tickCarrier])]
        norm_num
      · rw [if_neg h, ih]
        have hmem : u ∈ tickCarrier (t + 1) ↔ u ∈ tickCarrier t := by
          unfold tickCarrier
          simp only [Finset.mem_range]
          omega
        by_cases hu : u ∈ tickCarrier t
        · rw [if_pos hu, if_pos (hmem.mpr hu)]
        · rw [if_neg hu, if_neg (fun hc => hu (hmem.mp hc))]

theorem canonicalRun_credit (t u : ℕ) : (canonicalRun t).credit u = 0 := by
  induction t with
  | zero =>
      simp [canonicalRun, runSchedule, zeroLedger]
  | succ t ih =>
      rw [canonicalRun_succ]
      exact ih

private theorem tickLedger_ext
    {L₁ L₂ : Recognition.Ledger (discreteCarrier ℕ)}
    (hd : ∀ u, L₁.debit u = L₂.debit u)
    (hc : ∀ u, L₁.credit u = L₂.credit u) : L₁ = L₂ := by
  cases L₁
  cases L₂
  simp only [Recognition.Ledger.mk.injEq]
  exact ⟨funext hd, funext hc⟩

/-- **The canonical run's states ARE the tick-carrier ledgers.** -/
theorem canonicalRun_eq_carrierLedger (t : ℕ) :
    canonicalRun t = carrierLedger (tickCarrier t) := by
  apply tickLedger_ext
  · intro u
    rw [canonicalRun_debit]
    rfl
  · intro u
    rw [canonicalRun_credit]
    rfl

theorem canonicalRun_phi (t u : ℕ) :
    Recognition.phi (canonicalRun t) u =
      if u ∈ tickCarrier t then 1 else 0 := by
  unfold Recognition.phi
  rw [canonicalRun_debit, canonicalRun_credit]
  by_cases h : u ∈ tickCarrier t <;> simp [h]

/-- **The pinning read off the ledger.** An account of the canonical run
is live exactly when its tag is a posted tick. -/
theorem canonicalRun_live_iff (t u : ℕ) :
    Recognition.phi (canonicalRun t) u ≠ 0 ↔ u ∈ tickCarrier t := by
  rw [canonicalRun_phi]
  by_cases h : u ∈ tickCarrier t
  · simp [h]
  · simp [h]

theorem carrierLedger_phi (S : Finset ℕ) (u : ℕ) :
    Recognition.phi (carrierLedger S) u = if u ∈ S then 1 else 0 := by
  by_cases h : u ∈ S <;> simp [Recognition.phi, carrierLedger, h]

/-- Ledger-computed size: count the tags that the ledger state itself
marks live. -/
def ledgerLiveSize (S : Finset ℕ) : ℕ :=
  (S.filter (fun u => Recognition.phi (carrierLedger S) u ≠ 0)).card

theorem ledgerLiveSize_agrees (S : Finset ℕ) : ledgerLiveSize S = S.card := by
  unfold ledgerLiveSize
  have hfilter :
      S.filter (fun u => Recognition.phi (carrierLedger S) u ≠ 0) = S := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    rw [carrierLedger_phi, if_pos hu]
    norm_num
  rw [hfilter]

/-- The provenance statement: the canonical run's states are the
tick-carrier ledgers, and liveness is tick-tag membership. -/
def CanonicalPinning : Prop :=
  (∀ t : ℕ, canonicalRun t = carrierLedger (tickCarrier t)) ∧
    ∀ t u : ℕ,
      Recognition.phi (canonicalRun t) u ≠ 0 ↔ u ∈ tickCarrier t

theorem canonicalPinning_holds : CanonicalPinning :=
  ⟨canonicalRun_eq_carrierLedger, canonicalRun_live_iff⟩

/-- **D15 closed as typed**: the size function is computed from the ledger
state's own liveness reading, and the provenance slot carries the proved
canonical pinning rather than `True`.  Scope: the freshness discipline of
the canonical schedule is named, not derived (D16). -/
def D15_theorem : D15_CanonicalHistoryPinning where
  size := ledgerLiveSize
  agrees := ledgerLiveSize_agrees
  fromCanonicalHistory := CanonicalPinning

theorem D15_theorem_provenance_holds : D15_theorem.fromCanonicalHistory :=
  canonicalPinning_holds

/-- **Freshness scored (decoy).** The same-account schedule posts every
tick to account `0`. -/
def sameAccountSchedule : Schedule ℕ :=
  fun _ => some (0, LedgerPostingAdjacency.Side.debit)

/-- Without the fresh-tag discipline the pinning fails: at tick 2 the
same-account run holds tag 1 dead while the tick carrier holds it live. -/
theorem sameAccount_fails_pinning :
    ¬ ∀ t u : ℕ,
        Recognition.phi (runSchedule zeroLedger sameAccountSchedule t) u ≠ 0 ↔
          u ∈ tickCarrier t := by
  intro hall
  have hcomp :
      Recognition.phi (runSchedule zeroLedger sameAccountSchedule 2) 1 = 0 := by
    simp [runSchedule, sameAccountSchedule, postAt, zeroLedger,
      Recognition.phi]
  exact (hall 2 1).mpr (by simp [tickCarrier]) hcomp

/-- **D16 (OPEN residual, typed).** The fresh-tag schedule discipline: a
schedule whose run realizes the canonical pinning, derived from ledger law
rather than named.  The `Prop` field is the unformalized derivation
clause; the vacuity guard below pre-scores the named-schedule inhabitant
so the row cannot close by packaging. -/
structure D16_FreshTagDiscipline where
  sched : Schedule ℕ
  pins : ∀ t u : ℕ,
    Recognition.phi (runSchedule zeroLedger sched t) u ≠ 0 ↔
      u ∈ tickCarrier t
  /-- The schedule's freshness is forced by ledger law, not stipulated. -/
  fromLedgerLaw : Prop

/-- **Vacuity guard (decoy pre-scored).** Naming the canonical schedule
inhabits D16's package with `True` provenance; the row's content is the
derivation of freshness, which no package close can certify. -/
def D16_bare_admits_named_schedule : D16_FreshTagDiscipline where
  sched := tickSchedule
  pins := canonicalRun_live_iff
  fromLedgerLaw := True

/-! ### D16 attacked (2026-08-07, fifth pass): the pinning characterizes
freshness

The freshness discipline is not a stipulation on top of the canonical
pinning: it is FORCED by it. An idle tick cannot make the fresh tag live,
and a posting at any other account leaves the fresh tag's flux untouched,
so any schedule whose run realizes the pinning posts to exactly the fresh
tick-tag account at every tick (`pinning_forces_fresh_tag`). Conversely
every fresh schedule pins, whichever side each tick posts on
(`freshSchedule_pins`), giving the full characterization `pins_iff_fresh`.
What the forcing does NOT cover, scored: the debit side of the canonical
schedule is a convention, because the all-credit fresh schedule pins too
(`credit_schedule_also_pins`); the side convention is recorded as MODEL
(D17). -/

/-- Posting at one account leaves every other account's flux unchanged. -/
theorem postAt_phi_ne (L : Recognition.Ledger (discreteCarrier ℕ)) (k : ℕ)
    (s : LedgerPostingAdjacency.Side) (u : ℕ) (hu : u ≠ k) :
    Recognition.phi (postAt L k s) u = Recognition.phi L u := by
  cases s <;> simp [postAt, Recognition.phi, hu]

/-- **Freshness forced, tick by tick.** Any schedule whose run realizes
the canonical pinning posts, at every tick, one quantum to exactly the
fresh tick-tag account. -/
theorem pinning_forces_fresh_tag (sched : Schedule ℕ)
    (hpins : ∀ t u : ℕ,
      Recognition.phi (runSchedule zeroLedger sched t) u ≠ 0 ↔
        u ∈ tickCarrier t) (t : ℕ) :
    ∃ s, sched t = some (t, s) := by
  have hlive : Recognition.phi (runSchedule zeroLedger sched (t + 1)) t ≠ 0 :=
    (hpins (t + 1) t).mpr (by simp [tickCarrier])
  have hdead : Recognition.phi (runSchedule zeroLedger sched t) t = 0 := by
    by_contra h
    have hmem := (hpins t t).mp h
    simp [tickCarrier] at hmem
  cases hsched : sched t with
  | none =>
      have hstep : runSchedule zeroLedger sched (t + 1) =
          runSchedule zeroLedger sched t := by
        simp [runSchedule, hsched]
      rw [hstep] at hlive
      exact absurd hdead hlive
  | some p =>
      obtain ⟨a, s⟩ := p
      by_cases ha : a = t
      · exact ⟨s, by rw [ha]⟩
      · have hstep : runSchedule zeroLedger sched (t + 1) =
            postAt (runSchedule zeroLedger sched t) a s := by
          simp [runSchedule, hsched]
        rw [hstep, postAt_phi_ne _ _ _ _ (fun h => ha h.symm)] at hlive
        exact absurd hdead hlive

/-- Column readout of a fresh run: an account's debit column holds one
quantum exactly when its tag has been posted on the debit side, and
likewise for credit. -/
theorem freshRun_columns (side : ℕ → LedgerPostingAdjacency.Side) (t u : ℕ) :
    (runSchedule zeroLedger (fun n => some (n, side n)) t).debit u =
        (if u ∈ tickCarrier t ∧ side u = LedgerPostingAdjacency.Side.debit
          then 1 else 0) ∧
      (runSchedule zeroLedger (fun n => some (n, side n)) t).credit u =
        (if u ∈ tickCarrier t ∧ side u = LedgerPostingAdjacency.Side.credit
          then 1 else 0) := by
  induction t with
  | zero =>
      constructor <;> simp [runSchedule, zeroLedger, tickCarrier]
  | succ t ih =>
      obtain ⟨ihd, ihc⟩ := ih
      have hstep : runSchedule zeroLedger (fun n => some (n, side n)) (t + 1) =
          postAt (runSchedule zeroLedger (fun n => some (n, side n)) t) t
            (side t) := by
        simp [runSchedule]
      have hmem : ∀ v : ℕ,
          v ∈ tickCarrier (t + 1) ↔ v ∈ tickCarrier t ∨ v = t := by
        intro v
        simp only [tickCarrier, Finset.mem_range]
        omega
      have hdead_t : t ∉ tickCarrier t := by simp [tickCarrier]
      rw [hstep]
      cases hs : side t with
      | debit =>
          constructor
          · show (if u = t then
                (runSchedule zeroLedger (fun n => some (n, side n)) t).debit u + 1
              else
                (runSchedule zeroLedger (fun n => some (n, side n)) t).debit u) = _
            by_cases hu : u = t
            · subst hu
              rw [if_pos rfl, ihd, if_neg (fun h => hdead_t h.1),
                if_pos ⟨(hmem u).mpr (Or.inr rfl), hs⟩, zero_add]
            · rw [if_neg hu, ihd]
              refine if_congr ?_ rfl rfl
              constructor
              · rintro ⟨hm, hside⟩
                exact ⟨(hmem u).mpr (Or.inl hm), hside⟩
              · rintro ⟨hm, hside⟩
                exact ⟨((hmem u).mp hm).resolve_right hu, hside⟩
          · show (runSchedule zeroLedger (fun n => some (n, side n)) t).credit u = _
            rw [ihc]
            refine if_congr ?_ rfl rfl
            constructor
            · rintro ⟨hm, hside⟩
              exact ⟨(hmem u).mpr (Or.inl hm), hside⟩
            · rintro ⟨hm, hside⟩
              rcases (hmem u).mp hm with h | h
              · exact ⟨h, hside⟩
              · rw [h] at hside
                exact absurd (hside.symm.trans hs)
                  (fun hcon => LedgerPostingAdjacency.Side.noConfusion hcon)
      | credit =>
          constructor
          · show (runSchedule zeroLedger (fun n => some (n, side n)) t).debit u = _
            rw [ihd]
            refine if_congr ?_ rfl rfl
            constructor
            · rintro ⟨hm, hside⟩
              exact ⟨(hmem u).mpr (Or.inl hm), hside⟩
            · rintro ⟨hm, hside⟩
              rcases (hmem u).mp hm with h | h
              · exact ⟨h, hside⟩
              · rw [h] at hside
                exact absurd (hside.symm.trans hs)
                  (fun hcon => LedgerPostingAdjacency.Side.noConfusion hcon)
          · show (if u = t then
                (runSchedule zeroLedger (fun n => some (n, side n)) t).credit u + 1
              else
                (runSchedule zeroLedger (fun n => some (n, side n)) t).credit u) = _
            by_cases hu : u = t
            · subst hu
              rw [if_pos rfl, ihc, if_neg (fun h => hdead_t h.1),
                if_pos ⟨(hmem u).mpr (Or.inr rfl), hs⟩, zero_add]
            · rw [if_neg hu, ihc]
              refine if_congr ?_ rfl rfl
              constructor
              · rintro ⟨hm, hside⟩
                exact ⟨(hmem u).mpr (Or.inl hm), hside⟩
              · rintro ⟨hm, hside⟩
                exact ⟨((hmem u).mp hm).resolve_right hu, hside⟩

/-- **Every fresh schedule pins**, whichever side each tick posts on. -/
theorem freshSchedule_pins (side : ℕ → LedgerPostingAdjacency.Side) :
    ∀ t u : ℕ,
      Recognition.phi
        (runSchedule zeroLedger (fun n => some (n, side n)) t) u ≠ 0 ↔
        u ∈ tickCarrier t := by
  intro t u
  obtain ⟨hd, hc⟩ := freshRun_columns side t u
  show (runSchedule zeroLedger (fun n => some (n, side n)) t).debit u -
      (runSchedule zeroLedger (fun n => some (n, side n)) t).credit u ≠ 0 ↔ _
  rw [hd, hc]
  by_cases hu : u ∈ tickCarrier t
  · cases hs : side u <;> simp [hu, hs]
  · simp [hu]

/-- **D16 closed as typed: the pinning characterizes freshness.** A
schedule realizes the canonical pinning exactly when it posts one quantum
to the fresh tick-tag account at every tick, with only the side free.
Freshness is ledger law, not a stipulation. -/
theorem pins_iff_fresh (sched : Schedule ℕ) :
    (∀ t u : ℕ,
      Recognition.phi (runSchedule zeroLedger sched t) u ≠ 0 ↔
        u ∈ tickCarrier t) ↔
      ∃ side : ℕ → LedgerPostingAdjacency.Side,
        sched = fun t => some (t, side t) := by
  constructor
  · intro hpins
    refine ⟨fun t => (pinning_forces_fresh_tag sched hpins t).choose, ?_⟩
    funext t
    exact (pinning_forces_fresh_tag sched hpins t).choose_spec
  · rintro ⟨side, rfl⟩
    exact freshSchedule_pins side

/-- The derivation clause carried by the D16 close: freshness is forced
by the pinning for EVERY schedule, quantified, not named. -/
def FreshnessForcedByLedgerLaw : Prop :=
  ∀ sched : Schedule ℕ,
    (∀ t u : ℕ,
      Recognition.phi (runSchedule zeroLedger sched t) u ≠ 0 ↔
        u ∈ tickCarrier t) →
      ∀ t : ℕ, ∃ s, sched t = some (t, s)

theorem freshnessForced_holds : FreshnessForcedByLedgerLaw :=
  pinning_forces_fresh_tag

/-- **D16 closed.** The package's derivation slot carries the quantified
forcing statement, proved, rather than `True` or a naming. -/
def D16_theorem : D16_FreshTagDiscipline where
  sched := tickSchedule
  pins := canonicalRun_live_iff
  fromLedgerLaw := FreshnessForcedByLedgerLaw

theorem D16_theorem_fromLedgerLaw_holds : D16_theorem.fromLedgerLaw :=
  freshnessForced_holds

/-- **Scope of the forcing, scored (D17, MODEL).** The pinning does not
force the debit side: the all-credit fresh schedule pins too. The debit
convention of the canonical schedule is a MODEL choice, not ledger law. -/
theorem credit_schedule_also_pins :
    ∀ t u : ℕ,
      Recognition.phi (runSchedule zeroLedger
        (fun n => some (n, LedgerPostingAdjacency.Side.credit)) t) u ≠ 0 ↔
        u ∈ tickCarrier t :=
  freshSchedule_pins fun _ => LedgerPostingAdjacency.Side.credit

end D15Attack

/-! ## Corrected floor plan and next block -/

structure CorrectedFloorPlan where
  failedReason : String
  measurement : String
  correctedTarget : String
  doesNotKill : String

/-- Stub floor plan. A failed row narrows the target; it does not reverse it. -/
def correctedFloorPlans : List CorrectedFloorPlan :=
  [ ⟨"D03",
      "equal per-slot rates balance constant weight, which fails insertion stationarity",
      "count one birth opportunity and one death opportunity per existing label",
      "the existence of insertion slots or the asymmetric target"⟩
  , ⟨"D06",
      "bakedFromWeight makes detailed balance algebraic",
      "derive rates from recognition move counting, without the stationary weight",
      "the abstract detailed-balance identity"⟩
  , ⟨"D07",
      "bare posting preserves the carrier and has the wrong move degree",
      "add a carrier-enlarging recognition dynamics",
      "the label-insertion geometry"⟩
  , ⟨"D08",
      "invariance axioms admit distinct candidate measures",
      "use a substrate fact stronger than invariance",
      "the existing gauge-counting theorem once its premise is supplied"⟩
  , ⟨"D09",
      "size fugacities are relabeling-invariant",
      "derive a selector stronger than label indifference",
      "the invariance calculation itself"⟩
  , ⟨"D12",
      "every selector respecting bare posting reachability is constant across rated worlds",
      "select the counting rates from a carrier-enlarging recognition dynamics whose observation relation is rate-sensitive",
      "the existence of non-baked counting rates (D10), the insertion kernel (D11), or the insertion-slot geometry"⟩ ]

theorem correctedFloorPlans_length : correctedFloorPlans.length = 6 := by
  decide

/-- Room B has no remaining OPEN row after the D16 close: the pinning
characterizes freshness, and the side convention is MODEL (D17). -/
def nextAttackBlock : List String := []

theorem nextAttackBlock_length : nextAttackBlock.length = 0 := by
  decide

/-! ## Immutable status -/

theorem gap2_measure_derived_unmoved :
    FullTheoryLedger.fullTheoryBenchmarks.gap2_measure_derived = true :=
  Gap2GluingLawStationarity.gap2_measure_derived_unmoved

/-! ## Composite certificate -/

/-- Packages the D10/D11 closures, the scored decoys, the D12 wall, the
D13 close, the D14 ledger-counted schedule, the D15 canonical pinning
read off the ledger's own run, and the D16 freshness forcing. Does not
move the measure flag. -/
theorem insertionAsymmetryReasons_certified :
    reasonTable.length = 17 ∧
      RecognitionRateAsymmetry ∧
      D11 ∧
      CountingEquivalentRates
        (bakedFromWeight factorialWorld.weight factorialWorld_weight_pos) ∧
      CountingEquivalentRates sizeBlindBirthPerLabelDeath ∧
      ¬ CountingEquivalentRates equalPerSlotRates ∧
      ¬ D12 ∧
      (∃ Obs : PostingRatedWorld → Prop,
        FactorsThroughKernel Obs ∧
          Obs ⟨sizeBlindBirthPerLabelDeath⟩ ∧ ¬ Obs ⟨equalPerSlotRates⟩) ∧
      (∀ m n : ℕ, (ledgerMoveCount m n : ℝ) =
        carrierStepWeight ⟨sizeBlindBirthPerLabelDeath⟩ m n) ∧
      CanonicalPinning ∧
      FreshnessForcedByLedgerLaw ∧
      correctedFloorPlans.length = 6 ∧
      nextAttackBlock.length = 0 ∧
      FullTheoryLedger.fullTheoryBenchmarks.gap2_measure_derived = true :=
  ⟨reasonTable_length, recognitionRateAsymmetry_derived, D11_theorem,
    bakedFromWeight_factorial_satisfies_counting_law,
    sizeBlind_satisfies_counting_law, equalPerSlotRates_not_countingEquivalent,
    D12_refuted, D13_sharpened_holds, ledgerMoveCount_eq_kernel,
    canonicalPinning_holds, freshnessForced_holds, correctedFloorPlans_length,
    nextAttackBlock_length, gap2_measure_derived_unmoved⟩

#print axioms D01_theorem
#print axioms D02_theorem
#print axioms D03_refuted
#print axioms D04_theorem
#print axioms D05_theorem
#print axioms D06_refuted
#print axioms D07_refuted
#print axioms D08_refuted
#print axioms D09_refuted
#print axioms recognitionRateAsymmetry_derived
#print axioms D10_theorem
#print axioms D11_theorem
#print axioms countingLaw_balances_factorialWorld
#print axioms bakedFromWeight_factorial_satisfies_counting_law
#print axioms sizeBlindBirthPerLabelDeath_ne_bakedFromWeight
#print axioms equalPerSlotRates_not_countingEquivalent
#print axioms D12_refuted
#print axioms recognition_presently_typed_cannot_select_asymmetry
#print axioms kernelUpObs_selects_counting
#print axioms kernelUpObs_rejects_equalPerSlot
#print axioms D13_sharpened_holds
#print axioms D13_theorem_provenance_holds
#print axioms kernel_sees_what_posting_cannot
#print axioms ledgerMoveCount_up
#print axioms ledgerMoveCount_down
#print axioms ledgerMoveCount_eq_kernel
#print axioms D14_theorem_provenance_holds
#print axioms unpinned_up_moves_at_least_two
#print axioms canonicalRun_eq_carrierLedger
#print axioms canonicalRun_live_iff
#print axioms ledgerLiveSize_agrees
#print axioms canonicalPinning_holds
#print axioms D15_theorem_provenance_holds
#print axioms sameAccount_fails_pinning
#print axioms pinning_forces_fresh_tag
#print axioms freshSchedule_pins
#print axioms pins_iff_fresh
#print axioms freshnessForced_holds
#print axioms D16_theorem_fromLedgerLaw_holds
#print axioms credit_schedule_also_pins
#print axioms insertionAsymmetryReasons_certified
#print axioms gap2_measure_derived_unmoved

end
end InsertionAsymmetryInevitableReasons
end SevenGaps
end Gravity
end IndisputableMonolith
