import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingLawStationarity

/-!
# Gap-2 label-insertion dynamics (necessary-reasons census)

Assume the corrected Gap-2 target is required: an explicit carrier-enlarging
label-insertion / removal dynamics forces `InsertionStationarity`
(equivalently `GluingLaw`), hence inverse factorials and
`GaugeCountingPrinciple`, without assuming `mu`, `Aut`, unit fugacity, or
`InsertionStationarity` under a new name.

Then every fact that would make that forcing unavoidable is listed below.
Each reason is proved, left OPEN, recorded as MODEL, or refuted. A failed
reason does not automatically mean its opposite.

Method: `plans/Necessary_Reasons_Process_20260807.html`.
Parent modules: `Gap2GluingLawStationarity.lean`, `UnitFugacitySelector.lean`.
Binding prompt:
`plans/QG_Gap2_GluingLaw_Insertion_Stationarity_Session_Prompt_20260807.txt`.

Honesty:

* THEOREM: birth-death detailed balance equates the weight ratio to the rate
  ratio; equal per-slot insert and delete rates force a constant weight and
  therefore fail InsertionStationarity; size-blind birth with per-label death
  (counting-derived rates) forces InsertionStationarity once unit/atom are
  fixed; the geometry half is already inhabited; decoy rate laws that bake in
  the answer fail the derivation gate.
* REFUTED as a selector: equirating the `n+1` insertion slots with the `n+1`
  deletion choices at equal unit rate per choice; bare fixed-carrier posting
  (parent); renaming InsertionStationarity as a “rate.”
* OPEN: derive, from recognition structure, that birth is size-blind (one
  creation opportunity per tick) while death is per existing label — or an
  equivalent asymmetric counting that yields `μ_{n+1} = (n+1) λ_n` without
  writing the stationary law into the rates by hand.
* Cambrian Target Research can grind lemmas once this dynamics is typed; it
  cannot invent the missing physical rate asymmetry. No Target Research job
  is required to bank the census below.
* `gap2_measure_derived` is not moved.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LabelInsertionDynamics

open Gap2GluingLawStationarity Gap2GaugeVolume
open MeasureSubstrateBlocker FullTheoryLedger

noncomputable section

/-! ## Reason census

D01 detailed balance equates weight ratio to rate ratio
D02 equal per-slot insert/delete rates force constant weight
D03 equal per-slot rates fail InsertionStationarity (decoy)
D04 size-blind birth + per-label death forces InsertionStationarity
D05 geometry of n+1 slots is inhabited (parent)
D06 baking 1/(n+1) or factorials into a “rate” is not a derivation
D07 recognition forces size-blind birth / per-label death asymmetry
D08 LabelInsertionKernel inhabited from recognition dynamics
D09 GaugeCountingPrinciple derived (flag may move only then)
-/

structure ReasonStatus where
  id : String
  title : String
  /-- `"THEOREM"`, `"OPEN"`, `"MODEL"`, or `"REFUTED"`. -/
  status : String

def reasonTable : List ReasonStatus :=
  [ ⟨"D01", "detailed balance equates weight ratio to rate ratio", "THEOREM"⟩
  , ⟨"D02", "equal per-slot insert/delete rates force constant weight", "THEOREM"⟩
  , ⟨"D03", "equal per-slot rates fail InsertionStationarity", "REFUTED"⟩
  , ⟨"D04", "size-blind birth + per-label death forces InsertionStationarity", "THEOREM"⟩
  , ⟨"D05", "n+1 slot geometry inhabited", "THEOREM"⟩
  , ⟨"D06", "baking 1/(n+1) into a rate is not a derivation", "REFUTED"⟩
  , ⟨"D07", "recognition forces birth/death rate asymmetry", "OPEN"⟩
  , ⟨"D08", "LabelInsertionKernel from recognition dynamics", "OPEN"⟩
  , ⟨"D09", "GaugeCountingPrinciple derived from insertion dynamics", "OPEN"⟩ ]

theorem reasonTable_length : reasonTable.length = 9 := by
  decide

/-! ## Birth-death rates on carrier size -/

/-- Size-indexed birth and death rates for a one-kind label carrier.
`birth n` is the total forward rate `n → n+1`.
`death n` is the total backward rate `n → n-1` (used at `n = m+1`). -/
structure BirthDeathRates where
  birth : ℕ → ℝ
  death : ℕ → ℝ
  birth_pos : ∀ n, 0 < birth n
  death_pos : ∀ n, 0 < death (n + 1)

/-- Detailed balance for a size weight under birth-death rates. -/
def DetailedBalance (f : ℕ → ℝ) (R : BirthDeathRates) : Prop :=
  ∀ n : ℕ, f (n + 1) * R.death (n + 1) = f n * R.birth n

/-- **D01.** Under detailed balance and positivity, the weight ratio equals the
rate ratio. -/
theorem D01_balance_ratio (f : ℕ → ℝ) (R : BirthDeathRates)
    (h : DetailedBalance f R) (n : ℕ) :
    f (n + 1) * R.death (n + 1) = f n * R.birth n :=
  h n

/-- **D01 companion.** Solving for the recurrence form used by insertion
stationarity: if death is `(n+1)` times birth, balance is exactly
`f(n+1)·(n+1) = f n` after cancelling a common positive birth rate. -/
theorem D01_balance_of_scaled_death (f : ℕ → ℝ) (R : BirthDeathRates)
    (h : DetailedBalance f R)
    (hμ : ∀ n, R.death (n + 1) = (n + 1 : ℝ) * R.birth n) (n : ℕ) :
    f (n + 1) * (n + 1 : ℝ) = f n := by
  have hb := R.birth_pos n
  have hbal := h n
  have hμn := hμ n
  -- f(n+1) * ((n+1)*birth n) = f n * birth n
  have : f (n + 1) * ((n + 1 : ℝ) * R.birth n) = f n * R.birth n := by
    simpa [hμn] using hbal
  have hne : (R.birth n : ℝ) ≠ 0 := ne_of_gt hb
  -- cancel birth n
  have h' : f (n + 1) * (n + 1 : ℝ) * R.birth n = f n * R.birth n := by
    simpa [mul_assoc] using this
  exact mul_right_cancel₀ hne h'

/-! ## Equal per-slot rates (symmetric counting) -/

/-- The smallest symmetric dynamics: each of the `n+1` insertion slots fires at
unit rate, and each of the `n+1` labels may be deleted at unit rate. Total
birth and death are both `n+1`. -/
def equalPerSlotRates : BirthDeathRates where
  birth := fun n => (n + 1 : ℝ)
  death := fun n => (n : ℝ)
  birth_pos := fun n => by exact_mod_cast Nat.succ_pos n
  death_pos := fun n => by
    have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    simpa using this

/-- Constant unit weight. -/
def constantWeight : ℕ → ℝ := fun _ => 1

theorem constantWeight_detailedBalance_equalPerSlot :
    DetailedBalance constantWeight equalPerSlotRates := by
  intro n
  simp [constantWeight, equalPerSlotRates]

/-- **D02.** Equal per-slot rates put constant weight in detailed balance. -/
theorem D02_equal_per_slot_balances_constant :
    DetailedBalance constantWeight equalPerSlotRates :=
  constantWeight_detailedBalance_equalPerSlot

/-- **D03 REFUTED as a selector of InsertionStationarity.** The symmetric
slot/label counting dynamics balances the constant weight, which fails
insertion stationarity at `n = 1`. So “count insertion slots and deletion
choices the same way” does not force the gluing law. -/
theorem D03_equal_per_slot_fails_insertionStationarity :
    DetailedBalance constantWeight equalPerSlotRates ∧
      ¬ InsertionStationarity constantWeight := by
  refine ⟨D02_equal_per_slot_balances_constant, ?_⟩
  intro h
  have hs := h.insert 1
  norm_num [constantWeight] at hs

/-! ## Asymmetric counting: size-blind birth, per-label death -/

/-- Birth is size-blind (total forward rate `1`). Death is per existing label
(total backward rate `n` at size `n`). Both factors come from move counting:
one creation opportunity, `n` removable labels. The factor `n+1` never appears
as a hand-written stationary coefficient. -/
def sizeBlindBirthPerLabelDeath : BirthDeathRates where
  birth := fun _ => (1 : ℝ)
  death := fun n => (n : ℝ)
  birth_pos := fun _ => by norm_num
  death_pos := fun n => by exact_mod_cast Nat.succ_pos n

/-- **D04.** Under size-blind birth and per-label death, detailed balance plus
unit/atom is exactly `InsertionStationarity`. -/
theorem D04_asymmetric_rates_force_insertionStationarity (f : ℕ → ℝ)
    (hbal : DetailedBalance f sizeBlindBirthPerLabelDeath)
    (h0 : f 0 = 1) (h1 : f 1 = 1) :
    InsertionStationarity f where
  unit := h0
  atom := h1
  insert := by
    intro n
    -- death (n+1) = n+1, birth n = 1
    have hμ : ∀ k, sizeBlindBirthPerLabelDeath.death (k + 1)
        = (k + 1 : ℝ) * sizeBlindBirthPerLabelDeath.birth k := by
      intro k
      simp [sizeBlindBirthPerLabelDeath]
    simpa using D01_balance_of_scaled_death f sizeBlindBirthPerLabelDeath hbal hμ n

/-- Inverse-factorial weight satisfies the asymmetric-rate detailed balance. -/
theorem D04_factorial_is_stationary :
    DetailedBalance factorialWorld.weight sizeBlindBirthPerLabelDeath ∧
      InsertionStationarity factorialWorld.weight := by
  refine ⟨?_, factorialWorld_stationary⟩
  intro n
  -- (1/(n+1)!) * (n+1) = 1/n!
  simp only [factorialWorld, sizeBlindBirthPerLabelDeath, mul_one]
  have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [Nat.factorial_succ, hcast]
  push_cast
  field_simp

/-! ## Decoy: baking the answer into the rates -/

/-- A “rate” manufactured from a desired weight so that detailed balance holds
by algebra. This is the prompt’s decoy: it contains the stationary law, not a
physical counting. -/
def bakedFromWeight (f : ℕ → ℝ) (hf : ∀ n, 0 < f n) : BirthDeathRates where
  birth := fun _ => (1 : ℝ)
  death := fun n =>
    match n with
    | 0 => 1
    | n + 1 => f n / f (n + 1)
  birth_pos := fun _ => by norm_num
  death_pos := fun n => by
    have hnum := hf n
    have hden := hf (n + 1)
    exact div_pos hnum hden

theorem bakedFromWeight_balances (f : ℕ → ℝ) (hf : ∀ n, 0 < f n) :
    DetailedBalance f (bakedFromWeight f hf) := by
  intro n
  have hden := ne_of_gt (hf (n + 1))
  simp only [bakedFromWeight]
  field_simp [hden]

/-- **D06 REFUTED as a derivation.** For the constant decoy weight, the baked
rates balance it, yet InsertionStationarity fails. More generally, baking
`f n / f(n+1)` into death is renaming the stationary law as a rate. -/
theorem D06_baked_rates_are_not_a_derivation :
    (∀ f hf, DetailedBalance f (bakedFromWeight f hf)) ∧
      ¬ InsertionStationarity constantWeight := by
  refine ⟨fun f hf => bakedFromWeight_balances f hf, ?_⟩
  intro h
  have hs := h.insert 1
  norm_num [constantWeight] at hs

/-! ## Geometry re-stand and residual -/

/-- **D05.** Parent theorem: slot geometry is inhabited. -/
theorem D05_geometry_inhabited : Nonempty LabelInsertionGeometry :=
  succAboveGeometry_inhabited

structure CorrectedFloorPlan where
  failedReason : String
  measurement : String
  correctedTarget : String
  doesNotKill : String

def correctedFloorPlans : List CorrectedFloorPlan :=
  [ ⟨"D03",
      "equalPerSlotRates balances constantWeight; constantWeight fails InsertionStationarity.insert at n=1",
      "force an asymmetric counting: size-blind birth vs per-label death (or equivalent μ=(n+1)λ from move counts, not from the stationary formula)",
      "that n+1 insertion slots exist, or that deletion choices can be counted"⟩
  , ⟨"D06",
      "bakedFromWeight sets death(n+1)=f n/f(n+1) so balance is algebra",
      "rates must come from move counting or recognition schedule, never from the desired weight",
      "the abstract birth-death detailed-balance identity itself"⟩ ]

theorem correctedFloorPlans_length : correctedFloorPlans.length = 2 := by
  decide

/-- Surviving residual after this census: derive the asymmetric rate law
`sizeBlindBirthPerLabelDeath` (or any counting-equivalent) from recognition
structure / the posting schedule nature executes. -/
structure CorrectedInsertionDynamicsResidual where
  /-- Named recognition prior that forces size-blind birth and per-label death. -/
  namedRateAsymmetry : Prop
  /-- That prior is not equal per-slot insert/delete counting. -/
  notEqualPerSlot : Prop
  /-- That prior does not bake the stationary ratio into the rates. -/
  notBakedFromWeight : Prop
  /-- From the prior, InsertionStationarity holds of the physical size weight. -/
  forcesInsertionStationarity : Prop

def assumedTargetStatus : String := "OPEN_RATE_ASYMMETRY"

def firstAttackBlock : List String :=
  ["D07", "D04", "D03", "D06", "D08"]

theorem firstAttackBlock_length : firstAttackBlock.length = 5 := by
  decide

/-- Package: asymmetric counting rates + unit/atom + geometry close the kernel
and therefore GCP. This is a conditional closure, not a derivation of the rates. -/
noncomputable def D04_asymmetric_rates_give_kernel (f : ℕ → ℝ)
    (hbal : DetailedBalance f sizeBlindBirthPerLabelDeath)
    (h0 : f 0 = 1) (h1 : f 1 = 1) :
    LabelInsertionKernel f :=
  LabelInsertionKernel.ofStationarity succAboveGeometry
    (D04_asymmetric_rates_force_insertionStationarity f hbal h0 h1)

theorem D04_asymmetric_rates_give_gcp (B : ℕ) (f : ℕ → ℝ)
    (hbal : DetailedBalance f sizeBlindBirthPerLabelDeath)
    (h0 : f 0 = 1) (h1 : f 1 = 1) :
    GaugeCountingPrinciple
      (classMass (B := B) (fun K => f K.nV * f K.nE * f K.nT)) :=
  labelInsertionKernel_gives_gaugeCounting B
    (D04_asymmetric_rates_give_kernel f hbal h0 h1)

/-- Measure flag remains unmoved until D07/D08 close. -/
theorem gap2_measure_derived_unmoved :
    fullTheoryBenchmarks.gap2_measure_derived = true :=
  Gap2GluingLawStationarity.gap2_measure_derived_unmoved

/-! ## Composite certificate -/

theorem labelInsertionDynamics_certified :
    reasonTable.length = 9 ∧
      DetailedBalance constantWeight equalPerSlotRates ∧
      ¬ InsertionStationarity constantWeight ∧
      (DetailedBalance factorialWorld.weight sizeBlindBirthPerLabelDeath ∧
        InsertionStationarity factorialWorld.weight) ∧
      Nonempty LabelInsertionGeometry ∧
      correctedFloorPlans.length = 2 ∧
      firstAttackBlock.length = 5 ∧
      assumedTargetStatus = "OPEN_RATE_ASYMMETRY" ∧
      fullTheoryBenchmarks.gap2_measure_derived = true := by
  refine ⟨reasonTable_length, D02_equal_per_slot_balances_constant,
    D03_equal_per_slot_fails_insertionStationarity.2, D04_factorial_is_stationary,
    D05_geometry_inhabited, correctedFloorPlans_length, firstAttackBlock_length,
    rfl, gap2_measure_derived_unmoved⟩

#print axioms D01_balance_of_scaled_death
#print axioms D02_equal_per_slot_balances_constant
#print axioms D03_equal_per_slot_fails_insertionStationarity
#print axioms D04_asymmetric_rates_force_insertionStationarity
#print axioms D04_factorial_is_stationary
#print axioms D04_asymmetric_rates_give_gcp
#print axioms D06_baked_rates_are_not_a_derivation
#print axioms labelInsertionDynamics_certified

end

end Gap2LabelInsertionDynamics
end SevenGaps
end Gravity
end IndisputableMonolith
