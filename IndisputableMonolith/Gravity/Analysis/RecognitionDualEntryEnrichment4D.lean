import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Gravity.SevenGaps.RecognitionRatioSubstrateBlocker
import IndisputableMonolith.Gravity.SevenGaps.LedgerEnergyBridge

/-!
# Wave B residual R3: dual-entry signed-source enrichment (no xRatio)

QG full-completion session, Wave B attack on
`TypedResidual_signed_source_enrichment_schema` from
`plans/QG_WaveB_Gap1_Residual_DAG_Draft_20260721.txt`.

## Core idea

The bare cost ledger `RecognitionLedger` is a derived shadow of the
foundational `Recognition.Ledger`, which carries two signed columns
`debit, credit : M.U → ℤ` with `phi = debit - credit`. The J-cost quotient
is even and forgets exactly `sign(phi)`. The R3 enrichment is therefore the
dual-entry column orientation: `DualEntryStrainState` with integer debit /
credit columns, nonnegative magnitude, and a unit-flux cap.

## Convention (Z/2 pin)

`deficit iff debit-leads` is one global ℤ/2 convention: the ledger mirror of
the Regge sign convention in `meshGeometricDeficit_regge_convention`.
Flipping the global convention swaps columns and negates `phi` / `strain`
while leaving the bare J-ledger unchanged (`toBare_swap`).

## Honesty / scope

* Does **not** flip `gap1_bridge_derived`.
* Does **not** bind the ledger-named `recognition_ratio_derived` Prop
  (that is R5 composition of the conditional theorem with a named binding).
* Carrier for later mesh assembly remains the reshaped `H = ℝ` from R1/R2,
  not an encoded Freudenthal triangulation.
* R0a/R0b (validation name-binding) remain open.
* Posting-run realization (F3 / `LedgerPostingAdjacency`) is omitted as
  garnish; load-bearing content is F2 + separation (a)(b)(c).
* Anchor hardening: `DualEntryStrainState.ofLedger` builds the enrichment
  from an actual foundational `Recognition.Ledger` on a discrete carrier
  structure (`discreteCarrier`), with `phi_ofLedger` and
  `enrichedWitness_eq_ofLedger` as theorems (not docstring citations).

Vacuity guards: the only real-valued field is `mag` with `mag_nonneg`
(no signed real field); `flux_unit` caps orientation at one quantum; no
definition field mentions `xRatio`, `Real.log`, or `ratio_relation`
(`Real.log_exp` appears only in the toBare bridge lemma).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace RecognitionDualEntryEnrichment4D

open SevenGaps
open RecognitionLedger
open Recognition

noncomputable section

/-! ## §1. Dual-entry strain enrichment -/

/-- **MODEL (R3 enrichment).** Dual-entry column orientation: integer debit
and credit columns, nonnegative magnitude, unit flux. Strain is the signed
product `(debit - credit) * mag`. No field mentions `xRatio` or `Real.log`. -/
structure DualEntryStrainState (Λ : Type*) where
  debit : Λ → ℤ
  credit : Λ → ℤ
  mag : Λ → ℝ
  mag_nonneg : ∀ i, 0 ≤ mag i
  flux_unit : ∀ i, |debit i - credit i| ≤ 1

variable {Λ : Type*}

/-- Column imbalance (foundational `Recognition.phi` shape). -/
def DualEntryStrainState.phi (S : DualEntryStrainState Λ) : Λ → ℤ :=
  fun i => S.debit i - S.credit i

/-- Signed strain: integer orientation times nonnegative magnitude. -/
def DualEntryStrainState.strain (S : DualEntryStrainState Λ) : Λ → ℝ :=
  fun i => (S.phi i : ℝ) * S.mag i

/-- Extracted signed source field (enrichment → carrier → ℝ). -/
def DualEntryStrainState.extract (S : DualEntryStrainState Λ) : Λ → ℝ :=
  S.strain

/-- Bare J-cost ledger shadow (forgets sign via J-evenness). -/
noncomputable def DualEntryStrainState.toBare [Fintype Λ] [DecidableEq Λ]
    (S : DualEntryStrainState Λ) : RecognitionLedger Λ :=
  coboundaryStrainLedger S.strain

/-- Swap debit and credit columns (ℤ/2 orientation reverse). -/
def DualEntryStrainState.swap (S : DualEntryStrainState Λ) :
    DualEntryStrainState Λ where
  debit := S.credit
  credit := S.debit
  mag := S.mag
  mag_nonneg := S.mag_nonneg
  flux_unit := by
    intro i
    have h := S.flux_unit i
    -- |credit - debit| = |debit - credit|
    simpa [abs_sub_comm] using h

/-! ## §1b. Type-level anchor to foundational `Recognition.Ledger` -/

/-- Discrete recognition structure on a finite carrier: units are `Λ`,
relation is total (carrier-only; no posting graph is used by the bridge).
`abbrev` so `(discreteCarrier Λ).U` reduces to `Λ` (RecognitionStructure
fixes universe `Type`, not `Type*`). -/
abbrev discreteCarrier (Λ : Type) : RecognitionStructure where
  U := Λ
  R := fun _ _ => True

/-- **Type-level anchor.** Restrict a foundational `Recognition.Ledger` on
`discreteCarrier Λ` to a `DualEntryStrainState` by supplying a nonnegative
magnitude and a unit-flux hypothesis on `Recognition.phi`. -/
def DualEntryStrainState.ofLedger {Λ : Type}
    (L : Ledger (discreteCarrier Λ)) (mag : Λ → ℝ)
    (hmag : ∀ i, 0 ≤ mag i)
    (hflux : ∀ i, |Recognition.phi L i| ≤ 1) : DualEntryStrainState Λ where
  debit := L.debit
  credit := L.credit
  mag := mag
  mag_nonneg := hmag
  flux_unit := by
    intro i
    simpa [Recognition.phi] using hflux i

/-- **THEOREM.** Column imbalance of `ofLedger` is the foundational
`Recognition.phi` on the discrete carrier. -/
theorem DualEntryStrainState.phi_ofLedger {Λ : Type}
    (L : Ledger (discreteCarrier Λ)) (mag : Λ → ℝ)
    (hmag : ∀ i, 0 ≤ mag i)
    (hflux : ∀ i, |Recognition.phi L i| ≤ 1) :
    (DualEntryStrainState.ofLedger L mag hmag hflux).phi =
      Recognition.phi L := by
  funext i
  simp only [DualEntryStrainState.phi, DualEntryStrainState.ofLedger,
    Recognition.phi]

/-! ## §2. F2: swap negates signed data, preserves bare ledger -/

theorem DualEntryStrainState.phi_swap (S : DualEntryStrainState Λ) :
    (S.swap).phi = fun i => -S.phi i := by
  funext i
  simp only [DualEntryStrainState.phi, DualEntryStrainState.swap]
  omega

theorem DualEntryStrainState.strain_swap (S : DualEntryStrainState Λ) :
    (S.swap).strain = fun i => -S.strain i := by
  funext i
  have hφ : (S.swap).phi i = -S.phi i := congrFun S.phi_swap i
  have hmag : (S.swap).mag i = S.mag i := rfl
  simp only [DualEntryStrainState.strain, hφ, hmag, Int.cast_neg, neg_mul]

/-- Two recognition ledgers with the same cost function are equal
(remaining fields are proofs). Local re-proof of the blocker's private
`recognitionLedger_cost_ext`. -/
theorem recognitionLedger_cost_ext {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ']
    {L L' : RecognitionLedger Λ'} (h : L.cost = L'.cost) : L = L' := by
  cases L
  cases L'
  subst h
  rfl

/-- **THEOREM (F2).** Column swap preserves the bare J-ledger
(mirrors `signBlindBareLedger_neg_eq` via J-cost evenness). -/
theorem DualEntryStrainState.toBare_swap [Fintype Λ] [DecidableEq Λ]
    (S : DualEntryStrainState Λ) :
    (S.swap).toBare = S.toBare := by
  apply recognitionLedger_cost_ext
  funext i j
  -- cost i j = Jcost (exp (strain i - strain j))
  change Cost.Jcost (Real.exp ((S.swap).strain i - (S.swap).strain j))
      = Cost.Jcost (Real.exp (S.strain i - S.strain j))
  have hswap : (S.swap).strain = fun k => -S.strain k := S.strain_swap
  rw [show (S.swap).strain i = -S.strain i from congrFun hswap i,
    show (S.swap).strain j = -S.strain j from congrFun hswap j]
  have hinv :
      Real.exp (-S.strain i - (-S.strain j))
        = (Real.exp (S.strain i - S.strain j))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hinv]
  exact (Cost.Jcost_symm (Real.exp_pos _)).symm

/-! ## §3. Enriched witness family (Fin 2) -/

/-- Dual-entry witness realizing signed source `d` on two cells.
Debit-leads iff `0 ≤ d` (global ℤ/2 convention). Magnitude `|d|`. -/
noncomputable def enrichedWitness (d : ℝ) : DualEntryStrainState (Fin 2) where
  debit := fun σ =>
    if 0 ≤ d then (if σ = 0 then 1 else 0) else (if σ = 0 then 0 else 1)
  credit := fun σ =>
    if 0 ≤ d then (if σ = 0 then 0 else 1) else (if σ = 0 then 1 else 0)
  mag := fun _ => |d|
  mag_nonneg := fun _ => abs_nonneg d
  flux_unit := by
    intro σ
    by_cases hd : 0 ≤ d
    · simp [hd]
      by_cases hσ : σ = 0
      · simp [hσ]
      · simp [hσ]
    · simp [hd]
      by_cases hσ : σ = 0
      · simp [hσ]
      · simp [hσ]

theorem enrichedWitness_strain (d : ℝ) :
    (enrichedWitness d).strain = fun σ => if σ = 0 then d else -d := by
  funext σ
  simp only [DualEntryStrainState.strain, DualEntryStrainState.phi,
    enrichedWitness]
  by_cases hd : 0 ≤ d
  · simp only [hd, ↓reduceIte]
    by_cases hσ : σ = 0
    · simp [hσ, abs_of_nonneg hd]
    · simp [hσ, abs_of_nonneg hd]
  · have hd' : d < 0 := lt_of_not_ge hd
    simp only [hd, ↓reduceIte]
    by_cases hσ : σ = 0
    · simp [hσ, abs_of_neg hd']
    · simp [hσ, abs_of_neg hd']

theorem enrichedWitness_extract_zero (d : ℝ) :
    (enrichedWitness d).extract 0 = d := by
  simp [DualEntryStrainState.extract, enrichedWitness_strain d]

/-- Foundational ledger whose columns realize `enrichedWitness d`. -/
def enrichedWitnessLedger (d : ℝ) : Ledger (discreteCarrier (Fin 2)) where
  debit := fun σ =>
    if 0 ≤ d then (if σ = 0 then 1 else 0) else (if σ = 0 then 0 else 1)
  credit := fun σ =>
    if 0 ≤ d then (if σ = 0 then 0 else 1) else (if σ = 0 then 1 else 0)

theorem enrichedWitnessLedger_phi_abs_le_one (d : ℝ) (σ : Fin 2) :
    |Recognition.phi (enrichedWitnessLedger d) σ| ≤ 1 := by
  simp only [Recognition.phi, enrichedWitnessLedger]
  by_cases hd : 0 ≤ d
  · simp [hd]
    by_cases hσ : σ = 0
    · simp [hσ]
    · simp [hσ]
  · simp [hd]
    by_cases hσ : σ = 0
    · simp [hσ]
    · simp [hσ]

/-- **THEOREM.** The enriched witness is the foundational ledger restricted
to the carrier with magnitude `|d|` (type-level factoring through
`ofLedger`). -/
theorem enrichedWitness_eq_ofLedger (d : ℝ) :
    enrichedWitness d =
      DualEntryStrainState.ofLedger (enrichedWitnessLedger d)
        (fun _ => |d|) (fun _ => abs_nonneg d)
        (enrichedWitnessLedger_phi_abs_le_one d) :=
  rfl

/-- Bridge: enrichment bare shadow equals the blocker's sign-blind ledger. -/
theorem enrichedWitness_toBare (d : ℝ) :
    (enrichedWitness d).toBare = signBlindBareLedger d := by
  -- signBlindBareLedger d = coboundaryStrainLedger (log ∘ xRatio)
  -- and log (exp (if σ=0 then d else -d)) = if σ=0 then d else -d
  apply recognitionLedger_cost_ext
  funext i j
  change Cost.Jcost (Real.exp ((enrichedWitness d).strain i
      - (enrichedWitness d).strain j))
      = (signBlindBareLedger d).cost i j
  have hcost := ratioBridgeLedger_cost (twoHingeWitnessBridge d) i j
  -- Unfold signBlindBareLedger through ratioBridgeLedger
  have hsb :
      (signBlindBareLedger d).cost i j
        = Cost.Jcost ((twoHingeWitnessBridge d).xRatio i
            / (twoHingeWitnessBridge d).xRatio j) := hcost
  rw [hsb]
  -- strain = log ∘ xRatio of the witness
  have hlog :
      (fun σ : Fin 2 => Real.log ((twoHingeWitnessBridge d).xRatio σ))
        = (enrichedWitness d).strain := by
    funext σ
    simp only [twoHingeWitnessBridge, enrichedWitness_strain d]
    rw [Real.log_exp]
  -- coboundary cost from strain equals J(exp(Δ strain))
  -- and exp(log xRatio i - log xRatio j) = xRatio i / xRatio j
  have hstrain_i :
      (enrichedWitness d).strain i
        = Real.log ((twoHingeWitnessBridge d).xRatio i) := by
    rw [← hlog]
  have hstrain_j :
      (enrichedWitness d).strain j
        = Real.log ((twoHingeWitnessBridge d).xRatio j) := by
    rw [← hlog]
  rw [hstrain_i, hstrain_j, Real.exp_sub,
    Real.exp_log ((twoHingeWitnessBridge d).xRatio_pos i),
    Real.exp_log ((twoHingeWitnessBridge d).xRatio_pos j)]

/-! ## §4. Separation: enrichment strictly richer than bare ledger -/

/-- **(a)** The bare shadow is not injective on the enriched witness family. -/
theorem toBare_not_injective :
    (enrichedWitness (1 : ℝ)).toBare = (enrichedWitness (-1 : ℝ)).toBare ∧
      (enrichedWitness (1 : ℝ)).extract 0 ≠
        (enrichedWitness (-1 : ℝ)).extract 0 := by
  constructor
  · rw [enrichedWitness_toBare, enrichedWitness_toBare,
      signBlindBareLedger_neg_eq]
  · rw [enrichedWitness_extract_zero, enrichedWitness_extract_zero]
    norm_num

/-- **(b) / Decoy 1.** Any α-valued observable that factors through `toBare`
is swap-even (invariant under column exchange). -/
theorem bare_factorable_is_swap_even {α : Type*}
    (f : DualEntryStrainState (Fin 2) → α)
    (select : RecognitionLedger (Fin 2) → α)
    (hf : ∀ E, f E = select E.toBare) (E : DualEntryStrainState (Fin 2)) :
    f E.swap = f E := by
  rw [hf, hf, DualEntryStrainState.toBare_swap]

/-- Proposed recovery of the signed extract (hinge 0) from a bare ledger. -/
def RecoversExtractFromBare
    (select : RecognitionLedger (Fin 2) → ℝ) : Prop :=
  ∀ d : ℝ, select (enrichedWitness d).toBare = (enrichedWitness d).extract 0

/-- **(c) THEOREM.** No bare-ledger selector recovers the enriched extract.
Direct reduction to `no_bare_ledger_selector_recovers_signed_source`. -/
theorem extract_not_bare_factorable :
    ¬ ∃ select : RecognitionLedger (Fin 2) → ℝ,
      RecoversExtractFromBare select := by
  rintro ⟨select, hselect⟩
  exact no_bare_ledger_selector_recovers_signed_source ⟨select, by
    intro d
    have h := hselect d
    rw [enrichedWitness_toBare d, enrichedWitness_extract_zero d] at h
    exact h⟩

/-! ## §5. Typed residual R3 -/

/-- **R3.** Signed-source enrichment strictly richer than bare
`RecognitionLedger`: dual-entry state with extract recovering the signed
witness source, bare shadow equal to `signBlindBareLedger`, and no bare
selector recovering extract. -/
def TypedResidual_signed_source_enrichment_schema : Prop :=
  (∀ d : ℝ, (enrichedWitness d).extract 0 = d) ∧
    (∀ d : ℝ, (enrichedWitness d).toBare = signBlindBareLedger d) ∧
      (∀ S : DualEntryStrainState (Fin 2), (S.swap).toBare = S.toBare) ∧
        ¬ ∃ select : RecognitionLedger (Fin 2) → ℝ,
          RecoversExtractFromBare select

/-- **THEOREM:** R3 closed. -/
theorem typedResidual_signed_source_enrichment_schema_closed :
    TypedResidual_signed_source_enrichment_schema :=
  ⟨enrichedWitness_extract_zero, enrichedWitness_toBare,
    DualEntryStrainState.toBare_swap, extract_not_bare_factorable⟩

theorem TypedResidual_signed_source_enrichment_schema_closed :
    TypedResidual_signed_source_enrichment_schema :=
  typedResidual_signed_source_enrichment_schema_closed

/-! ## §6. Status (no ledger flag touch) -/

structure RecognitionDualEntryEnrichment4DStatus where
  r3Closed : Bool
  postingRunRealizationDropped : Bool
  gap1BridgeDerived : Bool

def recognitionDualEntryEnrichment4DStatus :
    RecognitionDualEntryEnrichment4DStatus where
  r3Closed := true
  postingRunRealizationDropped := true
  gap1BridgeDerived := false

theorem recognitionDualEntryEnrichment4DStatus_flags :
    recognitionDualEntryEnrichment4DStatus.r3Closed = true ∧
      recognitionDualEntryEnrichment4DStatus.postingRunRealizationDropped =
        true ∧
        recognitionDualEntryEnrichment4DStatus.gap1BridgeDerived = false := by
  decide

end

end RecognitionDualEntryEnrichment4D
end Analysis
end Gravity
end IndisputableMonolith
