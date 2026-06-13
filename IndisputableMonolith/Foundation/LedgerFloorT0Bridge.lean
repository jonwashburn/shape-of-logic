import Mathlib
import IndisputableMonolith.Foundation.RecognitionLedgerFloor
import IndisputableMonolith.Foundation.DistinctionToT4
import IndisputableMonolith.Foundation.UnifiedForcingChain

/-!
# The T0 floor IS the Boolean truncation of the extensive recognition ledger

This module closes the Phase 2 gap flagged in the strict T-1-to-T8 audit
(the colleague checklist: *"turns T0 from a chosen Boolean indicator into the
shadow of an extensive cost object"*).

Before this module, two worlds sat side by side with no formal connection:

* `DistinctionToT4` builds the **T0 floor** as the recognition-work cost on the
  observable quotient `ForcedQuotient h` forced by a distinction
  `h : ∃ x y : K, x ≠ y`; that quotient is two-state (`≃ Bool`) and its cost is
  the Boolean indicator `boolRecognitionCost`;
* `RecognitionLedgerFloor` builds the **extensive ledger** `DefectLedger I = I →₀ ℕ`
  with additive cost `ledgerCost w`, but it is never identified with the T0
  floor; the original `FloorBridgeStrict` fields only proved facts about the
  ledger in isolation (a unit-weight multiplicity identity on an unrelated
  carrier, an `ℕ → Bool` OR lemma, and a `rfl` cost-kernel).

Here we exhibit the explicit **truncation map** that makes the T0 floor the
two-state *shadow* of the extensive ledger:

```
ledgerToFloor h Γ := (forcedQuotientBoolEquiv h).symm (ledgerShadow Γ),
ledgerShadow Γ    := if Γ = 0 then false else true.
```

The bundled theorem `LedgerFloorT0Bridge` proves this map is:

* a **monoid homomorphism** onto the T0 join: `ledgerToFloor 0 = emp` and
  `ledgerToFloor (Γ + Δ) = join (ledgerToFloor Γ) (ledgerToFloor Δ)` (the
  additive ledger projects onto the Boolean OR of the floor);
* a **cost truncation**: the T0 recognition cost of the shadow is the clamp of
  the extensive ledger cost to `{0,1}` (`cost_is_truncated_ledger`); on a single
  primitive distinction this is literally `boolRecognitionCost ∘ booleanTruncation`
  of the natural-number multiplicity (`rank1_cost_is_boolean_truncation`);
* **surjective**: every floor state is the shadow of some ledger, so the floor
  is a genuine quotient (shadow) of the ledger, nothing is unhit
  (`ledgerToFloor_surjective`);
* a **kernel identification**: two ledgers share a shadow exactly when they
  agree on having zero extensive cost (`kernel_is_cost_kernel`), and the floor's
  consistency predicate is exactly "the ledger is costless"
  (`consistent_iff_costless`).

Together these turn T0 from a chosen Boolean indicator into the forced two-state
truncation of the extensive recognition ledger.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerFloorT0

open CostFromDistinction
open RecognitionLedgerFloor
open DistinctionToT4
open UnifiedForcingChain

universe u v

/-! ## The two-state shadow of a ledger and its lift to the forced quotient -/

open Classical in
/-- The Boolean two-state **shadow** of a ledger: `false` on the empty ledger,
`true` as soon as any recognition has been posted. This is the truncation of the
extensive `ℕ`-valued multiplicity to the two-state floor. -/
noncomputable def ledgerShadow {I : Type v} (Γ : DefectLedger I) : Bool :=
  if Γ = 0 then false else true

/-- The lift of the ledger shadow to the T0 floor forced by a distinction. This
is the truncation map whose target is the distinction-generated observable
quotient, not an unrelated carrier. -/
noncomputable def ledgerToFloor {K : Type*} (h : ∃ x y : K, x ≠ y)
    {I : Type v} (Γ : DefectLedger I) : ForcedQuotient h :=
  (forcedQuotientBoolEquiv h).symm (ledgerShadow Γ)

@[simp] theorem ledgerShadow_zero {I : Type v} :
    ledgerShadow (0 : DefectLedger I) = false := by
  unfold ledgerShadow; exact if_pos rfl

theorem ledgerShadow_eq_false_iff {I : Type v} {Γ : DefectLedger I} :
    ledgerShadow Γ = false ↔ Γ = 0 := by
  unfold ledgerShadow
  by_cases hΓ : Γ = 0 <;> simp [hΓ]

theorem ledgerShadow_eq_true_iff {I : Type v} {Γ : DefectLedger I} :
    ledgerShadow Γ = true ↔ Γ ≠ 0 := by
  unfold ledgerShadow
  by_cases hΓ : Γ = 0 <;> simp [hΓ]

/-- The free ledger is `0` exactly when both summands are `0`: in `I →₀ ℕ` there
are no negative entries to cancel a posting. -/
theorem ledger_add_eq_zero_iff {I : Type v} {Γ Δ : DefectLedger I} :
    Γ + Δ = 0 ↔ Γ = 0 ∧ Δ = 0 := by
  constructor
  · intro hsum
    refine ⟨?_, ?_⟩ <;> ext i
    · have hi : Γ i + Δ i = 0 := by
        have := congrArg (fun f : DefectLedger I => f i) hsum
        simpa [Finsupp.add_apply] using this
      have : Γ i = 0 := by omega
      simpa using this
    · have hi : Γ i + Δ i = 0 := by
        have := congrArg (fun f : DefectLedger I => f i) hsum
        simpa [Finsupp.add_apply] using this
      have : Δ i = 0 := by omega
      simpa using this
  · rintro ⟨h1, h2⟩; rw [h1, h2, add_zero]

/-- The shadow is a homomorphism from ledger addition to Boolean `OR`: posting
recognition in either summand lights the two-state floor. -/
theorem ledgerShadow_add {I : Type v} (Γ Δ : DefectLedger I) :
    ledgerShadow (Γ + Δ) = (ledgerShadow Γ || ledgerShadow Δ) := by
  unfold ledgerShadow
  by_cases hΓ : Γ = 0
  · by_cases hΔ : Δ = 0
    · simp [hΓ, hΔ]
    · simp [hΓ, hΔ]
  · have hsum : Γ + Δ ≠ 0 := fun hc => hΓ (ledger_add_eq_zero_iff.mp hc).1
    simp [hΓ, hsum]

/-- On a single primitive distinction the shadow is exactly the Boolean
truncation of the natural-number multiplicity. -/
theorem ledgerShadow_single {I : Type v} (i₀ : I) (n : ℕ) :
    ledgerShadow (Finsupp.single i₀ n) = booleanTruncation n := by
  by_cases hn : n = 0
  · subst hn
    rw [Finsupp.single_zero, ledgerShadow_zero, booleanTruncation_zero]
  · have hne : Finsupp.single i₀ n ≠ 0 := by
      rw [Ne, Finsupp.single_eq_zero]; exact hn
    rw [ledgerShadow_eq_true_iff.mpr hne, booleanTruncation_pos hn]

/-! ## The identification bundle -/

/-- **The T0 floor is the Boolean truncation of the extensive recognition
ledger.** For any distinction witness `h` and strictly positive per-distinction
weight `w`, the lift `ledgerToFloor h` is a surjective cost-and-join
homomorphism from the extensive ledger onto the distinction-generated T0 floor,
under which the floor cost is the two-state clamp of the extensive ledger cost. -/
structure LedgerFloorT0Bridge {K : Type*} (h : ∃ x y : K, x ≠ y)
    {I : Type v} (w : I → ℝ) : Prop where
  /-- The empty ledger maps to the consistent (empty) floor state. -/
  shadow_emp :
    ledgerToFloor h (0 : DefectLedger I) = (ConfigSpace.emp : ForcedQuotient h)
  /-- Ledger addition projects onto the Boolean `OR` join of the floor. -/
  shadow_join :
    ∀ Γ Δ : DefectLedger I,
      ledgerToFloor h (Γ + Δ) =
        ConfigSpace.join (ledgerToFloor h Γ) (ledgerToFloor h Δ)
  /-- The T0 recognition cost of the shadow is the truncation (clamp to `{0,1}`)
  of the extensive ledger cost. -/
  cost_is_truncated_ledger :
    ∀ Γ : DefectLedger I,
      (forcedQuotientRecognitionCost h).C (ledgerToFloor h Γ) =
        (if ledgerCost w Γ = 0 then (0 : ℝ) else 1)
  /-- The floor's consistency predicate is exactly "the ledger is costless". -/
  consistent_iff_costless :
    ∀ Γ : DefectLedger I,
      ConfigSpace.IsConsistent (ledgerToFloor h Γ) ↔ ledgerCost w Γ = 0
  /-- Two ledgers have the same shadow exactly when they agree on having zero
  extensive cost: the floor's identity is the truncated cost kernel. -/
  kernel_is_cost_kernel :
    ∀ Γ Δ : DefectLedger I,
      ledgerToFloor h Γ = ledgerToFloor h Δ ↔
        (ledgerCost w Γ = 0 ↔ ledgerCost w Δ = 0)

/-- The shadow lift surjects onto the T0 floor: every floor state is the shadow
of some ledger, so the floor is a genuine quotient (shadow) of the ledger. The
single primitive distinction `i₀` witnesses the marked state. -/
theorem ledgerToFloor_surjective {K : Type*} (h : ∃ x y : K, x ≠ y)
    {I : Type v} (i₀ : I) :
    Function.Surjective (ledgerToFloor (I := I) h) := by
  intro q
  by_cases hq : forcedQuotientBoolEquiv h q = false
  · refine ⟨0, ?_⟩
    unfold ledgerToFloor
    rw [ledgerShadow_zero]
    exact (Equiv.symm_apply_eq _).mpr hq.symm
  · have hqt : forcedQuotientBoolEquiv h q = true := by
      cases hb : forcedQuotientBoolEquiv h q
      · exact absurd hb hq
      · rfl
    refine ⟨Finsupp.single i₀ 1, ?_⟩
    unfold ledgerToFloor
    have hne : Finsupp.single i₀ (1 : ℕ) ≠ 0 := by
      rw [Ne, Finsupp.single_eq_zero]; exact one_ne_zero
    rw [ledgerShadow_eq_true_iff.mpr hne]
    exact (Equiv.symm_apply_eq _).mpr hqt.symm

/-- On a single primitive distinction with unit weight, the T0 floor cost is
literally the Boolean recognition cost of the truncated natural-number
multiplicity: `C = boolRecognitionCost ∘ booleanTruncation`. -/
theorem rank1_cost_is_boolean_truncation {K : Type*} (h : ∃ x y : K, x ≠ y)
    {I : Type v} (i₀ : I) (n : ℕ) :
    (forcedQuotientRecognitionCost h).C (ledgerToFloor h (Finsupp.single i₀ n)) =
      TMinus1ToT0.boolRecognitionCost.C (booleanTruncation n) := by
  rw [forcedQuotientRecognitionCost_transport]
  unfold ledgerToFloor
  rw [Equiv.apply_symm_apply, ledgerShadow_single]

/-- The Phase-2 identification holds for every distinction witness and every
strictly positive weight. -/
theorem ledger_floor_t0_bridge {K : Type*} (h : ∃ x y : K, x ≠ y)
    {I : Type v} (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    LedgerFloorT0Bridge h w where
  shadow_emp := by
    unfold ledgerToFloor
    rw [ledgerShadow_zero]
    rfl
  shadow_join := by
    intro Γ Δ
    apply (forcedQuotientBoolEquiv h).injective
    rw [forcedQuotientBoolEquiv_join]
    unfold ledgerToFloor
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ledgerShadow_add Γ Δ
  cost_is_truncated_ledger := by
    intro Γ
    rw [forcedQuotientRecognitionCost_transport]
    unfold ledgerToFloor
    rw [Equiv.apply_symm_apply]
    by_cases hΓ : Γ = 0
    · subst hΓ
      rw [ledgerShadow_zero, ledgerCost_zero]
      simp [TMinus1ToT0.boolRecognitionCost]
    · have hc : ledgerCost w Γ ≠ 0 :=
        fun he => hΓ ((ledgerCost_eq_zero_iff w hw Γ).mp he)
      rw [ledgerShadow_eq_true_iff.mpr hΓ]
      simp [TMinus1ToT0.boolRecognitionCost, hc]
  consistent_iff_costless := by
    intro Γ
    show forcedQuotientBoolEquiv h (ledgerToFloor h Γ) = false ↔ ledgerCost w Γ = 0
    unfold ledgerToFloor
    rw [Equiv.apply_symm_apply, ledgerShadow_eq_false_iff,
      ledgerCost_eq_zero_iff w hw Γ]
  kernel_is_cost_kernel := by
    intro Γ Δ
    have hinj : (ledgerToFloor h Γ = ledgerToFloor h Δ) ↔
        (ledgerShadow Γ = ledgerShadow Δ) := by
      unfold ledgerToFloor
      exact (forcedQuotientBoolEquiv h).symm.injective.eq_iff
    rw [hinj, ledgerCost_eq_zero_iff w hw Γ, ledgerCost_eq_zero_iff w hw Δ]
    by_cases hΓ : Γ = 0 <;> by_cases hΔ : Δ = 0 <;>
      simp [ledgerShadow, hΓ, hΔ]

/-! ## Citeable certificate -/

/-- The full Phase-2 identification, packaged for the strict T-1-to-T8 audit.
Specialised to a single primitive distinction (`Unit`) under unit weight, this
exhibits the T0 floor as the surjective two-state truncation of the extensive
recognition ledger. -/
structure LedgerT0IdentificationCertificate : Prop where
  /-- The truncation map is a surjective cost-and-join homomorphism from the
  extensive ledger onto the distinction-generated T0 floor. -/
  bridge :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y),
      LedgerFloorT0Bridge h (fun _ : Unit => (1 : ℝ))
  /-- On the single primitive distinction the floor cost is the Boolean
  recognition cost of the truncated multiplicity. -/
  rank1_cost_is_truncation :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y) (n : ℕ),
      (forcedQuotientRecognitionCost h).C
          (ledgerToFloor h (Finsupp.single (() : Unit) n)) =
        TMinus1ToT0.boolRecognitionCost.C (booleanTruncation n)
  /-- The T0 floor is a genuine quotient (shadow) of the extensive ledger. -/
  floor_is_quotient_of_ledger :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y),
      Function.Surjective (ledgerToFloor (I := Unit) h)

/-- The Phase-2 ledger-to-T0 identification is a theorem. -/
theorem ledger_t0_identification_certificate :
    LedgerT0IdentificationCertificate where
  bridge := fun h => ledger_floor_t0_bridge h _ (fun _ => one_pos)
  rank1_cost_is_truncation := fun h n => rank1_cost_is_boolean_truncation h () n
  floor_is_quotient_of_ledger := fun h => ledgerToFloor_surjective h ()

end LedgerFloorT0
end Foundation
end IndisputableMonolith
