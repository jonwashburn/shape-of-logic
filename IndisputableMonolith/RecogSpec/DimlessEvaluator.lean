import IndisputableMonolith.RecogSpec.Core
import IndisputableMonolith.RecogSpec.Spec

namespace IndisputableMonolith
namespace RecogSpec

/-!
# DimlessEvaluator (interface)

`dimlessPack_explicit` is currently the designated **spec-level placeholder evaluator** for
bridge/ledger → dimensionless pack.

## ⚠️ PLACEHOLDER WARNING ⚠️

**The current evaluator IGNORES the Ledger and Bridge arguments!**

All numerical outputs (α, masses, mixing angles, g-2) are computed purely from φ-formulas:
- `alpha := (1 - 1/φ) / 2`
- `massRatios := [φ, 1/φ²]`
- `mixingAngles := [1/φ]`
- `g2Muon := 1/φ⁵`

This means "matching" is currently **tautological**: we prove φ-formula = φ-formula,
NOT that structure forces these values.

## What IS Structure-Derived (Non-Placeholder)

Some fields ARE derived from structure (not φ-formulas):
- `strongCPNeutral` (kGateWitness) — from RSUnits structure
- `eightTickMinimal` (eightTickWitness) — from gray code structure
- `bornRule` (bornHolds) — from recognition paths

## Future Work

To make the future "derive the evaluator from real bridge/ledger structure" step clean and
non-invasive, we centralize the evaluation function behind a small interface:

* `DimlessEvaluator φ` – supplies an `eval` function producing a `DimlessPack` from any `(L,B)`.
* `explicitEvaluator φ` – the current default implementation (wraps `dimlessPack_explicit`).

A future `dimlessPack_fromStructure` would actually USE L and B to derive values.

Certified code should avoid treating `explicitEvaluator` as inevitable/derived; that's tracked
as an open expansion target in `docs/MATCHES_EVALUATOR_CLOSURE_PROMPT.md`.
-/

/-- Interface: an evaluator that produces a bridge-side dimensionless pack at scale `φ`. -/
structure DimlessEvaluator (φ : ℝ) where
  eval : (L : Ledger) → (B : Bridge L) → DimlessPack L B

/-- The current designated evaluator (placeholder): wraps `dimlessPack_explicit`. -/
noncomputable def explicitEvaluator (φ : ℝ) : DimlessEvaluator φ :=
  { eval := fun L B => dimlessPack_explicit φ L B }

/-- MatchesEval re-expressed through an explicit evaluator object (for future swapping). -/
def MatchesEvalWith {φ : ℝ} (E : DimlessEvaluator φ) (L : Ledger) (B : Bridge L) (U : UniversalDimless φ) : Prop :=
  PackMatches (φ:=φ) (P:=E.eval L B) U

@[simp] lemma matchesEvalWith_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    MatchesEvalWith (φ:=φ) (explicitEvaluator φ) L B (UD_explicit φ) := by
  simp [MatchesEvalWith, explicitEvaluator, PackMatches, dimlessPack_explicit, UD_explicit]

/-! ## Placeholder Nature: L and B Are Ignored

These lemmas make explicit that the **legacy** evaluator `explicitEvaluator` ignores
its structure arguments. The structural evaluator `dimlessPack_fromStructure`
(in `RSCompliance`) DOES read from ledger/bridge and is the intended replacement.

The remaining gap is not in the evaluator but in the structural premise: the
`CubeAdmissibleTorsion` predicate (in `GenerationTorsionBridge`) is an explicit
geometric assumption, not yet derived from the cost functional.
-/

/-- The evaluator produces the same α for ANY ledger/bridge pair.
This proves the evaluator ignores the Ledger argument for numerical outputs. -/
@[simp] lemma evaluator_alpha_ignores_structure (φ : ℝ) (L₁ L₂ : Ledger)
    (B₁ : Bridge L₁) (B₂ : Bridge L₂) :
    ((explicitEvaluator φ).eval L₁ B₁).alpha =
    ((explicitEvaluator φ).eval L₂ B₂).alpha := by
  simp [explicitEvaluator, dimlessPack_explicit]

/-- The evaluator produces the same mass ratios for ANY ledger/bridge pair. -/
@[simp] lemma evaluator_massRatios_ignores_structure (φ : ℝ) (L₁ L₂ : Ledger)
    (B₁ : Bridge L₁) (B₂ : Bridge L₂) :
    ((explicitEvaluator φ).eval L₁ B₁).massRatios =
    ((explicitEvaluator φ).eval L₂ B₂).massRatios := by
  simp [explicitEvaluator, dimlessPack_explicit]

/-- The evaluator produces the same mixing angles for ANY ledger/bridge pair. -/
@[simp] lemma evaluator_mixingAngles_ignores_structure (φ : ℝ) (L₁ L₂ : Ledger)
    (B₁ : Bridge L₁) (B₂ : Bridge L₂) :
    ((explicitEvaluator φ).eval L₁ B₁).mixingAngles =
    ((explicitEvaluator φ).eval L₂ B₂).mixingAngles := by
  simp [explicitEvaluator, dimlessPack_explicit]

/-- The evaluator produces the same g-2 for ANY ledger/bridge pair. -/
@[simp] lemma evaluator_g2Muon_ignores_structure (φ : ℝ) (L₁ L₂ : Ledger)
    (B₁ : Bridge L₁) (B₂ : Bridge L₂) :
    ((explicitEvaluator φ).eval L₁ B₁).g2Muon =
    ((explicitEvaluator φ).eval L₂ B₂).g2Muon := by
  simp [explicitEvaluator, dimlessPack_explicit]

end RecogSpec
end IndisputableMonolith
