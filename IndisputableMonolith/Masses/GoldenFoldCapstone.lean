import Mathlib
import IndisputableMonolith.Masses.GoldenFoldForcing
import IndisputableMonolith.Masses.GoldenGenerationForcing
import IndisputableMonolith.Masses.GoldenMinimalRealization
import IndisputableMonolith.Masses.GoldenMonodromyReturn
import IndisputableMonolith.Masses.GoldenFoldCostSelection
import IndisputableMonolith.Masses.GoldenMonodromyCarrier

/-!
# Golden Fold Capstone (`GD_fold_is_golden`, one verified object)

The `GD_fold_is_golden` program was built and banked as **six** independent certificates, each
axiom-clean (`#print axioms` = Mathlib base only) and each guarding against a distinct vacuity:

1. **GC** `GoldenFoldForcing.GoldenForcingCert` — the relation compression: the canonical integer
   witness satisfies `F² = F + 1`; every integral golden operator has `trace 1, det −1`; a positive
   real eigenvalue is forced to `φ`.
2. **GG** `GoldenGenerationForcing.GoldenGenerationCert` — the algebra spine: the golden cube, the
   exact mod-2 order-three (three generations), the eigenvalue→golden C–H tail, the swap·shear
   factorization and its determinant split, the duality-closed spectrum with Galois norm `−1`.
3. **GM** `GoldenMinimalRealization.MinimalIntegralRealizationCert` — the head statement: char poly
   `X²−X−1 = minpoly ℚ φ`, dimensional minimality over ℤ *and* ℚ (no `1×1` realizer).
4. **GR** `GoldenMonodromyReturn.MonodromyReturnCert` — the return-map algebra (N3/N4): the linked
   return map `returnMap k = !![0,1;1,k]` has `trace = k`, `det = −1`, is golden **iff** `k = 1`, and
   genuinely discriminates (involution at `k=0`, silver at `k=2`).
5. **GS** `GoldenFoldCostSelection.GoldenFoldCostCert` — the selection (Live Bet 1): among all
   growth-producing folds the golden linking `k = 1` is the **unique** minimizer of recognition cost.
6. **GMC** `GoldenMonodromyCarrier.MonodromyCarrierCert` — the topological front-end (N1/N2): an
   explicit finite ℤ-chain carrier with `H₁ ≅ ℤ²` **derived** from the boundary kernel, whose
   exchange/transport monodromy induces exactly `returnMap (linkingNumber cr)` on `H₁`, with `k`
   sourced as a signed crossing sum (differential oracle: `unlink/Hopf/clasp → 0/1/2`).

This module makes the composite claim a **single machine-checkable object**. `GDFoldCertificates`
bundles all six; `gdFoldCertificates_holds` proves the whole bundle in one term, so
`lake build IndisputableMonolith.Masses.GoldenFoldCapstone` re-verifies the entire program.

## The one MODEL premise, isolated

Every layer above is `THEOREM`-grade. The program reduces to a **single** physical identification:
that the physical generation-fold operator *is* the `H₁`-monodromy of the recognition link carrier
for the crossing word of the two forced 8-tick cycles. `FoldIsGoldenCarrier` names exactly that
premise (`F = returnMap (linkingNumber cr)` with the cost-forced unit linking `linkingNumber cr = 1`).
`gd_fold_is_golden_of_model` then discharges the whole conclusion (`F` golden, `F = goldenMulZ`, char
poly `X²−X−1`) from it — nothing else is assumed. The `= 1` conjunct is the cost-selection theorem
(GS); the `F = returnMap (…)` conjunct is the sole MODEL bridge (carrier = complement, GMC's honest
premise). The separation is deliberate: the reader sees exactly which single input is not a theorem.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenFoldCapstone

open Polynomial
open IndisputableMonolith.Masses.GoldenFoldForcing
open IndisputableMonolith.Masses.GoldenGenerationForcing
open IndisputableMonolith.Masses.GoldenMinimalRealization
open IndisputableMonolith.Masses.GoldenMonodromyReturn
open IndisputableMonolith.Masses.GoldenFoldCostSelection
open IndisputableMonolith.Masses.GoldenMonodromyCarrier

/-! ## The bundled certificate -/

/-- The whole `GD_fold_is_golden` program as one object: all six banked certificates. Each field
is a `THEOREM`-grade, axiom-clean certificate proved in its own module; bundling them here makes the
composite claim a single `#check`/`#print axioms` target and prevents silent drift of any leg. -/
structure GDFoldCertificates : Prop where
  /-- GC — the relation compression `F² = F + 1 ⇒ trace 1, det −1; positive eigenvalue = φ`. -/
  compression : Nonempty GoldenForcingCert
  /-- GG — the algebra spine (cube, mod-2 order 3, C–H tail, swap·shear, Galois norm −1). -/
  algebra_spine : Nonempty GoldenGenerationCert
  /-- GM — the head statement (char poly `X²−X−1 = minpoly ℚ φ`, dimensional minimality). -/
  head : Nonempty MinimalIntegralRealizationCert
  /-- GR — the return-map algebra (`returnMap k = !![0,1;1,k]`, golden iff `k = 1`). -/
  return_map : Nonempty MonodromyReturnCert
  /-- GS — the cost selection (`k = 1` uniquely minimizes recognition cost among growth folds). -/
  cost_selection : Nonempty GoldenFoldCostCert
  /-- GMC — the topological front-end (`H₁ ≅ ℤ²` derived; monodromy = `returnMap (linkingNumber cr)`). -/
  carrier : MonodromyCarrierCert

/-- **Capstone.** The six banked certificates hold simultaneously. This is the single verified
object for `GD_fold_is_golden`: one term re-checks the relation compression, the algebra spine, the
head statement, the return-map algebra, the cost selection, and the topological carrier. -/
theorem gdFoldCertificates_holds : GDFoldCertificates where
  compression := goldenForcingCert_holds
  algebra_spine := goldenGenerationCert_holds
  head := minimalIntegralRealizationCert_holds
  return_map := monodromyReturnCert_holds
  cost_selection := goldenFoldCostCert_holds
  carrier := monodromyCarrierCert_holds

/-! ## The isolated MODEL premise and the conditional conclusion -/

/-- The **single remaining MODEL premise** of `GD_fold_is_golden`, stated explicitly.

An integer operator `F` is a *golden fold carrier* when it is the `H₁`-monodromy of the recognition
link carrier for some frozen crossing word `cr` whose linking number is the cost-selected unit `1`:
`F = returnMap (linkingNumber cr)` with `linkingNumber cr = 1`.

- The conjunct `linkingNumber cr = 1` is `THEOREM`-forced by the cost selection (GS): among all
  growth-producing folds, `k = 1` is the unique recognition-cost minimizer.
- The conjunct `F = returnMap (linkingNumber cr)` is the sole non-theorem input: the modeling
  identification "the physical generation fold is the carrier monodromy" (GMC's honest MODEL premise,
  defended by the differential oracle and the standard `H₁ ≅ ℤ²` of a 2-component link complement),
  not asserted as a Lean theorem. -/
def FoldIsGoldenCarrier (F : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ cr : List Crossing, F = returnMap (linkingNumber cr) ∧ linkingNumber cr = 1

/-- **Conditional conclusion.** From the single MODEL premise `FoldIsGoldenCarrier F` the entire
`GD_fold_is_golden` conclusion follows with no further assumption: `F` satisfies the golden relation,
`F` is exactly the canonical integer witness `goldenMulZ`, and its characteristic polynomial is
`X² − X − 1` (whose real root is `φ`). Every implication used here is drawn from the banked
certificates; only `FoldIsGoldenCarrier` is a hypothesis. -/
theorem gd_fold_is_golden_of_model
    {F : Matrix (Fin 2) (Fin 2) ℤ} (h : FoldIsGoldenCarrier F) :
    GoldenRelation F ∧ F = goldenMulZ ∧ F.charpoly = (X ^ 2 - X - 1 : Polynomial ℤ) := by
  obtain ⟨cr, hF, hk⟩ := h
  have hgold : F = goldenMulZ := by
    rw [hF, hk]; exact returnMap_one_eq_goldenMulZ
  refine ⟨?_, hgold, ?_⟩
  · rw [hgold]; exact goldenRelation_of_goldenMulZ
  · rw [hgold]; exact goldenMulZ_charpoly

/-- The MODEL premise is **satisfiable and non-vacuous**: the Hopf carrier word (one positive
crossing, linking number `1`) realizes it, so `gd_fold_is_golden_of_model` is not proving a claim
from an impossible hypothesis. Witness: `F = returnMap 1 = goldenMulZ`. -/
theorem foldIsGoldenCarrier_hopf : FoldIsGoldenCarrier goldenMulZ :=
  ⟨hopfWord, by rw [linkingNumber_hopf, returnMap_one_eq_goldenMulZ], linkingNumber_hopf⟩

/-- The premise genuinely **selects**: the unlinked carrier word (linking number `0`) does *not*
satisfy it for its own monodromy, so `FoldIsGoldenCarrier` is not vacuously true of every return
map. Concretely `returnMap 0` is not a golden fold carrier. -/
theorem not_foldIsGoldenCarrier_unlink : ¬ FoldIsGoldenCarrier (returnMap 0) := by
  rintro ⟨cr, hF, hk⟩
  -- `returnMap` is injective in its trace, and `returnMap 0` has trace `0 ≠ 1 = linkingNumber cr`.
  have htr : (returnMap 0).trace = (returnMap (linkingNumber cr)).trace := by rw [hF]
  rw [returnMap_trace, returnMap_trace, hk] at htr
  exact zero_ne_one htr

end GoldenFoldCapstone
end Masses
end IndisputableMonolith
