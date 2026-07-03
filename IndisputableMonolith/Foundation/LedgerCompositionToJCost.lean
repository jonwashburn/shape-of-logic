import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.Foundation.LedgerToFactorization

/-!
# Ledger composition forces the recognition cost `J` (Phase 3 endpoint)

The Phase 3 checklist item "Apply `law_of_logic_forces_jcost`" was flagged
because `law_of_logic_forces_jcost` exists but its `SatisfiesCompositionLaw F`
hypothesis was *assumed*, not derived from the recognition ledger.

This module closes that gap structurally.  The composition law

  `F (x·y) + F (x/y) = 2 F x F y + 2 F x + 2 F y`

is, term for term, the statement that the cost's own two-point combiner
`(x, y) ↦ F (x·y) + F (x/y)` equals the RCL combiner `rclCombiner` evaluated at
the costs `(F x, F y)` (`rclCombiner u v = 2uv + 2u + 2v`).  So the composition
law is *not* an independent analytic input: it is exactly

  "the recognition cost composes through the RCL combiner".

Phase 3's directional ledger theorem
(`LedgerToFactorization.primitiveLedgerPosting_directional_forces_rcl`) already
forces *any* primitive ledger-posting combiner with per-slice directional
regularity to equal `rclCombiner`.  Composing the two:

* if `F` composes through *some* combiner `P` (the factorization/composability
  input), and
* `P` satisfies primitive ledger posting with directional regularity,

then `P = rclCombiner`, hence `SatisfiesCompositionLaw F`, hence — feeding the
remaining reciprocal/normalized/calibrated/continuous hypotheses into
`law_of_logic_forces_jcost` — `F = J`.

The `SatisfiesCompositionLaw` hypothesis of `law_of_logic_forces_jcost` is thus
replaced by a ledger-side statement: the cost composes through a ledger-posting
combiner.  The residual that remains is the bare *composability* of the cost
(`CostComposesThrough F P` for some `P`), isolated cleanly here; the "combiner
is RCL" half is now a theorem of the ledger, not a hypothesis.

`Cost.Jcost` itself composes through `rclCombiner`
(`jcost_composesThrough_rclCombiner`), so the construction is non-vacuous: `J`
is a genuine fixed point of the entire ledger-composition setup.

Status: 0 sorry, 0 new axiom.  Uses the proved `AczelSmoothnessPackage`
instance (`Cost/AczelProof.lean`), so the conclusion is unconditional.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerCompositionToJCost

open Cost.FunctionalEquation
open DAlembert.FactorizationForcing
open LedgerToFactorization

/-! ## The composition law is "the cost composes through the RCL combiner" -/

/-- **The composition law is the RCL combiner law on costs.**  `F` satisfies the
recognition composition law iff its symmetric two-point combination
`F (x·y) + F (x/y)` equals `rclCombiner (F x) (F y)`.  This is a pure
rearrangement: `rclCombiner u v = 2uv + 2u + 2v` is the composition-law RHS with
`u = F x`, `v = F y`. -/
theorem satisfiesCompositionLaw_iff_rclCombiner (F : ℝ → ℝ) :
    SatisfiesCompositionLaw F ↔
      ∀ x y : ℝ, 0 < x → 0 < y →
        F (x * y) + F (x / y) = rclCombiner (F x) (F y) := by
  unfold SatisfiesCompositionLaw rclCombiner
  constructor
  · intro h x y hx hy; rw [h x y hx hy]
  · intro h x y hx hy; rw [h x y hx hy]

/-- **The cost composes through a combiner `P`** if its symmetric two-point
combination is `P` evaluated at the costs.  This is the factorization /
composability input: `F (x·y) + F (x/y)` is governed by a binary law of the two
single-point costs. -/
def CostComposesThrough (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y)

/-- If the cost composes through the RCL combiner, it satisfies the composition
law. -/
theorem satisfiesCompositionLaw_of_composesThrough_rcl (F : ℝ → ℝ)
    (h : CostComposesThrough F rclCombiner) :
    SatisfiesCompositionLaw F :=
  (satisfiesCompositionLaw_iff_rclCombiner F).mpr h

/-- **Ledger posting + directional regularity force the cost's composition
law.**  If `F` composes through a combiner `P`, and `P` is a primitive
ledger-posting combiner with per-slice directional regularity, then `P` is
forced to be `rclCombiner` (Phase 3), so `F` satisfies the recognition
composition law. -/
theorem satisfiesCompositionLaw_of_ledgerComposes (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hP : PrimitiveLedgerPostingSemantics P)
    (hdir : ∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v))
    (hCompose : CostComposesThrough F P) :
    SatisfiesCompositionLaw F := by
  have hPrcl : ∀ u v, P u v = rclCombiner u v :=
    primitiveLedgerPosting_directional_forces_rcl P hP hdir
  apply satisfiesCompositionLaw_of_composesThrough_rcl
  intro x y hx hy
  rw [hCompose x y hx hy, hPrcl]

/-! ## Phase 3 endpoint: ledger composition forces `J` -/

/-- **Ledger composition forces `J`.**  If the recognition cost `F` is
reciprocal, normalized, calibrated, and continuous on the positive ray, and it
composes through a combiner `P` that satisfies primitive ledger posting with
per-slice directional regularity, then `F = J` on positives.

This is the genuine discharge of the Phase 3 "Apply `law_of_logic_forces_jcost`"
item: the previously-assumed `SatisfiesCompositionLaw F` hypothesis is replaced
by the ledger-side pair (cost composes through `P`) ∧ (`P` is a ledger-posting
combiner), and the "combiner = RCL" half is a theorem, not an assumption. -/
theorem ledgerComposition_forces_jcost
    (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hRecip : IsReciprocalCost F)
    (hNorm : IsNormalized F)
    (hCalib : IsCalibrated F)
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hP : PrimitiveLedgerPostingSemantics P)
    (hdir : ∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v))
    (hCompose : CostComposesThrough F P) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  have hComp : SatisfiesCompositionLaw F :=
    satisfiesCompositionLaw_of_ledgerComposes F P hP hdir hCompose
  exact law_of_logic_forces_jcost F hRecip hNorm hComp hCalib hCont

/-! ## Non-vacuity: `J` composes through the RCL combiner -/

/-- **`J` composes through the RCL combiner.**  The recognition cost
`J(x) = ½(x + x⁻¹) − 1` satisfies `J (x·y) + J (x/y) = rclCombiner (J x) (J y)`
for positive `x, y`.  This shows the ledger-composition setup is non-vacuous:
`J` is a fixed point of the composition law it forces. -/
theorem jcost_composesThrough_rclCombiner :
    CostComposesThrough Cost.Jcost rclCombiner := by
  intro x y hx hy
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  unfold Cost.Jcost rclCombiner
  field_simp
  ring

/-- Consequently `J` itself satisfies the recognition composition law. -/
theorem jcost_satisfiesCompositionLaw : SatisfiesCompositionLaw Cost.Jcost :=
  satisfiesCompositionLaw_of_composesThrough_rcl Cost.Jcost
    jcost_composesThrough_rclCombiner

/-! ## Certificate -/

/-- The Phase 3 ledger-composition closure certificate: every field is a proved
theorem of this module.  It records that the composition-law hypothesis of
`law_of_logic_forces_jcost` is reducible to a ledger-posting combiner plus bare
composability, that this forces `J`, and that `J` is a consistent fixed point. -/
structure LedgerCompositionCertificate : Prop where
  /-- The composition law is exactly "the cost composes through the RCL
  combiner". -/
  composition_law_is_rcl :
    ∀ F : ℝ → ℝ, SatisfiesCompositionLaw F ↔
      ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = rclCombiner (F x) (F y)
  /-- A cost composing through a ledger-posting + directional combiner satisfies
  the composition law. -/
  ledger_composes_forces_composition_law :
    ∀ (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ),
      PrimitiveLedgerPostingSemantics P →
      (∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v)) →
      CostComposesThrough F P →
      SatisfiesCompositionLaw F
  /-- Ledger composition (plus reciprocal/normalized/calibrated/continuous)
  forces `F = J`. -/
  ledger_composition_forces_jcost :
    ∀ (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ),
      IsReciprocalCost F → IsNormalized F → IsCalibrated F →
      ContinuousOn F (Set.Ioi 0) →
      PrimitiveLedgerPostingSemantics P →
      (∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v)) →
      CostComposesThrough F P →
      ∀ x : ℝ, 0 < x → F x = Cost.Jcost x
  /-- `J` composes through the RCL combiner (non-vacuity). -/
  jcost_composes : CostComposesThrough Cost.Jcost rclCombiner

/-- The ledger-composition certificate holds. -/
theorem ledgerCompositionCertificate : LedgerCompositionCertificate where
  composition_law_is_rcl := satisfiesCompositionLaw_iff_rclCombiner
  ledger_composes_forces_composition_law :=
    satisfiesCompositionLaw_of_ledgerComposes
  ledger_composition_forces_jcost := ledgerComposition_forces_jcost
  jcost_composes := jcost_composesThrough_rclCombiner

end LedgerCompositionToJCost
end Foundation
end IndisputableMonolith
