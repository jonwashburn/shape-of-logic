import IndisputableMonolith.DeltaKernel.Serialize
import IndisputableMonolith.DeltaKernel.Examples
import IndisputableMonolith.DeltaKernel.GodelTest

/-!
# δ-Kernel: the Golden Corpus (differential-validation anchor)

A fixed list of `(name, context, derivation, expected verdict)` entries.
The expected verdicts are LITERALS, frozen in this source file, and
`corpus_golden` proves by `decide` that the Lean-hosted `check` (evaluated
by Lean's kernel) reproduces every one of them.

The extracted binary (`deltak selftest`, see `Main.lean`) re-evaluates the
SAME `check` function through the compiler and native code and compares
against the SAME frozen literals. Agreement between the two evaluations of
the two trust paths (Lean kernel reduction vs compiled IR) is the Phase-2
differential validation the panel prescribed: the binary is validated
against the Lean-hosted version, never trusted on its own.

The corpus spans every verdict class the kernel issues:
FORCED (empty ledger), FORCED @ FULL-IND (tier flag), CONDITIONAL {EM},
CONDITIONAL {MP}, and REJECT (`none`), plus the Gödel-test pricing pair
(the same `add_comm` at QF-IND for free vs FULL-IND priced).
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-- One golden-corpus entry: a named checking job with its frozen verdict. -/
structure CorpusEntry where
  name : String
  ctx : Ctx
  deriv : Deriv
  expected : Option (DFormula × Ledger)

open Examples GodelTest in
/-- The golden corpus. Verdicts are literals frozen here, not recomputed. -/
def corpus : List CorpusEntry :=
  [ ⟨"one_plus_one", [], onePlusOne,
      some (.eq (.add one one) two, .empty)⟩
  , ⟨"zero_add", [], zeroAdd,
      some (.all zeroAddFormula, .empty)⟩
  , ⟨"full_ind_demo", [], fullIndDemo,
      some (.all quantFormula, .ofIndFull)⟩
  , ⟨"em_route", [], emRoute,
      some (.disj zeroEq zeroEq.neg, .ofEM)⟩
  , ⟨"forced_route", [], forcedRoute,
      some (.disj zeroEq zeroEq.neg, .empty)⟩
  , ⟨"mp_qf", [], .mpPosit qfMatrix,
      some (.impl (.neg (.neg (.ex qfMatrix))) (.ex qfMatrix), .ofMP)⟩
  , ⟨"mp_quantified_reject", [], .mpPosit (.all (.eq (.var 0) (.var 0))),
      none⟩
  , ⟨"succ_add", [], succAdd,
      some (.all (.all succAddFormula), .empty)⟩
  , ⟨"add_comm_qf", [], addComm,
      some (.all (.all commFormula), .empty)⟩
  , ⟨"add_comm_full", [], addCommFull,
      some (.all (.all commFormula), .ofIndFull)⟩
  ]

/-- THE FREEZE: Lean's kernel certifies that `check` reproduces every frozen
verdict in the corpus. The binary's `selftest` re-runs this comparison
through the compiler; this theorem is what it is differential AGAINST. -/
theorem corpus_golden :
    corpus.all (fun e => check e.ctx e.deriv == e.expected) = true := by
  decide

end DeltaKernel
end IndisputableMonolith
