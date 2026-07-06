import Mathlib

/-!
# Input Ledger (replaces the former `zero_knobs_policy`)

The former `theorem zero_knobs_policy : 0 = 0 := rfl` was removed in the
2026-07-06 honesty pass: a reflexivity proof of `0 = 0` carries no information
about the framework's inputs, and the 2026 internal audit (Thapa, T−2..T5
forcing report, §11) correctly identified it as vacuous.

What replaces it is the opposite of a vacuous certificate: an explicit,
enumerated ledger of every discrete modeling input, convention, and
calibration the T−2..T5 layer consumes. "Zero adjustable parameters" is true
only in the narrow sense that no CONTINUOUS parameter is fit to data; the
discrete structural choices below are real inputs and are named as such.
-/

namespace IndisputableMonolith
namespace Verification

/-- One named input consumed by the derivation layer. -/
structure LedgeredInput where
  name : String
  kind : String   -- "structural choice" | "convention/normalization" | "bridge hypothesis"
  where_used : String
deriving Repr, DecidableEq

/-- The explicit input ledger for the T−2..T5 layer (audit §11). Each entry is
a genuine input: not fit to data, but also not derived from logic alone. -/
def inputLedger : List LedgeredInput :=
  [ ⟨"observational relation (distinguishability structure)", "structural choice", "T−1 floor"⟩
  , ⟨"marked pair / orientation for Boolean projection", "structural choice", "T−1 → Bool coordinate"⟩
  , ⟨"Bool indicator model with unit recognition cost", "structural choice", "T0 recognition work"⟩
  , ⟨"positive-ratio continuum carrier (SI2, Hölder-type embedding)", "bridge hypothesis", "T4 → T5 comparison surface"⟩
  , ⟨"finite polynomial closure / composition law (C6)", "structural choice", "T5 characterization"⟩
  , ⟨"bilinear coefficient c = 2 in the combiner", "convention/normalization", "RCL polynomial P(u,v) = 2uv + 2u + 2v"⟩
  , ⟨"diagonal normalization P(1,1) = 6", "convention/normalization", "RCL forcing"⟩
  , ⟨"log-curvature calibration λ = 1 (C7)", "convention/normalization", "selects J among cosh(λ log x) − 1"⟩
  , ⟨"hyperbolic (sign) branch selection", "convention/normalization", "excludes the cosine branch"⟩
  ]

/-- The ledger is non-empty: the framework HAS inputs, and they are named. -/
theorem inputLedger_nonempty : inputLedger ≠ [] := by
  simp [inputLedger]

/-- Count of ledgered inputs (audit §11 enumeration). -/
theorem inputLedger_count : inputLedger.length = 9 := rfl

/-- Number of CONTINUOUS parameters fit to empirical data in the T−2..T5
proof layer: zero. This narrow claim is the honest survivor of the former
"zero knobs" language; the discrete inputs above remain real inputs. -/
def fittedContinuousParameterCount : Nat := 0

@[simp] theorem no_fitted_continuous_parameters : fittedContinuousParameterCount = 0 := rfl

end Verification
end IndisputableMonolith
