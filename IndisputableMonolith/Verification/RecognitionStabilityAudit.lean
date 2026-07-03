import IndisputableMonolith.Verification.RecognitionStabilityAudit.Core
import IndisputableMonolith.Verification.RecognitionStabilityAudit.FrontEnd
import IndisputableMonolith.Verification.RecognitionStabilityAudit.BackEnd
import IndisputableMonolith.Verification.RecognitionStabilityAudit.RStoRL

/-!
# Recognition Stability Audit (RSA) (umbrella module)

Paper reference: `papers/tex/Recognition_Stability_Audit.tex`.

This module re-exports the RSA core interface so downstream code can simply:

`import IndisputableMonolith.Verification.RecognitionStabilityAudit`

and then work with:

- `RecognitionStabilityAudit.Problem`
- `RecognitionStabilityAudit.FrontEnd`
- `RecognitionStabilityAudit.BackEnd`
- `RecognitionStabilityAudit.correctness`
- `RecognitionStabilityAudit.RStoRL` — RS→RL bridge (virtue actions, lexicographic selection, Gibbs)
-/
