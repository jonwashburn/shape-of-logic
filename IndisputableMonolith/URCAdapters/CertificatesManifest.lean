import Mathlib
import IndisputableMonolith.URCGenerators.UltimateCPMClosureCert

/-!
# Certificates Manifest (certified surface)

This module provides a **lightweight** consolidated manifest string for CI and for
audit scripts. It is intentionally scoped to the *certified surface* (the import
closure of the top certificate), and avoids importing quarantined or WIP bundles.

The CI guard (`scripts/ci_guard.sh`) expects the substring:

`CI smoke: toolchain OK`

to appear in the output of `lake exe ci_checks`.
-/

namespace IndisputableMonolith
namespace URCAdapters

/-- Consolidated manifest string for CI/audit logs.

The `let _ := ...` line forces elaboration of the top certificate theorem so CI
fails if the certified surface stops compiling. -/
@[simp] def certificates_manifest : String :=
  let _ := IndisputableMonolith.URCGenerators.UltimateCPMClosureCert.verified_any
    (c := ({} : IndisputableMonolith.URCGenerators.UltimateCPMClosureCert))
  String.intercalate "\n"
    [ "CI smoke: toolchain OK"
    , "Certified surface: UltimateCPMClosureCert verified"
    ]

end URCAdapters
end IndisputableMonolith

