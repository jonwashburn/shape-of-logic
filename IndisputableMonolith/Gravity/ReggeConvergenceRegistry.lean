import Mathlib
import IndisputableMonolith.Gravity.NonlinearConvergence

/-!
# Regge Convergence Registry

This module consolidates the four external convergence Propositions currently
scattered in `NonlinearConvergence.lean` into a single named structure
`ReggeConvergenceRegistry`.

The registry is a **faithful repackaging**: each field is typed by the exact
original proposition from `NonlinearConvergence`, and the faithful-projection
theorems below show that each registry field recovers the corresponding
original proposition.  No convergence content is restated or re-proved; only
references to the existing propositions are repackaged.

## Provenance

The four convergence inputs are external-mathematics results:

- `cms_measure_bound`: Cheeger–Müller–Schrader (1984), Theorem 5.1 —
  curvature-measure convergence with `η^(1/2)` bulk + boundary-tube term.
  Status: external theorem, axiomatized.
- `special_quadratic`: stronger `O(a²)` action-convergence hypothesis
  used in special weak-field / numerical settings.
  Status: external hypothesis, axiomatized.
- `ricci_convergence`: Regge Ricci-scalar convergence at `O(a²)`.
  Status: external hypothesis, axiomatized.
- `riemann_convergence`: Regge holonomy / Riemann convergence.
  Status: external hypothesis, axiomatized.
-/

namespace IndisputableMonolith
namespace Gravity

open NonlinearConvergence

namespace ReggeConvergenceRegistry

/-! ## The registry structure -/

/-- A registry that consolidates the four external convergence Propositions
from `NonlinearConvergence` into a single named structure.

Each field is typed by the **exact** original proposition, so this is a
faithful repackaging, not a weakening.  The `provenance` field documents
each input as an external-mathematics result with a status tag. -/
structure ReggeConvergenceRegistry where
  /-- CMS Theorem 5.1 curvature-measure bound (Cheeger–Müller–Schrader 1984). -/
  cms_measure_bound : cms_theorem_5_1_measure_bound
  /-- Special-purpose `O(a²)` action-convergence hypothesis. -/
  special_quadratic : special_quadratic_regge_to_eh_convergence_hypothesis
  /-- Regge Ricci-scalar convergence axiom. -/
  ricci_convergence : regge_ricci_convergence_axiom
  /-- Regge Riemann / holonomy convergence axiom. -/
  riemann_convergence : regge_riemann_convergence_axiom
  /-- Documentation of each external-math result with a status tag. -/
  provenance : List String

/-! ## Faithful-projection theorems

These theorems show that each registry field, when projected from a registry
value, yields a proof of the **exact** original proposition from
`NonlinearConvergence`.  This confirms the registry is a faithful
repackaging, not a weakening. -/

/-- The `cms_measure_bound` field of a registry is a proof of the original
`cms_theorem_5_1_measure_bound` proposition from `NonlinearConvergence`. -/
theorem cms_measure_bound_faithful (r : ReggeConvergenceRegistry) :
    cms_theorem_5_1_measure_bound := r.cms_measure_bound

/-- The `special_quadratic` field of a registry is a proof of the original
`special_quadratic_regge_to_eh_convergence_hypothesis` proposition. -/
theorem special_quadratic_faithful (r : ReggeConvergenceRegistry) :
    special_quadratic_regge_to_eh_convergence_hypothesis := r.special_quadratic

/-- The `ricci_convergence` field of a registry is a proof of the original
`regge_ricci_convergence_axiom` proposition. -/
theorem ricci_convergence_faithful (r : ReggeConvergenceRegistry) :
    regge_ricci_convergence_axiom := r.ricci_convergence

/-- The `riemann_convergence` field of a registry is a proof of the original
`regge_riemann_convergence_axiom` proposition. -/
theorem riemann_convergence_faithful (r : ReggeConvergenceRegistry) :
    regge_riemann_convergence_axiom := r.riemann_convergence

/-! ## Construction from original propositions -/

/-- Given proofs of all four original propositions and a provenance list,
construct a `ReggeConvergenceRegistry`.  This is the converse of the
faithful-projection theorems, showing the registry is a faithful
repackaging. -/
def mk (h1 : cms_theorem_5_1_measure_bound)
    (h2 : special_quadratic_regge_to_eh_convergence_hypothesis)
    (h3 : regge_ricci_convergence_axiom)
    (h4 : regge_riemann_convergence_axiom)
    (prov : List String) : ReggeConvergenceRegistry where
  cms_measure_bound := h1
  special_quadratic := h2
  ricci_convergence := h3
  riemann_convergence := h4
  provenance := prov

/-- Projecting the `cms_measure_bound` field of a registry built via `mk`
recovers the original proof. -/
theorem mk_cms_measure_bound
    (h1 : cms_theorem_5_1_measure_bound)
    (h2 : special_quadratic_regge_to_eh_convergence_hypothesis)
    (h3 : regge_ricci_convergence_axiom)
    (h4 : regge_riemann_convergence_axiom)
    (prov : List String) :
    (mk h1 h2 h3 h4 prov).cms_measure_bound = h1 := rfl

/-- Projecting the `special_quadratic` field of a registry built via `mk`
recovers the original proof. -/
theorem mk_special_quadratic
    (h1 : cms_theorem_5_1_measure_bound)
    (h2 : special_quadratic_regge_to_eh_convergence_hypothesis)
    (h3 : regge_ricci_convergence_axiom)
    (h4 : regge_riemann_convergence_axiom)
    (prov : List String) :
    (mk h1 h2 h3 h4 prov).special_quadratic = h2 := rfl

/-- Projecting the `ricci_convergence` field of a registry built via `mk`
recovers the original proof. -/
theorem mk_ricci_convergence
    (h1 : cms_theorem_5_1_measure_bound)
    (h2 : special_quadratic_regge_to_eh_convergence_hypothesis)
    (h3 : regge_ricci_convergence_axiom)
    (h4 : regge_riemann_convergence_axiom)
    (prov : List String) :
    (mk h1 h2 h3 h4 prov).ricci_convergence = h3 := rfl

/-- Projecting the `riemann_convergence` field of a registry built via `mk`
recovers the original proof. -/
theorem mk_riemann_convergence
    (h1 : cms_theorem_5_1_measure_bound)
    (h2 : special_quadratic_regge_to_eh_convergence_hypothesis)
    (h3 : regge_ricci_convergence_axiom)
    (h4 : regge_riemann_convergence_axiom)
    (prov : List String) :
    (mk h1 h2 h3 h4 prov).riemann_convergence = h4 := rfl

/-- Projecting the `provenance` field of a registry built via `mk`
recovers the original list. -/
theorem mk_provenance
    (h1 : cms_theorem_5_1_measure_bound)
    (h2 : special_quadratic_regge_to_eh_convergence_hypothesis)
    (h3 : regge_ricci_convergence_axiom)
    (h4 : regge_riemann_convergence_axiom)
    (prov : List String) :
    (mk h1 h2 h3 h4 prov).provenance = prov := rfl

/-! ## Round-trip: projection and construction are inverses -/

/-- Building a registry from the projections of `r` recovers `r`.
This confirms the registry is a faithful repackaging. -/
theorem mk_roundtrip (r : ReggeConvergenceRegistry) :
    mk r.cms_measure_bound r.special_quadratic r.ricci_convergence
       r.riemann_convergence r.provenance = r := rfl

/-! ## Default provenance -/

/-- The default provenance list documenting each external-math result
with a status tag. -/
def defaultProvenance : List String :=
  [ "cms_measure_bound: Cheeger–Müller–Schrader (1984), Theorem 5.1 — curvature-measure convergence; status: external theorem, axiomatized"
  , "special_quadratic: stronger O(a²) action-convergence hypothesis; status: external hypothesis, axiomatized"
  , "ricci_convergence: Regge Ricci-scalar O(a²) convergence; status: external hypothesis, axiomatized"
  , "riemann_convergence: Regge holonomy / Riemann convergence; status: external hypothesis, axiomatized" ]

end ReggeConvergenceRegistry
end Gravity
end IndisputableMonolith