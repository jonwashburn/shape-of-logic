import Mathlib
import IndisputableMonolith.Recognition.Certification
import IndisputableMonolith.RSBridge.Anchor

/-!
# AnchorPolicy Certified Interface (no RG-in-Lean required)

This module provides a **remedy** for the fact that `Physics/AnchorPolicy.lean` treats the
Standard-Model RG residue as an axiom/interface.

Instead of asserting a global axiom

  `|f_residue f μ⋆ - gap(ZOf f)| < 1e-6`

we express the dependency as a *certificate*: an externally produced table of residue intervals
(`Ires`) plus charge-wise gap intervals (`Igap`) with a validity proof. Lean can then derive:

  - per-species closeness to `gap(Z)` (inequality form),
  - equal-Z degeneracy bounds,

without assuming an equality axiom.

What this does **not** do: it does not implement the SM RG kernels/integration in Lean. It only
makes the dependency explicit and machine-checkable once you provide certified bounds from an
external computation (e.g. a Python audit).
-/

namespace IndisputableMonolith.Physics
namespace AnchorPolicyCertified

noncomputable section
open Classical

open IndisputableMonolith.Recognition.Certification
open IndisputableMonolith.RSBridge

/-! ## Specialize the generic certification schema to RSBridge fermions -/

abbrev Species : Type := Fermion

abbrev Z (f : Species) : Int := ZOf f

abbrev Fgap (z : Int) : ℝ := gap z

/-! ## Main certified consequences -/

/-- If an external certificate bounds the per-species residues at the anchor, then every species'
residue is close to the closed-form display `gap(Z)` (inequality form). -/
theorem anchor_identity_from_cert
    (C : AnchorCert Species)
    (hC : Valid Z Fgap C)
    (resAtAnchor : Species → ℝ)
    (hres : ∀ f, memI (C.Ires f) (resAtAnchor f)) :
    ∀ f : Species, |resAtAnchor f - Fgap (Z f)| ≤ 2 * C.eps (Z f) := by
  -- Directly reuse the generic lemma.
  simpa [Species, Z, Fgap] using
    (anchorIdentity_cert (Z := Z) (Fgap := Fgap) (C := C) hC resAtAnchor hres)

/-- Equal-Z degeneracy bound from a certificate: if two species share the same Z, their residues
must lie within the certified band. -/
theorem equalZ_residue_from_cert
    (C : AnchorCert Species)
    (hC : Valid Z Fgap C)
    (resAtAnchor : Species → ℝ)
    (hres : ∀ f, memI (C.Ires f) (resAtAnchor f))
    {f g : Species} (hZ : Z f = Z g) :
    |resAtAnchor f - resAtAnchor g| ≤ 2 * C.eps (Z f) := by
  simpa [Species, Z, Fgap] using
    (equalZ_residue_of_cert (Z := Z) (Fgap := Fgap) (C := C) hC resAtAnchor hres hZ)

end

end AnchorPolicyCertified
end IndisputableMonolith.Physics
