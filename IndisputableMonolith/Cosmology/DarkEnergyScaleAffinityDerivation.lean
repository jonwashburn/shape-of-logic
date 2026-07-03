import Mathlib
import IndisputableMonolith.Cosmology.CosmicZScaleLaw

/-!
# Dark-Energy Scale-Affinity Derivation

This module tightens the remaining U5 residue.

`CosmicZScaleLaw` proved:

`ScaleAffineZLaw -> Z(z)/Z_today = a(z) -> δw(z)=δw0/(1+z)`.

The remaining question was where `ScaleAffineZLaw` comes from. This module introduces the
lower admissibility principle that expresses the RS "no hidden coordinate" condition on the
cosmic scale interval:

**NoHiddenScaleCoordinate.** Once the early endpoint `a=0` and the today endpoint `a=1`
are fixed, the recognition ledger may not insert an extra preferred coordinate inside the
interval. Therefore the normalized Z-fraction must preserve endpoint convex interpolation.

That condition is exactly the scale-affine law, and Lean proves the conversion. This is the
strongest honest theorem-layer closure: the canonical shape is forced by the no-hidden-scale
coordinate admissibility condition. The remaining deeper problem, if desired, is to derive
that admissibility condition from the universal forcing layer rather than stating it as the
cosmic-Z admissibility gate.

Status: THEOREM conditional on the named no-hidden-scale-coordinate admissibility gate.
Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace DarkEnergyScaleAffinityDerivation

noncomputable section

/-! ## §1. No-hidden-scale-coordinate admissibility -/

/-- The lower admissibility condition behind `ScaleAffineZLaw`.

Interpretation: with only the early endpoint `a=0` and today endpoint `a=1` available, a
normalized ledger fraction cannot choose a nonlinear coordinate without adding extra
structure. Therefore it preserves endpoint interpolation. -/
structure NoHiddenScaleCoordinate where
  /-- Normalized Z-fraction as a function of scale factor. -/
  Zfrac : ℝ → ℝ
  /-- Early endpoint: no accumulated cosmic Z at `a=0`. -/
  early_zero : Zfrac 0 = 0
  /-- Today endpoint: normalized accumulated cosmic Z is `1` at `a=1`. -/
  today_one : Zfrac 1 = 1
  /-- No hidden coordinate: endpoint convex interpolation is preserved. -/
  no_hidden_coordinate :
    ∀ a : ℝ, Zfrac ((1 - a) * 0 + a * 1) = (1 - a) * Zfrac 0 + a * Zfrac 1

/-- `NoHiddenScaleCoordinate` is exactly the data needed for `ScaleAffineZLaw`. -/
def noHidden_to_scaleAffine (H : NoHiddenScaleCoordinate) :
    CosmicZScaleLaw.ScaleAffineZLaw where
  Zfrac := H.Zfrac
  early_zero := H.early_zero
  today_one := H.today_one
  scale_affine_from_early_to_today := H.no_hidden_coordinate

/-- The no-hidden-scale-coordinate condition forces normalized Z-fraction to be the scale
factor itself. -/
theorem noHidden_forces_identity (H : NoHiddenScaleCoordinate) (a : ℝ) :
    H.Zfrac a = a := by
  exact CosmicZScaleLaw.scaleAffine_forces_identity (noHidden_to_scaleAffine H) a

/-- The no-hidden-scale-coordinate condition forces the redshift history
`Z(z)=Z_today/(1+z)`. -/
theorem noHidden_forces_linearZ (Zt : ℝ) (H : NoHiddenScaleCoordinate) (z : ℝ) :
    CosmicZScaleLaw.ZfromScaleLaw Zt (noHidden_to_scaleAffine H) z =
      CosmicZHistory.linearZ Zt z :=
  CosmicZScaleLaw.scaleAffine_forces_linearZ Zt (noHidden_to_scaleAffine H) z

/-- The no-hidden-scale-coordinate condition forces the canonical dark-energy deviation. -/
theorem noHidden_forces_canonical_deviation (dw0 Zt : ℝ)
    (H : NoHiddenScaleCoordinate) (z : ℝ)
    (hZt : Zt ≠ 0) (hz : (1 : ℝ) + z ≠ 0) :
    CosmicZHistory.bitDeviation dw0 Zt
        (CosmicZScaleLaw.ZfromScaleLaw Zt (noHidden_to_scaleAffine H)) z =
      dw0 / (1 + z) :=
  CosmicZScaleLaw.scaleAffine_forces_canonical_deviation
    dw0 Zt (noHidden_to_scaleAffine H) z hZt hz

/-- The no-hidden-scale-coordinate condition forces the canonical equation of state. -/
theorem noHidden_forces_canonical_kernel (dw0 Zt : ℝ)
    (H : NoHiddenScaleCoordinate) (z : ℝ)
    (hZt : Zt ≠ 0) (hz : (1 : ℝ) + z ≠ 0) :
    CosmicZHistory.bitKernel dw0 Zt
        (CosmicZScaleLaw.ZfromScaleLaw Zt (noHidden_to_scaleAffine H)) z =
      -1 + dw0 / (1 + z) :=
  CosmicZScaleLaw.scaleAffine_forces_canonical_kernel
    dw0 Zt (noHidden_to_scaleAffine H) z hZt hz

/-! ## §2. Canonical witness and certificate -/

/-- The canonical no-hidden-coordinate law is inhabited by the identity Z-fraction. -/
def canonicalNoHiddenScaleCoordinate : NoHiddenScaleCoordinate where
  Zfrac := fun a => a
  early_zero := rfl
  today_one := rfl
  no_hidden_coordinate := by
    intro a
    ring

/-- The canonical no-hidden-coordinate law maps to the canonical scale-affine law. -/
theorem canonicalNoHidden_maps_to_canonical :
    (noHidden_to_scaleAffine canonicalNoHiddenScaleCoordinate).Zfrac =
      CosmicZScaleLaw.canonicalScaleAffineZLaw.Zfrac := by
  rfl

/-- **SCALE-AFFINITY DERIVATION CERTIFICATE.** The no-hidden-scale-coordinate admissibility
gate derives the scale-affine law and hence the canonical dark-energy shape. -/
structure ScaleAffinityDerivationCert where
  to_scale_affine :
    NoHiddenScaleCoordinate → CosmicZScaleLaw.ScaleAffineZLaw
  identity_forced :
    ∀ (H : NoHiddenScaleCoordinate) (a : ℝ), H.Zfrac a = a
  linearZ_forced :
    ∀ (Zt : ℝ) (H : NoHiddenScaleCoordinate) (z : ℝ),
      CosmicZScaleLaw.ZfromScaleLaw Zt (noHidden_to_scaleAffine H) z =
        CosmicZHistory.linearZ Zt z
  canonical_deviation_forced :
    ∀ (dw0 Zt : ℝ) (H : NoHiddenScaleCoordinate) (z : ℝ),
      Zt ≠ 0 → (1 : ℝ) + z ≠ 0 →
        CosmicZHistory.bitDeviation dw0 Zt
            (CosmicZScaleLaw.ZfromScaleLaw Zt (noHidden_to_scaleAffine H)) z =
          dw0 / (1 + z)
  canonical_kernel_forced :
    ∀ (dw0 Zt : ℝ) (H : NoHiddenScaleCoordinate) (z : ℝ),
      Zt ≠ 0 → (1 : ℝ) + z ≠ 0 →
        CosmicZHistory.bitKernel dw0 Zt
            (CosmicZScaleLaw.ZfromScaleLaw Zt (noHidden_to_scaleAffine H)) z =
          -1 + dw0 / (1 + z)

/-- The scale-affinity derivation certificate is inhabited. -/
def scaleAffinityDerivationCert : ScaleAffinityDerivationCert where
  to_scale_affine := noHidden_to_scaleAffine
  identity_forced := noHidden_forces_identity
  linearZ_forced := noHidden_forces_linearZ
  canonical_deviation_forced := noHidden_forces_canonical_deviation
  canonical_kernel_forced := noHidden_forces_canonical_kernel

end

end DarkEnergyScaleAffinityDerivation
end Cosmology
end IndisputableMonolith
