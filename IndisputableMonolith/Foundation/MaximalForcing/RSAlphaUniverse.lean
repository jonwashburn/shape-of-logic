import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Maximal Forcing: the alpha layer (Phase 2 extension, fine-structure constant)

Fourth concrete instantiation, reaching a physics-adjacent quantity rather than a
structural primitive. NB this layer forces a WINDOW (band containment) of the RS
**construction value**, not the measured constant: the seed 44π = 4π·11 is an
identification, not a derived coupling, so the exact infrared α⁻¹(0) = 137.035999
remains a boundary condition, OPEN (see `Verification.EMAlphaCert`). What is forced
here is precisely "the construction lands in the CODATA-bracketing window," which
is a real, non-vacuous claim about the parameter-free formula, not a derivation of α.

* The realization carrier is a candidate inverse fine-structure value `a : ℝ`.
* The loose class `Lalpha0` is every candidate real.
* The gate class `LalphaRS` pins `a` to the RS construction value
  `alphaInv = 44π · exp(-w8·ln φ / 44π)` (no fitted parameters; seed 44π OPEN).
* The claim under closure is "a lies in the CODATA-bracketing window
  (137.030, 137.039)."

Over `LalphaRS`, the window claim is forced, wrapping the proved interval bounds
`Numerics.alphaInv_gt` and `Numerics.alphaInv_lt`. Over `Lalpha0` it is
independent: the RS construction value is in the window, but `0` is not. The RS
assembly does real work; the window is forced by the parameter-free construction,
even though the construction itself is not a derivation of the measured α.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Constants (alphaInv)
open IndisputableMonolith.Numerics (alphaInv_gt alphaInv_lt)

/-- Loosest alpha class `Lalpha0`: every candidate value. -/
def Lalpha0 : AdmissibilityClass ℝ where
  admissible := Set.univ
  label := "every candidate inverse-coupling value"

/-- Gate-tightened alpha class `LalphaRS`: the candidate equals the RS-assembled
inverse fine-structure value. -/
def LalphaRS : AdmissibilityClass ℝ where
  admissible := { a | a = alphaInv }
  label := "RS-assembled inverse coupling: a = 44π·exp(-w8·ln φ/44π)"

/-- `LalphaRS` is a tightening of `Lalpha0`. -/
def tighten_Lalpha0_LalphaRS : Tightening Lalpha0 LalphaRS where
  subset := by
    intro a _
    trivial
  strict_witness := True

/-- The forced claim of the alpha layer: the value lies in the CODATA-bracketing
window `(137.030, 137.039)`. -/
def isAlphaWindowClaim : RealityClaim ℝ where
  label := "137.030 < a < 137.039"
  holds := fun a => (137.030 : ℝ) < a ∧ a < (137.039 : ℝ)

/-- The alpha-layer claim universe. -/
def alphaUniverse : ClaimUniverse where
  Realization := ℝ
  admissibility := LalphaRS
  claims := { isAlphaWindowClaim }

/-- **Alpha window as a forced invariant.** Over the RS-assembly gate, the value
lies in `(137.030, 137.039)`. Wraps the proved bounds; the only external content
is interval arithmetic, no fitted parameter. -/
theorem forced_alphaWindow : Forced LalphaRS.admissible isAlphaWindowClaim := by
  intro a ha
  have ha' : a = alphaInv := ha
  subst ha'
  exact ⟨alphaInv_gt, alphaInv_lt⟩

/-- The claim `isAlphaWindowClaim` is in the closure of the alpha universe. -/
theorem isAlphaWindowClaim_in_closure :
    InClosure Primitive.lawOfLogic alphaUniverse isAlphaWindowClaim := by
  show isAlphaWindowClaim ∈ alphaUniverse.claims
  exact Set.mem_singleton _

/-- Forced-register entry for the fine-structure window. -/
def alphaForcedInvariant : ForcedInvariant Primitive.lawOfLogic alphaUniverse where
  claim := isAlphaWindowClaim
  in_closure := isAlphaWindowClaim_in_closure
  forced := forced_alphaWindow

/-- The alpha-layer universe is fully classified. -/
theorem alphaUniverse_classifier :
    ∀ C : RealityClaim alphaUniverse.Realization,
      InClosure Primitive.lawOfLogic alphaUniverse C → ClaimClassification alphaUniverse C := by
  intro C hC
  have hCeq : C = isAlphaWindowClaim := Set.mem_singleton_iff.mp hC
  subst hCeq
  exact ClaimClassification.forced forced_alphaWindow

/-- A real `MaximalClosureCert` for the alpha-layer universe. -/
def alphaUniverseCert : MaximalClosureCert Primitive.lawOfLogic alphaUniverse where
  classifies := alphaUniverse_classifier

/-! ## The RS-assembly gate does real work -/

/-- Over the loose class `Lalpha0`, the window claim is independent: the RS value
satisfies it, and `0` does not. -/
theorem alphaWindow_independent_over_Lalpha0 :
    Independent Lalpha0.admissible isAlphaWindowClaim := by
  refine ⟨alphaInv, 0, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · exact ⟨alphaInv_gt, alphaInv_lt⟩
  · intro h
    have h1 : (137.030 : ℝ) < 0 := h.1
    norm_num at h1

/-- **The RS-assembly tightening is legitimate, not cheap.** The window claim is
independent over `Lalpha0` but forced over `LalphaRS`. -/
theorem tightening_Lalpha0_LalphaRS_effective :
    Independent Lalpha0.admissible isAlphaWindowClaim ∧
    Forced LalphaRS.admissible isAlphaWindowClaim :=
  ⟨alphaWindow_independent_over_Lalpha0, forced_alphaWindow⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
