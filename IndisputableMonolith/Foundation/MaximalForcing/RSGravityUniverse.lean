import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure
import IndisputableMonolith.Constants

/-!
# Maximal Forcing: the gravity layer (Phase 2 extension, Einstein coupling)

Fifth single-constant instantiation, reaching the gravitational sector. Where the
alpha layer pins the electromagnetic coupling, this layer pins the gravitational
one: the Einstein field-equation coupling `κ = 8πG/c⁴`, evaluated in RS-native
units (`λ_rec = c = 1`, `ℏ = φ⁻⁵`), is forced to the pure number `8·φ⁵` with no
fitted parameter.

* The realization carrier is a candidate Einstein-coupling value `k : ℝ`.
* The loose class `Lgrav0` is every candidate real.
* The gate class `LgravRS` pins `k` to the RS-native value `kappa_einstein`.
* The claim under closure is "k = 8·φ⁵".

Over `LgravRS` the value claim is forced, wrapping the proved
`Constants.kappa_einstein_eq`. Over `Lgrav0` it is independent: the RS value
satisfies it, `0` does not (`8φ⁵ > 0`). The RS derivation of `G` from
`λ_rec, c, ℏ` does real work; the value `8φ⁵` is not assumed, it is forced.

This is the gravitational analogue of `RSAlphaUniverse`: a derived physical
coupling forced to a parameter-free φ-expression.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Constants (phi kappa_einstein kappa_einstein_eq kappa_einstein_pos)

/-- Loosest gravity class `Lgrav0`: every candidate coupling value. -/
def Lgrav0 : AdmissibilityClass ℝ where
  admissible := Set.univ
  label := "every candidate Einstein-coupling value"

/-- Gate-tightened gravity class `LgravRS`: the candidate equals the RS-native
Einstein coupling `8πG/c⁴`. -/
def LgravRS : AdmissibilityClass ℝ where
  admissible := { k | k = kappa_einstein }
  label := "RS-native Einstein coupling: k = 8πG/c⁴"

/-- `LgravRS` is a tightening of `Lgrav0`. -/
def tighten_Lgrav0_LgravRS : Tightening Lgrav0 LgravRS where
  subset := by intro a _; trivial
  strict_witness := True

/-- The forced claim of the gravity layer: the coupling equals `8·φ⁵`. -/
def isKappaClaim : RealityClaim ℝ where
  label := "k = 8·φ^5 (Einstein coupling, parameter-free)"
  holds := fun k => k = 8 * phi ^ (5 : ℝ)

/-- The gravity-layer claim universe. -/
def gravUniverse : ClaimUniverse where
  Realization := ℝ
  admissibility := LgravRS
  claims := { isKappaClaim }

/-- **Einstein coupling as a forced invariant.** Over the RS-native gate, the
coupling equals `8·φ⁵`. Wraps `Constants.kappa_einstein_eq`; the only content is
the parameter-free RS derivation `G = λ_rec²c³/(πℏ)` with `ℏ = φ⁻⁵`. -/
theorem forced_kappa : Forced LgravRS.admissible isKappaClaim := by
  intro k hk
  have hk' : k = kappa_einstein := hk
  show k = 8 * phi ^ (5 : ℝ)
  rw [hk', kappa_einstein_eq]

/-- The claim `isKappaClaim` is in the closure of the gravity universe. -/
theorem isKappaClaim_in_closure :
    InClosure Primitive.lawOfLogic gravUniverse isKappaClaim := by
  show isKappaClaim ∈ gravUniverse.claims
  exact Set.mem_singleton _

/-- Forced-register entry for the Einstein coupling. -/
def gravForcedInvariant : ForcedInvariant Primitive.lawOfLogic gravUniverse where
  claim := isKappaClaim
  in_closure := isKappaClaim_in_closure
  forced := forced_kappa

/-- The gravity-layer universe is fully classified. -/
theorem gravUniverse_classifier :
    ∀ C : RealityClaim gravUniverse.Realization,
      InClosure Primitive.lawOfLogic gravUniverse C → ClaimClassification gravUniverse C := by
  intro C hC
  have hCeq : C = isKappaClaim := Set.mem_singleton_iff.mp hC
  subst hCeq
  exact ClaimClassification.forced forced_kappa

/-- A real `MaximalClosureCert` for the gravity-layer universe. -/
def gravUniverseCert : MaximalClosureCert Primitive.lawOfLogic gravUniverse where
  classifies := gravUniverse_classifier

/-! ## The RS-native gate does real work -/

/-- The forced value is strictly positive: `8φ⁵ > 0`. -/
theorem kappa_value_pos : 0 < 8 * phi ^ (5 : ℝ) := by
  rw [← kappa_einstein_eq]; exact kappa_einstein_pos

/-- Over the loose class `Lgrav0`, the value claim is independent: the RS coupling
satisfies it, and `0` does not. -/
theorem kappa_independent_over_Lgrav0 :
    Independent Lgrav0.admissible isKappaClaim := by
  refine ⟨kappa_einstein, 0, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · show kappa_einstein = 8 * phi ^ (5 : ℝ); exact kappa_einstein_eq
  · intro h
    have h0 : (0 : ℝ) = 8 * phi ^ (5 : ℝ) := h
    have hp := kappa_value_pos
    linarith

/-- **The RS-native tightening is legitimate, not cheap.** The value claim is
independent over `Lgrav0` but forced over `LgravRS`. -/
theorem tightening_Lgrav0_LgravRS_effective :
    Independent Lgrav0.admissible isKappaClaim ∧
    Forced LgravRS.admissible isKappaClaim :=
  ⟨kappa_independent_over_Lgrav0, forced_kappa⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
