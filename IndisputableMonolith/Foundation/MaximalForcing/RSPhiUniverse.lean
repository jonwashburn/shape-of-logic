import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Maximal Forcing: the phi-layer realization (Phase 2 expansion, T6)

Second concrete instantiation. It shows the forced-register pattern generalizes
beyond the cost layer to the next link of the chain (T6: phi forced by
self-similarity).

* The realization carrier is a candidate scale ratio `r : ℝ`.
* The loose class `Lphi0` is just the positive reals.
* The gate class `LphiGold` adds the golden constraint `r^2 = r + 1`.
* The claim under closure is "r equals the golden ratio phi."

Over `LphiGold`, "r = phi" is forced (wrapping `PhiForcing.phi_unique_self_similar`).
Over `Lphi0`, it is independent (phi satisfies it, but `r = 1` is a positive
candidate that does not). So the golden-constraint tightening does real work, the
same legitimacy evidence the cost layer produced for the gate conditions.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Foundation.PhiForcing

/-- Admissibility for the phi layer: a positive candidate ratio satisfying the
golden constraint `r^2 = r + 1`. -/
def PhiAdmissible (r : ℝ) : Prop :=
  0 < r ∧ satisfies_golden_constraint r

/-- Loosest phi class `Lphi0`: positive candidate ratios. -/
def Lphi0 : AdmissibilityClass ℝ where
  admissible := { r | 0 < r }
  label := "positive candidate ratios"

/-- Gate-tightened phi class `LphiGold`: positive ratios satisfying the golden
constraint. -/
def LphiGold : AdmissibilityClass ℝ where
  admissible := { r | PhiAdmissible r }
  label := "positive ratios with golden constraint r^2 = r + 1"

/-- `LphiGold` is a tightening of `Lphi0`. -/
def tighten_Lphi0_LphiGold : Tightening Lphi0 LphiGold where
  subset := by
    intro r hr
    exact hr.1
  strict_witness := True

/-- The forced claim of the phi layer: `r` equals the golden ratio. -/
def isPhiClaim : RealityClaim ℝ where
  label := "r = φ"
  holds := fun r => r = φ

/-- The phi-layer claim universe. -/
def phiUniverse : ClaimUniverse where
  Realization := ℝ
  admissibility := LphiGold
  claims := { isPhiClaim }

/-- **T6 as a forced invariant.** Over the gate class, "r = phi" is forced. Wraps
`PhiForcing.phi_unique_self_similar` with no new content. -/
theorem forced_isPhi : Forced LphiGold.admissible isPhiClaim := by
  intro r hr
  obtain ⟨hpos, hgold⟩ := hr
  exact phi_unique_self_similar hpos hgold

/-- The claim `isPhiClaim` is in the closure of the phi universe. -/
theorem isPhiClaim_in_closure :
    InClosure Primitive.lawOfLogic phiUniverse isPhiClaim := by
  show isPhiClaim ∈ phiUniverse.claims
  exact Set.mem_singleton _

/-- Forced-register entry for T6. -/
def isPhiForcedInvariant : ForcedInvariant Primitive.lawOfLogic phiUniverse where
  claim := isPhiClaim
  in_closure := isPhiClaim_in_closure
  forced := forced_isPhi

/-- The phi-layer universe is fully classified. -/
theorem phiUniverse_classifier :
    ∀ C : RealityClaim phiUniverse.Realization,
      InClosure Primitive.lawOfLogic phiUniverse C → ClaimClassification phiUniverse C := by
  intro C hC
  have hCeq : C = isPhiClaim := Set.mem_singleton_iff.mp hC
  subst hCeq
  exact ClaimClassification.forced forced_isPhi

/-- A real `MaximalClosureCert` for the phi-layer universe. -/
def phiUniverseCert : MaximalClosureCert Primitive.lawOfLogic phiUniverse where
  classifies := phiUniverse_classifier

/-! ## The golden-constraint tightening does real work -/

/-- Over the loose class `Lphi0`, "r = phi" is independent: `phi` is a positive
candidate that satisfies it, and `1` is a positive candidate that does not. -/
theorem isPhi_independent_over_Lphi0 : Independent Lphi0.admissible isPhiClaim := by
  refine ⟨φ, 1, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) < φ
    exact phi_pos
  · show (0 : ℝ) < 1
    norm_num
  · rfl
  · intro h
    have h1 : (1 : ℝ) = φ := h
    exact (ne_of_lt phi_gt_one) h1

/-- **The golden-constraint tightening is legitimate, not cheap.** `isPhiClaim`
is independent over `Lphi0` but forced over `LphiGold`. -/
theorem tightening_Lphi0_LphiGold_effective :
    Independent Lphi0.admissible isPhiClaim ∧ Forced LphiGold.admissible isPhiClaim :=
  ⟨isPhi_independent_over_Lphi0, forced_isPhi⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
