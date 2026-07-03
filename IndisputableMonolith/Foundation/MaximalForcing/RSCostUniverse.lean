import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure
import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.CostUniqueness

/-!
# Maximal Forcing: the cost-layer realization (Phase 1 + Phase 2.1)

This is the first concrete instantiation of the maximal-forcing scaffold. It
roots the program in an existing, published, sorry-free uniqueness theorem
rather than a fresh assumption.

* The realization carrier is a candidate recognition cost `F : ℝ → ℝ`.
* Admissibility is the conjunction of the five gate conditions that the Law of
  Logic imposes on any cost (reciprocal symmetry, normalization, the Recognition
  Composition Law, calibration, continuity). The `AczelSmoothnessPackage`
  instance is supplied by `Cost.AczelProof`, so it is a proved instance, not an
  added hypothesis.
* The claim placed under closure is "F equals the canonical cost J on the
  positive reals."

Phase 2.1 then discharges `Forced Lcost isJClaim` by wrapping
`law_of_logic_forces_jcost`. This proves the forced-register pattern end to end:
a real theorem of RS becomes a `ForcedInvariant` over an admissible class.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Cost.FunctionalEquation

/-- Admissibility for the cost-function layer: a candidate cost `F : ℝ → ℝ`
satisfies the five gate conditions that the Law of Logic imposes on any
recognition cost. -/
def CostAdmissible (F : ℝ → ℝ) : Prop :=
  IsReciprocalCost F ∧ IsNormalized F ∧ SatisfiesCompositionLaw F ∧
    IsCalibrated F ∧ ContinuousOn F (Set.Ioi 0)

/-- Loosest cost class `L0`: continuous candidate costs on the positive reals. -/
def L0 : AdmissibilityClass (ℝ → ℝ) where
  admissible := { F | ContinuousOn F (Set.Ioi 0) }
  label := "continuous candidate costs on (0,∞)"

/-- Gate-tightened cost class `Lcost`: candidates satisfying all five gate
conditions. -/
def Lcost : AdmissibilityClass (ℝ → ℝ) where
  admissible := { F | CostAdmissible F }
  label := "cost-gate conditions (reciprocal, normalized, RCL, calibrated, continuous)"

/-- `Lcost` is a tightening of `L0`: every gate-admissible cost is in particular
a continuous candidate cost. The strictness witness is deferred. -/
def tighten_L0_Lcost : Tightening L0 Lcost where
  subset := by
    intro F hF
    exact hF.2.2.2.2
  strict_witness := True

/-- The forced claim of the cost layer: `F` equals the canonical cost `J` on the
positive reals. -/
def isJClaim : RealityClaim (ℝ → ℝ) where
  label := "F = Jcost on (0,∞)"
  holds := fun F => ∀ x : ℝ, 0 < x → F x = Cost.Jcost x

/-- The cost-layer claim universe: realizations are candidate cost functions,
admissibility is the gate class, and the claim under closure is `isJClaim`. -/
def costUniverse : ClaimUniverse where
  Realization := ℝ → ℝ
  admissibility := Lcost
  claims := { isJClaim }

/-- **Phase 2.1.** Over the gate class, "equals `J`" is forced. This wraps the
published uniqueness theorem `law_of_logic_forces_jcost` with no new content and
no new axioms: the `AczelSmoothnessPackage` instance comes from `Cost.AczelProof`.
-/
theorem forced_isJ : Forced Lcost.admissible isJClaim := by
  intro F hF x hx
  obtain ⟨hRecip, hNorm, hComp, hCalib, hCont⟩ := hF
  exact law_of_logic_forces_jcost F hRecip hNorm hComp hCalib hCont x hx

/-- The claim `isJClaim` is in the closure of the cost universe. -/
theorem isJClaim_in_closure :
    InClosure Primitive.lawOfLogic costUniverse isJClaim := by
  show isJClaim ∈ costUniverse.claims
  exact Set.mem_singleton _

/-- **Forced-register entry.** `isJClaim`, rooted at the Law-of-Logic primitive,
with a real proof of forcedness. This is the first populated slot of the Phase 2
forced register. -/
def isJForcedInvariant : ForcedInvariant Primitive.lawOfLogic costUniverse where
  claim := isJClaim
  in_closure := isJClaim_in_closure
  forced := forced_isJ

/-- The cost-layer universe is fully classified: its single claim is forced,
hence the (transitional) classifier is total over its closure. -/
theorem costUniverse_classifier :
    ∀ C : RealityClaim costUniverse.Realization,
      InClosure Primitive.lawOfLogic costUniverse C → ClaimClassification costUniverse C := by
  intro C hC
  have hCeq : C = isJClaim := by
    have : C ∈ costUniverse.claims := hC
    exact Set.mem_singleton_iff.mp this
  subst hCeq
  exact ClaimClassification.forced forced_isJ

/-- A real `MaximalClosureCert` for the cost-layer universe: every claim in its
closure is classified. This discharges `maximal_forcing_closure` unconditionally
for `costUniverse`. -/
def costUniverseCert : MaximalClosureCert Primitive.lawOfLogic costUniverse where
  classifies := costUniverse_classifier

/-! ## Phase 3 / Phase 5: the gate tightening does real work

The risk flagged in the execution plan is cheap tightening: if `Lcost` did not
actually change any classification, the forcing result would be cosmetic. The
following shows the `L0 → Lcost` tightening is effective for `isJClaim`. Over the
loose class `L0` (continuous candidate costs), "equals J" is *independent*: the
canonical cost `J` satisfies it, but the constant-zero cost (also continuous)
does not. The gate conditions are what force `J`, not relabeling. -/

/-- Over the loose class `L0`, "equals J" is independent: `Jcost` is a continuous
candidate cost that satisfies it, and the constant-zero function is a continuous
candidate cost that does not. -/
theorem isJ_independent_over_L0 : Independent L0.admissible isJClaim := by
  refine ⟨Cost.Jcost, (fun _ => (0 : ℝ)), ?_, ?_, ?_, ?_⟩
  · show ContinuousOn Cost.Jcost (Set.Ioi 0)
    exact IndisputableMonolith.CostUniqueness.Jcost_continuous_pos
  · show ContinuousOn (fun _ => (0 : ℝ)) (Set.Ioi 0)
    exact continuousOn_const
  · intro x _; rfl
  · intro h
    have h2 := h 2 (by norm_num)
    simp only [Cost.Jcost] at h2
    norm_num at h2

/-- **The tightening is legitimate, not cheap.** `isJClaim` is independent over
`L0` but forced over `Lcost`. The gate conditions do real classificatory work:
they convert a free claim into a forced one. This is the per-step legitimacy
evidence the Phase 5 ladder requires for the `L0 → Lcost` rung. -/
theorem tightening_L0_Lcost_effective :
    Independent L0.admissible isJClaim ∧ Forced Lcost.admissible isJClaim :=
  ⟨isJ_independent_over_L0, forced_isJ⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
