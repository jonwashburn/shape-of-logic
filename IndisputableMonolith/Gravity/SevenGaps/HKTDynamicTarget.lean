import IndisputableMonolith.Gravity.SevenGaps.HypersurfaceDeformation
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureFunctionBlocker

/-!
# Wave C2 R5/R6 groundwork: widened HKT target with dynamic structure function

Definition module (no hard proofs). Codex adjudication rejected folding g into
momDensity and selling frozen unit structure as GR. Widened target carries an
explicit structureFunction slot with structure_nonconstant.

HKTRigidityStatementDyn is DEFINED, neither proved nor assumed. Original
HKTRigidityStatement is false as stated at n=1
(HKTOneSiteCounterexample.not_HKTRigidityStatement_one).

**Unsplit `mom_ham` is uninhabitable for honest nearest-neighbor local
profiles against the frozen quadratic Hamiltonian.** The field below keeps the
classical unsplit advection form as a falsification-adjacent record. The scoped
no-go
`HKTPointSplitTarget.unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam`
shows that at `n = 2` no Frechet-smooth local momentum profile
`f(d, π_j, π_{j+1})` can satisfy it against the frozen quadratic Hamiltonian
(forced singular relation `(π₀+π₁)∂_d f = π₀²+d²`). The HamDyn-level analogue is
the open Prop `UnsplitMomHamNoSmoothNearestNeighborWitnessHamDyn`. The
schema-only weak sibling is `HKTPointSplitTarget.HKTPointSplitTargetDyn`; the
load-bearing class is `HKTPointSplitStrong.HKTPointSplitTargetDynStrong` with
binding Prop `HKTRigidityStatementPointSplitDynN2Strong`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTDynamicTarget

open HypersurfaceDeformation DynamicStructureFunctionBlocker

noncomputable section

variable {n : ℕ} [NeZero n]

/-- OPEN TARGET (deliberately uninhabited). HKT hypotheses with explicit dynamic
structure function. structure_nonconstant excludes the frozen/background decoy. -/
structure HojmanKucharTeitelboimTargetDyn (n : ℕ) [NeZero n] where
  hamDensity : PhaseSpace n → ZMod n → ℝ
  momDensity : PhaseSpace n → ZMod n → ℝ
  structureFunction : PhaseSpace n → ZMod n → ℝ
  ham_differentiable : ∀ N : ZMod n → ℝ,
    Differentiable ℝ (fun x : PhaseSpace n => ∑ j : ZMod n, N j * hamDensity x j)
  mom_differentiable : ∀ w : ZMod n → ℝ,
    Differentiable ℝ (fun x : PhaseSpace n => ∑ j : ZMod n, w j * momDensity x j)
  structure_nonconstant : ¬ PhaseSpaceConstant structureFunction
  ham_local : ∀ (x y : PhaseSpace n) (j : ZMod n),
    x.1 j = y.1 j → x.1 (j + 1) = y.1 (j + 1) → x.2 j = y.2 j →
      hamDensity x j = hamDensity y j
  ham_covariant : ∀ (x : PhaseSpace n) (a j : ZMod n),
    hamDensity (fun i => x.1 (i + a), fun i => x.2 (i + a)) j = hamDensity x (j + a)
  structure_local : ∀ (x y : PhaseSpace n) (j : ZMod n),
    x.1 j = y.1 j → structureFunction x j = structureFunction y j
  mom_mom : ∀ (v w : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, v j * momDensity y j)
      (fun y => ∑ j : ZMod n, w j * momDensity y j) x = 0
  mom_ham : ∀ (w N : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, w j * momDensity y j)
      (fun y => ∑ j : ZMod n, N j * hamDensity y j) x
      = ∑ j : ZMod n, (w j * (N (j + 1) - N j)) * hamDensity x j
  ham_ham : ∀ (N M : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, N j * hamDensity y j)
      (fun y => ∑ j : ZMod n, M j * hamDensity y j) x
      = ∑ j : ZMod n,
          (N j * M (j + 1) - M j * N (j + 1)) *
            (structureFunction x j * momDensity x j)

/-- DEFINED, neither proved nor assumed. Repaired GR-strength rigidity target. -/
def HKTRigidityStatementDyn (n : ℕ) [NeZero n] : Prop :=
  ∀ T : HojmanKucharTeitelboimTargetDyn n,
    ∃ cKin cGrad cVac : ℝ, ∀ (x : PhaseSpace n) (j : ZMod n),
      T.hamDensity x j
        = cKin * (x.2 j * x.2 j)
          + cGrad *
              (T.structureFunction x j *
                ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))
          + cVac

def unitStructureHamHamRHS (momDensity : PhaseSpace n → ZMod n → ℝ)
    (N M : ZMod n → ℝ) (x : PhaseSpace n) : ℝ :=
  ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1)) * ((1 : ℝ) * momDensity x j)

theorem unitStructure_recovers_original_ham_ham_RHS
    (momDensity : PhaseSpace n → ZMod n → ℝ) (N M : ZMod n → ℝ)
    (x : PhaseSpace n) :
    unitStructureHamHamRHS momDensity N M x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1)) * momDensity x j := by
  unfold unitStructureHamHamRHS
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem unitStructure_is_phaseSpaceConstant :
    PhaseSpaceConstant (fun (_x : PhaseSpace n) (_j : ZMod n) => (1 : ℝ)) := by
  intro x y j
  rfl

structure HKTDynamicTargetStatus where
  dynTargetDefined : Bool
  dynRigidityDefined : Bool
  unitStructureDecoyExcluded : Bool
  dynInhabitantBanked : Bool
  gap5ConstraintRecovery : Bool

def hktDynamicTargetStatus : HKTDynamicTargetStatus where
  dynTargetDefined := true
  dynRigidityDefined := true
  unitStructureDecoyExcluded := true
  dynInhabitantBanked := false
  gap5ConstraintRecovery := false

theorem hktDynamicTargetStatus_flags :
    hktDynamicTargetStatus.dynTargetDefined = true ∧
      hktDynamicTargetStatus.dynRigidityDefined = true ∧
        hktDynamicTargetStatus.unitStructureDecoyExcluded = true ∧
          hktDynamicTargetStatus.dynInhabitantBanked = false ∧
            hktDynamicTargetStatus.gap5ConstraintRecovery = false := by
  decide

end
end HKTDynamicTarget
end SevenGaps
end Gravity
end IndisputableMonolith
