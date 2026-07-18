import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.WeightedHypersurfaceBracket

/-!
# Dynamic structure-function blocker for the background-weighted bracket

The exact theorem `bracket_HamW_HamW` puts a site-dependent weight in the
Dirac structure-function slot, and `weightedStructureSum_tendsto` carries its
smearing shape to the continuum.  Both results keep the weight fixed as the
phase-space point varies.  Full ADM gravity instead requires the inverse
spatial metric in that slot to vary with the canonical metric data.

This file certifies that distinction.  A fixed background weight represents a
phase-space-dependent inverse metric at every phase point only if that metric
is phase-space constant.  The positive two-site example
`concreteDynamicInverseMetric` is not constant, so no background weight can
represent it.  Thus the existing background-weighted bracket, despite its
exact lattice identity and continuum smearing reach, cannot by itself be the
full dynamic Dirac structure function.

No closure flag is changed.  `PhaseSpaceDependentHamiltonianConstruction`
names the missing Hamiltonian construction, and
`Gap5DynamicDiracAndHKTRigidityTarget` records that this construction and the
existing HKT rigidity statement are separate remaining obligations.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DynamicStructureFunctionBlocker

open HypersurfaceDeformation WeightedHypersurfaceBracket

noncomputable section

open Finset

variable {n : ℕ} [NeZero n]

/-! ## Exact fixed-background underdetermination -/

/-- A lattice inverse metric is phase-space constant when changing the
canonical data cannot change its value at any site. -/
def PhaseSpaceConstant (g : PhaseSpace n → ZMod n → ℝ) : Prop :=
  ∀ x y : PhaseSpace n, ∀ j : ZMod n, g x j = g y j

/-- A fixed site weight represents a candidate inverse metric at every
phase-space point when their values agree at every point and site. -/
def FixedBackgroundRepresents (w : ZMod n → ℝ)
    (g : PhaseSpace n → ZMod n → ℝ) : Prop :=
  ∀ x : PhaseSpace n, ∀ j : ZMod n, w j = g x j

/-- THEOREM. If one fixed background weight represents `g` at every
phase-space point, then `g` is phase-space constant. -/
theorem fixed_background_represents_only_constant
    (w : ZMod n → ℝ) (g : PhaseSpace n → ZMod n → ℝ)
    (h : FixedBackgroundRepresents w g) :
    PhaseSpaceConstant g := by
  intro x y j
  rw [← h x j, ← h y j]

/-- THEOREM (exact characterization). A candidate inverse metric admits one
fixed background representation at all phase points exactly when it is
phase-space constant. -/
theorem exists_fixed_background_iff_phaseSpaceConstant
    (g : PhaseSpace n → ZMod n → ℝ) :
    (∃ w : ZMod n → ℝ, FixedBackgroundRepresents w g) ↔
      PhaseSpaceConstant g := by
  constructor
  · rintro ⟨w, hw⟩
    exact fixed_background_represents_only_constant w g hw
  · intro hg
    let x₀ : PhaseSpace n := (fun _ => 0, fun _ => 0)
    refine ⟨g x₀, ?_⟩
    intro x j
    exact hg x₀ x j

/-! ## A concrete positive dynamic inverse metric on two sites -/

/-- MODEL. A positive inverse-metric candidate on the two-site phase space.
It depends on the configuration coordinate at each site. -/
def concreteDynamicInverseMetric (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  1 + (x.1 j) ^ 2

/-- The zero canonical point used to witness metric variation. -/
def zeroPhasePoint : PhaseSpace 2 :=
  (fun _ => 0, fun _ => 0)

/-- A canonical point with unit configuration and zero momentum. -/
def unitConfigurationPoint : PhaseSpace 2 :=
  (fun _ => 1, fun _ => 0)

/-- THEOREM. The concrete inverse-metric candidate is everywhere positive. -/
theorem concreteDynamicInverseMetric_pos
    (x : PhaseSpace 2) (j : ZMod 2) :
    0 < concreteDynamicInverseMetric x j := by
  unfold concreteDynamicInverseMetric
  positivity

/-- THEOREM. The concrete metric takes different values at two explicit
phase-space points on the two-site lattice. -/
theorem concreteDynamicInverseMetric_witness :
    concreteDynamicInverseMetric zeroPhasePoint (0 : ZMod 2) = 1 ∧
      concreteDynamicInverseMetric unitConfigurationPoint (0 : ZMod 2) = 2 := by
  norm_num [concreteDynamicInverseMetric, zeroPhasePoint, unitConfigurationPoint]

/-- THEOREM. The positive two-site metric candidate is genuinely
phase-space-dependent. -/
theorem concreteDynamicInverseMetric_not_constant :
    ¬ PhaseSpaceConstant concreteDynamicInverseMetric := by
  intro h
  have hEq := h zeroPhasePoint unitConfigurationPoint (0 : ZMod 2)
  have hw := concreteDynamicInverseMetric_witness
  rw [hw.1, hw.2] at hEq
  norm_num at hEq

/-- THEOREM (concrete no-go). No fixed two-site background weight represents
the concrete dynamic inverse metric at every phase-space point. -/
theorem no_fixed_background_represents_concrete
    (w : ZMod 2 → ℝ) :
    ¬ FixedBackgroundRepresents w concreteDynamicInverseMetric := by
  intro h
  exact concreteDynamicInverseMetric_not_constant
    (fixed_background_represents_only_constant w concreteDynamicInverseMetric h)

/-! ## What the current weighted bracket reaches -/

/-- The exact proposition proved by `bracket_HamW_HamW`: `HamW w` has fixed
background structure function `w` in its Hamiltonian-Hamiltonian bracket. -/
def HamWHasBackgroundStructureFunction (w : ZMod n → ℝ) : Prop :=
  ∀ (N M : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (HamW w N) (HamW w M) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1))
          * (w j * (x.2 (j + 1) * (x.1 (j + 1) - x.1 j)))

/-- THEOREM. The existing exact bracket theorem supplies the fixed-background
structure-function proposition. -/
theorem HamW_has_background_structure_function (w : ZMod n → ℝ) :
    HamWHasBackgroundStructureFunction w :=
  bracket_HamW_HamW w

/-- The continuum smearing reach of a fixed background profile `W`. -/
def BackgroundWeightedContinuumReach (W : ℝ → ℝ) : Prop :=
  ∀ (Wr S : ℝ → ℝ),
    ContinuousOn Wr (Set.Icc 0 1) →
    ContinuousOn S (Set.Icc 0 1) →
    Filter.Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.range N,
        W ((k : ℝ) / (N : ℝ)) *
          (Wr ((k : ℝ) / (N : ℝ)) * S ((k : ℝ) / (N : ℝ))))
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, W x * (Wr x * S x)))

/-- THEOREM. The existing quadrature theorem gives the full continuum
smearing reach for every continuous fixed background profile. -/
theorem background_weighted_continuum_reach
    (W : ℝ → ℝ) (hW : ContinuousOn W (Set.Icc 0 1)) :
    BackgroundWeightedContinuumReach W := by
  intro Wr S hWr hS
  exact weightedStructureSum_tendsto W Wr S hW hWr hS

/-! ## The missing dynamic Hamiltonian and HKT obligations -/

/-- OPEN TARGET. A Hamiltonian family whose exact Hamiltonian-Hamiltonian
bracket carries a genuinely phase-space-dependent inverse metric `g`.

The right side uses the same point-split momentum density as the current
background theorem, isolating the missing ingredient: constructing a
differentiable Hamiltonian whose bracket produces `g x j`, including all
derivative terms caused by the dependence of `g` on the canonical data. -/
structure PhaseSpaceDependentHamiltonianConstruction
    (g : PhaseSpace n → ZMod n → ℝ) where
  ham : (ZMod n → ℝ) → PhaseSpace n → ℝ
  ham_differentiable :
    ∀ N : ZMod n → ℝ, Differentiable ℝ (ham N)
  ham_ham :
    ∀ (N M : ZMod n → ℝ) (x : PhaseSpace n),
      bracket (ham N) (ham M) x
        = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1))
            * (g x j * (x.2 (j + 1) * (x.1 (j + 1) - x.1 j)))

/-- THEOREM. Every fixed `HamW` construction inhabits the dynamic target only
with the phase-space-constant metric `g x = w`.  This packages the exact
bracket theorem without promoting the background weight to a dynamic metric. -/
def backgroundHamiltonianConstruction (w : ZMod n → ℝ) :
    PhaseSpaceDependentHamiltonianConstruction
      (fun _ : PhaseSpace n => w) where
  ham := HamW w
  ham_differentiable := differentiable_HamW w
  ham_ham := by
    intro N M x
    exact bracket_HamW_HamW w N M x

/-- OPEN. The missing dynamic Dirac premise: a nonconstant inverse metric
together with a Hamiltonian construction whose exact bracket produces it. -/
def PhaseSpaceDependentDiracPremise (n : ℕ) [NeZero n] : Prop :=
  ∃ g : PhaseSpace n → ZMod n → ℝ,
    ¬ PhaseSpaceConstant g ∧
      Nonempty (PhaseSpaceDependentHamiltonianConstruction g)

/-- OPEN. Gap 5 requires both the phase-space-dependent Dirac construction
and an HKT rigidity theorem.  The current `HamW` theorem and its continuum
smearing result supply neither conjunct. -/
def Gap5DynamicDiracAndHKTRigidityTarget (n : ℕ) [NeZero n] : Prop :=
  PhaseSpaceDependentDiracPremise n ∧ HKTRigidityStatement n

/-- THEOREM (certified blocker). The present background-weighted family has
its exact bracket and continuum reach, but no choice of its fixed two-site
weight can represent the explicit positive dynamic metric at all phase
points. -/
theorem gap5_background_weight_blocker :
    (∀ w : ZMod 2 → ℝ, HamWHasBackgroundStructureFunction w) ∧
      (∀ W : ℝ → ℝ, ContinuousOn W (Set.Icc 0 1) →
        BackgroundWeightedContinuumReach W) ∧
      (∀ w : ZMod 2 → ℝ,
        ¬ FixedBackgroundRepresents w concreteDynamicInverseMetric) := by
  exact ⟨HamW_has_background_structure_function,
    background_weighted_continuum_reach,
    no_fixed_background_represents_concrete⟩

/-! ### Axiom receipts (expected: standard Mathlib basis only) -/

#print axioms fixed_background_represents_only_constant
#print axioms exists_fixed_background_iff_phaseSpaceConstant
#print axioms concreteDynamicInverseMetric_pos
#print axioms concreteDynamicInverseMetric_witness
#print axioms concreteDynamicInverseMetric_not_constant
#print axioms no_fixed_background_represents_concrete
#print axioms HamW_has_background_structure_function
#print axioms background_weighted_continuum_reach
#print axioms gap5_background_weight_blocker

end
end DynamicStructureFunctionBlocker
end SevenGaps
end Gravity
end IndisputableMonolith
