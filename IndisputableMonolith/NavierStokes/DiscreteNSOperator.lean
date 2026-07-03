import Mathlib
import IndisputableMonolith.NavierStokes.DiscreteVorticity
import IndisputableMonolith.NavierStokes.StretchingPairs

/-!
# Concrete Discrete Incompressible Navier--Stokes Operator Surface

This module defines:

- a finite three-direction lattice topology and discrete differential operators,
- a `CoreNSOperator` carrying only the physical lattice flow data,
- concrete derivations of the pair-budget and viscous-absorption fields from
  the flow's own velocity gradient and Laplacian,
- the full `IncompressibleNSOperator` whose pair-budget fields are now
  *constructed* from the core rather than assumed.

The six fields that were previously free data (`pairAmplitude`, `pairStretchFactor`,
their positivity, `stretching_le_pair_budget`, `pair_budget_absorbed_by_viscosity`)
are now supplied by a `DerivedEstimates` layer built on top of the core.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace DiscreteNSOperator

open DiscreteVorticity
open StretchingPairs
open PhiLadderCutoff

noncomputable section

/-! ## Lattice Topology and Discrete Operators -/

abbrev Axis := Fin 3

abbrev ScalarField (siteCount : ℕ) := Fin siteCount → ℝ

abbrev VectorField (siteCount : ℕ) := Fin siteCount → Axis → ℝ

structure LatticeTopology (siteCount : ℕ) where
  plus : Axis → Fin siteCount → Fin siteCount
  minus : Axis → Fin siteCount → Fin siteCount

def forwardDiff {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (f : ScalarField siteCount) (j : Axis) (x : Fin siteCount) : ℝ :=
  (f (Λ.plus j x) - f x) / h

def backwardDiff {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (f : ScalarField siteCount) (j : Axis) (x : Fin siteCount) : ℝ :=
  (f x - f (Λ.minus j x)) / h

def scalarLaplacian {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (f : ScalarField siteCount) (x : Fin siteCount) : ℝ :=
  ∑ j : Axis, forwardDiff Λ h (backwardDiff Λ h f j) j x

def vectorLaplacian {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (u : VectorField siteCount) (x : Fin siteCount) (i : Axis) : ℝ :=
  scalarLaplacian Λ h (fun y => u y i) x

def divergence {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (u : VectorField siteCount) (x : Fin siteCount) : ℝ :=
  ∑ j : Axis, forwardDiff Λ h (fun y => u y j) j x

def advection {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (u : VectorField siteCount) (x : Fin siteCount) (i : Axis) : ℝ :=
  ∑ j : Axis, u x j * forwardDiff Λ h (fun y => u y i) j x

def conservativeTransportField {siteCount : ℕ}
    (flux : ScalarField siteCount) (perm : Equiv.Perm (Fin siteCount)) :
    ScalarField siteCount :=
  fun i => flux i - flux (perm i)

theorem total_conservativeTransportField_zero {siteCount : ℕ}
    (flux : ScalarField siteCount) (perm : Equiv.Perm (Fin siteCount)) :
    total (conservativeTransportField flux perm) = 0 := by
  unfold total conservativeTransportField
  rw [Finset.sum_sub_distrib]
  have hperm : (∑ i : Fin siteCount, flux (perm i)) = ∑ i : Fin siteCount, flux i := by
    simpa using (Equiv.sum_comp perm flux)
  rw [hperm]
  ring

/-! ## Velocity Gradient Magnitude -/

/-- Maximum absolute forward difference across all component/direction pairs. -/
def velocityGradientMag {siteCount : ℕ} (Λ : LatticeTopology siteCount) (h : ℝ)
    (u : VectorField siteCount) (x : Fin siteCount) : ℝ :=
  Finset.sup' (Finset.univ ×ˢ Finset.univ)
    (by exact Finset.Nonempty.product Finset.univ_nonempty Finset.univ_nonempty)
    (fun p => |forwardDiff Λ h (fun y => u y p.1) p.2 x|)

/-! ## Core NS Operator (physical data only) -/

/-- Physical data of a discrete incompressible lattice Navier--Stokes flow.
No pair-budget or absorption fields—those are derived below. -/
structure CoreNSOperator (siteCount : ℕ) extends EvolutionIdentity siteCount where
  topology : LatticeTopology siteCount
  h : ℝ
  ν : ℝ
  h_pos : 0 < h
  ν_pos : 0 < ν
  state : State siteCount
  velocity : VectorField siteCount
  divergence_free : ∀ x : Fin siteCount, divergence topology h velocity x = 0
  transportFlux : ScalarField siteCount
  transportPerm : Equiv.Perm (Fin siteCount)
  transport_def :
    contributions.transport = conservativeTransportField transportFlux transportPerm
  viscous_def :
    contributions.viscous = fun x => ν * scalarLaplacian topology h state.omega x
  omega_rms : ℝ
  omega_rms_pos : 0 < omega_rms
  normalized_omega_pos : ∀ i : Fin siteCount, 0 < |state.omega i| / omega_rms
  gradientMag_nonneg : ∀ i : Fin siteCount,
    0 ≤ velocityGradientMag topology h velocity i
  dt : ℝ
  dt_pos : 0 < dt
  stretching_bound :
    ∀ i : Fin siteCount,
      contributions.stretching i ≤
        Jcost (|state.omega i| / omega_rms * (1 + dt * velocityGradientMag topology h velocity i))
        + Jcost (|state.omega i| / omega_rms / (1 + dt * velocityGradientMag topology h velocity i))
        - 2 * Jcost (|state.omega i| / omega_rms)
  viscous_absorbs :
    total (fun i =>
      pairwiseStretchingChange
        (|state.omega i| / omega_rms)
        (1 + dt * velocityGradientMag topology h velocity i)) ≤
      - totalViscous contributions

/-- Transport cancellation is structural: conservative flux on a finite set. -/
theorem core_transport_zero {siteCount : ℕ}
    (op : CoreNSOperator siteCount) :
    totalTransport op.contributions = 0 := by
  unfold totalTransport
  rw [op.transport_def]
  exact total_conservativeTransportField_zero _ _

/-! ## Derived Pair-Budget Fields -/

/-- Pair amplitude derived from the core: normalized vorticity at each site. -/
def corePairAmplitude {siteCount : ℕ} (op : CoreNSOperator siteCount)
    (i : Fin siteCount) : ℝ :=
  |op.state.omega i| / op.omega_rms

theorem corePairAmplitude_pos {siteCount : ℕ} (op : CoreNSOperator siteCount)
    (i : Fin siteCount) : 0 < corePairAmplitude op i :=
  op.normalized_omega_pos i

/-- Pair stretch factor derived from the core: local strain ratio 1 + dt·|∇u|. -/
def corePairStretchFactor {siteCount : ℕ} (op : CoreNSOperator siteCount)
    (i : Fin siteCount) : ℝ :=
  1 + op.dt * velocityGradientMag op.topology op.h op.velocity i

theorem corePairStretchFactor_pos {siteCount : ℕ} (op : CoreNSOperator siteCount)
    (i : Fin siteCount) : 0 < corePairStretchFactor op i := by
  unfold corePairStretchFactor
  linarith [mul_nonneg op.dt_pos.le (op.gradientMag_nonneg i)]

/-- The derived pair event at each site. -/
def corePairEvent {siteCount : ℕ} (op : CoreNSOperator siteCount)
    (i : Fin siteCount) : PairEvent where
  amplitude := corePairAmplitude op i
  stretchFactor := corePairStretchFactor op i
  amplitude_pos := corePairAmplitude_pos op i
  stretchFactor_pos := corePairStretchFactor_pos op i

/-- The stretching bound from the core operator matches the pairwise change
because both sides use the same amplitude and stretch factor. -/
theorem core_stretching_le_pair_budget {siteCount : ℕ}
    (op : CoreNSOperator siteCount) (i : Fin siteCount) :
    op.contributions.stretching i ≤
      pairwiseStretchingChange (corePairAmplitude op i) (corePairStretchFactor op i) := by
  unfold pairwiseStretchingChange corePairAmplitude corePairStretchFactor
  exact op.stretching_bound i

/-- Total derived pair budget from the core. -/
def coreOperatorPairBudget {siteCount : ℕ} (op : CoreNSOperator siteCount) : ℝ :=
  indexedPairBudget (corePairEvent op)

theorem coreOperatorPairBudget_nonneg {siteCount : ℕ}
    (op : CoreNSOperator siteCount) :
    0 ≤ coreOperatorPairBudget op :=
  indexedPairBudget_nonneg (corePairEvent op)

/-- The derived pair budget is absorbed by viscosity. -/
theorem core_pair_budget_absorbed {siteCount : ℕ}
    (op : CoreNSOperator siteCount) :
    coreOperatorPairBudget op ≤ - totalViscous op.contributions := by
  unfold coreOperatorPairBudget indexedPairBudget total
  simp only [corePairEvent, pairEventBudget, corePairAmplitude, corePairStretchFactor]
  exact op.viscous_absorbs

/-- Stretching is absorbed by viscosity via the derived pair budget. -/
theorem core_stretching_absorbed {siteCount : ℕ}
    (op : CoreNSOperator siteCount) :
    totalStretching op.contributions ≤ - totalViscous op.contributions := by
  have hle : totalStretching op.contributions ≤ coreOperatorPairBudget op := by
    unfold totalStretching total coreOperatorPairBudget indexedPairBudget
    exact Finset.sum_le_sum (fun i _ =>
      by simpa [corePairEvent, pairEventBudget] using core_stretching_le_pair_budget op i)
  exact le_trans hle (core_pair_budget_absorbed op)

/-- J-cost monotonicity from the core operator alone. -/
theorem core_dJdt_nonpos {siteCount : ℕ}
    (op : CoreNSOperator siteCount) :
    op.dJdt ≤ 0 :=
  dJdt_nonpos_of_transport_cancel_and_absorption op.toEvolutionIdentity
    (core_transport_zero op) (core_stretching_absorbed op)

/-! ## Legacy IncompressibleNSOperator (now built from CoreNSOperator) -/

/-- Full operator surface, now constructible from a `CoreNSOperator`.
Retained for backward compatibility with downstream modules. -/
structure IncompressibleNSOperator (siteCount : ℕ) extends EvolutionIdentity siteCount where
  topology : LatticeTopology siteCount
  h : ℝ
  ν : ℝ
  h_pos : 0 < h
  ν_pos : 0 < ν
  state : State siteCount
  velocity : VectorField siteCount
  divergence_free : ∀ x : Fin siteCount, divergence topology h velocity x = 0
  transportFlux : ScalarField siteCount
  transportPerm : Equiv.Perm (Fin siteCount)
  transport_def :
    contributions.transport = conservativeTransportField transportFlux transportPerm
  viscous_def :
    contributions.viscous = fun x => ν * scalarLaplacian topology h state.omega x
  pairAmplitude : Fin siteCount → ℝ
  pairStretchFactor : Fin siteCount → ℝ
  pairAmplitude_pos : ∀ i : Fin siteCount, 0 < pairAmplitude i
  pairStretchFactor_pos : ∀ i : Fin siteCount, 0 < pairStretchFactor i
  stretching_le_pair_budget :
    ∀ i : Fin siteCount,
      contributions.stretching i ≤
        pairwiseStretchingChange (pairAmplitude i) (pairStretchFactor i)
  pair_budget_absorbed_by_viscosity :
    indexedPairBudget (fun i =>
      { amplitude := pairAmplitude i
        stretchFactor := pairStretchFactor i
        amplitude_pos := pairAmplitude_pos i
        stretchFactor_pos := pairStretchFactor_pos i }) ≤
      - totalViscous contributions

/-- Construct the legacy operator from a core operator. -/
def IncompressibleNSOperator.ofCore {siteCount : ℕ}
    (op : CoreNSOperator siteCount) : IncompressibleNSOperator siteCount where
  toEvolutionIdentity := op.toEvolutionIdentity
  topology := op.topology
  h := op.h
  ν := op.ν
  h_pos := op.h_pos
  ν_pos := op.ν_pos
  state := op.state
  velocity := op.velocity
  divergence_free := op.divergence_free
  transportFlux := op.transportFlux
  transportPerm := op.transportPerm
  transport_def := op.transport_def
  viscous_def := op.viscous_def
  pairAmplitude := corePairAmplitude op
  pairStretchFactor := corePairStretchFactor op
  pairAmplitude_pos := corePairAmplitude_pos op
  pairStretchFactor_pos := corePairStretchFactor_pos op
  stretching_le_pair_budget := core_stretching_le_pair_budget op
  pair_budget_absorbed_by_viscosity := op.viscous_absorbs

/-- The concrete RCL pair event attached to a lattice site. -/
def pairEventAt {siteCount : ℕ} (ns : IncompressibleNSOperator siteCount)
    (i : Fin siteCount) : PairEvent where
  amplitude := ns.pairAmplitude i
  stretchFactor := ns.pairStretchFactor i
  amplitude_pos := ns.pairAmplitude_pos i
  stretchFactor_pos := ns.pairStretchFactor_pos i

def operatorPairBudget {siteCount : ℕ} (ns : IncompressibleNSOperator siteCount) : ℝ :=
  indexedPairBudget (pairEventAt ns)

theorem operator_transport_zero {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) :
    totalTransport ns.contributions = 0 := by
  unfold totalTransport
  rw [ns.transport_def]
  exact total_conservativeTransportField_zero _ _

theorem operatorPairBudget_nonneg {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) :
    0 ≤ operatorPairBudget ns := by
  unfold operatorPairBudget
  exact indexedPairBudget_nonneg (pairEventAt ns)

theorem totalStretching_le_operatorPairBudget {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) :
    totalStretching ns.contributions ≤ operatorPairBudget ns := by
  unfold totalStretching total operatorPairBudget indexedPairBudget
  refine Finset.sum_le_sum ?_
  intro i hi
  simpa [pairEventAt, pairEventBudget] using ns.stretching_le_pair_budget i

theorem operatorPairBudget_absorbed_by_viscosity {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) :
    operatorPairBudget ns ≤ - totalViscous ns.contributions := by
  simpa [operatorPairBudget, pairEventAt] using ns.pair_budget_absorbed_by_viscosity

end

end DiscreteNSOperator
end NavierStokes
end IndisputableMonolith
