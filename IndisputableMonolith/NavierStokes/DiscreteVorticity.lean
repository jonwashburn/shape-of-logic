import Mathlib
import IndisputableMonolith.NavierStokes.PhiLadderCutoff

/-!
# Discrete Vorticity Bookkeeping

This module packages the discrete objects needed for the J-cost monotonicity
program. The emphasis is on exact bookkeeping:

- finite vorticity fields on a lattice window,
- total / RMS / normalized amplitudes,
- transport / viscous / stretching contribution fields,
- exact decomposition of the J-cost derivative into those three pieces.

The hard PDE inequalities are intentionally separated from this bookkeeping
surface so they can be added one lemma at a time.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace DiscreteVorticity

open PhiLadderCutoff

noncomputable section

/-- A finite discrete vorticity field on a lattice window of `siteCount` sites. -/
structure State (siteCount : ℕ) where
  omega : Fin siteCount → ℝ

/-- Sum of a scalar field over the finite lattice window. -/
def total {siteCount : ℕ} (f : Fin siteCount → ℝ) : ℝ :=
  ∑ i : Fin siteCount, f i

/-- RMS square of a scalar field. -/
def rmsSq {siteCount : ℕ} (f : Fin siteCount → ℝ) : ℝ :=
  total (fun i => (f i) ^ 2) / siteCount

/-- RMS amplitude of a scalar field. -/
def rms {siteCount : ℕ} (f : Fin siteCount → ℝ) : ℝ :=
  Real.sqrt (rmsSq f)

/-- Pointwise normalized amplitude relative to the RMS scale. -/
def normalizedAmplitude {siteCount : ℕ} (f : Fin siteCount → ℝ) (i : Fin siteCount) : ℝ :=
  |f i| / rms f

/-- The total J-cost of a discrete vorticity field relative to its RMS scale. -/
def totalJcost {siteCount : ℕ} (f : Fin siteCount → ℝ) : ℝ :=
  total (fun i => Jcost (normalizedAmplitude f i))

/-- Contribution fields appearing in the J-cost derivative identity. -/
structure ContributionFields (siteCount : ℕ) where
  transport : Fin siteCount → ℝ
  viscous : Fin siteCount → ℝ
  stretching : Fin siteCount → ℝ

/-- Total contributions of the three pieces. -/
def totalTransport {siteCount : ℕ} (c : ContributionFields siteCount) : ℝ :=
  total c.transport

def totalViscous {siteCount : ℕ} (c : ContributionFields siteCount) : ℝ :=
  total c.viscous

def totalStretching {siteCount : ℕ} (c : ContributionFields siteCount) : ℝ :=
  total c.stretching

/-- Data recording an exact J-cost derivative split. -/
structure EvolutionIdentity (siteCount : ℕ) where
  contributions : ContributionFields siteCount
  dJdt : ℝ
  split :
    dJdt = totalTransport contributions
      + totalViscous contributions
      + totalStretching contributions

/-- If the transport contribution has zero total, it cancels exactly. -/
theorem transport_term_cancels {siteCount : ℕ} (c : ContributionFields siteCount)
    (htransport : totalTransport c = 0) :
    totalTransport c = 0 := htransport

/-- If every viscous contribution is nonpositive, then the total viscous term is
nonpositive. -/
theorem viscous_term_dissipative {siteCount : ℕ} (c : ContributionFields siteCount)
    (hvisc : ∀ i : Fin siteCount, c.viscous i ≤ 0) :
    totalViscous c ≤ 0 := by
  unfold totalViscous total
  exact Finset.sum_nonpos (fun i _ => hvisc i)

/-- If every stretching contribution is nonnegative, then the total stretching
term is nonnegative. -/
theorem stretching_term_nonneg {siteCount : ℕ} (c : ContributionFields siteCount)
    (hstretch : ∀ i : Fin siteCount, 0 ≤ c.stretching i) :
    0 ≤ totalStretching c := by
  unfold totalStretching total
  exact Finset.sum_nonneg (fun i _ => hstretch i)

/-- A pointwise transport field with zero entries has zero total. -/
theorem zero_transport_cancels {siteCount : ℕ} (c : ContributionFields siteCount)
    (hzero : ∀ i : Fin siteCount, c.transport i = 0) :
    totalTransport c = 0 := by
  unfold totalTransport total
  simp [hzero]

/-- The exact derivative identity can be rewritten after transport cancellation. -/
theorem dJdt_eq_viscous_plus_stretching {siteCount : ℕ} (e : EvolutionIdentity siteCount)
    (htransport : totalTransport e.contributions = 0) :
    e.dJdt = totalViscous e.contributions + totalStretching e.contributions := by
  rw [e.split, htransport, zero_add]

/-- If stretching is absorbed by viscosity, then the total derivative is nonpositive. -/
theorem dJdt_nonpos_of_transport_cancel_and_absorption
    {siteCount : ℕ} (e : EvolutionIdentity siteCount)
    (htransport : totalTransport e.contributions = 0)
    (habsorb :
      totalStretching e.contributions ≤ - totalViscous e.contributions) :
    e.dJdt ≤ 0 := by
  rw [dJdt_eq_viscous_plus_stretching e htransport]
  linarith

end

end DiscreteVorticity
end NavierStokes
end IndisputableMonolith
