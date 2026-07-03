import Mathlib
import IndisputableMonolith.NavierStokes.PhiLadderCutoff

/-!
# Lattice FRC Bridge

This module closes the logical loop between the lattice φ-ladder cutoff result
and the conditional-completion route from the Navier--Stokes regularity paper.

The key point is that on a finite RS lattice the normalized vorticity ratio
`ω_max / ω_rms` is automatically finite-volume controlled. This supplies a
finite recognition-cost bound, which can then be fed into any abstract
conditional-completion route of the form

`FRC -> injection_damping -> direction_constancy -> rigid_rotation_veto -> regularity`.

The PDE-heavy steps remain external to this module; what is formalized here is
the exact logical bridge from the lattice cutoff theorem to the hypothesis used
by the conditional paper.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace FRCBridge

open PhiLadderCutoff

noncomputable section

/-! ## Finite-volume lattice profile -/

/-- A finite-volume vorticity profile on an RS lattice.

`siteCount` is the number of active lattice sites in the finite window.
`omegaMax` and `omegaRms` package the relevant scale information.
The field `finiteVolumeControl` is the finite-volume norm-equivalence input:
on a finite lattice, pointwise amplitude is controlled by `sqrt(siteCount)` times
the RMS scale. -/
structure FiniteVolumeProfile where
  siteCount : ℕ
  siteCount_pos : 0 < siteCount
  omegaMax : ℝ
  omegaRms : ℝ
  omegaRms_pos : 0 < omegaRms
  omegaRms_le_max : omegaRms ≤ omegaMax
  finiteVolumeControl : omegaMax ≤ Real.sqrt siteCount * omegaRms

/-- The normalized ratio used by the lattice FRC bridge. -/
def normalizedRatio (s : FiniteVolumeProfile) : ℝ :=
  s.omegaMax / s.omegaRms

theorem normalizedRatio_pos (s : FiniteVolumeProfile) : 0 < normalizedRatio s := by
  unfold normalizedRatio
  exact div_pos (lt_of_lt_of_le s.omegaRms_pos s.omegaRms_le_max) s.omegaRms_pos

theorem normalizedRatio_ge_one (s : FiniteVolumeProfile) : 1 ≤ normalizedRatio s := by
  unfold normalizedRatio
  exact (one_le_div s.omegaRms_pos).2 s.omegaRms_le_max

theorem normalizedRatio_le_sqrt_siteCount (s : FiniteVolumeProfile) :
    normalizedRatio s ≤ Real.sqrt s.siteCount := by
  unfold normalizedRatio
  rw [div_le_iff₀ s.omegaRms_pos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using s.finiteVolumeControl

/-! ## Bounding J-cost on the lattice -/

/-- On the half-line `[1, ∞)`, the canonical cost is bounded by the identity.

This is the simple estimate needed for the finite-volume FRC bound:
`J(x) = (x + x⁻¹)/2 - 1 ≤ x` whenever `x ≥ 1`. -/
theorem Jcost_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Jcost x ≤ x := by
  unfold Jcost
  have hinv_one : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hinv_le : x⁻¹ ≤ x := le_trans hinv_one hx
  linarith

/-- The explicit finite-volume recognition-cost bound on the RS lattice. -/
theorem finiteVolume_Jcost_bound (s : FiniteVolumeProfile) :
    Jcost (normalizedRatio s) ≤ Real.sqrt s.siteCount := by
  have h₁ : 1 ≤ normalizedRatio s := normalizedRatio_ge_one s
  have h₂ : Jcost (normalizedRatio s) ≤ normalizedRatio s :=
    Jcost_le_self_of_one_le h₁
  exact le_trans h₂ (normalizedRatio_le_sqrt_siteCount s)

/-- Strong lattice FRC: the cost is bounded by the explicit finite-volume constant
`sqrt(siteCount)`. -/
def RSLatticeFRC (s : FiniteVolumeProfile) : Prop :=
  Jcost (normalizedRatio s) ≤ Real.sqrt s.siteCount

/-- Weak lattice FRC: there exists some finite bound. -/
def LatticeFRC (s : FiniteVolumeProfile) : Prop :=
  ∃ B : ℝ, Jcost (normalizedRatio s) ≤ B

theorem frc_holds_on_RS_lattice (s : FiniteVolumeProfile) : RSLatticeFRC s :=
  finiteVolume_Jcost_bound s

theorem frc_holds_on_RS_lattice_exists (s : FiniteVolumeProfile) : LatticeFRC s :=
  ⟨Real.sqrt s.siteCount, frc_holds_on_RS_lattice s⟩

/-! ## Abstract conditional-completion route -/

/-- Abstract interface for the conditional-completion route.

This isolates the heavy PDE part of the argument while making the logical bridge
fully explicit in Lean. -/
structure ConditionalCompletionRoute (α : Type) where
  FRC : α → Prop
  InjectionDamping : α → Prop
  DirectionConstancy : α → Prop
  RigidRotationVeto : α → Prop
  Regularity : α → Prop
  frc_to_injectionDamping : ∀ a, FRC a → InjectionDamping a
  injectionDamping_to_directionConstancy : ∀ a, InjectionDamping a → DirectionConstancy a
  directionConstancy_to_rigidRotationVeto : ∀ a, DirectionConstancy a → RigidRotationVeto a
  rigidRotationVeto_to_regularity : ∀ a, RigidRotationVeto a → Regularity a

/-- Once FRC is known on the lattice, any conditional-completion route closes. -/
theorem close_conditional_loop {α : Type} (route : ConditionalCompletionRoute α) {a : α}
    (hFRC : route.FRC a) : route.Regularity a := by
  have hID : route.InjectionDamping a := route.frc_to_injectionDamping a hFRC
  have hDC : route.DirectionConstancy a :=
    route.injectionDamping_to_directionConstancy a hID
  have hRR : route.RigidRotationVeto a :=
    route.directionConstancy_to_rigidRotationVeto a hDC
  exact route.rigidRotationVeto_to_regularity a hRR

/-- A regularity certificate obtained by running the conditional route on a
finite RS lattice profile. -/
structure LatticeRegularityCertificate
    (route : ConditionalCompletionRoute FiniteVolumeProfile)
    (profile : FiniteVolumeProfile) where
  frcBound : ℝ
  frcBound_nonneg : 0 ≤ frcBound
  frcProof : RSLatticeFRC profile
  injectionDamping : route.InjectionDamping profile
  directionConstancy : route.DirectionConstancy profile
  rigidRotationVeto : route.RigidRotationVeto profile
  regularity : route.Regularity profile

/-- The lattice FRC theorem is enough to instantiate the conditional route. -/
theorem lattice_regular_via_direction_constancy
    (route : ConditionalCompletionRoute FiniteVolumeProfile)
    (profile : FiniteVolumeProfile)
    (hFRCBridge : ∀ s : FiniteVolumeProfile, RSLatticeFRC s → route.FRC s) :
    route.Regularity profile := by
  apply close_conditional_loop route
  exact hFRCBridge profile (frc_holds_on_RS_lattice profile)

/-! ## Packaged certificate -/

/-- The full logical closure package for the lattice-to-conditional bridge. -/
structure FRCBridgeCert where
  frc_on_lattice :
    ∀ s : FiniteVolumeProfile, RSLatticeFRC s
  frc_exists_bound :
    ∀ s : FiniteVolumeProfile, LatticeFRC s
  conditional_loop :
    ∀ (route : ConditionalCompletionRoute FiniteVolumeProfile)
      (profile : FiniteVolumeProfile),
      (∀ s : FiniteVolumeProfile, RSLatticeFRC s → route.FRC s) →
      route.Regularity profile

/-- The lattice FRC bridge certificate. -/
def frcBridgeCert : FRCBridgeCert where
  frc_on_lattice := frc_holds_on_RS_lattice
  frc_exists_bound := frc_holds_on_RS_lattice_exists
  conditional_loop := fun route profile hFRCBridge =>
    lattice_regular_via_direction_constancy route profile hFRCBridge

end

end FRCBridge
end NavierStokes
end IndisputableMonolith
