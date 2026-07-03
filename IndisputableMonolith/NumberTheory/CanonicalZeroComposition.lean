import IndisputableMonolith.NumberTheory.GenuineZetaPhaseFromRCL

/-!
  CanonicalZeroComposition.lean

  Pull the generic zero-composition law out of the RH edge.

  `ZeroCompositionWitness` currently packages two things:
  1. a calibrated d'Alembert law, and
  2. the assertion that this law evaluates to its minimum value at the zero's
     deviation.

  Item (1) is not RH-specific. It is the canonical cosh law already forced by
  the RS/d'Alembert/J-cost machinery. This module proves it once, then reduces
  the remaining genuine-phase composition bridge to item (2): the genuine zeta
  phase must hit the canonical minimum at the witnessed zero deviation.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace CanonicalZeroComposition

open IndisputableMonolith.Cost.FunctionalEquation
open GenuineZetaPhaseFromRCL

noncomputable section

/-! ## 1. The canonical zero-composition law -/

/-- The canonical zero-composition law is `H(t)=cosh(t)`. All fields are
discharged by the already-proved real d'Alembert/cosh theorem surface. -/
def canonicalZeroCompositionLaw : ZeroCompositionLaw where
  H := Real.cosh
  H_zero := by simp [Real.cosh_zero]
  continuous := Real.continuous_cosh
  dAlembert := by
    intro t u
    rw [Real.cosh_add, Real.cosh_sub]
    ring
  curvature := by
    simpa using cosh_second_deriv_eq 0
  smooth_hyp := cosh_dAlembert_smooth
  ode_hyp := cosh_dAlembert_to_ODE
  cont_hyp := cosh_satisfies_continuous
  diff_hyp := cosh_satisfies_differentiable
  bootstrap_hyp := cosh_satisfies_bootstrap

theorem canonicalZeroCompositionLaw_forces_cosh :
    ∀ t : ℝ, canonicalZeroCompositionLaw.H t = Real.cosh t := by
  intro t
  rfl

/-- The canonical zero-composition law attains value `1` exactly at zero
deviation. -/
theorem canonical_value_one_iff_zeroDeviation (ρ : ℂ) :
    canonicalZeroCompositionLaw.H (zeroDeviation ρ) = 1 ↔ OnCriticalLine ρ :=
  zeroCompositionLaw_forces_eta_zero canonicalZeroCompositionLaw ρ

/-- If a point's deviation evaluates to the canonical minimum, it has a
`ZeroCompositionWitness`. -/
def zeroCompositionWitness_of_canonical_min
    (ρ : ℂ)
    (hmin : canonicalZeroCompositionLaw.H (zeroDeviation ρ) = 1) :
    ZeroCompositionWitness ρ where
  law := canonicalZeroCompositionLaw
  value_at_deviation := hmin

/-! ## 2. Rewriting the genuine phase bridge around the canonical law -/

/-- A genuine phase package realizes the canonical minimum at the zero
deviation. This is the only remaining non-generic content after the canonical
law itself has been derived. -/
structure GenuinePhaseCanonicalMinimumCert
    (sensor : WitnessedDefectSensor) (gzfd : GenuineZetaPhaseFamilyData) where
  sensor_match : gzfd.sensor = sensor.toDefectSensor
  family_match : gzfd.phaseFamily.sensor = sensor.toDefectSensor
  canonical_minimum :
    canonicalZeroCompositionLaw.H (zeroDeviation sensor.rho) = 1

/-- A canonical-minimum certificate gives the previous genuine phase-composition
certificate. -/
def genuinePhaseCompositionCert_of_canonicalMinimum
    {sensor : WitnessedDefectSensor} {gzfd : GenuineZetaPhaseFamilyData}
    (cert : GenuinePhaseCanonicalMinimumCert sensor gzfd) :
    GenuinePhaseCompositionCert sensor gzfd where
  sensor_match := cert.sensor_match
  family_match := cert.family_match
  witness := zeroCompositionWitness_of_canonical_min sensor.rho cert.canonical_minimum

/-- The sharpened bridge: all generic d'Alembert/J-cost content has been
derived; the only remaining input is canonical-minimum realization by the
genuine zeta phase package. -/
structure GenuinePhaseCanonicalMinimumBridge where
  minimum_of_genuine_phase :
    ∀ (sensor : WitnessedDefectSensor) (zfd : ZetaPhaseFamilyData),
      zfd.sensor = sensor.toDefectSensor →
      zfd.phaseFamily.sensor = sensor.toDefectSensor →
        GenuinePhaseCanonicalMinimumCert sensor (genuineOfHonestPhase zfd)

/-- The canonical-minimum bridge implies the earlier genuine-composition
bridge. -/
def genuinePhaseCompositionBridge_of_canonicalMinimum
    (bridge : GenuinePhaseCanonicalMinimumBridge) :
    GenuinePhaseCompositionBridge where
  composition_of_genuine_phase := by
    intro sensor zfd hzsensor hzfamily
    exact genuinePhaseCompositionCert_of_canonicalMinimum
      (bridge.minimum_of_genuine_phase sensor zfd hzsensor hzfamily)

/-- Therefore a canonical-minimum bridge proves the witnessed RH core. -/
theorem witnessed_rh_from_canonicalMinimumBridge
    (bridge : GenuinePhaseCanonicalMinimumBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  witnessed_rh_from_genuinePhaseCompositionBridge
    (genuinePhaseCompositionBridge_of_canonicalMinimum bridge)

/-- Attack surface after the canonical law is derived: only the minimum
realization remains open. -/
structure CanonicalMinimumAttackSurface where
  genuine_surface : GenuineVectorCAttackSurface
  canonical_law : ZeroCompositionLaw
  canonical_law_is_cosh : ∀ t : ℝ, canonical_law.H t = Real.cosh t
  open_minimum_bridge : GenuinePhaseCanonicalMinimumBridge → Prop

noncomputable def canonicalMinimumAttackSurface : CanonicalMinimumAttackSurface where
  genuine_surface := genuineVectorCAttackSurface
  canonical_law := canonicalZeroCompositionLaw
  canonical_law_is_cosh := canonicalZeroCompositionLaw_forces_cosh
  open_minimum_bridge := fun _ => True

end

end CanonicalZeroComposition
end NumberTheory
end IndisputableMonolith
