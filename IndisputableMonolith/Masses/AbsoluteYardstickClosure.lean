import IndisputableMonolith.Masses.CrossSectorYardstickCertificate

/-!
# Absolute yardstick closure: the mass spectrum has exactly one dimensionful parameter

Build-spine item HLG-4.4 of `simulation/Reality_Simulation_Master_Plan.html`.

`CrossSectorYardstickCertificate` and `DisplayBridgeAlgebra` already close the yardstick ALGEBRA:
every sector yardstick transports from one coherence unit `E_coh = phi^-5` by the integer cube
offsets `(B_pow s, r0 s)`. This module states the consequence that answers the absolute-MeV-yardstick
question directly: the entire predicted mass spectrum has EXACTLY ONE dimensionful degree of freedom.

Concretely, every predicted mass factors as

  `predict_mass s r Z = E_coh * structuralFactor s r Z`,

where `structuralFactor s r Z = 2^(B_pow s) * phi^(r0 s + (r - 8) + gap Z)` is a pure dimensionless
number built only from (a) the cube-edge integer `B_pow s`, (b) the cube/wallpaper integer `r0 s`,
(c) the integer rung `r`, and (d) the gap function `gap Z`. None of these is a free dimensionful
parameter. Therefore:

* `mass_ratio_scale_free`: `E_coh` cancels in every mass ratio, so all ratios are parameter-free pure
  `(2, phi)`-power numbers (the empirically tested predictions);
* `rescale_all_masses`: rescaling the single calibration `E_coh -> c * E_coh` rescales EVERY mass by
  the same `c`, so the spectrum has a single common multiplicative scale;
* `sector_constants_are_cube_geometry`: the per-sector constants are the forced cube counts
  `B_pow Lepton = -(2 * E_passive) = -22`, `r0` from wallpaper + cube geometry, etc. (no per-sector
  fit).

Honest status: CONDITIONAL THEOREM. The factorization and the scale-freedom of ratios are
THEOREMS (the ratios are what the lepton/quark scorecards test, parameter-free). The single
dimensionful calibration `E_coh` in MeV is anchored to ONE measured input,
`Foundation.DimensionalBridgeStructural.E_coh_MeV = m_e_SI / phi^3` (approximately `0.121` MeV, one
phi-step from the golden quantum `J(phi)`); deriving `E_coh` from RS primitives with NO measured mass
is the open dimensional bridge, the same residual named in HLG-1.2 (`tau_0` SI calibration). What is
closed here is that the absolute MeV yardstick is ONE calibration shared by all four sectors, not one
parameter per sector and not one per particle.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace AbsoluteYardstickClosure

open Constants

noncomputable section

/-- The dimensionless structural factor of a predicted mass: everything except the single
coherence-unit calibration `E_coh`. It is built only from the cube integer `B_pow s`, the cube/
wallpaper integer `r0 s`, the integer rung `r`, and the gap function `gap Z`. -/
noncomputable def structuralFactor (s : Anchor.Sector) (r Z : ℤ) : ℝ :=
  (2 : ℝ) ^ (Anchor.B_pow s) *
    phi ^ ((Anchor.r0 s : ℝ) + ((r : ℝ) - 8) + RSBridge.gap Z)

/-- The single coherence-unit calibration is positive (`E_coh = phi^-5 > 0`). -/
theorem E_coh_pos : 0 < Anchor.E_coh := by
  have hφ : (0 : ℝ) < phi := Constants.phi_pos
  unfold Anchor.E_coh
  positivity

/-- The structural factor is strictly positive for every sector, rung, and charge index. -/
theorem structuralFactor_pos (s : Anchor.Sector) (r Z : ℤ) :
    0 < structuralFactor s r Z := by
  have hφ : (0 : ℝ) < phi := Constants.phi_pos
  unfold structuralFactor
  positivity

/-- **THE SINGLE-CALIBRATION FACTORIZATION.** Every predicted mass is the one coherence-unit
calibration `E_coh` times the dimensionless structural factor. So the dimensionful content of the
entire spectrum is carried by the single scalar `E_coh`, shared across all sectors. -/
theorem predict_mass_eq_Ecoh_mul_structural (s : Anchor.Sector) (r Z : ℤ) :
    MassLaw.predict_mass s r Z = Anchor.E_coh * structuralFactor s r Z := by
  have hφ : (0 : ℝ) < phi := Constants.phi_pos
  rw [DisplayBridgeAlgebra.predict_mass_eq_yardstick_gap_factor]
  unfold Anchor.yardstick structuralFactor
  rw [← Real.rpow_intCast phi (Anchor.r0 s)]
  rw [show (Anchor.r0 s : ℝ) + ((r : ℝ) - 8) + RSBridge.gap Z
        = (Anchor.r0 s : ℝ) + (((r : ℝ) - 8) + RSBridge.gap Z) from by ring]
  rw [Real.rpow_add hφ (Anchor.r0 s : ℝ) (((r : ℝ) - 8) + RSBridge.gap Z)]
  ring

/-- **MASS RATIOS ARE SCALE-FREE.** The calibration `E_coh` cancels in every mass ratio: the ratio of
any two predicted masses is a pure dimensionless `(2, phi)`-power number, independent of the absolute
scale. These ratios are exactly the parameter-free predictions the lepton and quark scorecards test. -/
theorem mass_ratio_scale_free
    (s₁ s₂ : Anchor.Sector) (r₁ Z₁ r₂ Z₂ : ℤ) :
    MassLaw.predict_mass s₁ r₁ Z₁ / MassLaw.predict_mass s₂ r₂ Z₂
      = structuralFactor s₁ r₁ Z₁ / structuralFactor s₂ r₂ Z₂ := by
  rw [predict_mass_eq_Ecoh_mul_structural s₁ r₁ Z₁,
      predict_mass_eq_Ecoh_mul_structural s₂ r₂ Z₂]
  exact mul_div_mul_left _ _ (ne_of_gt E_coh_pos)

/-- A predicted mass evaluated with an arbitrary calibration scalar in place of `E_coh`. -/
noncomputable def predictWithScale (c : ℝ) (s : Anchor.Sector) (r Z : ℤ) : ℝ :=
  c * structuralFactor s r Z

/-- The actual mass law is `predictWithScale` at the canonical calibration `E_coh`. -/
theorem predict_mass_eq_predictWithScale_Ecoh (s : Anchor.Sector) (r Z : ℤ) :
    MassLaw.predict_mass s r Z = predictWithScale Anchor.E_coh s r Z :=
  predict_mass_eq_Ecoh_mul_structural s r Z

/-- **ONE COMMON MULTIPLICATIVE SCALE.** Rescaling the single calibration `E_coh -> c * E_coh`
rescales EVERY predicted mass by the same factor `c`. So the whole spectrum slides on one
dimensionful knob; fixing any one mass fixes all of them. -/
theorem rescale_all_masses (c : ℝ) (s : Anchor.Sector) (r Z : ℤ) :
    predictWithScale (c * Anchor.E_coh) s r Z = c * MassLaw.predict_mass s r Z := by
  unfold predictWithScale
  rw [predict_mass_eq_Ecoh_mul_structural]
  ring

/-- **PER-SECTOR CONSTANTS ARE FORCED CUBE GEOMETRY.** The dyadic offsets `B_pow` and the φ-offsets
`r0` are the cube-edge / wallpaper integers, not fitted: lepton `B_pow = -(2 * E_passive) = -22`,
`r0 = 62`; up `B_pow = -1`, `r0 = 35`; down `B_pow = 23`, `r0 = -5`; electroweak `B_pow = 1`,
`r0 = 55`. So no sector contributes a free dimensionful parameter; only the shared `E_coh` does. -/
theorem sector_constants_are_cube_geometry :
    Anchor.B_pow Anchor.Sector.Lepton = -(2 * (Anchor.E_passive : ℤ)) ∧
      Anchor.B_pow Anchor.Sector.Lepton = -22 ∧
      Anchor.B_pow Anchor.Sector.UpQuark = -1 ∧
      Anchor.B_pow Anchor.Sector.DownQuark = 23 ∧
      Anchor.B_pow Anchor.Sector.Electroweak = 1 ∧
      Anchor.r0 Anchor.Sector.Lepton = 62 ∧
      Anchor.r0 Anchor.Sector.UpQuark = 35 ∧
      Anchor.r0 Anchor.Sector.DownQuark = -5 ∧
      Anchor.r0 Anchor.Sector.Electroweak = 55 :=
  ⟨rfl,
   Anchor.B_pow_Lepton_eq, Anchor.B_pow_UpQuark_eq, Anchor.B_pow_DownQuark_eq,
   Anchor.B_pow_Electroweak_eq,
   Anchor.r0_Lepton_eq, Anchor.r0_UpQuark_eq, Anchor.r0_DownQuark_eq, Anchor.r0_Electroweak_eq⟩

/-! ## Master certificate -/

/-- **Absolute yardstick closure certificate.** Bundles the single-dimensionful-parameter result:

* `single_scale_factorization`: every mass is `E_coh` times a dimensionless structural factor;
* `ratios_scale_free`: `E_coh` cancels in all ratios (the parameter-free tested predictions);
* `one_common_scale`: rescaling `E_coh` rescales all masses uniformly;
* `cube_geometry_constants`: the per-sector constants are forced cube integers;
* `coherence_unit`: the shared calibration is the forced `phi^-5`.

Honest tag: CONDITIONAL THEOREM. The factorization, ratio scale-freedom, and forced cube constants
are kernel theorems; the absolute MeV value of `E_coh` is the single open dimensional-bridge
calibration (`Foundation.DimensionalBridgeStructural`, shared with HLG-1.2). -/
structure AbsoluteYardstickClosureCert where
  single_scale_factorization :
    ∀ (s : Anchor.Sector) (r Z : ℤ),
      MassLaw.predict_mass s r Z = Anchor.E_coh * structuralFactor s r Z
  ratios_scale_free :
    ∀ (s₁ s₂ : Anchor.Sector) (r₁ Z₁ r₂ Z₂ : ℤ),
      MassLaw.predict_mass s₁ r₁ Z₁ / MassLaw.predict_mass s₂ r₂ Z₂
        = structuralFactor s₁ r₁ Z₁ / structuralFactor s₂ r₂ Z₂
  one_common_scale :
    ∀ (c : ℝ) (s : Anchor.Sector) (r Z : ℤ),
      predictWithScale (c * Anchor.E_coh) s r Z = c * MassLaw.predict_mass s r Z
  cube_geometry_constants :
    Anchor.B_pow Anchor.Sector.Lepton = -(2 * (Anchor.E_passive : ℤ)) ∧
      Anchor.B_pow Anchor.Sector.Lepton = -22 ∧
      Anchor.B_pow Anchor.Sector.UpQuark = -1 ∧
      Anchor.B_pow Anchor.Sector.DownQuark = 23 ∧
      Anchor.B_pow Anchor.Sector.Electroweak = 1 ∧
      Anchor.r0 Anchor.Sector.Lepton = 62 ∧
      Anchor.r0 Anchor.Sector.UpQuark = 35 ∧
      Anchor.r0 Anchor.Sector.DownQuark = -5 ∧
      Anchor.r0 Anchor.Sector.Electroweak = 55
  coherence_unit :
    Anchor.E_coh = phi ^ (-(5 : ℤ))

/-- The absolute yardstick closure certificate holds. -/
def absoluteYardstickClosureCert : AbsoluteYardstickClosureCert where
  single_scale_factorization := predict_mass_eq_Ecoh_mul_structural
  ratios_scale_free := mass_ratio_scale_free
  one_common_scale := rescale_all_masses
  cube_geometry_constants := sector_constants_are_cube_geometry
  coherence_unit := rfl

/-- **ONE-STATEMENT SUMMARY.** The absolute mass spectrum has exactly one dimensionful parameter: a
single calibration `E_coh` shared by all sectors, with every mass equal to `E_coh` times a forced
dimensionless cube-geometry factor, all ratios independent of `E_coh`, and a uniform rescaling under
`E_coh -> c * E_coh`. -/
theorem absolute_yardstick_one_statement :
    (∀ (s : Anchor.Sector) (r Z : ℤ),
        MassLaw.predict_mass s r Z = Anchor.E_coh * structuralFactor s r Z) ∧
      (∀ (s₁ s₂ : Anchor.Sector) (r₁ Z₁ r₂ Z₂ : ℤ),
        MassLaw.predict_mass s₁ r₁ Z₁ / MassLaw.predict_mass s₂ r₂ Z₂
          = structuralFactor s₁ r₁ Z₁ / structuralFactor s₂ r₂ Z₂) ∧
      (∀ (c : ℝ) (s : Anchor.Sector) (r Z : ℤ),
        predictWithScale (c * Anchor.E_coh) s r Z = c * MassLaw.predict_mass s r Z) :=
  ⟨predict_mass_eq_Ecoh_mul_structural, mass_ratio_scale_free, rescale_all_masses⟩

end

end AbsoluteYardstickClosure
end Masses
end IndisputableMonolith
