/-
  PrimitiveRecognitionCalculus/DeltaRealCalibration.lean

  Phase 4 of the Delta-Native Analysis frontier: calibration from one act.

  The δ-forced cost form is the faithful one-parameter gauge family (log
  coordinates) `cosh(c·t) − 1`, `c > 0`. The calibration question is whether δ
  forces `c = 1` (the canonical J), i.e. whether the unit of scale is derived
  rather than chosen.

  The earlier modules resolved this NEGATIVELY at the discrete carrier:
  `PRCCalibrationTarget` and `PRCCalibrationIndependence` prove the family is a
  faithful torsor under positive rescaling, that the only invariant is the
  log-curvature `c²` at the unit, and that the discrete carrier ℚδ cannot fix it
  because curvature is a second-derivative (continuum) property.

  This module records the honest reading the `ℝδ` interface forces. The one-act
  log-curvature is exactly a continuum-interface datum: it is read at the limit
  ratio `x → 1`, which lives in the protocol layer of `DeltaReal`, not in the
  discrete rational carrier. So:

  * `unit_forced_by_one_act` : at the continuum interface, the single normalization
    "one-act curvature = 1" forces `c = 1`;
  * `discrete_does_not_force_unit` : the family is faithful and transitively
    rescaled, a one-real torsor, so without that one datum the unit is free;
  * `calibration_is_one_continuum_act` : the headline. `λ = 1` is forced by exactly
    one continuum-interface recognition act (the one-act curvature normalization),
    and by nothing in the discrete δ data. The residual gauge is one real, removed
    by one datum.

  Second-pass closure:

  * `NormalizedOneActInterface` packages the minimum extra interface datum needed
    to close calibration.
  * `normalized_interface_forces_J` proves that any such interface selects the
    canonical member.
  * `calibration_datum_necessary_and_sufficient` proves the datum is not an
    arbitrary patch: for positive units, it is exactly equivalent to `c = 1`.

  No disguise: this is a CONDITIONAL derivation. The condition (one-act curvature
  normalization) is a continuum-side recognition datum, named explicitly. It is not
  smuggled, and it is not claimed to be discrete-δ-forced.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationTarget

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DeltaRealCalibration

/-- The one-act log-curvature of the cost member with unit `c`: the second
derivative at the limit ratio `t = 0`. This is a continuum-interface quantity (it
is a second derivative), living in the `ℝδ` protocol layer, not in the discrete
rational carrier. -/
noncomputable def oneActCurvature (c : ℝ) : ℝ :=
  deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0

/-- The one-act curvature is `c²`: the residual gauge parameter read as a
second derivative. -/
theorem oneActCurvature_eq (c : ℝ) : oneActCurvature c = c ^ 2 :=
  Calibration.logCurvature c

/-- **One continuum datum fixes the unit.** At the continuum interface, the single
normalization "one-act curvature equals 1" forces `c = 1`, i.e. selects the
canonical J. -/
theorem unit_forced_by_one_act {c : ℝ} (hc : 0 < c) :
    oneActCurvature c = 1 ↔ c = 1 := by
  unfold oneActCurvature
  exact Calibration.curvature_one_iff_J hc

/-- **The discrete carrier does not force the unit.** The cost family is faithful
(distinct units give distinct costs) and transitively rescaled, so the residual
freedom is a one-real torsor. Without the one-act normalization datum the unit is
genuinely free. -/
theorem discrete_does_not_force_unit :
    (∀ c d : ℝ, 0 < c → 0 < d →
        (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d)
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          ∃ μ : ℝ, 0 < μ ∧
            (fun t => Real.cosh (c * (μ * t)) - 1) = (fun t => Real.cosh (d * t) - 1)) :=
  Calibration.cost_freedom_is_one_real_torsor

/-- **Phase 4 headline: calibration from one continuum act.** The unit `c` is a
faithful one-real torsor on the discrete carrier (no discrete δ datum fixes it),
while a single continuum-interface datum, the one-act curvature normalization,
forces `c = 1`. So `λ = 1` is derived from exactly one recognition act at the
`ℝδ` interface, with the residual gauge being one real removed by one datum.
This is the honest conditional: the calibration is not discrete-δ-forced, and the
one continuum datum is named rather than hidden. -/
theorem calibration_is_one_continuum_act :
    (∀ c : ℝ, oneActCurvature c = c ^ 2)
      ∧ (∀ c : ℝ, 0 < c → (oneActCurvature c = 1 ↔ c = 1))
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d) :=
  ⟨oneActCurvature_eq, fun _ hc => unit_forced_by_one_act hc,
    fun _ _ hc hd h => (Calibration.clog_inj hc hd h)⟩

/-! ## Second-pass closure: the minimal normalized interface -/

/-- The minimum continuum-side interface datum needed to close calibration. It is
not a full continuum and not a field completion. It is only: a positive cost unit
and the assertion that the primitive one-act chart has unit log-curvature. -/
structure NormalizedOneActInterface where
  unit : ℝ
  positive : 0 < unit
  curvature_unit : oneActCurvature unit = 1

/-- Any normalized one-act interface forces the canonical cost unit. -/
theorem normalized_interface_forces_J (I : NormalizedOneActInterface) :
    I.unit = 1 :=
  (unit_forced_by_one_act I.positive).mp I.curvature_unit

/-- For positive units, the one-act curvature datum is necessary and sufficient
for selecting the canonical member. This is the exact closure of the calibration
gap: one datum, no more and no less. -/
theorem calibration_datum_necessary_and_sufficient {c : ℝ} (hc : 0 < c) :
    c = 1 ↔ oneActCurvature c = 1 := by
  exact (unit_forced_by_one_act hc).symm

/-- Existence of a normalized interface: the canonical member itself carries one. -/
def canonicalInterface : NormalizedOneActInterface where
  unit := 1
  positive := by norm_num
  curvature_unit := by
    rw [oneActCurvature_eq]
    norm_num

/-- **Calibration closure theorem.** The discrete laws leave a faithful one-real
torsor (`discrete_does_not_force_unit`), while the normalized one-act interface is
both sufficient and necessary for `c = 1`. Thus the cost-unit issue is fully
classified: it is not discrete-forced; it is closed exactly by the minimal
second-order recognition interface. -/
theorem calibration_gap_closed_by_normalized_interface :
    (∀ I : NormalizedOneActInterface, I.unit = 1)
      ∧ (∀ c : ℝ, 0 < c → (c = 1 ↔ oneActCurvature c = 1))
      ∧ (∃ I : NormalizedOneActInterface, I.unit = 1)
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d) :=
  ⟨normalized_interface_forces_J, fun _ hc => calibration_datum_necessary_and_sufficient hc,
    ⟨canonicalInterface, rfl⟩, fun _ _ hc hd h => Calibration.clog_inj hc hd h⟩

end DeltaRealCalibration
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
