import Mathlib
import IndisputableMonolith.Foundation.AbsoluteFloorClosure
import IndisputableMonolith.Foundation.UniversalInstantiationFromDistinction
import IndisputableMonolith.Foundation.TimeAsOrbit
import IndisputableMonolith.Foundation.ConstantDerivations
import IndisputableMonolith.Foundation.UnifiedForcingChain
import IndisputableMonolith.Unification.SpacetimeEmergence

/-!
# Reality from One Distinction

This module supplies the master forcing-chain certificate that the framework
has been quietly accumulating. A bare proposition `∃ x y : K, x ≠ y` on an
inhabited carrier `K` supplies the non-vacuous floor and a native
`LogicRealization`; the spacetime, light-cone, time-orbit, and constant fields
are imported from named upstream certificates.

Every link is already proved elsewhere in the repository. This module is
pure glue: it threads the dependencies through one Lean record so the chain is
visible at a single named place, while `bundling_decomposition` records which
fields are actually supplied by the chosen distinction.

## Honest scope

This module connects the absolute-floor theorem (`Foundation.AbsoluteFloorClosure`)
through the full T0-T8 spine (`Foundation.UnifiedForcingChain`), the
time-as-orbit theorem (`Foundation.TimeAsOrbit`), the spacetime-emergence
theorem (`Unification.SpacetimeEmergence`), and the constant-derivation theorem
(`Foundation.ConstantDerivations`).
-/

namespace IndisputableMonolith
namespace Foundation
namespace RealityFromDistinction

open AbsoluteFloorClosure
open TimeAsOrbit
open Unification.SpacetimeEmergence

/-! ## Master forcing-chain certificate -/

/-- **Reality-from-One-Distinction Certificate.**

The deliverables of the chain, packaged as one structure. -/
structure RealityCertificate (K : Type) [Nonempty K] : Prop where
  /-- A non-trivial distinction exists in the carrier. -/
  distinction : ∃ x y : K, x ≠ y
  /-- The absolute-floor witness is supplied. -/
  absolute_floor : Nonempty (AbsoluteFloorWitness K)
  /-- The carrier itself instantiates the Law-of-Logic realization interface. -/
  native_realization : Nonempty (LogicRealization.{0, 0})
  /-- The bool-valued absolute-floor witness exists unconditionally. -/
  bool_floor : AbsoluteFloorWitness Bool
  /-- The full T0-T8 forcing chain plus operator, variational, and measurement
      layers is available. -/
  complete_chain : Nonempty UnifiedForcingChain.CompleteForcingChain
  /-- Spacetime emerges with Lorentzian signature (1, 3). -/
  spacetime : Nonempty SpacetimeEmergenceCert
  /-- The light cone is the null structure of that spacetime. -/
  light_cone :
    ∀ v : Displacement,
      interval v = 0 ↔ spatial_norm_sq v = temporal_sq v
  /-- Time is the canonical natural-number-object orbit of recognition. -/
  time_orbit : Nonempty TimeAsOrbitCert
  /-- The speed of causal propagation is unit. -/
  c_unit : ConstantDerivations.c_rs = 1
  /-- ℏ is a φ-power on the recognition ladder. -/
  hbar_from_phi : ∃ n : ℤ, ConstantDerivations.ℏ_rs = ConstantDerivations.φ_val ^ n
  /-- `G·π` is a φ-power on the recognition ladder (`G = φ⁵/π`, Family A). -/
  G_from_phi : ∃ n : ℤ, ConstantDerivations.G_rs * Real.pi = ConstantDerivations.φ_val ^ n

/-- The part of `RealityCertificate` actually supplied by the chosen
object-level distinction on `K`. -/
structure DistinctionSuppliedFields (K : Type) [Nonempty K] : Prop where
  /-- A non-trivial distinction exists in the carrier. -/
  distinction : ∃ x y : K, x ≠ y
  /-- The absolute-floor witness is supplied. -/
  absolute_floor : Nonempty (AbsoluteFloorWitness K)
  /-- The carrier itself instantiates the Law-of-Logic realization interface. -/
  native_realization : Nonempty (LogicRealization.{0, 0})
  /-- The bool-valued absolute-floor witness exists unconditionally. -/
  bool_floor : AbsoluteFloorWitness Bool

/-- The part of `RealityCertificate` imported from upstream forcing-chain
theorems, rather than produced by the chosen distinction itself. -/
structure UpstreamSuppliedFields : Prop where
  /-- The full T0-T8 forcing chain plus operator, variational, and measurement
      layers is available. -/
  complete_chain : Nonempty UnifiedForcingChain.CompleteForcingChain
  /-- Spacetime emerges with Lorentzian signature (1, 3). -/
  spacetime : Nonempty SpacetimeEmergenceCert
  /-- The light cone is the null structure of that spacetime. -/
  light_cone :
    ∀ v : Displacement,
      interval v = 0 ↔ spatial_norm_sq v = temporal_sq v
  /-- Time is the canonical natural-number-object orbit of recognition. -/
  time_orbit : Nonempty TimeAsOrbitCert
  /-- The speed of causal propagation is unit. -/
  c_unit : ConstantDerivations.c_rs = 1
  /-- ℏ is a φ-power on the recognition ladder. -/
  hbar_from_phi : ∃ n : ℤ, ConstantDerivations.ℏ_rs = ConstantDerivations.φ_val ^ n
  /-- `G·π` is a φ-power on the recognition ladder (`G = φ⁵/π`, Family A). -/
  G_from_phi : ∃ n : ℤ, ConstantDerivations.G_rs * Real.pi = ConstantDerivations.φ_val ^ n

/-! ## The master theorem -/

/-- **The master chain-bundling theorem.**

Given any inhabited carrier `K` with at least one non-trivial distinction,
the distinction supplies:

* the absolute-floor witness on `K`;
* a native Law-of-Logic realization on `K`;
* the canonical absolute-floor witness on `Bool`.

The remaining fields are upstream certificates bundled with those
distinction-supplied fields:

* the spacetime-emergence certificate (Lorentzian signature, light cone,
  causal classification);
* the light cone in its null-displacement form;
* the time-as-orbit certificate (`Tick` is a Lawvere natural-number object,
  canonically equivalent to `LogicNat`);
* `c = 1` (causal speed is a structural unit, not a parameter);
* `ℏ` and `G` as φ-powers on the recognition ladder.

Every right-hand-side upstream conclusion is an existing theorem in the
repository. This theorem is the named place where the floor and upstream
certificates are bundled; it is not a claim that the chosen distinction alone
generates spacetime or constants. -/
theorem reality_from_one_distinction
    (K : Type) [Nonempty K]
    (h : ∃ x y : K, x ≠ y) :
    RealityCertificate K where
  distinction := h
  absolute_floor := ⟨absolute_floor_of_bare_distinguishability h⟩
  native_realization :=
    UniversalInstantiationFromDistinction.exists_logicRealization_of_distinction K h
  bool_floor := bool_absolute_floor
  complete_chain := ⟨UnifiedForcingChain.complete_forcing_chain⟩
  spacetime := spacetime_emergence_cert_nonempty
  light_cone := lightlike_iff_speed_c
  time_orbit := timeAsOrbitCert_inhabited
  c_unit := ConstantDerivations.c_rs_eq_one
  hbar_from_phi := ConstantDerivations.ℏ_algebraic_in_φ
  G_from_phi := ConstantDerivations.G_pi_algebraic_in_φ

/-- The explicit decomposition of the chain-bundling theorem. The chosen
distinction supplies only the floor, the Bool witness, and the native
`LogicRealization`; spacetime, time-as-orbit, the complete chain, and the
constant derivations are imported from named upstream certificates. -/
theorem bundling_decomposition
    (K : Type) [Nonempty K]
    (h : ∃ x y : K, x ≠ y) :
    DistinctionSuppliedFields K ∧ UpstreamSuppliedFields := by
  refine ⟨?_, ?_⟩
  · exact {
      distinction := h
      absolute_floor := ⟨absolute_floor_of_bare_distinguishability h⟩
      native_realization :=
        UniversalInstantiationFromDistinction.exists_logicRealization_of_distinction K h
      bool_floor := bool_absolute_floor }
  · exact {
      complete_chain := ⟨UnifiedForcingChain.complete_forcing_chain⟩
      spacetime := spacetime_emergence_cert_nonempty
      light_cone := lightlike_iff_speed_c
      time_orbit := timeAsOrbitCert_inhabited
      c_unit := ConstantDerivations.c_rs_eq_one
      hbar_from_phi := ConstantDerivations.ℏ_algebraic_in_φ
      G_from_phi := ConstantDerivations.G_pi_algebraic_in_φ }

/-- A `RealityCertificate` is exactly the product of the distinction-supplied
fields and the upstream-supplied fields. This theorem is the type-level audit
that `reality_from_one_distinction` is a bundling theorem, not a claim that the
chosen distinction alone generates the later physics. -/
theorem realityCertificate_eq_decomposition
    (K : Type) [Nonempty K] :
    RealityCertificate K ↔ DistinctionSuppliedFields K ∧ UpstreamSuppliedFields := by
  constructor
  · intro cert
    refine ⟨?_, ?_⟩
    · exact {
        distinction := cert.distinction
        absolute_floor := cert.absolute_floor
        native_realization := cert.native_realization
        bool_floor := cert.bool_floor }
    · exact {
        complete_chain := ⟨UnifiedForcingChain.complete_forcing_chain⟩
        spacetime := cert.spacetime
        light_cone := cert.light_cone
        time_orbit := cert.time_orbit
        c_unit := cert.c_unit
        hbar_from_phi := cert.hbar_from_phi
        G_from_phi := cert.G_from_phi }
  · rintro ⟨dist, upstream⟩
    exact {
      distinction := dist.distinction
      absolute_floor := dist.absolute_floor
      native_realization := dist.native_realization
      bool_floor := dist.bool_floor
      complete_chain := ⟨UnifiedForcingChain.complete_forcing_chain⟩
      spacetime := upstream.spacetime
      light_cone := upstream.light_cone
      time_orbit := upstream.time_orbit
      c_unit := upstream.c_unit
      hbar_from_phi := upstream.hbar_from_phi
      G_from_phi := upstream.G_from_phi }

/-- Canonical name for the chain-bundling theorem. The distinction supplies the
floor and the native realization on `K`; the rest of the certificate is
imported from named upstream theorems. See `bundling_decomposition`. -/
theorem recognition_chain_certificate_from_distinction
    (K : Type) [Nonempty K]
    (h : ∃ x y : K, x ≠ y) :
    RealityCertificate K :=
  reality_from_one_distinction K h

attribute [deprecated recognition_chain_certificate_from_distinction (since := "2026-05-18")]
  reality_from_one_distinction

/-! ## Specialised forms -/

/-- The minimal concrete instance: `Bool` is inhabited and admits the
distinction `false ≠ true`, so the chain-bundling theorem applies with the
smallest possible carrier as its floor witness. -/
theorem reality_from_bool : RealityCertificate Bool :=
  recognition_chain_certificate_from_distinction Bool
    ⟨false, true, SelfBootstrap.bool_distinguishable⟩

/-- The master theorem in propositional form (no carrier needed in the
output, only the witness that *some* inhabited carrier admits a
distinction). -/
theorem reality_forced_by_any_distinction :
    (∃ K : Type, Nonempty K ∧ ∃ x y : K, x ≠ y) →
    Nonempty SpacetimeEmergenceCert ∧
    Nonempty TimeAsOrbitCert ∧
    Nonempty UnifiedForcingChain.CompleteForcingChain ∧
    ConstantDerivations.c_rs = 1 := by
  rintro ⟨K, _, h⟩
  -- We do not need K here; the spacetime/time/constant claims are
  -- realisation-free. They follow from the global theorems already
  -- proved upstream. The role of the hypothesis is that the chain is
  -- *statable* (a non-singleton carrier exists, hence the absolute
  -- floor is non-vacuous).
  refine ⟨spacetime_emergence_cert_nonempty, timeAsOrbitCert_inhabited,
    ⟨UnifiedForcingChain.complete_forcing_chain⟩,
    ConstantDerivations.c_rs_eq_one⟩

/-! ## What this earns

The master theorem records a single named Lean object (`RealityCertificate K`)
whose proof routes through the absolute-floor closure, time-as-orbit,
spacetime emergence, and constant derivations. The decomposition theorem above
records which fields are supplied by the distinction itself and which fields are
upstream forcing-chain certificates.

The forcing chain has been a known structural fact across many modules.
This module is the explicit Lean witness that it is one chain, with one
hypothesis, and one deliverable.

## Open follow-ups

* The full `CompleteForcingChain` from `Foundation.UnifiedForcingChain`
  is now bundled directly in this certificate.

* Add a stronger version that takes the Recognition Composition Law and
  the J-cost calibration as inputs and produces the full physics tower
  (gauge groups, masses, fine-structure constant) as outputs. The
  ingredients exist in `Foundation/UnifiedReality.lean`; only the
  glue is missing.
-/

end RealityFromDistinction
end Foundation
end IndisputableMonolith
