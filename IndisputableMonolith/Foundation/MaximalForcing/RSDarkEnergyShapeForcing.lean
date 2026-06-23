import IndisputableMonolith.Foundation.MaximalForcing.RSGrandUniverse
import IndisputableMonolith.Foundation.MaximalForcing.RSLegitimacy
import IndisputableMonolith.Cosmology.DeltaWKernel

/-!
# Maximal Forcing: forcing the dark-energy profile shape

The earlier cosmology layer correctly marked the specific `w(z)` profile as
independent over the *structural* gate `Lcosmo`: present match plus upward deviation
does not determine a function. The dynamical layer below closes that freedom by
installing the RS cosmic-aging flow as a legitimate tightening.

## The physical content (§"cosmic-aging kernel", the headline result)

The BIT cosmic-aging mechanism (`Cosmology.DeltaWKernel`, `Cosmology.CosmicZAging`)
writes `w(z) = -1 + δw(z)` where the deviation is **maximal today** and **decays into
the past**, vanishing in the early universe (no accumulated cosmic Z). Its conserved
form is the cosmic-aging flow law

  `∀ z > -1,  (1 + z) · (w z + 1) = J(φ)`,

i.e. the redshift-diluted deviation `(1+z)·δw(z)` is the conserved cosmic-aging
charge `J(φ) = φ - 3/2 ≈ 0.118` (the phantom-Carnot ceiling). This integrates
**uniquely** to

  `w(z) = -1 + J(φ)/(1 + z)`,

which `dark_energy_kernel_shape_forced` proves is forced, and
`w_RS_kernel_eq_canonical` proves equals the canonical `Cosmology.DeltaWKernel`. So the
forced shape is the physically correct antitone kernel: amplitude `J(φ)` today,
bounded by `J(φ)`, decaying to `-1` at high z. This is the corrected endpoint.

## Honest note on the earlier linear form

An earlier version of this module forced the *linear* profile `w(z) = -1 + φ⁻⁴⁴·z`
via a constant-additive generator (`CosmicZFlowLaw` below). That object is retained
because it is wired into the carrier-independence machinery as a generic non-ΛCDM
witness, but it is **not** the RS dark-energy prediction: its slope `φ⁻⁴⁴ ≈ 6×10⁻¹⁰`
is the baryogenesis `η_B` scale, it is zero today and grows unboundedly into the past
(the wrong sign and the wrong scale for cosmic aging). The physical shape is the
`w_RS_kernel` result above. The linear law is kept only as a scale-free structural
discriminator (it excludes exact ΛCDM and the quadratic witness), never as the
prediction.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Cosmology.DarkEnergyWofZStructural
open IndisputableMonolith.Constants (phi)

/-! ## The physically correct forced shape: the cosmic-aging kernel

This section is the corrected headline result. The forced dark-energy profile is the
antitone cosmic-aging kernel `w(z) = -1 + J(φ)/(1+z)`, not the linear placeholder. -/

/-- The physically correct RS dark-energy equation of state: deviation maximal today
(`J(φ)`), decaying as `1/(1+z)` into the past. This is `Cosmology.DeltaWKernel`'s
canonical kernel written as a `w(z)`. -/
noncomputable def w_RS_kernel (z : ℝ) : ℝ := -1 + Cost.Jcost phi / (1 + z)

/-- The conserved cosmic-aging flow law: the redshift-diluted deviation
`(1+z)·(w z + 1)` equals the conserved cosmic-aging charge `J(φ)` at every redshift
`z > -1`. This is the `Ĥ_RS` generator in its correct multiplicative (dilution) form:
the deviation is largest today and is diluted by `1/(1+z)` into the past, matching the
cosmic-Z accumulation history. -/
def CosmicAgingFlowLaw (w : ℝ → ℝ) : Prop :=
  ∀ z : ℝ, -1 < z → (1 + z) * (w z + 1) = Cost.Jcost phi

/-- The cosmic-aging flow law integrates **uniquely** to the kernel profile
`w(z) = -1 + J(φ)/(1+z)` on the redshift domain `z > -1`. -/
theorem cosmicAgingFlow_forces_kernel {w : ℝ → ℝ} (hw : CosmicAgingFlowLaw w) :
    ∀ z : ℝ, -1 < z → w z = w_RS_kernel z := by
  intro z hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hne : (1 + z) ≠ 0 := ne_of_gt h1z
  have hkey : (w z + 1) * (1 + z) = Cost.Jcost phi := by
    rw [mul_comm]; exact hw z hz
  have hdev : w z + 1 = Cost.Jcost phi / (1 + z) := by
    rw [eq_div_iff hne]; exact hkey
  unfold w_RS_kernel
  linarith

/-- The kernel profile satisfies its own conserved flow law. -/
theorem w_RS_kernel_flow : CosmicAgingFlowLaw w_RS_kernel := by
  intro z hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hne : (1 + z) ≠ 0 := ne_of_gt h1z
  unfold w_RS_kernel
  field_simp
  ring

/-- Present-day value: the deviation is the full cosmic-aging amplitude `J(φ)`. -/
theorem w_RS_kernel_today : w_RS_kernel 0 = -1 + Cost.Jcost phi := by
  unfold w_RS_kernel; norm_num

/-- **Bridge to the canonical kernel (resolves the two-representation conflict).**
On the physical redshift domain `z ≥ 0`, the forced shape equals the canonical
`Cosmology.DeltaWKernel` kernel written as `w(z) = -1 + δw(z)`. The maximal-forcing
endpoint and the cosmology kernel are the same object. -/
theorem w_RS_kernel_eq_canonical (z : ℝ) (hz : 0 ≤ z) :
    w_RS_kernel z = -1 + Cosmology.DeltaWKernel.canonicalDeltaW.deviation z := by
  have hdev : Cosmology.DeltaWKernel.canonicalDeltaW.deviation z
      = Cost.Jcost phi / (1 + z) := by
    show Cost.Jcost phi * Cosmology.DeltaWKernel.f_canonical z = Cost.Jcost phi / (1 + z)
    unfold Cosmology.DeltaWKernel.f_canonical
    rw [if_neg (by linarith : ¬ z < 0)]
    ring
  unfold w_RS_kernel
  rw [hdev]

/-- The forced kernel deviation is bounded by the phantom-Carnot ceiling `J(φ)` on the
physical redshift domain `z ≥ 0` (it equals `J(φ)` today and decays thereafter). -/
theorem w_RS_kernel_bounded_by_ceiling (z : ℝ) (hz : 0 ≤ z) :
    w_RS_kernel z + 1 ≤ Cost.Jcost phi := by
  have hJ : 0 < Cost.Jcost phi := IndisputableMonolith.Constants.Jcost_phi_pos
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hle : Cost.Jcost phi / (1 + z) ≤ Cost.Jcost phi := by
    rw [div_le_iff₀ h1z]
    nlinarith [hJ, hz]
  unfold w_RS_kernel
  linarith

/-- The forced kernel deviation is non-negative on `z ≥ 0` (softer-than-`-1`,
phantom side). -/
theorem w_RS_kernel_nonneg (z : ℝ) (hz : 0 ≤ z) :
    -1 ≤ w_RS_kernel z := by
  have hJ : 0 < Cost.Jcost phi := IndisputableMonolith.Constants.Jcost_phi_pos
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have : 0 ≤ Cost.Jcost phi / (1 + z) := le_of_lt (div_pos hJ h1z)
  unfold w_RS_kernel
  linarith

/-- **DARK-ENERGY SHAPE FORCED (corrected, physical headline).**

The conserved cosmic-aging flow law forces the unique antitone kernel profile
`w(z) = -1 + J(φ)/(1+z)`, which:
* is the canonical `Cosmology.DeltaWKernel` (bridge, on `z ≥ 0`);
* has its deviation maximal today (`= J(φ)`), bounded by the phantom-Carnot ceiling,
  and non-negative on the physical redshift domain.

This supersedes the linear `φ⁻⁴⁴·z` placeholder as the physical dark-energy shape:
the forced amplitude is the cosmic-aging scale `J(φ)`, and the forced z-dependence is
the matter-dilution `1/(1+z)`. -/
theorem dark_energy_kernel_shape_forced :
    (∀ w : ℝ → ℝ, CosmicAgingFlowLaw w → ∀ z : ℝ, -1 < z → w z = w_RS_kernel z) ∧
    CosmicAgingFlowLaw w_RS_kernel ∧
    w_RS_kernel 0 = -1 + Cost.Jcost phi ∧
    (∀ z : ℝ, 0 ≤ z → w_RS_kernel z = -1 + Cosmology.DeltaWKernel.canonicalDeltaW.deviation z) ∧
    (∀ z : ℝ, 0 ≤ z → w_RS_kernel z + 1 ≤ Cost.Jcost phi) :=
  ⟨fun _ hw => cosmicAgingFlow_forces_kernel hw,
   w_RS_kernel_flow,
   w_RS_kernel_today,
   w_RS_kernel_eq_canonical,
   w_RS_kernel_bounded_by_ceiling⟩

/-! ## The CPL image of the forced kernel (the DESI handle)

DESI fits dark energy with the Chevallier-Polarski-Linder (CPL) parameterization
`w(a) = w₀ + wₐ(1 - a)`, i.e. `w(z) = w₀ + wₐ·z/(1+z)`. The forced cosmic-aging kernel
is *exactly* a CPL model, which gives RS a sharp, falsifiable `(w₀, wₐ)` prediction. -/

/-- The CPL dark-energy equation of state in redshift form: `w(z) = w₀ + wₐ·z/(1+z)`. -/
noncomputable def w_CPL (w0 wa z : ℝ) : ℝ := w0 + wa * (z / (1 + z))

/-- **The forced kernel is exactly CPL with `(w₀, wₐ) = (-1 + J(φ), -J(φ))`.**

So RS predicts the DESI CPL parameters are pinned by the single scale `J(φ) ≈ 0.118`:
`w₀ = -1 + J(φ) ≈ -0.882` and `wₐ = -J(φ) ≈ -0.118`.

HONESTY NOTE: this is a sharp prediction, and it is in tension with DESI Y1 central
values (`w₀ ≈ -0.64`, `wₐ ≈ -1.28`, hence `w₀ + wₐ ≈ -1.92`). The simple `1/(1+z)`
kernel predicts much smaller deviations than DESI Y1 suggests. DESI Y3+ will adjudicate;
if large `|wₐ|` is confirmed, the single-scale kernel is falsified and the full
nonlinear cosmic-Z treatment is required. -/
theorem w_RS_kernel_eq_CPL (z : ℝ) (hz : -1 < z) :
    w_RS_kernel z = w_CPL (-1 + Cost.Jcost phi) (-(Cost.Jcost phi)) z := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hne : (1 + z) ≠ 0 := ne_of_gt h1z
  unfold w_RS_kernel w_CPL
  field_simp
  ring

/-- **The forced kernel's CPL parameters obey `w₀ + wₐ = -1`.** This is the
early-universe (`a → 0`, `z → ∞`) recovery of exact ΛCDM: the cosmic-aging deviation
vanishes when no cosmic Z has accumulated. It is the cleanest single falsifiable
constraint the RS dark-energy shape imposes on a DESI CPL fit. -/
theorem w_RS_kernel_CPL_sum_constraint :
    (-1 + Cost.Jcost phi) + (-(Cost.Jcost phi)) = -1 := by ring

/-! ## Deriving the conserved flow law from a cosmic Z-accumulation premise

The result above forces the kernel **given** the conserved cosmic-aging flow law
`(1+z)·δw(z) = J(φ)`. That flow law was itself posited. This section pushes one layer
deeper: it names a more primitive physical premise and shows the flow law (hence the
kernel) follows from it, and that the premise is the *unique* power-law shape that
conserves the order-1 cosmic recognition charge.

HONESTY TAG. The premise `LinearScaleFactorAccumulation` is a **HYPOTHESIS**, not a
T-1 theorem. Its physical content is: the dark-energy deviation is proportional to the
cosmic scale factor `a(z) = 1/(1+z)`, normalized to the phantom-Carnot ceiling `J(φ)`
today. Equivalently, the recognition charge that sources the deviation accumulates
linearly in `a`. This is *not* derived from distinction; it is the cosmological input.
Its named falsifier is the DESI CPL constraint `w₀ + wₐ = -1` proved above
(`w_RS_kernel_CPL_sum_constraint`): a confirmed DESI `w₀ + wₐ ≠ -1` falsifies the
linear-in-`a` premise and forces a higher-order cosmic-Z accumulation law.

What *is* a theorem here: (i) the premise is logically equivalent to conservation of the
order-1 charge `Q₁(z) = (1+z)·δw(z)`; (ii) the premise integrates uniquely to the kernel;
(iii) the two named competitor shapes (`n=2` volume-dilution and the linear-in-`z`
witness) both violate order-1 charge conservation, so the conserved-charge premise
*selects* the kernel among them. -/

/-- The cosmic scale factor in redshift form, `a(z) = 1/(1+z)`. -/
noncomputable def scaleFactor (z : ℝ) : ℝ := 1 / (1 + z)

/-- The order-1 cosmic recognition charge of a dark-energy profile:
`Q₁(z) = (1+z)·δw(z) = (1+z)·(w z + 1)`. It is the redshift-diluted deviation. -/
noncomputable def cosmicChargeOne (w : ℝ → ℝ) (z : ℝ) : ℝ := (1 + z) * (w z + 1)

/-- **The cosmic Z-accumulation premise (HYPOTHESIS).** The dark-energy deviation is
proportional to the scale factor `a(z)`, with present-day amplitude `J(φ)`:

  `δw(z) = J(φ)·a(z) = J(φ)/(1+z)`.

Physically: the recognition charge that sources cosmic aging accumulates linearly in the
scale factor, so the deviation tracks `a`. This is the cosmological input from which the
conserved flow law and the kernel shape follow. -/
def LinearScaleFactorAccumulation (w : ℝ → ℝ) : Prop :=
  ∀ z : ℝ, -1 < z → w z + 1 = Cost.Jcost phi * scaleFactor z

/-- The conserved flow law is exactly conservation of the order-1 cosmic recognition
charge `Q₁` at the value `J(φ)`. (Definitional reformulation, exposed for clarity.) -/
theorem flowLaw_iff_chargeOne_const {w : ℝ → ℝ} :
    CosmicAgingFlowLaw w ↔ ∀ z : ℝ, -1 < z → cosmicChargeOne w z = Cost.Jcost phi :=
  Iff.rfl

/-- **The accumulation premise is equivalent to the conserved cosmic-aging flow law.**
Linear-in-`a` accumulation `⟺` order-1 charge conservation. This is the honest content of
"deriving the flow law": the flow law is the conserved-charge image of the cosmological
accumulation premise. -/
theorem linearScaleFactorAccumulation_iff_flow {w : ℝ → ℝ} :
    LinearScaleFactorAccumulation w ↔ CosmicAgingFlowLaw w := by
  constructor
  · intro h z hz
    have h1z : (0 : ℝ) < 1 + z := by linarith
    have hne : (1 + z) ≠ 0 := ne_of_gt h1z
    have hacc := h z hz
    unfold scaleFactor at hacc
    rw [mul_one_div] at hacc
    rw [mul_comm]
    exact (eq_div_iff hne).mp hacc
  · intro h z hz
    have h1z : (0 : ℝ) < 1 + z := by linarith
    have hne : (1 + z) ≠ 0 := ne_of_gt h1z
    have hf := h z hz
    unfold scaleFactor
    rw [mul_one_div, eq_div_iff hne, mul_comm]
    exact hf

/-- **The accumulation premise integrates uniquely to the kernel.** Given linear-in-`a`
cosmic Z accumulation, the dark-energy profile is forced to be `w_RS_kernel`. -/
theorem accumulation_forces_kernel {w : ℝ → ℝ}
    (hw : LinearScaleFactorAccumulation w) : ∀ z : ℝ, -1 < z → w z = w_RS_kernel z :=
  fun z hz => cosmicAgingFlow_forces_kernel (linearScaleFactorAccumulation_iff_flow.mp hw) z hz

/-- The forced kernel does satisfy the linear-in-`a` accumulation premise. -/
theorem w_RS_kernel_linearAccum : LinearScaleFactorAccumulation w_RS_kernel :=
  linearScaleFactorAccumulation_iff_flow.mpr w_RS_kernel_flow

/-- Competitor 1: the `n=2` volume-dilution accumulation `δw(z) = J(φ)/(1+z)²`. This is
the shape obtained if the sourcing charge diluted with comoving *volume* rather than
linearly with the scale factor. -/
noncomputable def w_RS_quadratic_accum (z : ℝ) : ℝ := -1 + Cost.Jcost phi / (1 + z) ^ 2

/-- **The `n=2` competitor violates order-1 charge conservation.** Its `Q₁` is `J(φ)`
today but `J(φ)/2` at `z=1`, so it cannot satisfy the conserved cosmic-aging flow law.
The conserved-charge premise therefore excludes volume-dilution in favor of the kernel. -/
theorem quadratic_accum_breaks_chargeOne :
    cosmicChargeOne w_RS_quadratic_accum 0 ≠ cosmicChargeOne w_RS_quadratic_accum 1 := by
  have hJ : 0 < Cost.Jcost phi := IndisputableMonolith.Constants.Jcost_phi_pos
  have h0 : cosmicChargeOne w_RS_quadratic_accum 0 = Cost.Jcost phi := by
    unfold cosmicChargeOne w_RS_quadratic_accum; ring
  have h1 : cosmicChargeOne w_RS_quadratic_accum 1 = Cost.Jcost phi / 2 := by
    unfold cosmicChargeOne w_RS_quadratic_accum; ring
  rw [h0, h1]; intro h; linarith

/-- **The linear-in-`z` witness violates order-1 charge conservation.** Its present-day
`Q₁` is `0`, not `J(φ)`: the linear placeholder vanishes today instead of carrying the
full cosmic-aging amplitude, so the conserved-charge premise excludes it too. -/
theorem linear_witness_breaks_chargeOne :
    cosmicChargeOne w_RS_linear 0 ≠ Cost.Jcost phi := by
  have hJ : 0 < Cost.Jcost phi := IndisputableMonolith.Constants.Jcost_phi_pos
  have h0 : cosmicChargeOne w_RS_linear 0 = 0 := by
    unfold cosmicChargeOne; rw [w_RS_linear_at_zero]; ring
  rw [h0]; intro h; linarith

/-- **COSMIC-AGING KERNEL DERIVED FROM Z-ACCUMULATION (F4 option-a capstone).**

The kernel shape is forced from the cosmological accumulation premise, not merely from a
posited flow law:
* linear-in-`a` accumulation integrates uniquely to `w_RS_kernel`;
* the premise is equivalent to conservation of the order-1 cosmic recognition charge;
* the kernel realizes the premise;
* both named competitor shapes (volume-dilution `n=2`, linear-in-`z` witness) break
  order-1 charge conservation, so the conserved-charge premise *selects* the kernel.

HONESTY: the premise is HYPOTHESIS-grade (the cosmological input), with falsifier
`w₀ + wₐ = -1`. Everything downstream of the premise is THEOREM. -/
theorem cosmic_aging_kernel_derived_from_accumulation :
    (∀ w : ℝ → ℝ, LinearScaleFactorAccumulation w → ∀ z : ℝ, -1 < z → w z = w_RS_kernel z) ∧
    (∀ w : ℝ → ℝ, LinearScaleFactorAccumulation w ↔ CosmicAgingFlowLaw w) ∧
    LinearScaleFactorAccumulation w_RS_kernel ∧
    cosmicChargeOne w_RS_quadratic_accum 0 ≠ cosmicChargeOne w_RS_quadratic_accum 1 ∧
    cosmicChargeOne w_RS_linear 0 ≠ Cost.Jcost phi :=
  ⟨fun _ hw => accumulation_forces_kernel hw,
   fun _ => linearScaleFactorAccumulation_iff_flow,
   w_RS_kernel_linearAccum,
   quadratic_accum_breaks_chargeOne,
   linear_witness_breaks_chargeOne⟩

/-! ## The cosmic Z-flow law

WARNING (honesty): the linear `CosmicZFlowLaw` below is **not** the RS dark-energy
prediction. It is retained as a generic scale-free discriminator (it excludes exact
ΛCDM and the quadratic witness, and feeds the carrier-independence proofs). The
physical forced shape is `w_RS_kernel` above (`dark_energy_kernel_shape_forced`). -/

/-- The RS cosmic-redshift flow law for the dark-energy equation of state.

`w 0 = -1` fixes the present normalization. The second clause says the `Ĥ_RS`
redshift-flow generator is the rung-44 constant `φ⁻⁴⁴`: translating redshift by `s`
adds exactly `φ⁻⁴⁴ * s` to the equation-of-state deviation. -/
def CosmicZFlowLaw (w : ℝ → ℝ) : Prop :=
  w 0 = -1 ∧ ∀ z s : ℝ, w (z + s) - w z = phi_neg_44 * s

/-- The canonical linear profile satisfies the cosmic Z-flow law. -/
theorem w_RS_linear_cosmicZFlowLaw : CosmicZFlowLaw w_RS_linear := by
  refine ⟨w_RS_linear_at_zero, ?_⟩
  intro z s
  unfold w_RS_linear
  ring

/-- The cosmic Z-flow law uniquely integrates to the linear rung-44 profile. -/
theorem cosmicZFlow_forces_linear {w : ℝ → ℝ} (hw : CosmicZFlowLaw w) :
    ∀ z : ℝ, w z = -1 + phi_neg_44 * z := by
  intro z
  have hstep := hw.2 0 z
  rw [zero_add, hw.1] at hstep
  linarith

/-- The cosmic Z-flow law implies the earlier structural cosmology gate. -/
theorem cosmicZFlow_structural {w : ℝ → ℝ} (hw : CosmicZFlowLaw w) :
    CosmoStructural w := by
  refine ⟨hw.1, ?_⟩
  intro z hz
  rw [cosmicZFlow_forces_linear hw z]
  have hpos : 0 < phi_neg_44 * z := mul_pos phi_neg_44_pos hz
  linarith

/-! ## Tightened cosmology gate -/

/-- The dynamical dark-energy class: structural cosmology plus the `Ĥ_RS` cosmic
Z-flow law. The structural part follows from the flow, but storing only the flow keeps
the gate minimal. -/
def LcosmoFlow : AdmissibilityClass (ℝ → ℝ) where
  admissible := { w | CosmicZFlowLaw w }
  label := "RS dark-energy Ĥ_RS flow gate: w(0)=-1 and constant rung-44 redshift generator"

/-- The flow gate tightens the structural cosmology gate. -/
def tighten_Lcosmo_LcosmoFlow : Tightening Lcosmo LcosmoFlow where
  subset := by
    intro w hw
    exact cosmicZFlow_structural hw
  strict_witness := ∀ w : ℝ → ℝ, CosmicZFlowLaw w → ∀ z, w z = -1 + phi_neg_44 * z

/-- Under the cosmic-flow gate, the specific profile is forced. -/
theorem forced_cosmoLinearForm_under_flow :
    Forced LcosmoFlow.admissible cosmoLinearForm := by
  intro w hw
  exact cosmicZFlow_forces_linear hw

/-- The flow gate is legitimate: it flips the already-proved structural independence of
the profile into forcedness, and the named deeper law is the constant rung-44 cosmic
Z-flow equation. -/
noncomputable def legit_cosmo_profile_flow :
    LegitimateTightening Lcosmo LcosmoFlow :=
  legitimateTightening_of_flip
    tighten_Lcosmo_LcosmoFlow.subset
    cosmoLinearForm_independent
    forced_cosmoLinearForm_under_flow
    (∀ w : ℝ → ℝ, CosmicZFlowLaw w → ∀ z, w z = -1 + phi_neg_44 * z)
    (fun _w hw => cosmicZFlow_forces_linear hw)
    "Ĥ_RS cosmic Z-flow law: constant rung-44 generator integrates to w(z)=-1+φ^(-44)·z"

/-- **DARK-ENERGY SHAPE FORCING (cosmology layer).** The profile that was independent
over the structural gate is forced after the legitimate `Ĥ_RS` cosmic-flow tightening. -/
theorem dark_energy_shape_forced_after_flow :
    ForcedAfterTightening Lcosmo LcosmoFlow cosmoLinearForm :=
  ⟨⟨legit_cosmo_profile_flow.toTightening⟩, forced_cosmoLinearForm_under_flow⟩

/-! ## Tightened reality gate -/

/-- Reality gate tightened by the cosmic Z-flow law on the `eos` field. -/
def RealityAdmissibleFlow (c : RSReality) : Prop :=
  RealityAdmissible c ∧ CosmicZFlowLaw c.eos

/-- The physical reality class after the `Ĥ_RS` dark-energy shape law is installed. -/
def LrealityFlow : AdmissibilityClass RSReality where
  admissible := { c | RealityAdmissibleFlow c }
  label := "reality gate tightened by Ĥ_RS cosmic Z-flow; dark-energy shape forced"

/-- The flow-tightened reality gate is a genuine tightening of `Lreality`. -/
def tighten_Lreality_LrealityFlow : Tightening Lreality LrealityFlow where
  subset := by
    intro c hc
    exact hc.1
  strict_witness := ∀ c : RSReality, c ∈ LrealityFlow.admissible → gProfile.holds c

/-- Under the flow-tightened reality gate, the old profile claim is now forced. -/
theorem forced_gProfile_under_flow : Forced LrealityFlow.admissible gProfile := by
  intro c hc
  exact cosmicZFlow_forces_linear hc.2

/-- The flow-tightening is legitimate over the full reality carrier: it excludes the
quadratic profile countermodel and promotes `gProfile` from independent to forced by the
named `Ĥ_RS` cosmic Z-flow law. -/
noncomputable def legit_reality_profile_flow :
    LegitimateTightening Lreality LrealityFlow :=
  legitimateTightening_of_flip
    tighten_Lreality_LrealityFlow.subset
    gProfile_independent
    forced_gProfile_under_flow
    (∀ c : RSReality, c ∈ LrealityFlow.admissible → gProfile.holds c)
    forced_gProfile_under_flow
    "Ĥ_RS cosmic Z-flow law on the eos field forces the rung-44 dark-energy profile"

/-- **DARK-ENERGY SHAPE FORCING (reality carrier).** The last physically meaningful
independent coordinate of `RSReality` is promoted to `Forced` after the legitimate
cosmic-flow tightening. -/
theorem gProfile_forced_after_reality_flow :
    ForcedAfterTightening Lreality LrealityFlow gProfile :=
  ⟨⟨legit_reality_profile_flow.toTightening⟩, forced_gProfile_under_flow⟩

/-- **ONLY PURE GAUGE REMAINS (physical endpoint).** After the `Ĥ_RS` cosmic-flow
tightening, the dark-energy profile is forced. The remaining physical freedom in the
carrier is the yardstick, already proved to be pure gauge; the cost-off-domain artifact
is outside the positive-ratio recognition domain and is handled separately in
`RSCostDomainHonesty`. -/
theorem only_pure_gauge_remains_after_flow :
    Forced LrealityFlow.admissible gProfile ∧
    Independent Lreality.admissible gYard ∧
    Nonempty (LegitimateTightening Lreality LrealityFlow) :=
  ⟨forced_gProfile_under_flow, gYard_independent, ⟨legit_reality_profile_flow⟩⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
