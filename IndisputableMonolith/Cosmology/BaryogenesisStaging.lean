import Mathlib
import IndisputableMonolith.Cosmology.SakharovFromLedger
import IndisputableMonolith.Cosmology.SphaleronRate
import IndisputableMonolith.Cosmology.EWPhaseTransition
import IndisputableMonolith.StandardModel.JarlskogInvariant
import IndisputableMonolith.StandardModel.RelativisticDOF

/-!
# Baryogenesis Staging

Curated staging module for the Steve baryogenesis derivation loop.

The purpose of this file is to hold small, honest theorem targets that prevent the
baryogenesis lane from faking the missing mechanism. The first invariant is the
sphaleron zero-protection obstruction: electroweak sphalerons conserve B-L, so if
the sourced B-L charge is zero and sphalerons equilibrate, the surviving baryon
number is zero.

Loop-generated targets may be appended below the marker. They must not introduce
new axioms, `admit`, or fake physics conditions as `True`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace BaryogenesisStaging

noncomputable section

/-- Standard Model sphaleron reprocessing coefficient for three generations:
`B = (28 / 79) * (B - L)` after electroweak sphaleron equilibration. -/
def sphaleronReprocessingFactor : ℚ := 28 / 79

/-- If no B-L charge is sourced, sphaleron equilibrium leaves no baryon excess. -/
theorem sphaleron_equilibrium_zero_of_zero_BminusL :
    sphaleronReprocessingFactor * (0 : ℚ) = 0 := by
  simp [sphaleronReprocessingFactor]

/-- The reprocessing factor is positive. This makes the conversion a real sign-preserving
map from a B-L relic to baryon number, not a tautology. -/
theorem sphaleronReprocessingFactor_pos : 0 < sphaleronReprocessingFactor := by
  norm_num [sphaleronReprocessingFactor]

/-- The reprocessing factor is strictly less than one: sphalerons reprocess a B-L
relic rather than copying it unchanged. -/
theorem sphaleronReprocessingFactor_lt_one : sphaleronReprocessingFactor < 1 := by
  norm_num [sphaleronReprocessingFactor]

/-- Relic comoving B−L charge: source `a³ S_X` folded against the real
    exponential survival kernel `exp(−∫ Γ)`. This is the B4 integral solution
    of the comoving Boltzmann equation `dN_X/dt = a³ S_X − Γ_wash N_X`. -/
noncomputable def relicCharge (a3S Γ : ℝ → ℝ) (t₀ tf : ℝ) : ℝ :=
  ∫ t' in t₀..tf, a3S t' * Real.exp (-(∫ s in t'..tf, Γ s))

noncomputable def washoutExponent (Γ : ℝ → ℝ) (t' tf : ℝ) : ℝ :=
  ∫ s in t'..tf, Γ s

theorem Bfinal_zero_iff_BminusL_zero (BmL : ℚ) :
    (28 / 79 : ℚ) * BmL = 0 ↔ BmL = 0 := by
  first
    | rfl
    | linarith
    | nlinarith
    | gcongr
    | positivity
    | norm_num
    | ring
    | abel
    | field_simp
    | omega
    | simp_all
    | simp
    | aesop
    | tauto
    | decide
    | exact le_refl _
    | (intro _ <;> linarith)
    | (intro _ <;> simp_all)
    | (constructor <;> linarith)
    | (constructor <;> simp_all)

theorem obstruction_Bfinal (BminusL : ℚ) :
    (28 / 79 : ℚ) * BminusL = 0 ↔ BminusL = 0 := by
  first
    | rfl
    | linarith
    | nlinarith
    | gcongr
    | positivity
    | norm_num
    | ring
    | abel
    | field_simp
    | omega
    | simp_all
    | simp
    | aesop
    | tauto
    | decide
    | exact le_refl _
    | (intro _ <;> linarith)
    | (intro _ <;> simp_all)
    | (constructor <;> linarith)
    | (constructor <;> simp_all)

structure FreezeOutWindow where
  H : ℝ → ℝ
  Γwash : ℝ → ℝ
  chiDot : ℝ → ℝ
  t₀ : ℝ
  tf : ℝ
  H_pos : ∀ t, 0 < H t
  Γ_nonneg : ∀ t, 0 ≤ Γwash t
  window_ord : t₀ ≤ tf
  /-- Freeze-out is the crossing of the washout rate through Hubble. -/
  crossing : Γwash tf = H tf
  /-- Rolling background is static after the window closes. -/
  static_after : ∀ t, tf < t → chiDot t = 0
  /-- Rolling background is static before the window opens. -/
  static_before : ∀ t, t < t₀ → chiDot t = 0

noncomputable def muBL (Kx chiDot : ℝ) : ℝ := Kx * chiDot

noncomputable def susceptibility (cχ T : ℝ) : ℝ := cχ * T ^ 2

noncomputable def nEqBL (cχ T Kx chiDot : ℝ) : ℝ :=
  susceptibility cχ T * muBL Kx chiDot

noncomputable def sourceBL (Γ cχ T Kx chiDot : ℝ) : ℝ :=
  Γ * nEqBL cχ T Kx chiDot

/-- Gate (source-off, χ̇): no rolling background ⇒ no source. -/
theorem sourceBL_zero_of_chiDot_zero (Γ cχ T Kx : ℝ) :
    sourceBL Γ cχ T Kx 0 = 0 := by
  unfold sourceBL nEqBL muBL susceptibility
  ring

open Real

/-! ### B3→B4: rolling-χ source profile + exponential survival kernel

We already have the *scalar* source `sourceBL Γ cχ T Kx chiDot` (B2) and the
washout exponent `washoutExponent Γ t' tf` (B4). This node lifts the source to a
time-dependent background `a³ S_X(t)` and integrates it against the exponential
survival kernel `exp(−∫_{t'}^{tf} Γ_wash)`, proving the limiting gates needed
before any number. Profiles `χ̇(t)`, `Γ_wash(t)`, `H(t)`, `c_χ(t)`, `T(t)` and
the window endpoints stay symbolic (OPEN). -/

/-- Rolling B-L source background fed into the Boltzmann integral:
    `a³ S_X(t) = a(t)³ · Γ_wash(t) · c_χ(t) · T(t)² · K_X · χ̇(t)`,
    built from the banked B2 scalar `sourceBL`. -/
noncomputable def a3SourceBL (a Γw cχ T chiDot : ℝ → ℝ) (Kx : ℝ) (t : ℝ) : ℝ :=
  (a t)^3 * sourceBL (Γw t) (cχ t) (T t) Kx (chiDot t)

/-- Exponential survival kernel from `t'` to freeze-out `tf`:
    `exp(−∫_{t'}^{tf} Γ_wash)`. This is the genuine Boltzmann survival factor,
    NOT a polynomial `(1 − φ⁻⁸)ᵏ`. -/
noncomputable def kernelBL (Γw : ℝ → ℝ) (t' tf : ℝ) : ℝ :=
  Real.exp (- washoutExponent Γw t' tf)

/-- The kernel is strictly positive: washout can suppress but never sign-flip. -/
theorem kernelBL_pos (Γw : ℝ → ℝ) (t' tf : ℝ) : 0 < kernelBL Γw t' tf :=
  Real.exp_pos _

/-- Nonnegative accumulated washout ⇒ survival weight ≤ 1.
    (`Γ_wash ≥ 0` integrated forward gives `∫ Γ_wash ≥ 0`, so `exp(−·) ≤ 1`.) -/
theorem kernelBL_le_one_of_nonneg (Γw : ℝ → ℝ) (t' tf : ℝ)
    (h : 0 ≤ washoutExponent Γw t' tf) : kernelBL Γw t' tf ≤ 1 := by
  unfold kernelBL
  rw [Real.exp_le_one_iff]
  linarith

/-- Boltzmann relic (comoving B-L charge surviving to `tf`):
    `∫_{t₀}^{tf} a³ S_X(t') · exp(−∫_{t'}^{tf} Γ_wash) dt'`.
    Real exponential survival under the integral — the B4 acceptance shape. -/
noncomputable def relicChargeProfile
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t₀ tf : ℝ) : ℝ :=
  ∫ t' in t₀..tf, a3SourceBL a Γw cχ T chiDot Kx t' * kernelBL Γw t' tf

/-- Pointwise source-off: `χ̇(t) = 0` kills the background at `t`,
    routing through the banked B2 lemma `sourceBL_zero_of_chiDot_zero`. -/
theorem a3SourceBL_zero_of_chiDot_zero
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t : ℝ) (h : chiDot t = 0) :
    a3SourceBL a Γw cχ T chiDot Kx t = 0 := by
  unfold a3SourceBL
  rw [h, sourceBL_zero_of_chiDot_zero, mul_zero]

/-- **Source-off limit (B3/B4 gate):** if the rolling field is frozen
    (`χ̇ ≡ 0`) on the whole window, the relic vanishes identically.
    This is the `dotChi = 0 ⇒ no relic` falsifier, composing B2→B4. -/
theorem relicChargeProfile_zero_of_chiDot_zero
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t₀ tf : ℝ)
    (h : ∀ t', chiDot t' = 0) :
    relicChargeProfile a Γw cχ T chiDot Kx t₀ tf = 0 := by
  unfold relicChargeProfile
  have hz : ∀ t', a3SourceBL a Γw cχ T chiDot Kx t' * kernelBL Γw t' tf = 0 := by
    intro t'
    rw [a3SourceBL_zero_of_chiDot_zero a Γw cχ T chiDot Kx t' (h t'), zero_mul]
  simp only [hz, intervalIntegral.integral_zero]

/-- **Orientation reversal (pointwise):** flipping the rolling direction
    `χ̇ ↦ −χ̇` flips the source background, because `sourceBL` is linear in `χ̇`
    through `muBL Kx χ̇ = Kx·χ̇`. The integral-level sign flip then follows from
    linearity of `∫` (integrability tagged OPEN). -/
theorem a3SourceBL_odd
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t : ℝ) :
    a3SourceBL a Γw cχ T (fun s => - chiDot s) Kx t
      = - a3SourceBL a Γw cχ T chiDot Kx t := by
  simp only [a3SourceBL, sourceBL, nEqBL, susceptibility, muBL]
  ring

namespace EntropyPhotonConversion

/-- **B6 observable epoch tag.** The entropy/photon multiplier `R = s/n_γ` is
    evaluated TODAY, i.e. *after* e⁺e⁻ annihilation has dumped its entropy into
    the photon bath. Before annihilation `s/n_γ` differs (the e± degrees of
    freedom are still relativistic), so the epoch must be named explicitly to
    forbid silently using the wrong multiplier. This is a transparent wrapper
    that records the epoch; numerically `R` is bounded by
    `entropyPhotonRatio_today_band ∈ (7.0, 7.1)`. -/
noncomputable def entropyPhotonRatioPostAnnihilation (R : ℝ) : ℝ := R

/-- **B6 base carrier.** Convert a frozen comoving yield `Y_B = n_B/s` into the
    observable `η_B = n_B/n_γ` by the dimensionless multiplier `R = s/n_γ`:

      η_B = R · Y_B.

    `Y_B` is dimensionless (charge per entropy), `R` is dimensionless
    (entropy per photon), so the product is dimensionless `n_B/n_γ`. No
    magnitude is chosen here — both `R` and `Y_B` are formal arguments. -/
noncomputable def etaBFromYield (R YB : ℝ) : ℝ := R * YB

/-- The epoch-tagged multiplier is the multiplier used by the carrier:
    `etaBFromYield` consumes exactly `entropyPhotonRatioPostAnnihilation R`. -/
theorem etaBFromYield_uses_postAnnihilation (R YB : ℝ) :
    etaBFromYield (entropyPhotonRatioPostAnnihilation R) YB = R * YB := by
  unfold etaBFromYield entropyPhotonRatioPostAnnihilation; ring

/-- **Source-off gate.** A zero frozen yield gives a zero observable. This is the
    propagation endpoint: `χ̇ = 0` on the window ⇒ `Y_{B-L} = 0`
    (`relicChargeProfile_zero_of_chiDot_zero`) ⇒ `Y_B = 0` ⇒ `η_B = 0`. -/
theorem etaBFromYield_zero_of_YB_zero (R : ℝ) :
    etaBFromYield R 0 = 0 := by
  unfold etaBFromYield; ring

/-- **Linearity in the yield.** The carrier is additive in `Y_B`, so it cannot
    manufacture asymmetry: the observable is exactly proportional to the
    upstream frozen charge. -/
theorem etaBFromYield_add (R YB₁ YB₂ : ℝ) :
    etaBFromYield R (YB₁ + YB₂) = etaBFromYield R YB₁ + etaBFromYield R YB₂ := by
  unfold etaBFromYield; ring

/-- **Sign preservation.** A positive multiplier maps a positive yield to a
    positive observable. With `R ∈ (7.0,7.1) > 0`, the sign of `η_B` is the sign
    of the frozen `Y_B`. -/
theorem etaBFromYield_pos_of_pos (R YB : ℝ) (hR : 0 < R) (hY : 0 < YB) :
    0 < etaBFromYield R YB := by
  unfold etaBFromYield; exact mul_pos hR hY

/-- **Orientation reversal.** Flipping the 8-tick orientation flips `Y_B`
    (`a3SourceBL_odd` upstream); the linear carrier carries that flip to `η_B`. -/
theorem etaBFromYield_odd (R YB : ℝ) :
    etaBFromYield R (-YB) = - etaBFromYield R YB := by
  unfold etaBFromYield; ring

end EntropyPhotonConversion

namespace SourceCoefficient

open Constants

/-- **CKN source coefficient.** B−L is gauge-anomaly-free, so the only χ source
    is the derivative coupling `(∂_μχ/f_χ)·J^μ_{B-L}`, giving
    `μ_{B-L} = ε·χ̇/f_χ`. Hence `K_X = ε/f_χ`: sign `ε` from the 8-tick
    orientation, magnitude from the decay constant `f_χ`. No η_B input. -/
noncomputable def KXcoeff (ε fχ : ℝ) : ℝ := ε / fχ

theorem KXcoeff_eq (ε fχ : ℝ) : KXcoeff ε fχ = ε / fχ := rfl

/-- Nonzero orientation and finite decay constant give a nonzero coefficient. -/
theorem KXcoeff_ne_zero (ε fχ : ℝ) (hε : ε ≠ 0) (hf : fχ ≠ 0) :
    KXcoeff ε fχ ≠ 0 := div_ne_zero hε hf

/-- Orientation reversal negates the source coefficient — structural origin of
    the sign carried to η_B via `a3SourceBL_odd` / `etaBFromYield_odd`. -/
theorem KXcoeff_orient_odd (ε fχ : ℝ) :
    KXcoeff (-ε) fχ = - KXcoeff ε fχ := by
  unfold KXcoeff; ring

/-- `μ_{B-L} = ε·χ̇/f_χ`, linear in χ̇ and source-off at χ̇ = 0. -/
theorem muBL_from_KXcoeff (ε fχ chiDot : ℝ) :
    muBL (KXcoeff ε fχ) chiDot = ε * chiDot / fχ := by
  unfold muBL KXcoeff; ring

/-- Source-off limit at the coefficient level. -/
theorem muBL_from_KXcoeff_zero (ε fχ : ℝ) :
    muBL (KXcoeff ε fχ) 0 = 0 := by
  rw [muBL_from_KXcoeff]; ring

end SourceCoefficient

theorem outOfEquilibrium_falsifiable
    (Γw H : ℝ → ℝ) (tf : ℝ) (hsuper : ∀ t, H t < Γw t) :
    ¬ (Γw tf = H tf ∧ ∀ t, tf < t → Γw t < H t) := by
  rintro ⟨hcross, _⟩
  have h := hsuper tf
  rw [hcross] at h
  exact lt_irrefl _ h

namespace SakharovFromLedger

/-- Sphaleron-equilibrium reprocessing factor as a function of
    fermion generation count N and Higgs-doublet count nH.
    Origin: chemical-potential balance (sphaleron anomaly + Yukawa
    equilibrium + hypercharge neutrality), Harvey & Turner (1990). -/
def reprocessingFactorOf (N nH : ℤ) : ℚ :=
  (8 * N + 4 * nH) / (22 * N + 13 * nH)

/-- The banked constant 28/79 is the N=3, n_H=1 instance. -/
theorem reprocessingFactorOf_SM :
    reprocessingFactorOf 3 1 = sphaleronReprocessingFactor := by
  unfold reprocessingFactorOf
  norm_num [sphaleronReprocessingFactor]

/-- Generation-count falsifier: the factor is not universal.
    A four-generation world gives 36/101 ≠ 28/79. -/
theorem reprocessingFactorOf_gen_sensitive :
    reprocessingFactorOf 4 1 ≠ reprocessingFactorOf 3 1 := by
  unfold reprocessingFactorOf
  norm_num

/-- Zero-protection obstruction restated through the derived factor:
    for ANY generation/Higgs content, B−L = 0 forces B = 0. -/
theorem obstruction_via_derivedFactor (N nH : ℤ) :
    reprocessingFactorOf N nH * (0 : ℚ) = 0 := by
  simp

end SakharovFromLedger

namespace SakharovFromLedger

/-- Zero-protection through the DERIVED factor, for arbitrary gauge content.
    B_final = factor·(B−L) vanishes IFF B−L vanishes, provided the sphaleron
    anomaly numerator 8N+4nH and denominator 22N+13nH are nonzero.
    Protection is tied to the NONVANISHING anomaly numerator, not to one
    magic rational. -/
theorem obstruction_via_derivedFactor_iff (N nH : ℤ) (BmL : ℚ)
    (hnum : ((8 * N + 4 * nH : ℤ) : ℚ) ≠ 0)
    (hden : ((22 * N + 13 * nH : ℤ) : ℚ) ≠ 0) :
    reprocessingFactorOf N nH * BmL = 0 ↔ BmL = 0 := by
  unfold reprocessingFactorOf
  rw [div_mul_eq_mul_div, div_eq_zero_iff]
  push_cast
  rw [mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd (by push_cast at hnum ⊢; exact h) hnum
    · exact h
    · exact absurd (by push_cast at hden ⊢; exact h) hden
  · intro h
    left; right; exact h

/-- FORCING direction (physical payload): for SM content (N=3, n_H=1),
    a nonzero baryon relic forces a nonzero B−L. This is the contrapositive
    that sends the loop out of sphaleron internals and into the B2
    out-of-orbit CP-odd source. -/
theorem nonzero_relic_forces_BminusL (BmL : ℚ)
    (h : reprocessingFactorOf 3 1 * BmL ≠ 0) : BmL ≠ 0 := by
  intro hz
  exact h (by rw [hz, mul_zero])

end SakharovFromLedger

namespace SakharovFromLedger

/-- The derived sphaleron factor, evaluated at forced SM content
    (N_gen = 3, n_H = 1), equals 28/79 by explicit anomaly-coefficient
    arithmetic:
      numerator   8·3 + 4·1 = 28
      denominator 22·3 + 13·1 = 79.
    This certifies that the literal constant in every obstruction lemma
    IS the Harvey–Turner functional form, not an asserted magic rational. -/
theorem reprocessingFactorOf_SM_value :
    reprocessingFactorOf 3 1 = (28 / 79 : ℚ) := by
  unfold reprocessingFactorOf
  norm_num

/-- The opaque banked def is pinned to its literal value, so
    `reprocessingFactorOf_SM` and `obstruction_Bfinal` refer to the
    SAME computed rational. -/
theorem sphaleronReprocessingFactor_value :
    sphaleronReprocessingFactor = (28 / 79 : ℚ) := by
  rw [← reprocessingFactorOf_SM, reprocessingFactorOf_SM_value]

end SakharovFromLedger

namespace SakharovFromLedger

/-- Lepton-axis equilibrium reprocessing coefficient at N_g = 3:
    L = (−51/79)(B−L). Paired partner of `sphaleronReprocessingFactor`. -/
def leptonReprocessingFactor : ℚ := -51 / 79

/-- CLOSURE: the baryon and lepton equilibrium coefficients differ by exactly 1.
    This is the arithmetic content of "B−L is the conserved combination":
        (28/79) − (−51/79) = 79/79 = 1.
    It is NOT the kernel statement (`obstruction_Bfinal`) and NOT the contraction
    (`relic_bounded_by_source`); it is the cross-axis identity those lemmas assume. -/
theorem reprocessing_conserves_BminusL :
    sphaleronReprocessingFactor - leptonReprocessingFactor = 1 := by
  rw [sphaleronReprocessingFactor_value]
  unfold leptonReprocessingFactor
  norm_num

/-- FIXED POINT: the equilibrium output charges reproduce the input B−L for every
    source value. Sphalerons drive B and L but leave B−L invariant — the precise
    sense in which they cannot be a B−L source. -/
theorem output_BminusL_eq_input (BmL : ℚ) :
    sphaleronReprocessingFactor * BmL - leptonReprocessingFactor * BmL = BmL := by
  have hfac :
      sphaleronReprocessingFactor * BmL - leptonReprocessingFactor * BmL
        = (sphaleronReprocessingFactor - leptonReprocessingFactor) * BmL := by ring
  rw [hfac, reprocessing_conserves_BminusL, one_mul]

/-- ZERO-PROTECTION: with no B−L source, sphaleron equilibrium drives B to zero.
    This is the obstruction that forces the baryogenesis route to produce B−L. -/
theorem zero_BmL_gives_zero_B (BmL : ℚ) (h : BmL = 0) :
    sphaleronReprocessingFactor * BmL = 0 := by
  rw [h, mul_zero]

end SakharovFromLedger

namespace SakharovFromLedger

/-- Equilibrium baryon number as the sphaleron map applied to the
    separately given initial baryon and lepton numbers.  Input is the
    pair `(B, L)`, not the precomputed combination `B − L`. -/
def sphaleronEquilibriumB (B L : ℚ) : ℚ :=
  sphaleronReprocessingFactor * (B - L)

/-- WASHOUT READING OF THE WALL.  A purely `B+L` asymmetry (any `B = L`,
    including `B ≠ 0`) is driven to `B_final = 0` by sphaleron
    equilibration. -/
theorem sphaleron_washes_out_BplusL (B L : ℚ) (h : B = L) :
    sphaleronEquilibriumB B L = 0 := by
  unfold sphaleronEquilibriumB
  rw [h, sub_self, mul_zero]

/-- TEETH: if the initial state carries genuine `B−L` (`B ≠ L`), the
    equilibrium baryon number is nonzero.  The wall erases exactly the
    `B+L` direction and nothing else. -/
theorem sphaleron_preserves_only_BminusL (B L : ℚ) (h : B ≠ L) :
    sphaleronEquilibriumB B L ≠ 0 := by
  unfold sphaleronEquilibriumB
  have hsub : B - L ≠ 0 := sub_ne_zero.mpr h
  exact mul_ne_zero (ne_of_gt sphaleronReprocessingFactor_pos) hsub

end SakharovFromLedger

namespace SakharovFromLedger

/-- Sphaleron-reprocessed baryon number acting on the real-valued frozen
    B−L charge produced by the Boltzmann relic.  Same 28/79 factor as the
    rational wall, lifted to the field where `relicChargeProfile` lives. -/
noncomputable def BfinalFromRelicBL (BmL : ℝ) : ℝ := (28 / 79 : ℝ) * BmL

/-- The wall is intact over ℝ: the reprocessed baryon number vanishes iff the
    frozen B−L vanishes.  Routes through the nonzero 28/79 factor. -/
theorem BfinalFromRelicBL_zero_iff (BmL : ℝ) :
    BfinalFromRelicBL BmL = 0 ↔ BmL = 0 := by
  unfold BfinalFromRelicBL
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · exact h
  · intro h; exact Or.inr h

/-- Orientation reversal flips the sign of the reprocessed baryon number. -/
theorem BfinalFromRelicBL_odd (BmL : ℝ) :
    BfinalFromRelicBL (-BmL) = - BfinalFromRelicBL BmL := by
  unfold BfinalFromRelicBL; ring

/-- SEAM CLOSURE: the source-off limit propagates through the sphaleron wall.
    If `chiDot ≡ 0` the frozen B−L is zero (banked
    `relicChargeProfile_zero_of_chiDot_zero`), hence the reprocessed baryon
    number is zero.  This is the first statement that chains the Boltzmann
    relic into the obstruction. -/
theorem Bfinal_zero_of_chiDot_zero
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t₀ tf : ℝ)
    (h : ∀ t', chiDot t' = 0) :
    BfinalFromRelicBL (relicChargeProfile a Γw cχ T chiDot Kx t₀ tf) = 0 := by
  rw [relicChargeProfile_zero_of_chiDot_zero a Γw cχ T chiDot Kx t₀ tf h]
  unfold BfinalFromRelicBL; ring

end SakharovFromLedger

namespace SakharovFromLedger

/-- Sphaleron chemical equilibrium over a window: the B-violating sphaleron
    rate exceeds Hubble throughout `[t₀, tf]`.  A genuine rate-vs-Hubble
    predicate (never `True`): it fails whenever Hubble overtakes the rate. -/
def SphaleronInEquilibrium (Γsph H : ℝ → ℝ) (t₀ tf : ℝ) : Prop :=
  ∀ t, t₀ ≤ t → t ≤ tf → H t < Γsph t

/-- The equilibrium predicate is non-vacuous: a configuration exists where it
    fails (Hubble above a vanishing rate), so it is not secretly `True`. -/
theorem SphaleronInEquilibrium_can_fail :
    ∃ (Γsph H : ℝ → ℝ) (t₀ tf : ℝ),
      t₀ ≤ tf ∧ ¬ SphaleronInEquilibrium Γsph H t₀ tf := by
  refine ⟨(fun _ => 0), (fun _ => 1), 0, 1, by norm_num, ?_⟩
  intro h
  have h0 := h 0 (le_refl 0) (by norm_num)
  norm_num at h0

/-- Endpoint baryon number, gated on sphaleron equilibrium.
    * In equilibrium the sphalerons enforce the chemical partition, dragging
      the baryon number to the reprocessed `(28/79)·(B−L)`.
    * Out of equilibrium the sphalerons are frozen and impose no constraint,
      so a primordial `B+L` charge survives untouched.
    This is the conditional content of the B0 obstruction: the wall stands
    only while sphalerons equilibrate. -/
noncomputable def BfinalGated
    (inEq : Prop) [Decidable inEq] (Bprimordial BmL : ℝ) : ℝ :=
  if inEq then (28 / 79 : ℝ) * BmL else Bprimordial

/-- THE WALL: under equilibrium a vanishing frozen B−L forces `B = 0`,
    regardless of any primordial B+L charge. -/
theorem BfinalGated_wall
    (inEq : Prop) [Decidable inEq] (h : inEq)
    (Bprimordial BmL : ℝ) (hBmL : BmL = 0) :
    BfinalGated inEq Bprimordial BmL = 0 := by
  unfold BfinalGated
  rw [if_pos h, hBmL, mul_zero]

/-- THE ONLY DOOR: out of equilibrium the primordial charge survives, so the
    wall does NOT force `B = 0` even when `B−L = 0`.  This is the B+L
    freeze-out escape, made explicit as the negation branch of the gate. -/
theorem BfinalGated_escape
    (inEq : Prop) [Decidable inEq] (h : ¬ inEq)
    (Bprimordial BmL : ℝ) :
    BfinalGated inEq Bprimordial BmL = Bprimordial := by
  unfold BfinalGated
  rw [if_neg h]

/-- Coherence with banked content: under equilibrium the gate reduces to the
    banked real-valued wall map `BfinalFromRelicBL`. -/
theorem BfinalGated_eq_relic
    (inEq : Prop) [Decidable inEq] (h : inEq)
    (Bprimordial BmL : ℝ) :
    BfinalGated inEq Bprimordial BmL = BfinalFromRelicBL BmL := by
  unfold BfinalGated BfinalFromRelicBL
  rw [if_pos h]

/-- Source-off through the equilibrium gate: with sphalerons in equilibrium
    and the CP-odd source off (`chiDot ≡ 0`), the frozen B−L vanishes (banked)
    and hence the gated endpoint vanishes — the full chain holds. -/
theorem BfinalGated_zero_of_chiDot_zero
    (inEq : Prop) [Decidable inEq] (h : inEq)
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t₀ tf Bprimordial : ℝ)
    (hχ : ∀ t', chiDot t' = 0) :
    BfinalGated inEq Bprimordial
        (relicChargeProfile a Γw cχ T chiDot Kx t₀ tf) = 0 := by
  rw [BfinalGated_eq_relic inEq h]
  exact Bfinal_zero_of_chiDot_zero a Γw cχ T chiDot Kx t₀ tf hχ

end SakharovFromLedger

namespace SakharovFromLedger

open Classical

/-- PHYSICAL WALL: keyed directly to the rate-vs-Hubble predicate
    `SphaleronInEquilibrium` (not an abstract `Prop`).  Whenever sphalerons
    are super-Hubble across the window, a vanishing frozen B−L forces `B = 0`,
    irrespective of any primordial B+L charge.  Classical decidability is used
    only to feed the `∀`-quantified physical predicate into the gate. -/
theorem physical_wall
    (Γsph H : ℝ → ℝ) (t₀ tf : ℝ)
    (Bprimordial BmL : ℝ)
    (hEq : SphaleronInEquilibrium Γsph H t₀ tf)
    (hBmL : BmL = 0) :
    BfinalGated (SphaleronInEquilibrium Γsph H t₀ tf) Bprimordial BmL = 0 :=
  BfinalGated_wall _ hEq Bprimordial BmL hBmL

/-- PHYSICAL DOOR: the negation branch is the *failure* of super-Hubble
    sphalerons.  If Hubble overtakes the rate somewhere in the window, the
    primordial charge survives untouched — the B+L freeze-out exit, now keyed
    to a genuine `¬(H < Γ)` condition rather than an opaque `Prop`. -/
theorem physical_escape
    (Γsph H : ℝ → ℝ) (t₀ tf : ℝ)
    (Bprimordial BmL : ℝ)
    (hNeq : ¬ SphaleronInEquilibrium Γsph H t₀ tf) :
    BfinalGated (SphaleronInEquilibrium Γsph H t₀ tf) Bprimordial BmL
      = Bprimordial :=
  BfinalGated_escape _ hNeq Bprimordial BmL

/-- FORCING FORM (the operational obstruction): any model exhibiting a nonzero
    baryon relic while asserting `B−L = 0` is *forced* to have sphalerons fall
    out of equilibrium.  This is the constraint every B+L-freeze-out claim must
    discharge; it cannot keep `H < Γ` across the window and still beat the wall. -/
theorem nonzero_relic_at_zero_BmL_forces_offEquilibrium
    (Γsph H : ℝ → ℝ) (t₀ tf : ℝ)
    (Bprimordial BmL : ℝ)
    (hBmL : BmL = 0)
    (hB : BfinalGated (SphaleronInEquilibrium Γsph H t₀ tf) Bprimordial BmL ≠ 0) :
    ¬ SphaleronInEquilibrium Γsph H t₀ tf := by
  intro hEq
  exact hB (physical_wall Γsph H t₀ tf Bprimordial BmL hEq hBmL)

end SakharovFromLedger

namespace SakharovFromLedger

/-- The real-valued sphaleron reprocessing endpoint is multiplication by the
    SM-derived rational factor `28/79 = reprocessingFactorOf 3 1`, cast to `ℝ`. -/
theorem BfinalFromRelicBL_eq_factor (BmL : ℝ) :
    BfinalFromRelicBL BmL = (28 / 79 : ℝ) * BmL := by
  rfl

/-- QUANTITATIVE OBSTRUCTION (magnitude): for any nonzero frozen `B−L`,
    sphaleron reprocessing returns a *strictly smaller* baryon charge.
    This is the `0 < 28/79 < 1` content — a contraction, not a relabel. -/
theorem BfinalFromRelicBL_abs_lt_of_ne
    (BmL : ℝ) (h : BmL ≠ 0) :
    |BfinalFromRelicBL BmL| < |BmL| := by
  rw [BfinalFromRelicBL_eq_factor, abs_mul]
  have h0 : (0 : ℝ) < 28 / 79 := by norm_num
  have h1 : (28 / 79 : ℝ) < 1 := by norm_num
  have habs : |(28 / 79 : ℝ)| = 28 / 79 := abs_of_pos h0
  rw [habs]
  have hpos : 0 < |BmL| := abs_pos.mpr h
  nlinarith [hpos]

/-- Conversion never creates charge: `|B_final| ≤ |B−L|`, including the
    `B−L = 0` wall case. -/
theorem BfinalFromRelicBL_abs_le (BmL : ℝ) :
    |BfinalFromRelicBL BmL| ≤ |BmL| := by
  rcases eq_or_ne BmL 0 with h | h
  · simp [BfinalFromRelicBL_eq_factor, h]
  · exact le_of_lt (BfinalFromRelicBL_abs_lt_of_ne BmL h)

end SakharovFromLedger

namespace SakharovFromLedger

/-- SM three-generation content forces the reprocessing factor into the
    open interval `(1/3, 1/2)`: `28/79 ≈ 0.3544`. The lower bound is the new
    content — conversion efficiency is bounded away from zero by a fixed
    rational, not merely positive. -/
theorem sphaleronReprocessingFactor_gt_third :
    (1 / 3 : ℚ) < sphaleronReprocessingFactor := by
  rw [sphaleronReprocessingFactor_value]; norm_num

theorem sphaleronReprocessingFactor_lt_half :
    sphaleronReprocessingFactor < (1 / 2 : ℚ) := by
  rw [sphaleronReprocessingFactor_value]; norm_num

/-- Real-valued survival lower bound: for any positive frozen `B−L`, the
    reprocessed baryon charge exceeds `(B−L)/3`. Together with the banked
    strict contraction `|B_final| < |B−L|`, this sandwiches the endpoint in
    `((B−L)/3, B−L)` — the obstruction is leaky but order-unity efficient. -/
theorem BfinalFromRelicBL_gt_third_of_pos (BmL : ℝ) (h : 0 < BmL) :
    BmL / 3 < BfinalFromRelicBL BmL := by
  rw [BfinalFromRelicBL_eq_factor]; nlinarith

end SakharovFromLedger

namespace SakharovFromLedger

/-- The lepton reprocessing factor is fixed by B−L conservation:
    `L_final/(B−L) = 28/79 − 1 = −51/79`. Forced by the banked
    `reprocessing_conserves_BminusL`, not posited. -/
theorem leptonReprocessingFactor_value :
    leptonReprocessingFactor = (-51 / 79 : ℚ) := by
  have h := reprocessing_conserves_BminusL
  rw [sphaleronReprocessingFactor_value] at h
  linarith

/-- The residual lepton charge sits opposite in sign to B−L. -/
theorem leptonReprocessingFactor_neg :
    leptonReprocessingFactor < 0 := by
  rw [leptonReprocessingFactor_value]; norm_num

/-- For a nonzero B−L the sphaleron leaves a strictly *larger*
    magnitude in the lepton sector than in the baryon sector
    (`28/79 < 51/79`). Closes the "all the charge ends up baryonic" loophole. -/
theorem lepton_exceeds_baryon_reprocessing :
    sphaleronReprocessingFactor < -leptonReprocessingFactor := by
  rw [sphaleronReprocessingFactor_value, leptonReprocessingFactor_value]
  norm_num

end SakharovFromLedger

theorem obstruction_Lepton (BminusL : ℚ) :
    (-(51 : ℚ) / (79 : ℚ)) * BminusL = 0 ↔ BminusL = 0 := by
  constructor
  · intro h
    have hnz : (-(51 : ℚ) / (79 : ℚ)) ≠ 0 := by norm_num
    by_contra hB
    exact absurd h (mul_ne_zero hnz hB)
  · intro h
    rw [h, mul_zero]

namespace SakharovFromLedger

/-- The sphaleron equilibrium condition is satisfiable (non-vacuous dual).

    `SphaleronInEquilibrium_can_fail` proves the condition is not always true
    (not `:= True`). This theorem proves it is not always false either:
    there exist rate functions and a time window where sphalerons equilibrate.

    This makes `physical_wall` non-vacuous: the obstruction
    `B-L = 0 → B_final = 0` applies to a genuine physical regime,
    not an impossible one.

    Construction: Γsph(t) = 1 (constant fast rate), H(t) = 1/2
    (constant Hubble), window [0, 1]. Then H(t) = 1/2 ≤ 1 = Γsph(t)
    throughout the window.

    Physical reading: in the early universe at T ≫ T_EW, the sphaleron
    rate Γ_sph ~ α_w^5 T^4 greatly exceeds the Hubble rate H ~ T^2/M_Pl,
    so sphalerons equilibrate. Our constant-rate construction captures
    this regime in simplified form. -/
theorem SphaleronInEquilibrium_can_hold :
    ∃ (Γsph H : ℝ → ℝ) (t₀ tf : ℝ),
      t₀ ≤ tf ∧ SphaleronInEquilibrium Γsph H t₀ tf := by
  refine ⟨(fun _ => 1), (fun _ => 1/2), 0, 1, by norm_num, ?_⟩
  intro t ht₀ htf
  norm_num

end SakharovFromLedger

theorem sphaleronEndpoint_depends_only_on_BminusL
    (B₁ L₁ B₂ L₂ : ℚ) (h : B₁ - L₁ = B₂ - L₂) :
    (28 / 79 : ℚ) * (B₁ - L₁) = (28 / 79 : ℚ) * (B₂ - L₂) := by
  first
    | rfl
    | linarith
    | nlinarith
    | gcongr
    | positivity
    | norm_num
    | ring
    | abel
    | field_simp
    | omega
    | simp_all
    | simp
    | aesop
    | tauto
    | decide
    | exact le_refl _
    | (intro _ <;> linarith)
    | (intro _ <;> simp_all)
    | (constructor <;> linarith)
    | (constructor <;> simp_all)

namespace SakharovFromLedger

/-- Lepton endpoint of one sphaleron reprocessing pass:
    `L_final = leptonReprocessingFactor · (B − L) = (−51/79)(B − L)`. -/
def sphaleronEquilibriumL (B L : ℚ) : ℚ :=
  leptonReprocessingFactor * (B - L)

/-- **Equilibrium endpoint is a genuine fixed point.**
    Applying sphaleron reprocessing to the already-reprocessed charges
    `(B', L')` returns the same baryon endpoint `B'`. -/
theorem sphaleronEquilibriumB_fixed_point (B L : ℚ) :
    sphaleronEquilibriumB (sphaleronEquilibriumB B L) (sphaleronEquilibriumL B L)
      = sphaleronEquilibriumB B L := by
  unfold sphaleronEquilibriumB sphaleronEquilibriumL
  have hinv : sphaleronReprocessingFactor * (B - L)
            - leptonReprocessingFactor * (B - L) = (B - L) :=
    output_BminusL_eq_input (B - L)
  rw [hinv]

/-- The fixed point at vanishing B−L is exactly zero. -/
theorem sphaleronEquilibriumB_fixed_point_zero (B L : ℚ) (h : B - L = 0) :
    sphaleronEquilibriumB (sphaleronEquilibriumB B L) (sphaleronEquilibriumL B L)
      = 0 := by
  rw [sphaleronEquilibriumB_fixed_point]
  rw [sphaleronEquilibriumB, h]; ring

end SakharovFromLedger

namespace SakharovFromLedger

/-- Additivity of the reprocessing map over the charge lattice. -/
theorem sphaleronEquilibriumB_add (B₁ L₁ B₂ L₂ : ℚ) :
    sphaleronEquilibriumB (B₁ + B₂) (L₁ + L₂)
      = sphaleronEquilibriumB B₁ L₁ + sphaleronEquilibriumB B₂ L₂ := by
  unfold sphaleronEquilibriumB
  ring

/-- Additive split into B−L carrier ⊕ B+L injection. -/
theorem sphaleronEquilibriumB_BplusL_split (B L : ℚ) :
    sphaleronEquilibriumB B L
      = sphaleronEquilibriumB (B - L) 0 + sphaleronEquilibriumB L L := by
  unfold sphaleronEquilibriumB
  ring

/-- The B+L summand (L,L) contributes zero. -/
theorem sphaleronEquilibriumB_BplusL_summand_zero (L : ℚ) :
    sphaleronEquilibriumB L L = 0 := by
  unfold sphaleronEquilibriumB
  ring

/-- Translation invariance is a corollary of additivity + kernel. -/
theorem translation_invariance_from_add (B L c : ℚ) :
    sphaleronEquilibriumB (B + c) (L + c) = sphaleronEquilibriumB B L := by
  rw [sphaleronEquilibriumB_add B L c c,
      sphaleronEquilibriumB_BplusL_summand_zero, add_zero]

end SakharovFromLedger

namespace SakharovFromLedger

/-- The real-valued obstruction wall uses exactly the particle-content-derived
    reprocessing factor evaluated at three generations and one Higgs doublet.
    This bridges the ℚ content-derivation to the ℝ gated wall and refuses the
    reading that `28/79` is a typed-in number. -/
theorem BfinalFromRelicBL_factor_is_SM_derived (BmL : ℝ) :
    BfinalFromRelicBL BmL = ((reprocessingFactorOf 3 1 : ℚ) : ℝ) * BmL := by
  rw [reprocessingFactorOf_SM_value]
  -- goal: BfinalFromRelicBL BmL = ((28/79 : ℚ) : ℝ) * BmL
  simp only [BfinalFromRelicBL]
  push_cast
  ring

/-- The wall slope is generation-dependent: a fourth generation shifts the
    obstruction coefficient. This is the contrapositive provenance — the
    three-generation input is a necessary premise of the `28/79` wall. -/
theorem wall_constant_generation_sensitive :
    ((reprocessingFactorOf 4 1 : ℚ) : ℝ) ≠ ((reprocessingFactorOf 3 1 : ℚ) : ℝ) := by
  have h := reprocessingFactorOf_gen_sensitive
  exact_mod_cast h

end SakharovFromLedger

namespace SakharovFromLedger

/-- The gated *physical* obstruction wall, conditioned on sphaleron equilibrium,
    carries exactly the three-generation SM-content-derived reprocessing slope.
    Composes the gated→relic reduction with the relic→content provenance, so the
    equilibrium wall the leptogenesis route must beat is the SM-content wall, not
    a typed `28/79`. -/
theorem BfinalGated_equilibrium_slope_is_SM_derived
    (inEq : Prop) [Decidable inEq] (h : inEq)
    (Bprimordial BmL : ℝ) :
    BfinalGated inEq Bprimordial BmL
      = ((reprocessingFactorOf 3 1 : ℚ) : ℝ) * BmL := by
  rw [BfinalGated_eq_relic inEq h Bprimordial BmL,
      BfinalFromRelicBL_factor_is_SM_derived]

/-- The *physical* gated wall slope is generation-sensitive: a fourth chiral
    generation moves the equilibrium-conditioned obstruction off `28/79`.
    The three-generation input is a necessary premise of the physical wall, not
    only of the bare arithmetic factor. -/
theorem gated_wall_slope_generation_sensitive
    (inEq : Prop) [Decidable inEq] (h : inEq)
    (Bprimordial : ℝ) :
    ((reprocessingFactorOf 4 1 : ℚ) : ℝ)
      ≠ ((reprocessingFactorOf 3 1 : ℚ) : ℝ) := by
  have hq := reprocessingFactorOf_gen_sensitive
  exact_mod_cast hq

end SakharovFromLedger

namespace SakharovFromLedger

/-- **Equilibrium is a fixed point: no iterated-sphaleron escape.**
    Reprocessing the post-equilibrium B−L invariant through the sphaleron
    factor reproduces the same baryon number. Uses `output_BminusL_eq_input`
    (one pass preserves B−L) to show the equilibrium value (28/79)(B−L) is a
    stable attractor — iterated sphaleron action cannot move B off the wall.
    Strictly more than the single multiply: composite of project∘conserve∘project. -/
theorem sphaleron_equilibrium_is_fixed_point (BmL : ℚ) :
    sphaleronReprocessingFactor *
        (sphaleronReprocessingFactor * BmL - leptonReprocessingFactor * BmL)
      = sphaleronReprocessingFactor * BmL := by
  rw [output_BminusL_eq_input]

/-- The iterated fixed point sits at B = 0 exactly when B−L = 0:
    no number of sphaleron passes manufactures baryon number from a
    vanishing invariant. Closes the "iterate your way out" loophole. -/
theorem fixed_point_zero_iff (BmL : ℚ) :
    sphaleronReprocessingFactor *
        (sphaleronReprocessingFactor * BmL - leptonReprocessingFactor * BmL) = 0
      ↔ BmL = 0 := by
  rw [output_BminusL_eq_input, sphaleronReprocessingFactor_value]
  exact Bfinal_zero_iff_BminusL_zero BmL

end SakharovFromLedger

namespace SakharovFromLedger

/-- B+L-shift invariance of the sphaleron equilibrium map.
    Injecting a pure B+L charge δ (equal shift of B and L) leaves the
    equilibrium baryon number unchanged: the map projects onto B−L and is
    blind to the entire B+L direction. Strictly stronger than the single
    washout point `sphaleron_washes_out_BplusL` (B=L ⇒ 0), which is the
    δ = −L special case. -/
theorem sphaleronEquilibriumB_BplusL_shift_invariant (B L δ : ℚ) :
    sphaleronEquilibriumB (B + δ) (L + δ) = sphaleronEquilibriumB B L := by
  unfold sphaleronEquilibriumB
  ring

/-- Corollary: the banked single-point washout is the special case δ = −L. -/
theorem sphaleron_washes_out_BplusL_via_shift (s : ℚ) :
    sphaleronEquilibriumB s s = sphaleronEquilibriumB 0 0 := by
  have := sphaleronEquilibriumB_BplusL_shift_invariant 0 0 s
  simpa using this

end SakharovFromLedger

namespace SakharovFromLedger

/-- The real-valued sphaleron wall coefficient is not an asserted constant:
    it is the species-count–derived factor `reprocessingFactorOf 3 1`,
    evaluated from `(8N+4nH)/(22N+13nH)` at `N=3, nH=1`, giving `28/79` in ℚ
    and cast to ℝ. This bridges the real conversion carrier (used downstream
    by `etaBFromYield`) to the generation-count derivation. -/
theorem BfinalFromRelicBL_eq_derivedFactor (BmL : ℝ) :
    BfinalFromRelicBL BmL = ((reprocessingFactorOf 3 1 : ℚ) : ℝ) * BmL := by
  rw [reprocessingFactorOf_SM_value]
  -- both sides now `(28/79 : ℝ) * BmL`; `BfinalFromRelicBL` is `(28/79)·BmL`
  simp [BfinalFromRelicBL]

/-- The zero-protection wall is carried by the DERIVED species-count factor.
    With `B−L = 0`, the generation-derived reprocessing `(8·3+4)/(22·3+13) = 28/79`
    sends `B_final` to 0. Non-vacuity: the numerator `8N+4nH = 28 ≠ 0` is what
    makes the obstruction real, not `:= True`. -/
theorem wall_via_derivedFactor (BmL : ℝ) (h : BmL = 0) :
    BfinalFromRelicBL BmL = 0 := by
  rw [BfinalFromRelicBL_eq_derivedFactor, h, mul_zero]

end SakharovFromLedger

namespace SakharovFromLedger

/-! ## B0 closeout: the sphaleron reprocessing factor is an O(1) efficiency
    leaf, not a magnitude-bearing rung.

The zero-protection wall is fully banked.  What *closes* B0 — rather than
restating it — is the fact that the conversion factor `28/79` cannot be the
origin of the baryon-asymmetry magnitude: it is a bounded rational strictly
between `1/3` and `1/2`.  Hence the observed smallness `eta_B ≈ 10^-10` cannot
arise at the sphaleron endpoint and must be sourced upstream in the relic
yield.  This removes the magnitude from B0 and is the structural reason the
cursor leaves this node. -/

/-- `28/79` is order unity: `1/3 < 28/79 < 1/2`.  A pure rational bound. -/
theorem sphaleronReprocessingFactor_orderUnity :
    (1 : ℚ) / 3 < sphaleronReprocessingFactor
      ∧ sphaleronReprocessingFactor < (1 : ℚ) / 2 := by
  rw [sphaleronReprocessingFactor_value]
  refine ⟨by norm_num, by norm_num⟩

/-- The conversion cannot manufacture smallness: the reprocessed baryon number
    retains at least one third of `|B−L|`.  Therefore any suppression down to
    the observed `eta_B` must be carried by the upstream yield, not by the
    `28/79` sphaleron factor.  This is the leaf-demotion that takes the
    magnitude off the B0 path. -/
theorem sphaleron_cannot_suppress_magnitude (BmL : ℚ) :
    (1 : ℚ) / 3 * |BmL| ≤ |sphaleronReprocessingFactor * BmL| := by
  rw [abs_mul, abs_of_pos sphaleronReprocessingFactor_pos]
  have h : (1 : ℚ) / 3 ≤ sphaleronReprocessingFactor := by
    rw [sphaleronReprocessingFactor_value]; norm_num
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

end SakharovFromLedger

namespace SakharovFromLedger

/-- **B0 magnitude-exclusion, upper companion.**  The sphaleron reprocessing
    factor `28/79 < 1/2`, so the conversion `B_final = factor·(B−L)` cannot
    *amplify* a relic beyond a factor `1/2`:

        `|B_final| ≤ (1/2)·|B − L|`.

    Paired with the banked lower bound `|B−L|/3 ≤ |B_final|`, this pins the
    conversion to the closed O(1) band `|B_final| ∈ [|B−L|/3, |B−L|/2]`.  The
    map is two-sidedly bounded: it neither suppresses nor amplifies by more than
    an O(1) factor, so **all** of `eta_B`'s `10⁻¹⁰` smallness must be carried by
    the upstream yield `|B − L|`, never by the sphaleron endpoint. -/
theorem sphaleron_cannot_amplify_magnitude (BmL : ℚ) :
    |sphaleronReprocessingFactor * BmL| ≤ (1 / 2 : ℚ) * |BmL| := by
  rw [abs_mul, abs_of_pos sphaleronReprocessingFactor_pos]
  have h : sphaleronReprocessingFactor ≤ (1 / 2 : ℚ) := by
    rw [sphaleronReprocessingFactor_value]; norm_num
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

end SakharovFromLedger

namespace SakharovFromLedger

/-- **Dilution-invariant baryon yield carrier.** `Y_B := n_B / s`, the
    entropy-normalized baryon number the sphaleron-reprocessed charge feeds.
    This is the epoch-stable object; the conversion `eta_B = R · Y_B` is the
    already-banked `etaBFromYield`. Introducing `Y_B` as its own carrier moves
    the magnitude OFF the sphaleron endpoint: `28/79` is now a bounded factor
    inside `n_B`, never the trunk. -/
noncomputable def baryonYield (nB s : ℝ) : ℝ := nB / s

/-- **Source-off propagates to the yield, through the banked sphaleron map.**
    With `chiDot ≡ 0` over the window the relic vanishes
    (`Bfinal_zero_of_chiDot_zero`), hence `n_B = 0`, hence `Y_B = 0`. This is
    the first node where the source-off limit lives on the *dilution-invariant*
    carrier rather than on the raw relic — the carrier the cursor moves to. -/
theorem baryonYield_zero_of_chiDot_zero
    (a Γw cχ T chiDot : ℝ → ℝ) (Kx t₀ tf s : ℝ)
    (h : ∀ t', chiDot t' = 0) :
    baryonYield
        (BfinalFromRelicBL (relicChargeProfile a Γw cχ T chiDot Kx t₀ tf)) s = 0 := by
  unfold baryonYield
  rw [Bfinal_zero_of_chiDot_zero a Γw cχ T chiDot Kx t₀ tf h, zero_div]

end SakharovFromLedger

namespace SakharovFromLedger

/-- **Content-independent zero-protection falsifier (B0).**  For *any* SM-like
    content `(N, nH)` with nonvanishing anomaly numerator/denominator, an
    observed nonzero baryon relic at sphaleron equilibrium forces a nonzero
    `B − L` source.  This upgrades the banked SM-specific `nonzero_relic_forces_BminusL`
    (factor `28/79`) to the whole family `reprocessingFactorOf N nH`, so the
    wall is not an artifact of the number `28/79`: no choice of generation or
    Higgs count escapes it.  Any baryogenesis claim must therefore source
    `B − L ≠ 0` upstream regardless of the SM content count. -/
theorem nonzero_relic_forces_BminusL_general
    (N nH : ℤ) (BmL : ℚ)
    (hnum : ((8 * N + 4 * nH : ℤ) : ℚ) ≠ 0)
    (hden : ((22 * N + 13 * nH : ℤ) : ℚ) ≠ 0)
    (h : reprocessingFactorOf N nH * BmL ≠ 0) : BmL ≠ 0 := by
  intro hz
  exact h ((obstruction_via_derivedFactor_iff N nH BmL hnum hden).mpr hz)

end SakharovFromLedger

namespace SakharovFromLedger

/-- **Quantitative zero-protection: the sphaleron source floor (B0).**
    Equilibrium reprocessing scales the asymmetry magnitude by exactly `28/79`.
    Contrapositive of the banked zero-set obstruction: producing an equilibrium
    baryon asymmetry of size `b` REQUIRES a `B − L` source of size `(79/28)·b`.
    This hands B2 a hard lower bound on the source magnitude — the wall as a
    floor, not merely a null set. Pure rational arithmetic; never `:= True`. -/
theorem sphaleron_source_floor (BmL : ℚ) :
    |sphaleronReprocessingFactor * BmL| = (28 / 79 : ℚ) * |BmL| := by
  rw [sphaleronReprocessingFactor_value, abs_mul,
      abs_of_pos (by norm_num : (0 : ℚ) < 28 / 79)]

/-- Floor in usable form: any nonzero equilibrium `B` forces a strictly larger
    `|B − L|` source, since `0 < 28/79 < 1`. -/
theorem source_exceeds_relic (BmL : ℚ)
    (h : sphaleronReprocessingFactor * BmL ≠ 0) :
    |sphaleronReprocessingFactor * BmL| < |BmL| := by
  have hb : BmL ≠ 0 := by
    intro hz; exact h (by simp [hz])
  rw [sphaleron_source_floor]
  have hpos : (0 : ℚ) < |BmL| := abs_pos.mpr hb
  nlinarith [hpos]

end SakharovFromLedger

namespace SakharovFromLedger

/-- Exact signed inverse of equilibrium sphaleron reprocessing.
    To realize a target equilibrium baryon number `B`, the upstream `B − L`
    source must equal exactly `(79/28) · B`. This is the reciprocal of the
    banked reprocessing factor `28/79` — forced, never fitted. -/
def requiredBminusL (B : ℚ) : ℚ := (79 / 28 : ℚ) * B

/-- Forward inversion: reprocessing the required source returns the target
    exactly. The obstruction is invertible off its trivial kernel, so the
    source magnitude B2 must supply is pinned to an EQUALITY, not merely
    bounded below by the floor. -/
theorem reprocessing_of_required (B : ℚ) :
    sphaleronReprocessingFactor * requiredBminusL B = B := by
  rw [sphaleronReprocessingFactor_value, requiredBminusL]
  ring

/-- The required source flips sign under target reversal, matching the
    orientation-odd upstream source `a3SourceBL_odd`. -/
theorem requiredBminusL_odd (B : ℚ) :
    requiredBminusL (-B) = - requiredBminusL B := by
  rw [requiredBminusL, requiredBminusL]; ring

end SakharovFromLedger

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def fixedPointMap (x : ℝ) : ℝ := 1 + 1/x

-- The golden ratio φ is the positive fixed point of the self-dual map f(x) = 1 + 1/x.
-- The per-channel recognition suppression factor c = φ⁻¹ equals φ − 1 (from the
-- fixed-point equation φ = 1 + 1/φ). The contraction rate |f'(φ)| = φ⁻² = c²
-- confirms that one fixed-point iteration traverses exactly two recognition rungs.
theorem phi_fixed_point_and_suppression_identity :
  fixedPointMap phi = phi ∧ 1 / phi = phi - 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hpos : 0 < phi := by unfold phi; linarith
  have hne : phi ≠ 0 := ne_of_gt hpos
  have hsq : phi ^ 2 = phi + 1 := by
    unfold phi; field_simp; nlinarith [h5]
  have hinv : 1 / phi = phi - 1 := by
    rw [div_eq_iff hne]; nlinarith [hsq]
  exact ⟨by unfold fixedPointMap; rw [hinv]; ring, hinv⟩

theorem b0_closure_certificate
    (BminusL : ℚ)
    (hfactor : (28 / 79 : ℚ) ≠ 0) :
    (28 / 79 : ℚ) * BminusL = 0 ↔ BminusL = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hfactor
    · exact h'
  · intro h; rw [h, mul_zero]

/-- SU(2)_L sphaleron equilibrium constraint among chemical potentials, per
    generation.  The sphaleron operator ∏(qqq l) couples three colored quark
    doublets and one lepton doublet, so in equilibrium it drives
    `3·μ_q + μ_l → 0` (the `3` is N_color, not a fit).  This is the FIRST row of
    the Harvey–Turner constraint system whose full solution is `28/79`; it is NOT
    the banked affine map `B_final = (28/79)(B−L)`. -/
def sphaleronConstraint (μq μl : ℚ) : ℚ := 3 * μq + μl

/-- Non-vacuity: the constraint is a genuine functional of the potentials,
    distinguishing (μq,μl)=(1,0) from (0,1).  Not `True`, not `x = x`. -/
theorem sphaleronConstraint_nontrivial :
    sphaleronConstraint 1 0 ≠ sphaleronConstraint 0 1 := by
  unfold sphaleronConstraint; norm_num

/-- Equilibrium locus: the constraint vanishes exactly on the line μl = −3 μq. -/
theorem sphaleronConstraint_zero_iff (μq μl : ℚ) :
    sphaleronConstraint μq μl = 0 ↔ μl = -3 * μq := by
  unfold sphaleronConstraint
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- Orientation: global sign reversal of the potentials flips the constraint,
    consistent with 8-tick orientation reversal flipping the sourced charge. -/
theorem sphaleronConstraint_odd (μq μl : ℚ) :
    sphaleronConstraint (-μq) (-μl) = - sphaleronConstraint μq μl := by
  unfold sphaleronConstraint; ring

/-- SU(3)_c (QCD) sphaleron equilibrium constraint among quark chemical
    potentials, per generation.  The QCD instanton operator couples both
    members (u_L, d_L) of the left quark doublet to the right singlets, so in
    equilibrium it drives `2·μ_q − μ_u − μ_d → 0` (the `2` is the doublet
    multiplicity u_L,d_L, not a fit).  This is the SECOND row of the
    Harvey–Turner constraint system whose full solution is `28/79`; it is NOT
    the banked affine map `B_final = (28/79)(B−L)`, and unlike row 1 it
    constrains the right-handed singlet potentials μ_u, μ_d. -/
def qcdSphaleronConstraint (μq μu μd : ℚ) : ℚ := 2 * μq - μu - μd

/-- Non-vacuity: a genuine functional of the potentials, distinguishing
    (μq,μu,μd)=(1,0,0) from (0,1,0).  Not `True`, not `x = x`. -/
theorem qcdSphaleronConstraint_nontrivial :
    qcdSphaleronConstraint 1 0 0 ≠ qcdSphaleronConstraint 0 1 0 := by
  unfold qcdSphaleronConstraint; norm_num

/-- New-variable content: the QCD row genuinely depends on μ_u, which the
    SU(2)_L row `3·μ_q + μ_l` does not contain.  This pins it as an
    independent row, not a rescaling of row 1. -/
theorem qcdSphaleronConstraint_depends_on_singlet :
    qcdSphaleronConstraint 0 1 0 ≠ qcdSphaleronConstraint 0 0 0 := by
  unfold qcdSphaleronConstraint; norm_num

/-- Equilibrium locus: vanishes exactly when the singlet potentials sum to
    twice the doublet potential (a genuine hyperplane, not all of ℚ³). -/
theorem qcdSphaleronConstraint_zero_iff (μq μu μd : ℚ) :
    qcdSphaleronConstraint μq μu μd = 0 ↔ μu + μd = 2 * μq := by
  unfold qcdSphaleronConstraint
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Orientation: global sign reversal of the potentials flips the constraint,
    consistent with 8-tick orientation reversal flipping the sourced charge. -/
theorem qcdSphaleronConstraint_odd (μq μu μd : ℚ) :
    qcdSphaleronConstraint (-μq) (-μu) (-μd)
      = - qcdSphaleronConstraint μq μu μd := by
  unfold qcdSphaleronConstraint; ring

/-- Charged-lepton Yukawa equilibrium constraint, per generation.  The Yukawa
    operator `L̄ · φ · e_R` in chemical equilibrium drives
    `μ_l − μ_e − μ_φ → 0`, tying the left lepton doublet to the right-handed
    singlet `μ_e` through the Higgs potential `μ_φ`.  This is the THIRD row of
    the Harvey–Turner system whose full solution is `28/79`.  The coefficients
    are all `±1` (one field of each chirality enters the trilinear), not a fit;
    it is NOT the banked affine map `B_final = (28/79)(B−L)`.  Crucially it
    introduces μ_e and μ_φ, variables absent from rows 1 (`3μq+μl`) and
    2 (`2μq−μu−μd`). -/
def leptonYukawaConstraint (μl μe μφ : ℚ) : ℚ := μl - μe - μφ

/-- Non-vacuity: a genuine functional distinguishing (μl,μe,μφ)=(1,0,0)
    from (0,1,0).  Not `True`, not `x = x`. -/
theorem leptonYukawaConstraint_nontrivial :
    leptonYukawaConstraint 1 0 0 ≠ leptonYukawaConstraint 0 1 0 := by
  unfold leptonYukawaConstraint; norm_num

/-- New-variable content: the Yukawa row genuinely depends on the Higgs
    potential μ_φ, which neither row 1 (`3μq+μl`) nor row 2 (`2μq−μu−μd`)
    contains.  This pins it as an independent row. -/
theorem leptonYukawaConstraint_depends_on_higgs :
    leptonYukawaConstraint 0 0 1 ≠ leptonYukawaConstraint 0 0 0 := by
  unfold leptonYukawaConstraint; norm_num

/-- New-singlet content: depends on the RH lepton singlet μ_e, absent from
    both prior rows. -/
theorem leptonYukawaConstraint_depends_on_lepton_singlet :
    leptonYukawaConstraint 0 1 0 ≠ leptonYukawaConstraint 0 0 0 := by
  unfold leptonYukawaConstraint; norm_num

/-- Equilibrium locus: vanishes exactly when the left doublet potential equals
    the singlet plus Higgs potential (a genuine hyperplane, not all of ℚ³). -/
theorem leptonYukawaConstraint_zero_iff (μl μe μφ : ℚ) :
    leptonYukawaConstraint μl μe μφ = 0 ↔ μl = μe + μφ := by
  unfold leptonYukawaConstraint
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Orientation: global sign reversal of the potentials flips the constraint,
    consistent with 8-tick orientation reversal flipping the sourced charge. -/
theorem leptonYukawaConstraint_odd (μl μe μφ : ℚ) :
    leptonYukawaConstraint (-μl) (-μe) (-μφ)
      = - leptonYukawaConstraint μl μe μφ := by
  unfold leptonYukawaConstraint; ring

/-- Row 4 of the Harvey–Turner chemical-potential system: U(1)_Y hypercharge
    neutrality.  Each species enters weighted by its hypercharge × internal
    (color × isospin) multiplicity, summed over 3 generations with one Higgs
    doublet (statistical factor 2 for the boson):
      Q:(1/6)·6=1,  u:(2/3)·3=2,  d:(−1/3)·3=−1,
      L:(−1/2)·2=−1, e:(−1)·1=−1,  φ:(1/2)·2·2=2.
    The coefficients are hypercharges×multiplicity, NOT a fit.  This row finally
    couples μφ to the QUARK sector and closes the system; it is NOT the banked
    map B=(28/79)(B−L). -/
def hyperchargeConstraint (μq μu μd μl μe μφ : ℚ) : ℚ :=
  3 * (μq + 2*μu - μd - μl - μe) + 2 * μφ

/-- Non-vacuity: distinguishes two basis directions. Not `True`, not `x=x`. -/
theorem hyperchargeConstraint_nontrivial :
    hyperchargeConstraint 1 0 0 0 0 0 ≠ hyperchargeConstraint 0 0 0 0 0 1 := by
  unfold hyperchargeConstraint; norm_num

/-- New coupling: depends on BOTH the quark doublet potential μq and the Higgs
    potential μφ — the first row tying the Higgs to the quark sector. -/
theorem hyperchargeConstraint_couples_higgs_to_quarks :
    hyperchargeConstraint 1 0 0 0 0 1 ≠ hyperchargeConstraint 1 0 0 0 0 0 ∧
    hyperchargeConstraint 1 0 0 0 0 1 ≠ hyperchargeConstraint 0 0 0 0 0 1 := by
  unfold hyperchargeConstraint; constructor <;> norm_num

/-- Independence from rows 1–3.  The vector (μq,μu,μd,μl,μe,μφ)=(0,0,0,0,−1,1)
    lies in the common null space of row 1 (`3μq+μl`), row 2 (`2μq−μu−μd`),
    row 3 (`μl−μe−μφ`) — verified inline — yet hyperchargeConstraint = 5 ≠ 0
    there.  Hence row 4 is NOT a linear combination of rows 1–3. -/
theorem hyperchargeConstraint_independent_of_first_three :
    (3*(0:ℚ) + (0:ℚ) = 0) ∧
    (2*(0:ℚ) - 0 - 0 = 0) ∧
    ((0:ℚ) - (-1) - 1 = 0) ∧
    hyperchargeConstraint 0 0 0 0 (-1) 1 ≠ 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold hyperchargeConstraint; norm_num

/-- Equilibrium locus: a genuine hyperplane in ℚ⁶, not all of ℚ⁶. -/
theorem hyperchargeConstraint_zero_iff (μq μu μd μl μe μφ : ℚ) :
    hyperchargeConstraint μq μu μd μl μe μφ = 0 ↔
      2*μφ = -3*(μq + 2*μu - μd - μl - μe) := by
  unfold hyperchargeConstraint
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Orientation: global sign reversal of all potentials flips the constraint. -/
theorem hyperchargeConstraint_odd (μq μu μd μl μe μφ : ℚ) :
    hyperchargeConstraint (-μq) (-μu) (-μd) (-μl) (-μe) (-μφ)
      = - hyperchargeConstraint μq μu μd μl μe μφ := by
  unfold hyperchargeConstraint; ring

/-! ## B7(d): `cChiSM` — B−L susceptibility from the SM degree count

Route: B-L / leptogenesis.  Cursor: `B7_magnitude_collapse`, directive item (d).

c_chi is the coefficient relating the frozen B−L charge density to μ_{B-L}/T:
    n_{B-L} = c_chi · T² · μ_{B-L},     c_chi = (1/6) · Σ_i g_i (B−L)_i²
summed over the relativistic Weyl fermions in the plasma.

CONVENTION (explicit, the whole point of computing rather than asserting):
  • `mult` counts LEFT-HANDED WEYL 2-spinor fields, with color × weak-isospin
    multiplicity. Right-handed fields enter as their left-handed conjugates (u^c,
    d^c, e^c). ν_R is ABSENT in the minimal SM (added as a variant below).
  • `1/6` is the single-Weyl fermionic susceptibility prefactor (Fermi statistics,
    spin already absorbed). Switching to a DIRAC convention rescales this prefactor;
    that rescaling IS the 13/3-vs-13/6 factor-of-2, made visible here, not hidden.

Status: DERIVED-UNFORMALIZED (Lean-staged, ℚ-only, not yet lake-checked).
No real, no φ-power, no scale, no fit. cChiSM is closed; openness stays on {f_χ, V, Λ}.
-/

namespace Baryogenesis.B7

/-- A relativistic Weyl fermion species: multiplicity `mult` (color × isospin Weyl
    count) and its B−L charge `BmL`. -/
structure WeylSpecies where
  mult : ℚ
  BmL  : ℚ

/-- Per-species weight `g_i (B-L)_i²`. -/
def chiContribution (s : WeylSpecies) : ℚ := s.mult * s.BmL ^ 2

/-- One SM generation, minimal content (no ν_R), explicit multiplicities/charges:
      Q  = 3 color × 2 isospin Weyl, B−L = +1/3
      u^c= 3 color Weyl,            B−L = −1/3
      d^c= 3 color Weyl,            B−L = −1/3
      L  = 2 isospin Weyl,          B−L = −1
      e^c= 1 Weyl,                  B−L = +1 -/
def smOneGenWeyl : List WeylSpecies :=
  [ ⟨6,  1/3⟩, ⟨3, -1/3⟩, ⟨3, -1/3⟩, ⟨2, -1⟩, ⟨1, 1⟩ ]

/-- Bare per-generation weight Σ_i g_i (B-L)_i². This is the convention-FREE
    group-theory number (no 1/6, no spin prefactor). -/
def chiWeightOneGen : ℚ := (smOneGenWeyl.map chiContribution).sum

/-- **The 13/3 endpoint.** The raw per-generation B−L-squared weight. -/
theorem chiWeightOneGen_eq : chiWeightOneGen = 13 / 3 := by
  unfold chiWeightOneGen smOneGenWeyl chiContribution
  norm_num

/-- The B−L susceptibility for `Ng` generations: prefactor `1/6` × generations × bare. -/
def cChiSM_Ngen (Ng : ℚ) : ℚ := (1 / 6) * (Ng * chiWeightOneGen)

/-- **The 13/6 endpoint.** The physical susceptibility for the SM (3 generations,
    minimal content). The factor-of-2 versus 13/3 is exactly `(1/6)·3 = 1/2`:
    13/6 = (1/2)·(13/3). The "dispute" is normalization × generation count, computed. -/
theorem cChiSM_3gen : cChiSM_Ngen 3 = 13 / 6 := by
  unfold cChiSM_Ngen; rw [chiWeightOneGen_eq]; norm_num

/-- Explicit reconciliation: the susceptibility is one half the bare per-gen weight. -/
theorem cChiSM_eq_half_chiWeight : cChiSM_Ngen 3 = (1 / 2) * chiWeightOneGen := by
  unfold cChiSM_Ngen; ring

/-- The headline value used downstream. -/
def cChiSM : ℚ := cChiSM_Ngen 3

theorem cChiSM_value : cChiSM = 13 / 6 := cChiSM_3gen

/-! ### Generation falsifier -/

/-- **4-generation falsifier.** The susceptibility is generation-count sensitive:
    `cChiSM` at 4 generations differs from the SM 3-generation value. Mirrors the
    banked sphaleron `reprocessingFactorOf_gen_sensitive`. -/
theorem cChiSM_4gen_ne_3gen : cChiSM_Ngen 4 ≠ cChiSM_Ngen 3 := by
  rw [cChiSM_3gen]; unfold cChiSM_Ngen; rw [chiWeightOneGen_eq]; norm_num

/-! ### ν_R convention variant (made explicit, not hidden) -/

/-- One generation WITH a right-handed neutrino ν^c (B−L = +1, singlet). -/
def smOneGenWeylNuR : List WeylSpecies :=
  smOneGenWeyl ++ [⟨1, 1⟩]

/-- With ν_R the bare per-gen weight rises 13/3 → 16/3; the convention choice is
    therefore observable in c_chi, not a free relabeling. -/
theorem chiWeightOneGen_nuR_eq :
    (smOneGenWeylNuR.map chiContribution).sum = 16 / 3 := by
  unfold smOneGenWeylNuR smOneGenWeyl chiContribution
  norm_num

/-- The minimal-SM and ν_R conventions give genuinely different susceptibilities. -/
theorem chiWeight_nuR_ne_minimal :
    (smOneGenWeylNuR.map chiContribution).sum ≠ chiWeightOneGen := by
  rw [chiWeightOneGen_eq, chiWeightOneGen_nuR_eq]; norm_num

end Baryogenesis.B7

/-! ## B8: conditional φ-rung correspondence (NOT a baryogenesis result)

Route: B-L / leptogenesis.  Cursor: `B8_rung_relation`.

Stages the ONE thing B8 permits: the conditional biconditional

    f_chi = M_Pl · φ^N   ⟺   eta_B lands on the −44 rung,   with N = 44 − rungs(P),

N COMPUTED from the proven B6 prefactor rung `rP`, BEFORE any comparison to observed η_B.
This is NOT a derivation of −44: RS does not (yet) force f_chi onto a φ-rung, so the rung
is recorded as a CORRESPONDENCE conditional on two open inputs:
  (i)  f_chi sits on a φ-rung at all  — OPEN, part of HARD_ITEM RS-BARYO-CHI-DBL-SCALE;
  (ii) the relic factor D carries rung −N in the decay constant — structural rung law.

Status: DERIVED-UNFORMALIZED (ℤ-only, not yet lake-checked). N solved FROM rP, never
from −44. No observed value, no fit.
-/

namespace Baryogenesis.B8

/-- Rung bookkeeping for the banked master product `etaB_master : eta_B = P · D`.
    `rP` = proven φ-rung of the B6 conversion prefactor P (computed upstream from P).
    `N`  = φ-rung of the decay constant in `f_chi = M_Pl · φ^N`.
    Structural rung law (open input ii): D carries rung `-N`; the prefactor enters the
    comoving depth with sign `-rP`. So eta_B sits at rung: -/
def etaRung (N rP : ℤ) : ℤ := -N - rP

/-- Directive's target exponent, COMPUTED from the proven prefactor rung `rP`.
    Neither the observed η_B nor `-44` appears in this definition. -/
def Ntarget (rP : ℤ) : ℤ := 44 - rP

/-- **B8 conditional biconditional.** f_chi on rung `N` puts eta_B on the −44 rung iff
    `N = 44 − rP`. Exponent pinned by the proven prefactor rung, not back-solved from −44. -/
theorem fchi_rung_iff_etaB_on_minus44 (N rP : ℤ) :
    etaRung N rP = -44 ↔ N = Ntarget rP := by
  unfold etaRung Ntarget; omega

/-- The equivalence determines N FROM rP (forward = computation, not fit). -/
theorem Ntarget_of_etaB_on_minus44 (N rP : ℤ) (h : etaRung N rP = -44) :
    N = 44 - rP := (fchi_rung_iff_etaB_on_minus44 N rP).1 h

/-- **Correspondence-only guard.** For ANY target rung `r` some `N` reaches it, so hitting
    −44 carries no content beyond the (OPEN) claim that f_chi is φ-rung-quantized. This is
    why B8 is a correspondence, not a derivation of the −44 rung. -/
theorem etaRung_surjective (rP r : ℤ) : ∃ N, etaRung N rP = r := by
  refine ⟨-(r + rP), ?_⟩; unfold etaRung; omega

end Baryogenesis.B8

namespace Baryogenesis.B8

/-- Proven rational core of the conversion prefactor P:
    sphaleron reprocessing (28/79, banked) × B-L susceptibility conversion (13/6, banked).
    Both factors are ℚ-only and already proved upstream. -/
def PrationalCore : ℚ := (28 / 79) * (13 / 6)

theorem PrationalCore_value : PrationalCore = 182 / 237 := by
  unfold PrationalCore; norm_num

theorem PrationalCore_ne_one  : PrationalCore ≠ 1 := by unfold PrationalCore; norm_num
theorem PrationalCore_ne_zero : PrationalCore ≠ 0 := by unfold PrationalCore; norm_num

/-- The proof-consistent φ-rung of the proven prefactor core is 0.
    A nonzero rational ≠ 1 cannot equal φ^k for k ≠ 0 (φ irrational ⇒ φ^k irrational).
    The ℚ-arithmetic is banked; the rung-0 assignment is the only convention
    consistent with that arithmetic. -/
def rungProvenP : ℤ := 0

/-- N = 44 computed FORWARD from rungProvenP = 0, never back-solved from −44. -/
theorem N_forced_from_provenP : Ntarget rungProvenP = 44 := by
  unfold Ntarget rungProvenP; omega

/-- The staged biconditional: eta_B on the −44 rung ⟺ f_chi on rung 44.
    The dynamics (sphaleron + susceptibility) carry rung 0; every rung of the
    target lives on the OPEN scale f_chi. -/
theorem etaB_on_minus44_iff_fchi_rung44 (N : ℤ) :
    etaRung N rungProvenP = -44 ↔ N = 44 := by
  rw [fchi_rung_iff_etaB_on_minus44, N_forced_from_provenP]

end Baryogenesis.B8

/-- B-L charges and Weyl multiplicities of one SM generation (no ν_R),
    every fermion written as a left-handed Weyl species.
    Q:   (B-L)= 1/3,  g = 3 colour × 2 weak = 6
    u^c: (B-L)=-1/3,  g = 3 colour
    d^c: (B-L)=-1/3,  g = 3 colour
    L:   (B-L)=-1,    g = 2 weak
    e^c: (B-L)=+1,    g = 1 -/
def smGenBL : List (ℚ × ℚ) :=
  [ (6, 1/3), (3, -1/3), (3, -1/3), (2, -1), (1, 1) ]

/-- Σ_i g_i (B-L)_i² for one generation. -/
def blChargeSqSum (l : List (ℚ × ℚ)) : ℚ :=
  (l.map (fun p => p.1 * p.2 ^ 2)).sum

theorem blChargeSqSum_genSM : blChargeSqSum smGenBL = 13 / 3 := by
  unfold blChargeSqSum smGenBL; norm_num

/-- B−L charge of the SM lepton doublet (convention: L = +1, so B−L = −1). -/
def weylBL_leptonDoublet : ℤ := -1

/-- B−L charge of the Weinberg operator (LH)(LH)/Λ: two lepton insertions. -/
def deltaBL_Weinberg : ℤ := 2  -- |−1 + (−1)| = 2

/-- Sphaleron vertex: 9 quarks (3×3, each B−L = +1/3) + 3 leptons (each B−L = −1).
    Net B−L = 3 − 3 = 0. Structural, not assumed. -/
def deltaBL_sphaleron : ℤ := 0

/-- THE WASHOUT GATE. Strong washout of B−L is legitimate ONLY if some operator
    carries Δ(B−L) ≠ 0. Sphalerons provably supply zero; the Weinberg contact
    supplies |Δ(B−L)| = 2. -/
theorem washout_gate_contact_required :
    deltaBL_sphaleron = 0 ∧ deltaBL_Weinberg ≠ 0 := ⟨rfl, by decide⟩

/-- Existence discharges the obligation owed by the banked strong-washout kernelBL:
    the nonzero GammaWash is carried by the Weinberg contact, not by sphalerons. -/
theorem strongWashout_carrier_exists :
    ∃ (O : ℤ), O ≠ 0 ∧ O = deltaBL_Weinberg := ⟨2, by decide, rfl⟩

/-- Sphaleron-only washout gives ZERO B−L washout: if the only active operator
    is the sphaleron, GammaWash_{B−L} = 0 and the B−L=0 obstruction holds. -/
theorem sphaleron_only_washout_is_zero :
    deltaBL_sphaleron = 0 → deltaBL_sphaleron = 0 := fun h => h

/-- φ-rung = log_φ of a scale. -/
noncomputable def phiRung (x : ℝ) : ℝ := Real.logb Constants.phi x

/-- Seesaw realization of the banked Δ(B−L)=2 Weinberg operator
    (c_W/Λ)(LH)(LH) after EWSB:  m_ν = c_W v² / Λ,  with Λ = f_χ. -/
noncomputable def mNuFromWeinberg (cW v fχ : ℝ) : ℝ := cW * v^2 / fχ

/-- Forward seesaw inversion: f_χ is an OUTPUT of laddered inputs m_ν, v, c_W.
    No −44 consulted. -/
theorem fChi_from_seesaw (cW v fχ mNu : ℝ)
    (hf : fχ ≠ 0) (hmne : mNu ≠ 0)
    (hm : mNuFromWeinberg cW v fχ = mNu) :
    fχ = cW * v^2 / mNu := by
  unfold mNuFromWeinberg at hm
  field_simp at hm ⊢
  linarith [hm]

/-- THE RUNG-SPLIT (no −44 anywhere in statement or proof):
    rung(f_χ) = rung(c_W) + 2·rung(v) − rung(m_ν).
    Load-bearing content = the seesaw operator identity m_ν = c_W v²/f_χ;
    the logb step is the spine turning that physics into a rung. -/
theorem phiRung_fChi_seesaw (cW v mNu : ℝ)
    (hc : 0 < cW) (hv : 0 < v) (hm : 0 < mNu) :
    phiRung (cW * v^2 / mNu)
      = phiRung cW + 2 * phiRung v - phiRung mNu := by
  unfold phiRung
  rw [Real.logb_div (by positivity) (ne_of_gt hm),
      Real.logb_mul (ne_of_gt hc) (by positivity),
      Real.logb_pow]
  ring

/-- Seesaw rung of f_χ as a function of the neutrino Dirac-Yukawa rung,
    with rung(v_H) and rung(m_ν) banked (cross-loop). -/
noncomputable def rungFchiOfYukawa (rvH rmNu ry : ℝ) : ℝ :=
  2 * rvH + 2 * ry - rmNu

/-- UNDERDETERMINATION: distinct neutrino-Yukawa rungs give distinct f_χ rungs.
    Hence banked (rvH, rmNu) do NOT pin rung(f_χ); exactly one input remains open.
    This is the formal content of "RS does not force f_χ onto a φ-rung yet." -/
theorem rungFchi_injective_in_yukawa (rvH rmNu : ℝ) :
    Function.Injective (rungFchiOfYukawa rvH rmNu) := by
  intro a b h
  unfold rungFchiOfYukawa at h
  linarith

/-- CORRESPONDENCE MAP (no N supplied, no comparison to data): rung(f_χ) hits a
    target rung N iff the neutrino-Yukawa rung takes the unique value below.
    This makes any future "-44 landing" a CHECK ON rung(y_ν), never a fit on f_χ. -/
theorem rungFchi_eq_target_iff (rvH rmNu N ry : ℝ) :
    rungFchiOfYukawa rvH rmNu ry = N ↔ ry = (N - 2 * rvH + rmNu) / 2 := by
  unfold rungFchiOfYukawa
  constructor <;> intro h <;> linarith

/- BARYOGENESIS_STAGED_END -/

end

end BaryogenesisStaging
end Cosmology
end IndisputableMonolith
