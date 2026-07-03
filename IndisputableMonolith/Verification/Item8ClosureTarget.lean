import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Physics.RunningCouplings

/-!
# Item 8 Closure Target — Unified Sub-Leading Mass Formula

This module develops the smallest precise theorem framework that would close the
open quark sub-leading correction item (Item 8) and make the all-sector
generalization falsifiable.

## Summary of Results

### Proved (sorry-free)

1. **`consistency_of_ratioFamily`**: The sign-split family forces
   `gen12·s₁₂ + gen23·s₂₃ = 0` — a structural rigidity that PDG data violates.

2. **`etaFromData` + `etaL_gen12_identity` + `etaL_gen23_identity`**:
   Closed-form η formula absorbs the consistency violation:
   `η = (g₁₂·s₁₂ + g₂₃·s₂₃) / (ln(s₁₂/s₂₃) · (g₁₂·s₁₂ − g₂₃·s₂₃))`
   with algebraic identities `1 + η·L = 2·g₁₂·s₁₂/D` and `1 − η·L = −2·g₂₃·s₂₃/D`.

3. **`refinedFamily_neg_solvable` / `refinedFamily_pos_solvable`**:
   For any residual pair with nonzero gen12, non-degenerate cross-difference,
   distinct steps, and nonzero coupling, the refined family has a solution.
   Constructive proof via explicit coefficient formulas.

4. **`refinedFamily_neg_unique` / `refinedFamily_pos_unique`**:
   If two coefficient sets produce identical refined-family outputs on a given
   signature, their active coefficient `c` and `eta` must agree.
   Proof via `calc`+`ring` to cancel common factors, then `linarith` for the
   addition step and `mul_left_cancel₀`/`mul_right_cancel₀` for cancellation.
   Combined with solvability (item 3), this gives **`∃!` for each sector**.

5. **`refined_neg_sector_closure`**: Full `∃!` for any `.neg` sector:
   there exist unique `(c, η)` matching the data, and any solution (with
   arbitrary `cPos`) must have the same `(c, η)`.  Combines items 3–4 with
   a helper `neg_cPos_irrelevant` showing `cPos` is unused for `.neg`.

6. **`signClass_collapse_to_refined`**: Sign-class family collapses to the
   refined family when both η values agree.

### Documented obstructions

* **Universal η**: The 3-parameter refined family (universal η) is
  unsatisfiable with mixed-scheme PDG quark data: η_up = −2.72 vs η_dn = −0.88
  (3.1× disagreement).

* **Mixed-scheme artifact**: LO QCD running reveals that the "universal sign
  pattern" (δ₁₂ > 0, δ₂₃ < 0) is partly an artifact of comparing masses at
  different renormalization scales.  The c/u SDGT step of 13 is nearly exact
  at a common scale (δ₁₂ ≈ −0.01).

* **Lepton benchmark**: Leptons — with scheme-free pole masses — give
  perturbative η = +0.065 (|η·L| ≈ 4%), validating the family form.

### Strategy

The lepton-anchored approach fixes η and cNeg from the two scheme-free lepton
equations, then predicts anchor-scale quark residuals as genuine out-of-sample
tests.  The `RunningCouplings` module now provides LO mass transport with
threshold matching (`transport_mass_through`); quark closure awaits NLO
refinement of the running to reduce residual scheme dependence.

## Interface

* A sign class induced by `B_pow`
* The ordered SDGT step pair `(step12, step23)` — sector-specific rung spacings
  from the Q₃ cube decomposition
* One coupling scalar `kappa`

## Concrete data (§ ConcreteInstantiation)

* PDG 2022 quark masses at mixed reference scales
  (u,d,s at 2 GeV MS-bar; c at m_c; b at m_b; t pole)
* Charged-lepton pole masses (scheme-free)
* α_s = 2/17 from wallpaper-group fraction (proved in StrongForce)
* Rung-unit residuals: δ = log_φ(observed ratio) − SDGT step

### Approximate residual values (mixed-scheme PDG)

| Sector | gen12 step | δ₁₂ (rungs) | gen23 step | δ₂₃ (rungs) | η     |
|--------|-----------|-------------|-----------|-------------|-------|
| Up     | 13        | +0.25       | 11        | −0.79       | −2.72 |
| Down   | 6         | +0.23       | 8         | −0.10       | −0.88 |
| Lepton | 11        | +0.08       | 6         | −0.13       | +0.06 |

Lepton η is perturbative (4%); quark η values are inflated by mixed-scale
PDG artifacts, especially the t/c ratio (pole mass vs MS-bar at m_c).
-/

namespace IndisputableMonolith
namespace Verification
namespace Item8ClosureTarget

/-- Sign class induced by the sign of `B_pow`. -/
inductive BpowSign | neg | pos
  deriving DecidableEq, Repr

/-- Minimal structural signature for a sector's sub-leading correction law.
    `step12` and `step23` are the sector-specific SDGT rung spacings
    (cube-cell counts from the Q₃ decomposition). -/
structure ResidualSignature where
  sign : BpowSign
  step12 : ℕ
  step23 : ℕ
  coupling : ℝ
  step12_pos : 0 < step12
  step23_pos : 0 < step23

/-- Two sub-leading rung corrections: generation `1 → 2` and `2 → 3`. -/
@[ext]
structure ResidualPair where
  gen12 : ℝ
  gen23 : ℝ

/-- The two global coefficients allowed by the smallest sign-split candidate family. -/
structure RatioFamilyCoeffs where
  cNeg : ℝ
  cPos : ℝ

/-- Negative-`B_pow` lepton signature, using the derived SDGT pair `(11, 6)`. -/
def leptonSignature (kappa : ℝ) : ResidualSignature where
  sign := .neg
  step12 := 11
  step23 := 6
  coupling := kappa
  step12_pos := by decide
  step23_pos := by decide

/-- Negative-`B_pow` up-quark signature, using the derived SDGT pair `(13, 11)`. -/
def upQuarkSignature (kappa : ℝ) : ResidualSignature where
  sign := .neg
  step12 := 13
  step23 := 11
  coupling := kappa
  step12_pos := by decide
  step23_pos := by decide

/-- Positive-`B_pow` down-quark signature, using the derived SDGT pair `(6, 8)`. -/
def downQuarkSignature (kappa : ℝ) : ResidualSignature where
  sign := .pos
  step12 := 6
  step23 := 8
  coupling := kappa
  step12_pos := by decide
  step23_pos := by decide

/-- Sign-split ratio family: the smallest closed-form candidate using only

1. `sign(B_pow)` → selects `cNeg` or `cPos`
2. the ordered SDGT step pair → weights the correction via step fraction
3. one coupling scalar κ

The gen-1→2 correction inherits the sign of `c`; the gen-2→3 correction
inherits `−c`.  This captures the universal empirical pattern δ₁₂ > 0,
δ₂₃ < 0 when `c > 0`. -/
noncomputable def ratioFamily (coeffs : RatioFamilyCoeffs)
    (sig : ResidualSignature) : ResidualPair :=
  let c :=
    match sig.sign with
    | .neg => coeffs.cNeg
    | .pos => coeffs.cPos
  let total := (sig.step12 : ℝ) + (sig.step23 : ℝ)
  { gen12 := c * sig.coupling * (sig.step23 : ℝ) / total
  , gen23 := -(c * sig.coupling * (sig.step12 : ℝ) / total)
  }

/-- The exact prediction produced by the candidate family for any signature. -/
noncomputable def predictedResiduals (coeffs : RatioFamilyCoeffs)
    (sig : ResidualSignature) : ResidualPair :=
  ratioFamily coeffs sig

/-- Equal structural signatures give equal predictions.  This is the precise
no-extra-knob property needed for later out-of-sample tests. -/
theorem same_signature_same_prediction
    (coeffs : RatioFamilyCoeffs) {sig1 sig2 : ResidualSignature}
    (h : sig1 = sig2) :
    predictedResiduals coeffs sig1 = predictedResiduals coeffs sig2 := by
  subst h; rfl

/-- Smallest precise target that would close Item 8.

`upExact` and `downExact` are the exact quark residual pairs once derived.
Proving this proposition would do two things:

1. close Item 8 by fixing both quark residual pairs inside one closed family
2. freeze the two global coefficients `(cNeg, cPos)`, making every later
   lepton / genetic / theta instantiation an out-of-sample test rather than a
   new fit
-/
def item8ClosureTarget
    (upExact downExact : ResidualPair)
    (kappaUp kappaDown : ℝ) : Prop :=
  ∃! coeffs : RatioFamilyCoeffs,
    predictedResiduals coeffs (upQuarkSignature kappaUp) = upExact ∧
    predictedResiduals coeffs (downQuarkSignature kappaDown) = downExact

/-! ## Structural Obstruction of the Sign-Split Family

The sign-split family satisfies a rigid algebraic constraint: for any
signature, the cross-product `gen12 · step12 + gen23 · step23 = 0`.
This is a **necessary condition** for the family to match any given
residual pair.  Numerically:

| Sector | gen12·s₁₂ + gen23·s₂₃ | violation |
|--------|----------------------|-----------|
| Lepton |  +0.066              |  3.9%     |
| Down   |  +0.546              | 25.3%     |
| Up     |  −5.439              | 45.4%     |

The lepton data nearly satisfies the condition (scheme-free pole masses);
the quark violations are larger, partly because PDG values mix scales.
The up-quark t/c ratio (pole vs MS-bar at m_c) is the main outlier.
-/

theorem consistency_of_ratioFamily
    (coeffs : RatioFamilyCoeffs) (sig : ResidualSignature) :
    (ratioFamily coeffs sig).gen12 * (sig.step12 : ℝ) +
    (ratioFamily coeffs sig).gen23 * (sig.step23 : ℝ) = 0 := by
  obtain ⟨sign, s12, s23, κ, hs12, hs23⟩ := sig
  unfold ratioFamily
  dsimp only [ResidualPair.gen12, ResidualPair.gen23]
  have htotal : (s12 : ℝ) + (s23 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (s12 : ℝ) := Nat.cast_pos.mpr hs12
    have : (0 : ℝ) < (s23 : ℝ) := Nat.cast_pos.mpr hs23
    linarith
  cases sign <;> simp only [] <;> field_simp [htotal] <;> ring

/-- If the sign-split family matches a residual pair, that pair must satisfy
    the cross-product identity.  Contrapositive: if the identity fails,
    no coefficients can make the family fit. -/
theorem consistency_necessary
    (coeffs : RatioFamilyCoeffs) (sig : ResidualSignature) (exact : ResidualPair)
    (h : predictedResiduals coeffs sig = exact) :
    exact.gen12 * (sig.step12 : ℝ) + exact.gen23 * (sig.step23 : ℝ) = 0 := by
  rw [← h]; simp only [predictedResiduals]; exact consistency_of_ratioFamily coeffs sig

/-! ## Refined Family: Log-Asymmetry Correction

Since the sign-split family's structural constraint is violated by the data,
we introduce a **single universal parameter** `η` that breaks the rigid
ratio `gen12/gen23 = −step23/step12`.  The correction is multiplicative and
logarithmic in the step ratio:

    gen12 = c · κ · (s₂₃/total) · (1 + η · ln(s₁₂/s₂₃))
    gen23 = −c · κ · (s₁₂/total) · (1 − η · ln(s₁₂/s₂₃))

With 3 parameters (cNeg, cPos, η) and 4 quark equations, the system is
overdetermined by 1, making the `∃!` condition a genuine test (not a tautology).
-/

/-- Three global coefficients: two sign-class amplitudes plus a universal
    log-asymmetry that modulates the gen12/gen23 ratio. -/
structure RefinedCoeffs where
  cNeg : ℝ
  cPos : ℝ
  eta  : ℝ

noncomputable def refinedFamily (coeffs : RefinedCoeffs)
    (sig : ResidualSignature) : ResidualPair :=
  let c :=
    match sig.sign with
    | .neg => coeffs.cNeg
    | .pos => coeffs.cPos
  let s12 := (sig.step12 : ℝ)
  let s23 := (sig.step23 : ℝ)
  let total := s12 + s23
  let logAsym := Real.log (s12 / s23)
  { gen12 := c * sig.coupling * s23 / total * (1 + coeffs.eta * logAsym)
  , gen23 := -(c * sig.coupling * s12 / total * (1 - coeffs.eta * logAsym))
  }

noncomputable def refinedPrediction (coeffs : RefinedCoeffs)
    (sig : ResidualSignature) : ResidualPair :=
  refinedFamily coeffs sig

/-- At η = 0, the refined family collapses to the original sign-split family. -/
theorem refined_at_eta_zero (cN cP : ℝ) (sig : ResidualSignature) :
    refinedFamily ⟨cN, cP, 0⟩ sig =
    ratioFamily ⟨cN, cP⟩ sig := by
  simp only [refinedFamily, ratioFamily, zero_mul, add_zero, sub_zero, mul_one]

def refinedItem8ClosureTarget
    (upExact downExact : ResidualPair)
    (kappaUp kappaDown : ℝ) : Prop :=
  ∃! coeffs : RefinedCoeffs,
    refinedPrediction coeffs (upQuarkSignature kappaUp) = upExact ∧
    refinedPrediction coeffs (downQuarkSignature kappaDown) = downExact

/-! ## Closed-Form η Solution

For any sector with residual pair `(g₁₂, g₂₃)` and SDGT steps `(s₁₂, s₂₃)`,
the log-asymmetry parameter η that makes the refined family match the data
exactly has a unique closed-form expression:

    η = (g₁₂·s₁₂ + g₂₃·s₂₃) / (ln(s₁₂/s₂₃) · (g₁₂·s₁₂ − g₂₃·s₂₃))

The numerator is exactly the consistency violation of the sign-split family
(which forces `g₁₂·s₁₂ + g₂₃·s₂₃ = 0`), and the denominator is the
log-asymmetry times the cross-difference.

### Key algebraic identities

When η has this value, the multiplicative correction factors simplify:

    1 + η·L = 2·g₁₂·s₁₂ / (g₁₂·s₁₂ − g₂₃·s₂₃)
    1 − η·L = −2·g₂₃·s₂₃ / (g₁₂·s₁₂ − g₂₃·s₂₃)

where `L = ln(s₁₂/s₂₃)`.  These identities reduce the solution for `c`
to a single division, and the entire system closes algebraically.

### Obstruction for universal η

The formula yields different η values per sector with current PDG data:

| Sector | η       | |η·L|  | Perturbative? |
|--------|---------|--------|---------------|
| Lepton | +0.065  | 0.039  | ✓ (4%)        |
| Down   | −0.879  | 0.253  | marginal      |
| Up     | −2.720  | 0.454  | ✗ (flips sign)|

The 3-parameter refined family (universal η) is therefore UNSATISFIABLE
with current mixed-scheme PDG quark data.  Leptons — with scheme-free
pole masses — give a perturbative η, validating the family structure.
The quark η inflation is attributed to mixed-scale PDG artifacts
(especially the t/c ratio: pole vs MS-bar at m_c).
-/

/-- Closed-form η from residual data: absorbs the consistency violation
    of the sign-split family into a log-asymmetry correction.
    Well-defined when `s₁₂ ≠ s₂₃` and `g₁₂·s₁₂ ≠ g₂₃·s₂₃`. -/
noncomputable def etaFromData (g12 g23 s12 s23 : ℝ) : ℝ :=
  (g12 * s12 + g23 * s23) / (Real.log (s12 / s23) * (g12 * s12 - g23 * s23))

/-- When η is computed from the data, `1 + η·L` simplifies to
    `2·g₁₂·s₁₂ / (g₁₂·s₁₂ − g₂₃·s₂₃)`.  This is the identity that
    makes the gen-1→2 equation close algebraically. -/
theorem etaL_gen12_identity (g12 g23 s12 s23 : ℝ)
    (hD : g12 * s12 - g23 * s23 ≠ 0)
    (hL : Real.log (s12 / s23) ≠ 0) :
    1 + etaFromData g12 g23 s12 s23 * Real.log (s12 / s23) =
    2 * g12 * s12 / (g12 * s12 - g23 * s23) := by
  unfold etaFromData
  field_simp
  ring

/-- Companion identity: `1 − η·L = −2·g₂₃·s₂₃ / (g₁₂·s₁₂ − g₂₃·s₂₃)`.
    This closes the gen-2→3 equation. -/
theorem etaL_gen23_identity (g12 g23 s12 s23 : ℝ)
    (hD : g12 * s12 - g23 * s23 ≠ 0)
    (hL : Real.log (s12 / s23) ≠ 0) :
    1 - etaFromData g12 g23 s12 s23 * Real.log (s12 / s23) =
    -(2 * g23 * s23) / (g12 * s12 - g23 * s23) := by
  unfold etaFromData
  field_simp
  ring

/-- The consistency violation of the sign-split family is EXACTLY
    what η absorbs: `g₁₂·s₁₂ + g₂₃·s₂₃ = η · L · (g₁₂·s₁₂ − g₂₃·s₂₃)`.
    This is the fundamental equation relating the log-asymmetry parameter
    to the data's departure from the rigid `gen12·s12 + gen23·s23 = 0` law. -/
theorem eta_absorbs_consistency (g12 g23 s12 s23 : ℝ)
    (hD : g12 * s12 - g23 * s23 ≠ 0)
    (hL : Real.log (s12 / s23) ≠ 0) :
    g12 * s12 + g23 * s23 =
    etaFromData g12 g23 s12 s23 * Real.log (s12 / s23) *
      (g12 * s12 - g23 * s23) := by
  unfold etaFromData
  field_simp

/-- **SINGLE-SECTOR EXISTENCE**: For any residual pair with nonzero gen12,
    non-degenerate cross-difference, distinct steps, and nonzero coupling,
    the refined family has a solution.  The proof constructs explicit
    coefficients using `etaFromData` and verifies both components
    via the `etaL_gen12/gen23_identity` theorems. -/
theorem refinedFamily_neg_solvable
    (g12 g23 : ℝ) (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23)
    (hκ : κ ≠ 0)
    (hg12 : g12 ≠ 0)
    (hD : g12 * (s12 : ℝ) - g23 * (s23 : ℝ) ≠ 0)
    (hL : Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0) :
    ∃ coeffs : RefinedCoeffs,
      refinedFamily coeffs ⟨.neg, s12, s23, κ, hs12, hs23⟩ =
        ⟨g12, g23⟩ := by
  have hs23_ne : (s23 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs12_ne : (s12 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h12 := etaL_gen12_identity g12 g23 (s12 : ℝ) (s23 : ℝ) hD hL
  have h23 := etaL_gen23_identity g12 g23 (s12 : ℝ) (s23 : ℝ) hD hL
  have h_corr_ne : 1 + etaFromData g12 g23 (s12 : ℝ) (s23 : ℝ) *
      Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0 := by
    rw [h12]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hg12) hs12_ne) hD
  refine ⟨⟨g12 * ((s12 : ℝ) + (s23 : ℝ)) /
    (κ * (s23 : ℝ) * (1 + etaFromData g12 g23 (s12 : ℝ) (s23 : ℝ) *
      Real.log ((s12 : ℝ) / (s23 : ℝ)))),
    0, etaFromData g12 g23 (s12 : ℝ) (s23 : ℝ)⟩, ?_⟩
  have hD_swap : g12 * (s12 : ℝ) - (s23 : ℝ) * g23 ≠ 0 := by
    rw [show g12 * (s12 : ℝ) - (s23 : ℝ) * g23 =
        g12 * (s12 : ℝ) - g23 * (s23 : ℝ) from by ring]; exact hD
  have hD_comm : -(g23 * (s23 : ℝ)) + g12 * (s12 : ℝ) ≠ 0 := by
    intro h; exact hD (by linarith)
  simp only [refinedFamily]
  ext
  · -- gen12: direct cancellation of cNeg · κ · s23 / total · (1 + η·L)
    dsimp [ResidualPair.gen12]
    field_simp
  · -- gen23: substitute correction factors, then cancel D/D
    dsimp [ResidualPair.gen23]
    rw [h12, h23]
    field_simp [hD_comm, hD_swap]

/-- The positive-sign variant: same existence for `BpowSign.pos` sectors. -/
theorem refinedFamily_pos_solvable
    (g12 g23 : ℝ) (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23)
    (hκ : κ ≠ 0)
    (hg12 : g12 ≠ 0)
    (hD : g12 * (s12 : ℝ) - g23 * (s23 : ℝ) ≠ 0)
    (hL : Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0) :
    ∃ coeffs : RefinedCoeffs,
      refinedFamily coeffs ⟨.pos, s12, s23, κ, hs12, hs23⟩ =
        ⟨g12, g23⟩ := by
  have hs23_ne : (s23 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs12_ne : (s12 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h12 := etaL_gen12_identity g12 g23 (s12 : ℝ) (s23 : ℝ) hD hL
  have h23 := etaL_gen23_identity g12 g23 (s12 : ℝ) (s23 : ℝ) hD hL
  have h_corr_ne : 1 + etaFromData g12 g23 (s12 : ℝ) (s23 : ℝ) *
      Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0 := by
    rw [h12]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hg12) hs12_ne) hD
  have hD_swap : g12 * (s12 : ℝ) - (s23 : ℝ) * g23 ≠ 0 := by
    rw [show g12 * (s12 : ℝ) - (s23 : ℝ) * g23 =
        g12 * (s12 : ℝ) - g23 * (s23 : ℝ) from by ring]; exact hD
  have hD_comm : -(g23 * (s23 : ℝ)) + g12 * (s12 : ℝ) ≠ 0 := by
    intro h; exact hD (by linarith)
  refine ⟨⟨0, g12 * ((s12 : ℝ) + (s23 : ℝ)) /
    (κ * (s23 : ℝ) * (1 + etaFromData g12 g23 (s12 : ℝ) (s23 : ℝ) *
      Real.log ((s12 : ℝ) / (s23 : ℝ)))),
    etaFromData g12 g23 (s12 : ℝ) (s23 : ℝ)⟩, ?_⟩
  simp only [refinedFamily]
  ext
  · dsimp [ResidualPair.gen12]
    field_simp
  · dsimp [ResidualPair.gen23]
    rw [h12, h23]
    field_simp [hD_comm, hD_swap]

/-- **SINGLE-SECTOR UNIQUENESS (neg)**: If two coefficient sets (with sign
    class `.neg`) produce identical refined-family outputs on a given
    signature, their active coefficient `cNeg` and `eta` must agree.
    Combined with `refinedFamily_neg_solvable`, this gives `∃!`.

    Proof strategy: extract gen12/gen23 component equations, cancel the
    common factor `κ·s/total` from each, then add the two simplified
    equations to get `c₁ = c₂`, and substitute back to get `eta₁ = eta₂`. -/
theorem refinedFamily_neg_unique
    (c₁ c₂ p₁ p₂ eta₁ eta₂ : ℝ)
    (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23)
    (hκ : κ ≠ 0) (hc1 : c₁ ≠ 0)
    (hL : Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0)
    (h : refinedFamily ⟨c₁, p₁, eta₁⟩ ⟨.neg, s12, s23, κ, hs12, hs23⟩ =
         refinedFamily ⟨c₂, p₂, eta₂⟩ ⟨.neg, s12, s23, κ, hs12, hs23⟩) :
    c₁ = c₂ ∧ eta₁ = eta₂ := by
  have hs23_ne : (s23 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs12_ne : (s12 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htotal_ne : (s12 : ℝ) + (s23 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  -- Extract gen12 and gen23 component equations from the ResidualPair equality
  have hg12 := congr_arg ResidualPair.gen12 h
  have hg23 := congr_arg ResidualPair.gen23 h
  dsimp only [refinedFamily] at hg12 hg23
  -- hg23 has negation on both sides; strip it
  replace hg23 := neg_inj.mp hg23
  -- Cancel κ·s23/total from gen12 equation via calc + ring
  have h1 : c₁ * (1 + eta₁ * Real.log (↑s12 / ↑s23)) =
             c₂ * (1 + eta₂ * Real.log (↑s12 / ↑s23)) := by
    have hf : κ * (↑s23 : ℝ) / ((↑s12 : ℝ) + ↑s23) ≠ 0 :=
      div_ne_zero (mul_ne_zero hκ hs23_ne) htotal_ne
    exact mul_right_cancel₀ hf (show
      c₁ * (1 + eta₁ * Real.log (↑s12 / ↑s23)) * (κ * ↑s23 / (↑s12 + ↑s23)) =
      c₂ * (1 + eta₂ * Real.log (↑s12 / ↑s23)) * (κ * ↑s23 / (↑s12 + ↑s23)) from by
        calc _ = c₁ * κ * ↑s23 / (↑s12 + ↑s23) *
                   (1 + eta₁ * Real.log (↑s12 / ↑s23)) := by ring
             _ = c₂ * κ * ↑s23 / (↑s12 + ↑s23) *
                   (1 + eta₂ * Real.log (↑s12 / ↑s23)) := hg12
             _ = _ := by ring)
  -- Cancel κ·s12/total from gen23 equation
  have h2 : c₁ * (1 - eta₁ * Real.log (↑s12 / ↑s23)) =
             c₂ * (1 - eta₂ * Real.log (↑s12 / ↑s23)) := by
    have hf : κ * (↑s12 : ℝ) / ((↑s12 : ℝ) + ↑s23) ≠ 0 :=
      div_ne_zero (mul_ne_zero hκ hs12_ne) htotal_ne
    exact mul_right_cancel₀ hf (show
      c₁ * (1 - eta₁ * Real.log (↑s12 / ↑s23)) * (κ * ↑s12 / (↑s12 + ↑s23)) =
      c₂ * (1 - eta₂ * Real.log (↑s12 / ↑s23)) * (κ * ↑s12 / (↑s12 + ↑s23)) from by
        calc _ = c₁ * κ * ↑s12 / (↑s12 + ↑s23) *
                   (1 - eta₁ * Real.log (↑s12 / ↑s23)) := by ring
             _ = c₂ * κ * ↑s12 / (↑s12 + ↑s23) *
                   (1 - eta₂ * Real.log (↑s12 / ↑s23)) := hg23
             _ = _ := by ring)
  -- Add h1 and h2: eta terms cancel, leaving 2·c₁ = 2·c₂
  have hc : c₁ = c₂ := by linarith
  -- Substitute c₁ = c₂ into h1, cancel c₁ (≠ 0) then L (≠ 0)
  have heta : eta₁ = eta₂ := by
    rw [← hc] at h1
    have := mul_left_cancel₀ hc1 h1
    have : eta₁ * Real.log (↑s12 / ↑s23) = eta₂ * Real.log (↑s12 / ↑s23) := by linarith
    exact mul_right_cancel₀ hL this
  exact ⟨hc, heta⟩

/-- **SINGLE-SECTOR UNIQUENESS (pos)**: Symmetric variant for `.pos` sign class. -/
theorem refinedFamily_pos_unique
    (n₁ n₂ c₁ c₂ eta₁ eta₂ : ℝ)
    (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23)
    (hκ : κ ≠ 0) (hc1 : c₁ ≠ 0)
    (hL : Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0)
    (h : refinedFamily ⟨n₁, c₁, eta₁⟩ ⟨.pos, s12, s23, κ, hs12, hs23⟩ =
         refinedFamily ⟨n₂, c₂, eta₂⟩ ⟨.pos, s12, s23, κ, hs12, hs23⟩) :
    c₁ = c₂ ∧ eta₁ = eta₂ := by
  have hs23_ne : (s23 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs12_ne : (s12 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htotal_ne : (s12 : ℝ) + (s23 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hg12 := congr_arg ResidualPair.gen12 h
  have hg23 := congr_arg ResidualPair.gen23 h
  dsimp only [refinedFamily] at hg12 hg23
  replace hg23 := neg_inj.mp hg23
  have h1 : c₁ * (1 + eta₁ * Real.log (↑s12 / ↑s23)) =
             c₂ * (1 + eta₂ * Real.log (↑s12 / ↑s23)) := by
    have hf : κ * (↑s23 : ℝ) / ((↑s12 : ℝ) + ↑s23) ≠ 0 :=
      div_ne_zero (mul_ne_zero hκ hs23_ne) htotal_ne
    exact mul_right_cancel₀ hf (show
      c₁ * (1 + eta₁ * Real.log (↑s12 / ↑s23)) * (κ * ↑s23 / (↑s12 + ↑s23)) =
      c₂ * (1 + eta₂ * Real.log (↑s12 / ↑s23)) * (κ * ↑s23 / (↑s12 + ↑s23)) from by
        calc _ = c₁ * κ * ↑s23 / (↑s12 + ↑s23) *
                   (1 + eta₁ * Real.log (↑s12 / ↑s23)) := by ring
             _ = c₂ * κ * ↑s23 / (↑s12 + ↑s23) *
                   (1 + eta₂ * Real.log (↑s12 / ↑s23)) := hg12
             _ = _ := by ring)
  have h2 : c₁ * (1 - eta₁ * Real.log (↑s12 / ↑s23)) =
             c₂ * (1 - eta₂ * Real.log (↑s12 / ↑s23)) := by
    have hf : κ * (↑s12 : ℝ) / ((↑s12 : ℝ) + ↑s23) ≠ 0 :=
      div_ne_zero (mul_ne_zero hκ hs12_ne) htotal_ne
    exact mul_right_cancel₀ hf (show
      c₁ * (1 - eta₁ * Real.log (↑s12 / ↑s23)) * (κ * ↑s12 / (↑s12 + ↑s23)) =
      c₂ * (1 - eta₂ * Real.log (↑s12 / ↑s23)) * (κ * ↑s12 / (↑s12 + ↑s23)) from by
        calc _ = c₁ * κ * ↑s12 / (↑s12 + ↑s23) *
                   (1 - eta₁ * Real.log (↑s12 / ↑s23)) := by ring
             _ = c₂ * κ * ↑s12 / (↑s12 + ↑s23) *
                   (1 - eta₂ * Real.log (↑s12 / ↑s23)) := hg23
             _ = _ := by ring)
  have hc : c₁ = c₂ := by linarith
  have heta : eta₁ = eta₂ := by
    rw [← hc] at h1
    have := mul_left_cancel₀ hc1 h1
    have : eta₁ * Real.log (↑s12 / ↑s23) = eta₂ * Real.log (↑s12 / ↑s23) := by linarith
    exact mul_right_cancel₀ hL this
  exact ⟨hc, heta⟩

/-- For `.neg` signatures, the `cPos` field is unused and can be changed freely. -/
theorem neg_cPos_irrelevant (c q₁ q₂ η : ℝ) (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23) :
    refinedFamily ⟨c, q₁, η⟩ ⟨.neg, s12, s23, κ, hs12, hs23⟩ =
    refinedFamily ⟨c, q₂, η⟩ ⟨.neg, s12, s23, κ, hs12, hs23⟩ := by
  simp [refinedFamily]

/-- For `.pos` signatures, the `cNeg` field is unused and can be changed freely. -/
theorem pos_cNeg_irrelevant (q₁ q₂ c η : ℝ) (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23) :
    refinedFamily ⟨q₁, c, η⟩ ⟨.pos, s12, s23, κ, hs12, hs23⟩ =
    refinedFamily ⟨q₂, c, η⟩ ⟨.pos, s12, s23, κ, hs12, hs23⟩ := by
  simp [refinedFamily]

/-- **SECTOR CLOSURE (neg)**: For any `.neg` sector with nonzero gen12,
    non-degenerate cross-difference, distinct steps, and nonzero coupling,
    the refined family has a **unique** active-coefficient solution (c, η).
    This is the full `∃!` on the active parameters.

    Combines `refinedFamily_neg_solvable` (existence) with
    `refinedFamily_neg_unique` (uniqueness). -/
theorem refined_neg_sector_closure
    (g12 g23 : ℝ) (s12 s23 : ℕ) (κ : ℝ)
    (hs12 : 0 < s12) (hs23 : 0 < s23)
    (hκ : κ ≠ 0) (hg12 : g12 ≠ 0)
    (hD : g12 * (s12 : ℝ) - g23 * (s23 : ℝ) ≠ 0)
    (hL : Real.log ((s12 : ℝ) / (s23 : ℝ)) ≠ 0) :
    ∃ c η : ℝ,
      refinedFamily ⟨c, 0, η⟩ ⟨.neg, s12, s23, κ, hs12, hs23⟩ = ⟨g12, g23⟩ ∧
      ∀ c' p' η',
        refinedFamily ⟨c', p', η'⟩ ⟨.neg, s12, s23, κ, hs12, hs23⟩ = ⟨g12, g23⟩ →
        c' = c ∧ η' = η := by
  obtain ⟨⟨c, cp, η⟩, hexist⟩ :=
    refinedFamily_neg_solvable g12 g23 s12 s23 κ hs12 hs23 hκ hg12 hD hL
  refine ⟨c, η, ?_, ?_⟩
  · -- Existence: swap cPos from cp to 0 (irrelevant for .neg)
    exact (neg_cPos_irrelevant c 0 cp η s12 s23 κ hs12 hs23).trans hexist
  · -- Uniqueness: any solution (c', p', η') must have c' = c, η' = η
    intro c' p' η' h'
    have hc_ne : c ≠ 0 := by
      intro hc
      exact hg12 (by
        have := congr_arg ResidualPair.gen12 hexist
        dsimp only [refinedFamily] at this
        simp [hc] at this
        linarith)
    have ⟨hc, hη⟩ := refinedFamily_neg_unique c c' cp p' η η' s12 s23 κ
      hs12 hs23 hκ hc_ne hL (hexist.trans h'.symm)
    exact ⟨hc.symm, hη.symm⟩

/-! ## Sign-Class Family: Independent η per B_pow Sign

Since universal η is ruled out with current data, the natural generalization
gives each sign class its own log-asymmetry parameter.  With 4 parameters
(cNeg, etaNeg, cPos, etaPos) and 4 quark equations, the system is exactly
determined — each sector's 2 equations uniquely fix its (c, η) pair. -/

/-- Four global coefficients: two (amplitude, log-asymmetry) pairs,
    one per `B_pow` sign class. -/
structure SignClassCoeffs where
  cNeg   : ℝ
  etaNeg : ℝ
  cPos   : ℝ
  etaPos : ℝ

/-- Sign-class family with independent η per sign.  Each sector's
    gen12/gen23 ratio is individually adjustable via its sign-class η,
    while the overall amplitude is set by c and coupling. -/
noncomputable def signClassFamily (coeffs : SignClassCoeffs)
    (sig : ResidualSignature) : ResidualPair :=
  let (c, eta) :=
    match sig.sign with
    | .neg => (coeffs.cNeg, coeffs.etaNeg)
    | .pos => (coeffs.cPos, coeffs.etaPos)
  let s12 := (sig.step12 : ℝ)
  let s23 := (sig.step23 : ℝ)
  let total := s12 + s23
  let logAsym := Real.log (s12 / s23)
  { gen12 := c * sig.coupling * s23 / total * (1 + eta * logAsym)
  , gen23 := -(c * sig.coupling * s12 / total * (1 - eta * logAsym))
  }

/-- When both η values agree, the sign-class family collapses
    to the refined family with universal η. -/
theorem signClass_collapse_to_refined
    (cN cP eta : ℝ) (sig : ResidualSignature) :
    signClassFamily ⟨cN, eta, cP, eta⟩ sig =
    refinedFamily ⟨cN, cP, eta⟩ sig := by
  simp only [signClassFamily, refinedFamily]
  cases sig.sign <;> rfl

/-! ## Concrete Instantiation: PDG Data + RS Coupling

PDG 2022 experimental masses (MeV) at mixed reference scales.
Quark masses carry the standard scheme caveat: u, d, s at 2 GeV MS-bar;
c at m_c; b at m_b; t as pole mass.  At LO in QCD the within-sector mass
ratio is RG-invariant; NLO corrections are O(α_s) ≈ 12%.  Once the RG
bridge module compiles, quark residuals should be refined to anchor-scale
ratios; the present values serve as the first concrete target.

Charged-lepton pole masses are scheme-free (no RG caveat). -/

section ConcreteInstantiation

def pdg_up       : ℝ := 2.16
def pdg_charm    : ℝ := 1270
def pdg_top      : ℝ := 172690
def pdg_down     : ℝ := 4.67
def pdg_strange  : ℝ := 93.4
def pdg_bottom   : ℝ := 4180
def pdg_electron : ℝ := 0.510999
def pdg_muon     : ℝ := 105.658
def pdg_tau      : ℝ := 1776.86

/-- RS-derived strong coupling constant: α_s = 2/17 (wallpaper-group fraction).
    Proved to within 0.3σ of PDG α_s(M_Z) = 0.1179 ± 0.0009. -/
noncomputable def alphaStrong : ℝ := 2 / 17

/-- Rung-unit residual: `log_φ(observed ratio) − integer step`.
    Measures the sub-leading correction in units of φ-ladder rungs. -/
noncomputable def rungResidual (ratio : ℝ) (step : ℕ) : ℝ :=
  Real.log ratio / Real.log Constants.phi - (step : ℝ)

noncomputable def upGen12Residual : ℝ :=
  rungResidual (pdg_charm / pdg_up) 13

noncomputable def upGen23Residual : ℝ :=
  rungResidual (pdg_top / pdg_charm) 11

noncomputable def downGen12Residual : ℝ :=
  rungResidual (pdg_strange / pdg_down) 6

noncomputable def downGen23Residual : ℝ :=
  rungResidual (pdg_bottom / pdg_strange) 8

noncomputable def leptonGen12Residual : ℝ :=
  rungResidual (pdg_muon / pdg_electron) 11

noncomputable def leptonGen23Residual : ℝ :=
  rungResidual (pdg_tau / pdg_muon) 6

/-- Exact up-quark residual pair (from PDG mass ratios vs φ^{SDGT step}).
    Approximate values: gen12 ≈ +0.25, gen23 ≈ −0.79 rungs. -/
noncomputable def upExact : ResidualPair where
  gen12 := upGen12Residual
  gen23 := upGen23Residual

/-- Exact down-quark residual pair (from PDG mass ratios vs φ^{SDGT step}).
    Approximate values: gen12 ≈ +0.23, gen23 ≈ −0.10 rungs. -/
noncomputable def downExact : ResidualPair where
  gen12 := downGen12Residual
  gen23 := downGen23Residual

/-- Observed lepton residual pair (pole-mass ratios — no RG ambiguity).
    Approximate values: gen12 ≈ +0.08, gen23 ≈ −0.13 rungs. -/
noncomputable def leptonObserved : ResidualPair where
  gen12 := leptonGen12Residual
  gen23 := leptonGen23Residual

/-! ### Specialized Closure Targets -/

/-- **Item 8 Closure (Specialized)**: Both quark sectors fit the sign-split
    ratio family with coupling κ = α_s = 2/17.
    Proving this closes the open item and freezes the two global coefficients. -/
noncomputable def item8Specialized : Prop :=
  item8ClosureTarget upExact downExact alphaStrong alphaStrong

/-- **All-Sector Verification**: The coefficients frozen by quark data also
    reproduce the observed lepton residuals — a genuine out-of-sample test.

    Leptons share `BpowSign.neg` with up quarks, so `cNeg` is already fixed
    by the quark closure.  If that same `cNeg` reproduces the lepton residuals
    under the lepton signature `(11, 6)` and lepton coupling `κ_lep`, the
    family is vindicated across sign classes.

    The parameter `kappaLepton` is left free: the leading candidate is
    `1 / (4 · π · 11)` (the RS electromagnetic coupling from α_seed). -/
noncomputable def allSectorTest (kappaLepton : ℝ) : Prop :=
  ∃ coeffs : RatioFamilyCoeffs,
    predictedResiduals coeffs (upQuarkSignature alphaStrong) = upExact ∧
    predictedResiduals coeffs (downQuarkSignature alphaStrong) = downExact ∧
    predictedResiduals coeffs (leptonSignature kappaLepton) = leptonObserved

/-! ### Refined Closure Targets -/

/-- **Refined Item 8 Closure**: Both quark sectors fit the log-asymmetry
    ratio family with κ = α_s = 2/17 and a single universal η.
    This is overdetermined (3 parameters, 4 equations): the `∃!` is
    a genuine test, not a tautology. -/
noncomputable def refinedItem8Specialized : Prop :=
  refinedItem8ClosureTarget upExact downExact alphaStrong alphaStrong

/-- **Refined All-Sector Test**: The 3 coefficients frozen by quark data
    also reproduce the lepton residuals (6 equations, 3 unknowns).
    This is the strongest available falsification target. -/
noncomputable def refinedAllSectorTest (kappaLepton : ℝ) : Prop :=
  ∃ coeffs : RefinedCoeffs,
    refinedPrediction coeffs (upQuarkSignature alphaStrong) = upExact ∧
    refinedPrediction coeffs (downQuarkSignature alphaStrong) = downExact ∧
    refinedPrediction coeffs (leptonSignature kappaLepton) = leptonObserved

/-! ### Per-Sector η Values (from closed-form formula)

Each sector's η is computed via `etaFromData` using PDG residuals and
SDGT steps.  The lepton value is small and perturbative (|η·L| ≈ 4%),
confirming the family form works for scheme-free pole masses.  Quark
values are inflated by mixed-scale PDG artifacts. -/

/-- Lepton η from pole-mass residuals: +0.065.
    This is the cleanest data point — no RG ambiguity. -/
noncomputable def leptonEta : ℝ :=
  etaFromData leptonGen12Residual leptonGen23Residual 11 6

/-- Up-quark η from mixed-scheme PDG: −2.72.
    Inflated by the t/c mixed-scheme comparison (pole vs MS-bar at m_c). -/
noncomputable def upQuarkEta : ℝ :=
  etaFromData upGen12Residual upGen23Residual 13 11

/-- Down-quark η from mixed-scheme PDG: −0.88. -/
noncomputable def downQuarkEta : ℝ :=
  etaFromData downGen12Residual downGen23Residual 6 8

/-! ### Concrete Lepton Closure

The lepton sector is the cleanest `.neg` test case because the masses are pole
masses (no QCD scheme ambiguity).  The non-degeneracy hypotheses needed by
`refined_neg_sector_closure` can be verified directly from φ-power comparisons:

* `μ/e > φ¹¹`, so `leptonGen12Residual > 0`
* `τ/μ < φ⁶`, so `leptonGen23Residual < 0`

This gives the full `∃!` closure for the concrete lepton signature `(11, 6)`
at the candidate electromagnetic coupling `κ_lep = 1 / alpha_seed`. -/

/-- Leading lepton coupling candidate from the RS electromagnetic seed:
    `κ_lep = 1 / alpha_seed = 1 / (4π·11)`. -/
noncomputable def kappaLeptonCandidate : ℝ := 1 / Constants.alpha_seed

theorem kappaLeptonCandidate_pos : 0 < kappaLeptonCandidate := by
  unfold kappaLeptonCandidate Constants.alpha_seed
  positivity

theorem kappaLeptonCandidate_ne_zero : kappaLeptonCandidate ≠ 0 :=
  ne_of_gt kappaLeptonCandidate_pos

/-- The lepton step log-asymmetry is positive: `log(11/6) > 0`. -/
theorem leptonLogAsym_pos : 0 < Real.log ((11 : ℝ) / 6) := by
  have hratio_gt_one : (1 : ℝ) < (11 : ℝ) / 6 := by norm_num
  exact Real.log_pos hratio_gt_one

theorem leptonLogAsym_ne_zero : Real.log ((11 : ℝ) / 6) ≠ 0 :=
  ne_of_gt leptonLogAsym_pos

/-- The μ/e residual is positive because the observed ratio exceeds `φ¹¹`. -/
theorem leptonGen12Residual_pos : 0 < leptonGen12Residual := by
  unfold leptonGen12Residual rungResidual
  have hlogphi : 0 < Real.log Constants.phi := Real.log_pos Constants.one_lt_phi
  have hphi11_lt : Constants.phi ^ (11 : ℕ) < pdg_muon / pdg_electron := by
    have hphi11_lt_200 : Constants.phi ^ (11 : ℕ) < (200 : ℝ) := by
      rw [Constants.phi_eleventh_eq]
      linarith [Constants.phi_lt_onePointSixTwo]
    have hratio_gt_200 : (200 : ℝ) < pdg_muon / pdg_electron := by
      norm_num [pdg_muon, pdg_electron]
    linarith
  have hmain : (11 : ℝ) < Real.log (pdg_muon / pdg_electron) / Real.log Constants.phi := by
    apply (lt_div_iff₀ hlogphi).2
    rw [show (11 : ℝ) = (11 : ℕ) by norm_num, ← Real.log_rpow Constants.phi_pos]
    apply Real.log_lt_log
    · exact Real.rpow_pos_of_pos Constants.phi_pos 11
    · simpa [Real.rpow_natCast] using hphi11_lt
  linarith

theorem leptonGen12Residual_ne_zero : leptonGen12Residual ≠ 0 :=
  ne_of_gt leptonGen12Residual_pos

/-- The τ/μ residual is negative because the observed ratio lies below `φ⁶`. -/
theorem leptonGen23Residual_neg : leptonGen23Residual < 0 := by
  unfold leptonGen23Residual rungResidual
  have hlogphi : 0 < Real.log Constants.phi := Real.log_pos Constants.one_lt_phi
  have hratio_lt : pdg_tau / pdg_muon < Constants.phi ^ (6 : ℕ) := by
    have hratio_lt_17 : pdg_tau / pdg_muon < (17 : ℝ) := by
      norm_num [pdg_tau, pdg_muon]
    have h17_lt_phi6 : (17 : ℝ) < Constants.phi ^ (6 : ℕ) := by
      rw [Constants.phi_sixth_eq]
      linarith [Constants.phi_gt_onePointFive]
    linarith
  have hratio_pos : 0 < pdg_tau / pdg_muon := by
    norm_num [pdg_tau, pdg_muon]
  have hmain : Real.log (pdg_tau / pdg_muon) / Real.log Constants.phi < (6 : ℝ) := by
    apply (div_lt_iff₀ hlogphi).2
    rw [show (6 : ℝ) = (6 : ℕ) by norm_num, ← Real.log_rpow Constants.phi_pos]
    apply Real.log_lt_log
    · exact hratio_pos
    · simpa [Real.rpow_natCast] using hratio_lt
  linarith

/-- The lepton cross-difference is strictly positive, hence nonzero. -/
theorem leptonCrossDiff_pos :
    0 < leptonGen12Residual * (11 : ℝ) - leptonGen23Residual * (6 : ℝ) := by
  nlinarith [leptonGen12Residual_pos, leptonGen23Residual_neg]

theorem leptonCrossDiff_ne_zero :
    leptonGen12Residual * (11 : ℝ) - leptonGen23Residual * (6 : ℝ) ≠ 0 :=
  ne_of_gt leptonCrossDiff_pos

/-- Concrete `∃!` closure for the lepton `.neg` sector at the candidate
    electromagnetic coupling `κ_lep = 1 / (4π·11)`.  This freezes the active
    pair `(cNeg, eta)` independently of the quark data. -/
theorem leptonSectorClosure :
    ∃ c η : ℝ,
      refinedFamily ⟨c, 0, η⟩ (leptonSignature kappaLeptonCandidate) = leptonObserved ∧
      ∀ c' p' η',
        refinedFamily ⟨c', p', η'⟩ (leptonSignature kappaLeptonCandidate) = leptonObserved →
        c' = c ∧ η' = η := by
  have hs12 : 0 < 11 := by norm_num
  have hs23 : 0 < 6 := by norm_num
  simpa [leptonSignature, leptonObserved] using
    refined_neg_sector_closure leptonGen12Residual leptonGen23Residual 11 6
      kappaLeptonCandidate hs12 hs23 kappaLeptonCandidate_ne_zero
      leptonGen12Residual_ne_zero leptonCrossDiff_ne_zero leptonLogAsym_ne_zero

/-- Closed-form lepton anchor for the active `.neg` amplitude.  This is the
    explicit `cNeg` obtained from the lepton gen12 equation once `eta` is fixed
    to `leptonEta`. -/
noncomputable def leptonAnchoredCNeg (kappaLepton : ℝ) : ℝ :=
  leptonGen12Residual * ((11 : ℝ) + 6) /
    (kappaLepton * 6 * (1 + leptonEta * Real.log ((11 : ℝ) / 6)))

/-- The lepton-anchored global coefficient package.  `cPos` is left at `0`
    because leptons only freeze the `.neg` branch. -/
noncomputable def leptonAnchoredCoeffs (kappaLepton : ℝ) : RefinedCoeffs :=
  ⟨leptonAnchoredCNeg kappaLepton, 0, leptonEta⟩

/-! ### Anchor-Scale Quark Transport (LO scaffold)

The current LO scaffold transports the PDG quark masses to the RS anchor scale
`μ* = 182.201 GeV` using piecewise one-loop α_s and the one-loop mass anomalous
dimension.  This is the concrete bridge needed to compare lepton-frozen
predictions against scheme-consistent quark residuals. -/

/-- One-loop α_s in the `n_f = 6` region, anchored at `μ*`. -/
noncomputable def alphaS6At (μ : ℝ) : ℝ :=
  Physics.RG.alpha_s_running Physics.RG.rs_alpha_s_anchor (Physics.RG.b0_qcd 6)
    μ Physics.RG.rs_anchor_scale

/-- Boundary value α_s(m_t) obtained from the `n_f = 6` branch. -/
noncomputable def alphaSAtTopThreshold : ℝ :=
  alphaS6At Physics.RG.top_threshold.scale

/-- One-loop α_s in the `n_f = 5` region, matched at the top threshold. -/
noncomputable def alphaS5At (μ : ℝ) : ℝ :=
  Physics.RG.alpha_s_running alphaSAtTopThreshold (Physics.RG.b0_qcd 5)
    μ Physics.RG.top_threshold.scale

/-- Boundary value α_s(m_b) obtained from the `n_f = 5` branch. -/
noncomputable def alphaSAtBottomThreshold : ℝ :=
  alphaS5At Physics.RG.bottom_threshold.scale

/-- One-loop α_s in the `n_f = 4` region, matched at the bottom threshold. -/
noncomputable def alphaS4At (μ : ℝ) : ℝ :=
  Physics.RG.alpha_s_running alphaSAtBottomThreshold (Physics.RG.b0_qcd 4)
    μ Physics.RG.bottom_threshold.scale

/-- Boundary value α_s(m_c) obtained from the `n_f = 4` branch. -/
noncomputable def alphaSAtCharmThreshold : ℝ :=
  alphaS4At Physics.RG.charm_threshold.scale

/-- One-loop α_s in the `n_f = 3` region, matched at the charm threshold. -/
noncomputable def alphaS3At (μ : ℝ) : ℝ :=
  Physics.RG.alpha_s_running alphaSAtCharmThreshold (Physics.RG.b0_qcd 3)
    μ Physics.RG.charm_threshold.scale

/-- Piecewise one-loop α_s stitched across the heavy-quark thresholds. -/
noncomputable def alphaSPiecewise (μ : ℝ) : ℝ :=
  if Physics.RG.top_threshold.scale ≤ μ then alphaS6At μ
  else if Physics.RG.bottom_threshold.scale ≤ μ then alphaS5At μ
  else if Physics.RG.charm_threshold.scale ≤ μ then alphaS4At μ
  else alphaS3At μ

/-- Shared PDG reference scale for the light MS-bar quarks (`u,d,s`). -/
def quarkReferenceScale2GeV : ℝ := 2

/-- Threshold lists for upward transport to the anchor scale. -/
def thresholdsFromTwoGeV : List Physics.RG.FlavorThreshold :=
  [Physics.RG.bottom_threshold, Physics.RG.top_threshold]

def thresholdsFromCharm : List Physics.RG.FlavorThreshold :=
  [Physics.RG.bottom_threshold, Physics.RG.top_threshold]

def thresholdsFromBottom : List Physics.RG.FlavorThreshold :=
  [Physics.RG.top_threshold]

/-- Light and heavy quark masses transported to the anchor scale `μ*`. -/
noncomputable def upMassAtAnchor : ℝ :=
  Physics.RG.transport_mass_through pdg_up alphaSPiecewise quarkReferenceScale2GeV
    Physics.RG.rs_anchor_scale thresholdsFromTwoGeV 4

noncomputable def downMassAtAnchor : ℝ :=
  Physics.RG.transport_mass_through pdg_down alphaSPiecewise quarkReferenceScale2GeV
    Physics.RG.rs_anchor_scale thresholdsFromTwoGeV 4

noncomputable def strangeMassAtAnchor : ℝ :=
  Physics.RG.transport_mass_through pdg_strange alphaSPiecewise quarkReferenceScale2GeV
    Physics.RG.rs_anchor_scale thresholdsFromTwoGeV 4

noncomputable def charmMassAtAnchor : ℝ :=
  Physics.RG.transport_mass_through pdg_charm alphaSPiecewise
    Physics.RG.charm_threshold.scale Physics.RG.rs_anchor_scale thresholdsFromCharm 4

noncomputable def bottomMassAtAnchor : ℝ :=
  Physics.RG.transport_mass_through pdg_bottom alphaSPiecewise
    Physics.RG.bottom_threshold.scale Physics.RG.rs_anchor_scale thresholdsFromBottom 5

noncomputable def topMassAtAnchor : ℝ :=
  Physics.RG.transport_mass_through pdg_top alphaSPiecewise
    Physics.RG.top_threshold.scale Physics.RG.rs_anchor_scale [] 6

/-- Anchor-scale quark residuals built from the transported masses.  Under the
    current LO scaffold, shell evaluation gives approximately:
    up `(0.02, +0.57)` and down `(0.23, +0.19)` in rung units. -/
noncomputable def anchorUpGen12Residual : ℝ :=
  rungResidual (charmMassAtAnchor / upMassAtAnchor) 13

noncomputable def anchorUpGen23Residual : ℝ :=
  rungResidual (topMassAtAnchor / charmMassAtAnchor) 11

noncomputable def anchorDownGen12Residual : ℝ :=
  rungResidual (strangeMassAtAnchor / downMassAtAnchor) 6

noncomputable def anchorDownGen23Residual : ℝ :=
  rungResidual (bottomMassAtAnchor / strangeMassAtAnchor) 8

noncomputable def anchorUpExact : ResidualPair where
  gen12 := anchorUpGen12Residual
  gen23 := anchorUpGen23Residual

noncomputable def anchorDownExact : ResidualPair where
  gen12 := anchorDownGen12Residual
  gen23 := anchorDownGen23Residual

/-- Up-sector out-of-sample prediction after freezing `(cNeg, eta)` on leptons. -/
noncomputable def leptonAnchoredUpPrediction (kappaLepton : ℝ) : ResidualPair :=
  refinedPrediction (leptonAnchoredCoeffs kappaLepton) (upQuarkSignature alphaStrong)

/-- Two down-sector amplitudes implied by the transported anchor residuals once
    the lepton value of `eta` is frozen.  Equality of these two expressions is
    the one-parameter down-sector consistency test under lepton anchoring. -/
noncomputable def downAnchorCPosFromGen12 : ℝ :=
  anchorDownGen12Residual * ((6 : ℝ) + 8) /
    (alphaStrong * 8 * (1 + leptonEta * Real.log ((6 : ℝ) / 8)))

noncomputable def downAnchorCPosFromGen23 : ℝ :=
  -(anchorDownGen23Residual * ((6 : ℝ) + 8) /
    (alphaStrong * 6 * (1 - leptonEta * Real.log ((6 : ℝ) / 8))))

/-- The concrete anchor-scale lepton-anchored falsification target:
    the up prediction must match the transported anchor residuals, and the down
    sector must induce a single consistent `cPos`. -/
noncomputable def leptonAnchoredAnchorTest : Prop :=
  leptonAnchoredUpPrediction kappaLeptonCandidate = anchorUpExact ∧
  downAnchorCPosFromGen12 = downAnchorCPosFromGen23

/-! ### Lepton-Anchored Closure Strategy

Since leptons provide scheme-free data with perturbative η ≈ 0.065,
the resolution strategy is:

1. **Anchor on leptons**: Fix η and cNeg from the two lepton equations
   (both generations share `BpowSign.neg` with up quarks).
2. **Predict quarks at anchor scale**: The frozen (cNeg, η) pair
   predicts up-quark residuals at the anchor scale μ* = 182 GeV.
   Down quarks provide an independent prediction via cPos.
3. **RG bridge**: Compile the `RunningCouplings` module to transport
   PDG quark masses to the anchor scale, producing scheme-consistent
   residuals for comparison.

This makes the quark mass predictions genuine out-of-sample tests
rather than fits, and keeps the family form validated by clean data. -/

/-- Lepton-anchored closure: the refined family with lepton-derived η
    fits both leptons (by construction) and predicts anchor-scale quarks.
    The proposition is: there exist global coefficients such that
    the family simultaneously fits leptons at coupling κ_lep and
    predicts quark residuals at the anchor scale. -/
noncomputable def leptonAnchoredTarget
    (kappaLepton : ℝ)
    (anchorUpExact anchorDownExact : ResidualPair) : Prop :=
  ∃ coeffs : RefinedCoeffs,
    refinedPrediction coeffs (leptonSignature kappaLepton) = leptonObserved ∧
    refinedPrediction coeffs (upQuarkSignature alphaStrong) = anchorUpExact ∧
    refinedPrediction coeffs (downQuarkSignature alphaStrong) = anchorDownExact

/-- Sign-class family closure: the 4-parameter family with independent η
    per sign class fits all three sectors simultaneously.
    This is the full all-sector test (6 equations, 4 unknowns + 1 free κ_lep). -/
noncomputable def signClassAllSectorTarget (kappaLepton : ℝ) : Prop :=
  ∃ coeffs : SignClassCoeffs,
    signClassFamily coeffs (upQuarkSignature alphaStrong) = upExact ∧
    signClassFamily coeffs (downQuarkSignature alphaStrong) = downExact ∧
    signClassFamily coeffs (leptonSignature kappaLepton) = leptonObserved

end ConcreteInstantiation

end Item8ClosureTarget
end Verification
end IndisputableMonolith
