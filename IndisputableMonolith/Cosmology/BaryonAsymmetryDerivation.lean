import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.GrayCodeChirality
import IndisputableMonolith.Foundation.ParticleGenerations
import IndisputableMonolith.StandardModel.CKMFromCube
import IndisputableMonolith.StandardModel.JarlskogInvariant
import IndisputableMonolith.Cosmology.SakharovFromLedger

/-!
# Baryon Asymmetry η_B: Structural Scaffold + φ-Rung Hypothesis

STATUS TAGS (honest split, per the 2026-06-25 external review):

- **THEOREM (structural)**: η_B > 0 follows from J_CP > 0 (Jarlskog from
  Gray-code chirality) plus the Sakharov conditions. The SIGN of the
  asymmetry (matter exists) is the derived content of this module.
- **SCAFFOLD (does NOT match the observed number)**: `eta_B_structural :=
  J_CP / g_★` is the textbook proportionality skeleton. Numerically it is
  ≈ 3×10⁻⁵ / 106.75 ≈ 3×10⁻⁷, i.e. roughly 500× LARGER than the observed
  6.1×10⁻¹⁰. Only positivity and smallness (< 1) are proved. It is not the
  prediction, and no theorem here claims it is. The missing physics is the
  order-parameter dynamics through the transition (Boltzmann transport,
  washout), which is OPEN.
- **HYPOTHESIS (empirical rung match)**: the Planck-matched expression is
  η_B = φ⁻⁴⁴·(1−φ⁻⁸)² (see EtaBPrefactorDerivation / EtaBIntervalCert).
  Note it contains NO g_★ and no Γ_sph/H: the structural scaffold above and
  the rung match are two different objects, and this module does not
  pretend they are connected. Falsifier: a tightened CMB measurement of
  η_B outside the φ⁻⁴⁴·(1−φ⁻⁸)² band.

## The Observable

The baryon-to-photon ratio:
  η_B = n_B / n_γ ≈ 6.1 × 10⁻¹⁰

Measured from:
- Big Bang Nucleosynthesis (BBN): η_B = (6.1 ± 0.3) × 10⁻¹⁰
- CMB (Planck 2018): η_B = (6.12 ± 0.04) × 10⁻¹⁰

## The Structural Formula (scaffold)

In electroweak baryogenesis, the baryon asymmetry has the shape:

  η_B ∝ (ε_CP / g_★) × (washout factor)

where:
- ε_CP ∝ J_CP (CP asymmetry, from JarlskogInvariant — RS-derived)
- g_★ = relativistic DOF at T_EW (SM bookkeeping with RS-sourced gauge
  group + generation count; see StandardModel.RelativisticDOF for the
  derived-vs-imported split — NOT "all forced by Q₃")
- the washout factor requires transport dynamics (OPEN; see
  EWPhaseTransition for the positive-definite Γ_sph/H scaffold)

## The φ-rung hypothesis

  η_B ≈ φ⁻⁴⁴ ≈ 6.38 × 10⁻¹⁰ (within ~4.5% of Planck before the prefactor;
  φ⁻⁴⁴·(1−φ⁻⁸)² lands within the Planck band).

Note φ⁻⁴⁵ ≈ 3.9×10⁻¹⁰ is the Θ_crit reciprocal; the rung used for η_B is
−44 = 1 − 45, i.e. η_B ≈ φ/Θ_crit. Earlier drafts quoted φ⁻⁴⁵ for η_B
itself; that was a REAL inconsistency and −44 is the operative rung.

## Main Results

1. `eta_B_structural`: structural formula (scaffold; wrong magnitude, see tag)
2. `eta_B_positive`: η_B > 0 (matter dominates) — the derived sign
3. `eta_B_rung` + `saturation_exponent`: the −44 = 1 − 45 rung arithmetic
4. `BaryonAsymmetryCert`: master certificate
-/

namespace IndisputableMonolith
namespace Cosmology
namespace BaryonAsymmetryDerivation

open Constants
open Foundation.ParticleGenerations
open Foundation.GrayCodeChirality
open StandardModel.CKMFromCube
open StandardModel.JarlskogInvariant
open SakharovFromLedger

/-! ## Part 1: The Particle Content

The effective number of relativistic degrees of freedom at the EW scale
uses the SM particle content. Provenance (see StandardModel.RelativisticDOF
for the full split): the gauge GROUP and generation COUNT are RS-derived;
the matter representations, minimal-neutrino convention, and the 7/8
thermal integral are imported standard physics. The single number 106.75
is the high-temperature value; the temperature dependence g_★(T) is
implemented in Cosmology.GStarThresholds. -/

/-- The SM relativistic DOF at T > T_EW: g_★ = 106.75.
    Standard high-temperature SM bookkeeping (bosons 28, fermions 90 with
    the 7/8 thermal weight; minimal-neutrino convention). Imported SM
    content with RS-sourced gauge group and generation count — NOT an
    independent RS prediction of a new number. Machine-checked assembly in
    StandardModel.RelativisticDOF (g_star_derived_eq); temperature-dependent
    version in Cosmology.GStarThresholds (g_star 200 = 427/4). -/
noncomputable def g_star : ℝ := 106.75

/-- The number of generations enters the DOF count. -/
theorem dof_includes_three_gen : face_pairs 3 = 3 := rfl

/-! ## Part 2: The Sphaleron Rate

Sphalerons are nonperturbative gauge field configurations that violate B+L;
their rate at T > T_EW scales as Γ_sph/V ∝ κ·α_W⁵·T⁴. The dimensionless
rate and its positivity are formalized in Cosmology.SphaleronRate
(`sphaleron_rate_dimensionless`, `kappa_sph`), and the Γ_sph/H ratio
scaffold in Cosmology.EWPhaseTransition. A previous version of this module
carried a `sphaleron_rate_structure : Prop := True` placeholder here; it
was vacuous and has been removed (the review was right to flag it). -/

/-! ## Part 3: The η_B Structural Formula (SCAFFOLD)

Combining the shape of the ingredients:

  η_B = c × J_CP / g_★

where c is a dimensionless constant that requires the detailed EW phase
transition dynamics (OPEN — not computed anywhere in this repository).

HONEST NUMERICS: with the repository's own J_CP ≈ 3×10⁻⁵ and g_★ = 106.75,
this structural value is ≈ 3×10⁻⁷ — roughly 500× larger than the observed
6.1×10⁻¹⁰. So `eta_B_structural` is NOT the prediction and is not used as
one; the theorems below prove only its SIGN (positive: matter exists,
inherited from J_CP > 0) and that it is < 1. The Planck-matched expression
φ⁻⁴⁴·(1−φ⁻⁸)² is a separate object (see module header). -/

/-- The structural η_B: proportional to J_CP / g_★.
    SCAFFOLD ONLY — numerically ≈ 3×10⁻⁷, about 500× the observed value,
    because the order-one-suppressed washout constant c is not derived.
    Used solely for the sign theorem (η_B > 0) and the smallness bound. -/
noncomputable def eta_B_structural : ℝ := jarlskog_structural / g_star

/-- η_B is positive: matter dominates over antimatter.
    This follows directly from J_CP > 0 and is the genuine derived content
    (the SIGN of the asymmetry, not its magnitude). -/
theorem eta_B_positive : eta_B_structural > 0 := by
  unfold eta_B_structural
  apply div_pos jarlskog_positive
  norm_num [g_star]

/-- η_B is small: the structural value is below 1.
    (A weak bound; the honest magnitude statement is in the module header.) -/
theorem eta_B_small : eta_B_structural < 1 := by
  unfold eta_B_structural
  rw [div_lt_one (by norm_num [g_star] : (0:ℝ) < g_star)]
  linarith [(cp_small_but_nonzero).2, show g_star = 106.75 from rfl]

/-! ## Part 4: The φ-Ladder Connection (HYPOTHESIS)

The observed η_B ≈ 6.1 × 10⁻¹⁰ is close to φ⁻⁴⁴ ≈ 6.376 × 10⁻¹⁰ (within
~4.5%; the prefactor (1−φ⁻⁸)² moves it into the Planck band — see
EtaBIntervalCert). This is an empirical rung match with a named falsifier,
not a theorem.

On the integer 44: it can be written as 4 × 11 (Gray-code flip count ×
torsion gap), as 45 − 1 (dimension gap D²(D+2) minus one), or as g_f/2 − 1
(half the fermionic DOF minus one). These are re-expressions of the SAME
integer, not independent derivations, and none of them is a mechanism that
forces the rung. The honest status: −44 is a HYPOTHESIS-grade rung
assignment whose support is the numerical match itself. The α⁻¹ seed 44π
uses the same integer; that is a shared numerological observation, not
independent evidence (see soul.mdc: the 44π seed is itself an
identification, not a derived coupling). -/

/-- The φ-rung exponent for the baryon asymmetry scale.
    φ⁴⁴ ≈ 1.568 × 10⁹, so φ⁻⁴⁴ ≈ 6.376 × 10⁻¹⁰.
    The observed η_B ≈ 6.1 × 10⁻¹⁰ is within ~4.5% (before the
    (1−φ⁻⁸)² prefactor). HYPOTHESIS-grade rung assignment. -/
def eta_B_rung : ℤ := -44

/-- The complementary φ-exponent 45 (the saturation threshold Θ_crit = φ⁴⁵
    in the full `reality` repository's extended framework; kept here as a
    bare integer definition). -/
def saturation_exponent : ℤ := 45

/-- Rung arithmetic: η_B rung (−44) plus the saturation exponent (45)
    equals 1, i.e. η_B ≈ φ/Θ_crit at the rung level.

    HONEST STATUS: this is exact integer arithmetic on two DEFINED rung
    assignments, each of which is a HYPOTHESIS-grade empirical match. The
    theorem proves the arithmetic relation between the two definitions,
    not a physical mechanism linking the two scales. Any interpretive
    reading of the −44/45 complementarity is a gloss on the arithmetic,
    falsifiable through either rung. -/
theorem eta_B_times_saturation :
    eta_B_rung + saturation_exponent = 1 := by
  simp [eta_B_rung, saturation_exponent]

/-! ## Part 5: The Connection Chain

The derivation chain from RCL to the SIGN of η_B:

  RCL → J unique → φ forced → 8-tick + D=3 → Q₃
    → Gray code (chiral, [4,2,2])
      → CKM (torsion overlap)
        → δ_CKM (Berry phase ≠ 0)
          → J_CP > 0 (Jarlskog)
            → Sakharov conditions (3 from ledger)
              → η_B > 0 (matter exists)  [THEOREM — the derived content]

The MAGNITUDE η_B ≈ φ⁻⁴⁴·(1−φ⁻⁸)² is a separate HYPOTHESIS-grade rung
match (Part 4), not the endpoint of this chain. -/

/-- The chain to the SIGN of the asymmetry is complete: from the Sakharov
    conditions + J_CP > 0, a positive baryon asymmetry follows.

    RS-derived ingredients in the chain:
    - 3 generations → from D = 3 (face_pairs)
    - chirality → from Gray code [0,1,3,2,6,7,5,4]
    - flip asymmetry → [4,2,2] from the specific Gray code path
    - torsion → {0, 11, 17} from CW filtration
    - J_CP → from Berry phase × torsion overlap
    - Sakharov → from ledger + J_CP + EW transition

    NOT in this chain: the magnitude (the −44 rung is HYPOTHESIS; the
    structural J_CP/g_★ scaffold is ~500× too large — see header). -/
theorem derivation_chain_complete :
    face_pairs 3 = 3 ∧                          -- 3 generations
    IsChiral grayFlipCounts ∧                    -- chirality
    jarlskog_structural > 0 ∧                    -- CP violation
    deltaB_per_sphaleron = 3 ∧                   -- B violation
    eta_B_structural > 0 :=                      -- matter exists (sign)
  ⟨rfl, cycle_is_chiral, jarlskog_positive, rfl, eta_B_positive⟩

/-! ## Part 6: Certificate -/

/-- Baryon asymmetry certificate: the SIGN chain (THEOREM) plus the rung
    arithmetic (HYPOTHESIS-grade assignments; see Part 4 docstrings).

    Parameterized over the UNDERIVED out-of-equilibrium proposition
    `EWFirstOrder` (see `SakharovFromLedger`): the certificate exists only
    conditionally on that named physical hypothesis. -/
structure BaryonAsymmetryCert (EWFirstOrder : Prop) where
  sakharov : SakharovConditions EWFirstOrder
  jarlskog_pos : jarlskog_structural > 0
  eta_pos : eta_B_structural > 0
  eta_small : eta_B_structural < 1
  phi_rung_connection : eta_B_rung + saturation_exponent = 1
  chain_complete : face_pairs 3 = 3 ∧ IsChiral grayFlipCounts ∧
                   jarlskog_structural > 0 ∧ deltaB_per_sphaleron = 3 ∧
                   eta_B_structural > 0

/-- The baryon asymmetry certificate, CONDITIONAL on the out-of-equilibrium
    hypothesis (not derived here). -/
def baryonAsymmetryCert {EWFirstOrder : Prop} (hEW : EWFirstOrder) :
    BaryonAsymmetryCert EWFirstOrder where
  sakharov := sakharov_from_RS hEW
  jarlskog_pos := jarlskog_positive
  eta_pos := eta_B_positive
  eta_small := eta_B_small
  phi_rung_connection := by simp [eta_B_rung, saturation_exponent]
  chain_complete := derivation_chain_complete

end BaryonAsymmetryDerivation
end Cosmology
end IndisputableMonolith
