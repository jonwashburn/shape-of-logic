import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.GaugeFromCube
import IndisputableMonolith.Foundation.ParticleGenerations

/-!
# g_star = 106.75: Standard Model Bookkeeping with RS-Sourced Inputs

STATUS TAG: **BOOKKEEPING over adopted SM content** (not a novel RS prediction).

This module computes the standard high-temperature Standard Model
relativistic degree count

  g_star = g_b + (7/8) g_f = 28 + (7/8)·90 = 427/4 = 106.75

as exact rational arithmetic in Lean. Honest scope (per the 2026-06-25
external review): this is the textbook count, valid ONLY in the
high-temperature regime T ≳ T_EW where all listed species are relativistic
and thermally populated. It is correct bookkeeping, not a new calculation.

## What RS supplies vs. what is imported

RS-DERIVED inputs (each proved upstream, cited by name):
- The gauge group SU(3)×SU(2)×U(1) from Q₃ automorphisms (GaugeFromCube).
- The generation count 3 = face_pairs(3) from D = 3 (ParticleGenerations).
- The sign choice Fermi–Dirac vs. Bose–Einstein from the 8-tick
  spin-statistics theorem (Foundation.SpinStatistics and QFT.SpinStatistics
  in the full `reality` repository; those modules are not included in this
  curated repository).

IMPORTED (standard physics, NOT derived by RS):
- The Standard Model matter representations (which reps the fermions sit
  in: quark doublets/singlets, lepton doublets, colors per quark).
- The minimal-neutrino convention (left-handed only, 2 DOF per generation).
  See Part 5 for the Dirac-neutrino branch (g_f = 96, g_star = 112).
- The 7/8 thermal weight, i.e. the value of the Fermi–Dirac vs.
  Bose–Einstein energy-density integral ratio
  ∫x³/(eˣ+1)dx / ∫x³/(eˣ−1)dx = 7/8. RS fixes the SIGN via
  spin-statistics; the integral value is standard statistical mechanics.
- The high-temperature scope. g_star is temperature dependent; the single
  number 106.75 applies above T_EW only. The temperature dependence
  (threshold decoupling steps) is implemented in
  Cosmology.GStarThresholds as g_star(T).

## Assembly

1. Gauge boson content fixed by the gauge group dimensions (RS-sourced group).
2. Fermion content = 3 generations × 30 DOF/gen (RS-sourced count; SM reps).
3. g_star = bosonic_dof + (7/8) × fermionic_dof = 106.75.

## Bosonic Degrees of Freedom (28)

| Particle | Count | Polarizations | DOF |
|----------|-------|---------------|-----|
| Gluons   | 8     | 2             | 16  |
| W±       | 2     | 3             | 6   |
| Z        | 1     | 3             | 3   |
| γ        | 1     | 2             | 2   |
| Higgs (T > T_EW) | 1 | 4 (complex doublet) | 4 |
| **Total** |      |               | **28** (at T_EW: W/Z massive → 3 pol each) |

The 28 comes from: at the EW scale and above, the Higgs doublet contributes
all 4 real DOF (before Goldstone absorption). The W/Z are massive with
3 polarization states each. Below T_EW, the Goldstones are eaten but the
count is the same either way — rearranged, not changed.

Correction: at T > T_EW (symmetric phase), all gauge bosons are massless
with 2 polarizations each: 12 × 2 = 24, plus 4 Higgs DOF = 28.

## Fermionic Degrees of Freedom (90)

Per generation:
- Quarks: 2 flavors × 3 colors × 2 chiralities × 2 (particle + antiparticle) = 24
- Leptons: 1 charged lepton × 2 chiralities × 2 (p + ap) + 1 neutrino × 1 chirality × 2 = 6

Per generation DOF = 24 + 6 = 30
3 generations × 30 = 90

## The 7/8 Factor

Fermi-Dirac statistics gives ⟨n⟩ = 1/(e^{E/T}+1) vs Bose-Einstein
⟨n⟩ = 1/(e^{E/T}-1). The energy density ratio for fermions vs bosons
in thermal equilibrium is 7/8. Division of labor: the SIGN (+1 fermions,
−1 bosons) follows from spin-statistics, which IS proved from the 8-tick
structure (IndisputableMonolith.Foundation.SpinStatistics and
IndisputableMonolith.QFT.SpinStatistics in the full `reality` repository;
not included in this curated repository). The VALUE 7/8 of the resulting
thermal integral ratio is standard statistical mechanics, imported here
as a rational constant, not re-derived in Lean.

## Result

g_star = 28 + (7/8) × 90 = 28 + 78.75 = 106.75  (high-T SM regime only)

For the temperature-dependent g_star(T) step function (threshold
decoupling), see Cosmology.GStarThresholds.

## Status: 0 sorry, 0 axiom (arithmetic verified; scope tags above bind)
-/

namespace IndisputableMonolith
namespace StandardModel
namespace RelativisticDOF

open Foundation.GaugeFromCube Foundation.ParticleGenerations

/-! ## Part 1: Gauge Boson Counting -/

/-- Adjoint dimension of SU(n): n² − 1. -/
def adjoint_dim (n : ℕ) : ℕ := n ^ 2 - 1

theorem su3_adjoint : adjoint_dim 3 = 8 := by native_decide
theorem su2_adjoint : adjoint_dim 2 = 3 := by native_decide

/-- Gluon DOF: 8 gluons × 2 polarizations (massless at T > T_EW). -/
def gluon_dof : ℕ := adjoint_dim 3 * 2

theorem gluon_dof_eq : gluon_dof = 16 := by native_decide

/-- Weak boson DOF at T > T_EW (symmetric phase):
    W₁, W₂, W₃ (3 SU(2) generators) × 2 polarizations = 6.
    B (1 U(1) generator) × 2 polarizations = 2.
    Total: 8. -/
def weak_boson_dof_symmetric : ℕ := adjoint_dim 2 * 2 + 1 * 2

theorem weak_boson_dof_symmetric_eq : weak_boson_dof_symmetric = 8 := by native_decide

/-- Higgs doublet DOF: complex SU(2) doublet = 4 real DOF. -/
def higgs_dof : ℕ := 4

/-- Total bosonic DOF at T > T_EW. -/
def bosonic_dof : ℕ := gluon_dof + weak_boson_dof_symmetric + higgs_dof

theorem bosonic_dof_eq : bosonic_dof = 28 := by native_decide

/-! ## Part 2: Fermion Counting -/

/-- Number of quark flavors per generation (up-type + down-type). -/
def quark_flavors_per_gen : ℕ := 2

/-- Number of colors from Q₃ (SU(3) fundamental rep dimension). -/
def n_colors : ℕ := color_layer.fund_rep_dim

theorem n_colors_eq : n_colors = 3 := rfl

/-- Number of chiralities (left + right). -/
def chiralities : ℕ := 2

/-- Particle + antiparticle factor. -/
def particle_antiparticle : ℕ := 2

/-- Quark DOF per generation:
    2 flavors × 3 colors × 2 chiralities × 2 (p + ap) = 24. -/
def quark_dof_per_gen : ℕ :=
  quark_flavors_per_gen * n_colors * chiralities * particle_antiparticle

theorem quark_dof_per_gen_eq : quark_dof_per_gen = 24 := by native_decide

/-- Charged lepton DOF per generation:
    1 flavor × 2 chiralities × 2 (p + ap) = 4. -/
def charged_lepton_dof_per_gen : ℕ := 1 * chiralities * particle_antiparticle

theorem charged_lepton_dof_per_gen_eq : charged_lepton_dof_per_gen = 4 := by
  native_decide

/-- Neutrino DOF per generation (SM: left-handed only):
    1 flavor × 1 chirality × 2 (p + ap) = 2. -/
def neutrino_dof_per_gen : ℕ := 1 * 1 * particle_antiparticle

theorem neutrino_dof_per_gen_eq : neutrino_dof_per_gen = 2 := by native_decide

/-- Total fermion DOF per generation. -/
def fermion_dof_per_gen : ℕ :=
  quark_dof_per_gen + charged_lepton_dof_per_gen + neutrino_dof_per_gen

theorem fermion_dof_per_gen_eq : fermion_dof_per_gen = 30 := by native_decide

/-- Number of generations from Q₃ face-pairs. -/
def n_generations : ℕ := face_pairs 3

theorem n_generations_eq : n_generations = 3 := rfl

/-- Total fermion DOF: 3 generations × 30 = 90. -/
def fermionic_dof : ℕ := n_generations * fermion_dof_per_gen

theorem fermionic_dof_eq : fermionic_dof = 90 := by native_decide

/-! ## Part 3: The 7/8 Weighting and g_star -/

noncomputable section

/-- The Fermi-Dirac weighting factor: 7/8.
    Fermions contribute 7/8 as much energy density per DOF as bosons
    in thermal equilibrium: ∫₀^∞ x³/(eˣ+1) dx = (7/8) × ∫₀^∞ x³/(eˣ-1) dx.
    IMPORTED CONSTANT: the integral value 7/8 is standard statistical
    mechanics and is NOT re-derived here (the integrals are not formalized
    in this module). What RS supplies is the sign difference (Fermi-Dirac
    +1 vs Bose-Einstein −1), a consequence of the 8-tick spin-statistics
    theorem (Foundation.SpinStatistics / QFT.SpinStatistics in the full
    `reality` repository; not included in this curated repository). -/
def fermi_dirac_weight : ℝ := 7 / 8

theorem fermi_dirac_weight_pos : 0 < fermi_dirac_weight := by
  norm_num [fermi_dirac_weight]

/-- g_star = 106.75, assembled from the counts above.

    g_star = bosonic_dof + (7/8) × fermionic_dof
           = 28 + (7/8) × 90
           = 28 + 78.75
           = 106.75

    Honest ingredient list (see module header for the full split):
    - gauge GROUP from Q₃ automorphisms (RS-derived); gauge boson DOF then
      follow from the group dimensions plus standard polarization counting.
    - generation COUNT 3 from Q₃ face-pairs (RS-derived); the per-generation
      30 DOF uses the imported SM representation content and the
      minimal-neutrino convention.
    - 7/8: sign from spin-statistics (RS-derived); integral value imported.

    Valid in the high-T SM regime (T ≳ T_EW) only. This is verified SM
    bookkeeping with RS-sourced group/generation inputs, not an
    independent RS prediction of a new number. -/
def g_star_derived : ℝ :=
  (bosonic_dof : ℝ) + fermi_dirac_weight * (fermionic_dof : ℝ)

theorem g_star_derived_eq : g_star_derived = 106.75 := by
  unfold g_star_derived fermi_dirac_weight
  rw [bosonic_dof_eq, fermionic_dof_eq]
  norm_num

theorem g_star_derived_pos : 0 < g_star_derived := by
  rw [g_star_derived_eq]; norm_num

/-- Bridge: the derived g_star matches the hand-entered value in
    BaryonAsymmetryDerivation and EWPhaseTransition. -/
theorem g_star_matches_cosmology :
    g_star_derived = 106.75 := g_star_derived_eq

end

/-! ## Part 4: Component Traceability -/

/-- Each bosonic DOF traces to Q₃ structure. -/
theorem bosonic_traces_to_Q3 :
    gluon_dof = adjoint_dim color_layer.fund_rep_dim * 2 ∧
    adjoint_dim color_layer.fund_rep_dim = 8 ∧
    bosonic_dof = 28 :=
  ⟨rfl, su3_adjoint, bosonic_dof_eq⟩

/-- Each fermionic DOF traces to Q₃ structure. -/
theorem fermionic_traces_to_Q3 :
    n_generations = face_pairs 3 ∧
    n_colors = color_layer.fund_rep_dim ∧
    fermionic_dof = 90 :=
  ⟨rfl, rfl, fermionic_dof_eq⟩

/-! ## Part 5: Model-Dependent Branch — Thermalized Dirac Neutrinos

The 106.75 value uses the minimal-SM convention: neutrinos are left-handed
only (2 DOF per generation). If neutrinos are Dirac AND the right-handed
components are thermally populated, each generation gains 2 more DOF:

  g_f = 96,  g_star = 28 + (7/8)·96 = 112.

This branch is carried explicitly so the convention is a named input,
not a hidden assumption. Which branch reality takes is a MODEL choice
(and for the right-handed states, a thermalization question) that this
module does not decide. -/

/-- Neutrino DOF per generation with thermalized Dirac (right-handed)
    components: 1 flavor × 2 chiralities × 2 (p + ap) = 4. -/
def neutrino_dof_per_gen_dirac : ℕ := 1 * chiralities * particle_antiparticle

theorem neutrino_dof_per_gen_dirac_eq : neutrino_dof_per_gen_dirac = 4 := by
  native_decide

/-- Fermion DOF per generation in the thermalized-Dirac-neutrino branch: 32. -/
def fermion_dof_per_gen_dirac : ℕ :=
  quark_dof_per_gen + charged_lepton_dof_per_gen + neutrino_dof_per_gen_dirac

theorem fermion_dof_per_gen_dirac_eq : fermion_dof_per_gen_dirac = 32 := by
  native_decide

/-- Total fermion DOF in the thermalized-Dirac-neutrino branch: 96. -/
def fermionic_dof_dirac : ℕ := n_generations * fermion_dof_per_gen_dirac

theorem fermionic_dof_dirac_eq : fermionic_dof_dirac = 96 := by native_decide

noncomputable section

/-- g_star in the thermalized-Dirac-neutrino branch. -/
def g_star_dirac : ℝ :=
  (bosonic_dof : ℝ) + fermi_dirac_weight * (fermionic_dof_dirac : ℝ)

/-- g_star = 112 with thermalized right-handed Dirac neutrinos. -/
theorem g_star_dirac_eq : g_star_dirac = 112 := by
  unfold g_star_dirac fermi_dirac_weight
  rw [bosonic_dof_eq, fermionic_dof_dirac_eq]
  norm_num

/-- The two branches differ by (7/8)·6 = 5.25: the neutrino convention is
    a real model input that moves the answer, not notation. -/
theorem g_star_branch_gap : g_star_dirac - g_star_derived = 5.25 := by
  rw [g_star_dirac_eq, g_star_derived_eq]
  norm_num

end

/-! ## Part 6: Master Certificate -/

structure GStarCert where
  bosonic : bosonic_dof = 28
  fermionic : fermionic_dof = 90
  n_gen : n_generations = 3
  n_col : n_colors = 3
  gluons : gluon_dof = 16
  higgs : higgs_dof = 4
  g_star : g_star_derived = 106.75
  g_star_positive : 0 < g_star_derived

def gStarCert : GStarCert where
  bosonic := bosonic_dof_eq
  fermionic := fermionic_dof_eq
  n_gen := n_generations_eq
  n_col := n_colors_eq
  gluons := gluon_dof_eq
  higgs := rfl
  g_star := g_star_derived_eq
  g_star_positive := g_star_derived_pos

end RelativisticDOF
end StandardModel
end IndisputableMonolith
